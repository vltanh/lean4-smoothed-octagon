"""Hash-consed expression DAG mirroring SmoothedOctagon.Interval.IExpr, with
natural / slope evaluators that mirror IExpr.evalR / IExpr.evalS exactly, and a Lean emitter."""
from fractions import Fraction
import fx

import os
NEWSLOPE = os.environ.get('NEWSLOPE', '1') == '1'
_nodes = []          # id -> node tuple
_index = {}          # node tuple -> id
names = {}           # id -> lean name (named intermediates)


def mk(t):
    i = _index.get(t)
    if i is None:
        i = len(_nodes)
        _nodes.append(t)
        _index[t] = i
    return E(i)


class E:
    __slots__ = ('i',)

    def __init__(self, i):
        self.i = i

    @property
    def t(self):
        return _nodes[self.i]

    def const_value(self):
        t = self.t
        if t[0] == 'const':
            return Fraction(t[1], t[2])
        return None

    def __add__(self, o):
        o = lift(o)
        a, b = self.const_value(), o.const_value()
        if a is not None and b is not None:
            return C(a + b)
        if b == 0:
            return self
        if a == 0:
            return o
        return mk(('add', self.i, o.i))

    __radd__ = lambda self, o: lift(o) + self

    def __sub__(self, o):
        o = lift(o)
        a, b = self.const_value(), o.const_value()
        if a is not None and b is not None:
            return C(a - b)
        if b == 0:
            return self
        if a == 0:
            return -o
        return mk(('sub', self.i, o.i))

    __rsub__ = lambda self, o: lift(o) - self

    def __neg__(self):
        a = self.const_value()
        if a is not None:
            return C(-a)
        return mk(('neg', self.i))

    def __mul__(self, o):
        o = lift(o)
        a, b = self.const_value(), o.const_value()
        if a is not None and b is not None:
            return C(a * b)
        if a == 0 or b == 0:
            return C(0)
        if b == 1:
            return self
        if a == 1:
            return o
        return mk(('mul', self.i, o.i))

    __rmul__ = lambda self, o: lift(o) * self

    def __truediv__(self, o):
        o = lift(o)
        a, b = self.const_value(), o.const_value()
        if a is not None and b is not None and b != 0:
            return C(a / b)
        if a == 0:
            return C(0)
        if b == 1:
            return self
        return mk(('div', self.i, o.i))

    __rtruediv__ = lambda self, o: lift(o) / self

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        a = self.const_value()
        if a is not None:
            return C(a ** n)
        if n == 1:
            return self
        if n == 0:
            return C(1)
        return mk(('pow', self.i, n))


def C(q):
    q = Fraction(q)
    return mk(('const', q.numerator, q.denominator))


def lift(o):
    if isinstance(o, E):
        return o
    return C(o)


def var(i):
    return mk(('var', i))


def sqrt(a):
    return mk(('sqrt', a.i))


def log(a):
    a0 = a.const_value()
    if a0 == 1:
        return C(0)
    return mk(('log', a.i))


def hlog(a):
    return mk(('hlog', a.i))


def atan(a):
    return mk(('atan', a.i))


def logdiv(a):
    return mk(('logdiv', a.i))


def name(nm, e):
    if e.i not in names:
        names[e.i] = nm
    return e


# ------------------------------------------------------------------ evaluation

def children(t):
    k = t[0]
    if k in ('add', 'sub', 'mul', 'div'):
        return (t[1], t[2])
    if k in ('neg', 'pow', 'sqrt', 'log', 'hlog', 'atan', 'logdiv'):
        return (t[1],)
    return ()


def evalR(B, i, memo):
    """Mirror of IExpr.evalR; memo maps node id -> result (None = domain failure)."""
    if i in memo:
        return memo[i]
    t = _nodes[i]
    k = t[0]
    r = None
    if k == 'var':
        r = B[t[1]] if t[1] < len(B) else None
    elif k == 'const':
        r = fx.ofRat(t[1], t[2])
    elif k in ('add', 'sub', 'mul', 'div'):
        x = evalR(B, t[1], memo)
        if x is not None:
            y = evalR(B, t[2], memo)
            if y is not None:
                if k == 'add':
                    r = fx.add(x, y)
                elif k == 'sub':
                    r = fx.sub(x, y)
                elif k == 'mul':
                    r = fx.mul(x, y)
                else:
                    yi = fx.inv(y)
                    r = None if yi is None else fx.mul(x, yi)
    else:
        x = evalR(B, t[1], memo)
        if x is not None:
            if k == 'neg':
                r = fx.neg(x)
            elif k == 'pow':
                r = fx.powI(x, t[2])
            elif k == 'sqrt':
                r = fx.sqrtI(x)
            elif k == 'log':
                r = fx.logI(x)
            elif k == 'hlog':
                r = fx.hlogI(x)
            elif k == 'atan':
                r = fx.atanI(x)
            elif k == 'logdiv':
                r = fx.logDivI(x)
    memo[i] = r
    return r


# slopes: (r, v, g) with g a list of intervals

def gadd(xs, ys):
    if not xs:
        return ys
    if not ys:
        return xs
    out = [fx.add(x, y) for x, y in zip(xs, ys)]
    if len(xs) > len(ys):
        out += xs[len(ys):]
    elif len(ys) > len(xs):
        out += ys[len(xs):]
    return out


def s_const(k):
    return (k, k, [])


def s_add(s, t):
    return (fx.add(s[0], t[0]), fx.add(s[1], t[1]), gadd(s[2], t[2]))


def s_neg(s):
    return (fx.neg(s[0]), fx.neg(s[1]), [fx.neg(a) for a in s[2]])


def s_sub(s, t):
    return s_add(s, s_neg(t))


def s_mul(s, t):
    return (fx.mul(s[0], t[0]), fx.mul(s[1], t[1]),
            gadd([fx.mul(a, t[0]) for a in s[2]], [fx.mul(s[1], b) for b in t[2]]))


def s_sq(s):
    vr = fx.add(s[1], s[0])
    return (fx.sq(s[0]), fx.sq(s[1]), [fx.mul(a, vr) for a in s[2]])


def s_inv(s):
    ri = fx.inv(s[0])
    if ri is None:
        return None
    vi = fx.inv(s[1])
    if vi is None:
        return None
    return (ri, vi, [fx.neg(fx.mul(fx.mul(a, ri), vi)) for a in s[2]])


def s_pow(s, n):
    if n == 0:
        return s_const(fx.ONE)
    if n == 1:
        return s
    if n == 2:
        return s_sq(s)
    return s_mul(s_pow(s, n - 1), s)


def s_hornerS(x, cs):
    acc = s_const(fx.ZERO)
    for c in reversed(cs):
        acc = s_add(s_const(c), s_mul(x, acc))
    return acc


def s_logdiv(s):
    if not (s[0][0] >= 1):
        return None
    W = s_inv(s_add(s, s_const(fx.ONE)))
    if W is None:
        return None
    T = s_sub(s_const(fx.ONE), s_scale(2, W))
    T2 = s_sq(T)
    tau = T2[0][1]
    if not (tau + 1 <= fx.U):
        return None
    d = fx.inv(fx.sub(fx.ONE, fx.point(tau)))
    if d is None:
        return None
    tail = fx.mul(fx.pow24(fx.point(tau)), d)
    P = s_hornerS(T2, fx.LD24)
    return s_mul(s_sub(s_const(fx.ONE), T), s_add(P, s_const((0, tail[1]))))


def s_atan(s):
    a = fx.atanI(s[0]); b = fx.atanI(s[1])
    if a is None or b is None:
        return None
    H = (min(s[0][0], s[1][0]), max(s[0][1], s[1][1]))
    D = fx.inv(fx.add(fx.ONE, fx.sq(H)))
    if D is None:
        return None
    return (a, b, [fx.mul(g, D) for g in s[2]])


def s_logdiv8(s):
    if not (s[0][0] >= 1):
        return None
    W = s_inv(s_add(s, s_const(fx.ONE)))
    if W is None:
        return None
    T = s_sub(s_const(fx.ONE), s_scale(2, W))
    T2 = s_sq(T)
    tau = T2[0][1]
    if not (tau + 1 <= fx.U):
        return None
    d = fx.inv(fx.sub(fx.ONE, fx.point(tau)))
    if d is None:
        return None
    tail = fx.mul(fx.pow8(fx.point(tau)), d)
    P = s_hornerS(T2, fx.LD8)
    return s_mul(s_sub(s_const(fx.ONE), T), s_add(P, s_const((0, tail[1]))))


def s_logdivQ(s):
    if not (s[0][0] >= 1):
        return None
    s1 = s_sqrt(s)
    s2 = s_sqrt(s1)
    L = s_logdiv8(s2)
    if L is None:
        return None
    i1 = s_inv(s_add(s_const(fx.ONE), s1))
    if i1 is None:
        return None
    i2 = s_inv(s_add(s_const(fx.ONE), s2))
    if i2 is None:
        return None
    return s_mul(s_mul(L, s_scale(2, i2)), s_scale(2, i1))


def s_sqrt(s):
    R, V = s[0], s[1]
    sr, sv = fx.sqrtI(R), fx.sqrtI(V)
    if R[0] >= 0 and V[0] >= 0:
        w = fx.inv(fx.add(sr, sv))
        if w is not None:
            return (sr, sv, [fx.mul(a, w) for a in s[2]])
    return (sr, sr, [])


def s_scale(w, s):
    return (fx.smul(w, s[0]), fx.smul(w, s[1]), [fx.smul(w, a) for a in s[2]])


def evalS(B, i, memo):
    if i in memo:
        return memo[i]
    t = _nodes[i]
    k = t[0]
    r = None
    if k == 'var':
        j = t[1]
        if j < len(B):
            b = B[j]
            r = (b, fx.point(fx.mid(b)), [fx.ZERO] * j + [fx.ONE])
    elif k == 'const':
        r = s_const(fx.ofRat(t[1], t[2]))
    elif k in ('add', 'sub', 'mul', 'div'):
        x = evalS(B, t[1], memo)
        if x is not None:
            y = evalS(B, t[2], memo)
            if y is not None:
                if k == 'add':
                    r = s_add(x, y)
                elif k == 'sub':
                    r = s_sub(x, y)
                elif k == 'mul':
                    r = s_mul(x, y)
                else:
                    yi = s_inv(y)
                    r = None if yi is None else s_mul(x, yi)
    else:
        x = evalS(B, t[1], memo)
        if x is not None:
            if k == 'neg':
                r = s_neg(x)
            elif k == 'pow':
                r = s_pow(x, t[2])
            elif k == 'sqrt':
                r = s_sqrt(x) if NEWSLOPE else (fx.sqrtI(x[0]), fx.sqrtI(x[0]), [])
            elif k == 'log':
                v = fx.logI(x[0])
                r = None if v is None else (v, v, [])
            elif k == 'logdiv' and NEWSLOPE:
                r = s_logdivQ(x)
            elif k == 'atan' and NEWSLOPE:
                r = s_atan(x)
            elif k in ('hlog', 'atan', 'logdiv'):
                v = {'hlog': fx.hlogI, 'atan': fx.atanI, 'logdiv': fx.logDivI}[k](x[0])
                r = None if v is None else (v, v, [])
    memo[i] = r
    return r


def lin(gs, B):
    acc = fx.ZERO
    terms = []
    for j, b in enumerate(B):
        g = gs[j] if j < len(gs) else fx.ZERO
        terms.append(fx.mul(g, fx.sub(b, fx.point(fx.mid(b)))))
    # Lean: lin gs (b :: bs) = term0.add (lin gs.tail bs), lin _ [] = zero
    for tm in reversed(terms):
        acc = fx.add(tm, acc)
    return acc


def bound(B, s):
    return fx.add(s[1], lin(s[2], B))


def slope_hi(B, s):
    """zmin (bound B s).hi s.r.hi"""
    return min(bound(B, s)[1], s[0][1])


# ------------------------------------------------------------------ DAG utilities

def subdag(roots):
    seen = set()
    order = []
    stack = [(r, False) for r in roots]
    while stack:
        i, done = stack.pop()
        if done:
            order.append(i)
            continue
        if i in seen:
            continue
        seen.add(i)
        stack.append((i, True))
        for c in children(_nodes[i]):
            if c not in seen:
                stack.append((c, False))
    return order


# ------------------------------------------------------------------ Lean emission

def lean_term(i, defname, depth=0):
    t = _nodes[i]
    k = t[0]
    if k == 'var':
        return f'(.var {t[1]})'
    if k == 'const':
        n, d = t[1], t[2]
        ns = f'({n})' if n < 0 else str(n)
        return f'(.const {ns} {d})'
    def sub_(c):
        return defname[c] if c in defname else lean_term(c, defname, depth + 1)
    if k in ('add', 'sub', 'mul', 'div'):
        return f'(.{k} {sub_(t[1])} {sub_(t[2])})'
    if k == 'pow':
        return f'(.pow {sub_(t[1])} {t[2]})'
    return f'(.{k} {sub_(t[1])})'


def emit_lean(roots, prefix, root_names):
    """Emit `def`s for named or shared nodes of the DAG under roots. Returns (text, defname)."""
    order = subdag(roots)
    uses = {}
    for i in order:
        for c in children(_nodes[i]):
            uses[c] = uses.get(c, 0) + 1
    defname = {}
    for r, nm in zip(roots, root_names):
        defname[r] = f'{prefix}{nm}'
    cnt = 0
    for i in order:
        if i in defname:
            continue
        t = _nodes[i]
        if t[0] in ('var', 'const'):
            continue
        if i in names:
            defname[i] = f'{prefix}{names[i]}'
        elif uses.get(i, 0) >= 2:
            cnt += 1
            defname[i] = f'{prefix}t{cnt}'
    lines = []
    for i in order:
        if i in defname:
            body = lean_term(i, {k: v for k, v in defname.items() if k != i})
            lines.append(f'def {defname[i]} : IExpr := {body}')
    return '\n'.join(lines), defname
