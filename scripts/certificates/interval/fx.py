"""Exact mirror of SmoothedOctagon/Interval/{Ival,Special,Expr,Check}.lean arithmetic.

An interval is a tuple (lo, hi) of Python ints, read as [lo/2^P, hi/2^P].
Every function mirrors the Lean definition of the same name operation by operation.
"""
P = 60
U = 1 << P
UNIT2 = 1 << (2 * P)
ZERO = (0, 0)
ONE = (U, U)


def fl(x):
    return x >> P


def ce(x):
    return -((-x) >> P)


def point(n):
    return (n, n)


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def neg(x):
    return (-x[1], -x[0])


def sub(x, y):
    return (x[0] - y[1], x[1] - y[0])


def smul(w, x):
    return (w * x[0], w * x[1])


def mulRaw(a, b, c, d):
    if a >= 0:
        if c >= 0:
            return (a * c, b * d)
        if d <= 0:
            return (b * c, a * d)
        return (b * c, b * d)
    if b <= 0:
        if c >= 0:
            return (a * d, b * c)
        if d <= 0:
            return (b * d, a * c)
        return (a * d, a * c)
    if c >= 0:
        return (a * d, b * d)
    if d <= 0:
        return (b * c, a * c)
    return (min(a * d, b * c), max(a * c, b * d))


def mul(x, y):
    p = mulRaw(x[0], x[1], y[0], y[1])
    return (fl(p[0]), ce(p[1]))


def sq(x):
    lo, hi = x
    if lo >= 0:
        return (fl(lo * lo), ce(hi * hi))
    if hi <= 0:
        return (fl(hi * hi), ce(lo * lo))
    return (0, ce(max(lo * lo, hi * hi)))


def ndiv(a, b):  # Nat division, n/0 = 0
    return 0 if b == 0 else a // b


def inv(x):
    lo, hi = x
    if lo >= 1 and hi >= 0:
        l = lo - 1
        h = hi
        return (ndiv(UNIT2, h), ndiv(UNIT2 + l, l + 1))
    if lo < 0 and hi < 0:
        l = -lo - 1
        h = -hi - 1
        return (-ndiv(UNIT2 + h, h + 1), -ndiv(UNIT2, l + 1))
    return None


def zdiv(a, d):  # Int.ediv by a natural d (d = 0 gives 0)
    return 0 if d == 0 else a // d


def ofRat(n, d):
    return (zdiv(n * U, d), -zdiv(-n * U, d))


def powI(x, n):
    if n == 0:
        return ONE
    if n == 1:
        return x
    if n == 2:
        return sq(x)
    return mul(powI(x, n - 1), x)


def mid(x):
    return (x[0] + x[1]) >> 1


# ---------------------------------------------------------------- special functions

def log2n(n):
    return n.bit_length() - 1 if n > 0 else 0


def isqrtIter(fuel, n, g):
    while fuel > 0:
        g2 = (g + ndiv(n, g)) // 2
        if g <= g2:
            return g
        g = g2
        fuel -= 1
    return g


def isqrt(n):
    return isqrtIter(64, n, 2 ** (log2n(n) // 2 + 1))


def sqrtLo(n):
    s = isqrt(n)
    return s if s * s <= n else 0


def sqrtHi(n):
    s = isqrt(n)
    if n <= s * s:
        return s
    if n <= (s + 1) * (s + 1):
        return s + 1
    return n + 1


def toNat0(n):
    return n if n >= 0 else 0


def sqrtI(x):
    return (sqrtLo(toNat0(x[0]) * U), sqrtHi(toNat0(x[1]) * U))


def hornerI(x, cs):
    acc = ZERO
    for c in reversed(cs):
        acc = add(c, mul(x, acc))
    return acc


def zsmul(e, x):
    if e >= 0:
        return smul(e, x)
    return neg(smul(-e, x))


def ratI(n, d):
    return (ndiv(n * U, d), ndiv(n * U + max(d - 1, 0), d))


ATANH = [ofRat(1, 2 * k + 1) for k in range(20)]


def logT(T):
    S = mul(T, hornerI(sq(T), ATANH))
    return (2 * S[0], 2 * S[1] + 1)


LOG2 = logT(ofRat(1, 3))


def logPt(m):
    k = log2n(m)
    pk = 1 << k
    return add(logT(ratI(max(m - pk, 0), m + pk)), zsmul(k - P, LOG2))


def logI(x):
    lo, hi = x
    if lo >= 1 and hi >= 0:
        return (logPt(lo)[0], logPt(hi)[1])
    return None


HC = [ofRat(1 if k % 2 == 0 else -1, k + 3) for k in range(32)]

_hcache = {}


def hPt(m):
    r = _hcache.get(m)
    if r is not None or m in _hcache:
        return r
    if 4 * m <= U:
        S = hornerI(point(m), HC)
        r = (S[0] - 1, S[1] + 1)
    else:
        Z = point(m)
        N = add(sub(logPt(U + m), Z), mul(sq(Z), ofRat(1, 2)))
        w = inv(mul(sq(Z), Z))
        r = None if w is None else mul(N, w)
    if len(_hcache) > 200000:
        _hcache.clear()
    _hcache[m] = r
    return r


def hlogI(x):
    lo, hi = x
    if lo >= 0 and hi >= 0:
        a = hPt(hi)
        b = hPt(lo)
        if a is None or b is None:
            return None
        return (a[0], b[1])
    return None


# ---------------------------------------------------------------- logDiv and arctan (Trig.lean)

LDC = [ofRat(1, 2 * k + 1) for k in range(40)]


def pow40(x):
    x2 = sq(x); x4 = sq(x2); x5 = mul(x4, x); x10 = sq(x5); x20 = sq(x10)
    return sq(x20)


def logDivI(x):
    lo, hi = x
    if lo >= 1:
        w = inv(add(x, ONE))
        if w is None:
            return None
        T = sub(ONE, smul(2, w))
        T2 = sq(T)
        if T2[1] + 1 <= U:
            tau = point(T2[1])
            d = inv(sub(ONE, tau))
            if d is None:
                return None
            tail = mul(pow40(tau), d)
            return mul(sub(ONE, T), add(hornerI(T2, LDC), (0, tail[1])))
        return None
    return None


ATC = [ofRat(1 if k % 2 == 0 else -1, 2 * k + 1) for k in range(26)]


def halfI(Y):
    w = inv(add(ONE, sqrtI(add(ONE, sq(Y)))))
    return None if w is None else mul(Y, w)


def atanSmall(Y):
    Y2 = sq(Y)
    if 10000 * Y2[1] <= 1764 * U:
        S = mul(Y, hornerI(Y2, ATC))
        return (S[0] - 1, S[1] + 1)
    return None


_acache = {}


def atanPt(m):
    if m in _acache:
        return _acache[m]
    r = None
    y1 = halfI(point(m))
    if y1 is not None:
        y2 = halfI(y1)
        if y2 is not None:
            s = atanSmall(y2)
            if s is not None:
                r = smul(4, s)
    if len(_acache) > 200000:
        _acache.clear()
    _acache[m] = r
    return r


def atanI(x):
    a = atanPt(x[0]); b = atanPt(x[1])
    if a is None or b is None:
        return None
    return (a[0], b[1])


LD24 = [ofRat(1, 2 * k + 1) for k in range(24)]


def pow24(x):
    x2 = sq(x); x3 = mul(x2, x); x6 = sq(x3); x12 = sq(x6)
    return sq(x12)


LD8 = [ofRat(1, 2 * k + 1) for k in range(8)]


def pow8(x):
    return sq(sq(sq(x)))
