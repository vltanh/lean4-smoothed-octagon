"""Branch and bound with the Lean evaluator's exact arithmetic (fx/expr mirrors).
Produces a certificate tree (nested tuples) mirroring SmoothedOctagon.Interval.Cert:
  ('split', j, L, R) | ('cut', j, p, L, R) | ('R', i) | ('S', [(i, w), ...])
"""
import sys, time, pickle, os
import fx, expr

SCALE = None  # axis scale function


class Problem:
    def __init__(self, residuals, names, scales, lp=False, maxdepth=60):
        self.res = [r.i for r in residuals]
        self.names = names
        self.cost = [len(expr.subdag([i])) for i in self.res]
        self.order = sorted(range(len(self.res)), key=lambda k: self.cost[k])
        self.scales = scales
        self.lp = lp
        self.maxdepth = maxdepth
        self.last_slopes = None

    def judge(self, B):
        self.last_slopes = None
        memo = {}
        for k in self.order:
            r = expr.evalR(B, self.res[k], memo)
            if r is not None and r[1] < 0:
                return ('R', k)
        memoS = {}
        slopes = {}
        for k in self.order:
            s = expr.evalS(B, self.res[k], memoS)
            slopes[k] = s
            if s is not None and expr.slope_hi(B, s) < 0:
                return ('S', [(k, 1)])
        self.last_slopes = slopes
        if self.lp:
            w = lp_combo(B, slopes)
            if w is not None:
                return ('S', w)
        return None

    def find_cut(self, B):
        """C++-style contraction: a cut whose outer slab is excluded by a cheap residual."""
        if not getattr(self, 'contractors', None):
            return None
        best = None
        for (k, j, side, bound) in self.contractors:
            try:
                bnd = bound([(lo / fx.U, hi / fx.U) for lo, hi in B])
            except (ZeroDivisionError, ValueError):
                continue
            if bnd is None:
                continue
            lo, hi = B[j]
            w = hi - lo
            if w <= 0:
                continue
            p = int(bnd * fx.U) + (1 if side == 'hi' else -1) * max(16, w >> 12)
            for attempt in range(4):
                if not (lo < p < hi):
                    break
                frac = (hi - p) / w if side == 'hi' else (p - lo) / w
                if frac < 0.02:
                    break
                slab = list(B); slab[j] = (p, hi) if side == 'hi' else (lo, p)
                r = expr.evalR(slab, self.res[k], {})
                if r is not None and r[1] < 0:
                    if best is None or frac > best[0]:
                        best = (frac, j, p, side, k)
                    break
                # move the cut further out
                p = (p + hi) >> 1 if side == 'hi' else (p + lo) >> 1
        return best

    def split_axis(self, B):
        if getattr(self, 'smart', False) and self.last_slopes:
            # residual with the smallest slope upper bound; split the axis with largest |G_j| rad_j
            bestk, bestv = None, None
            for k, s in self.last_slopes.items():
                if s is None:
                    continue
                v = expr.slope_hi(B, s)
                if bestv is None or v < bestv:
                    bestk, bestv = k, v
            if bestk is not None:
                s = self.last_slopes[bestk]
                bj, bc = 0, -1
                for j, b in enumerate(B):
                    g = s[2][j] if j < len(s[2]) else fx.ZERO
                    contrib = max(abs(g[0]), abs(g[1])) * (b[1] - b[0])
                    if contrib > bc:
                        bc, bj = contrib, j
                if bc > 0:
                    return bj
        best, bj = -1, 0
        for j, (lo, hi) in enumerate(B):
            s = (hi - lo) / self.scales[j](lo)
            if s > best:
                best, bj = s, j
        return bj


def lp_combo(B, slopes):
    """Propose nonnegative integer weights w with slope bound of sum w_k f_k < 0 (verified exactly)."""
    try:
        import numpy as np
        from scipy.optimize import linprog
    except ImportError:
        return None
    ks = [k for k, s in slopes.items() if s is not None]
    if len(ks) < 2:
        return None
    n = len(B)
    rad = [(b[1] - b[0]) / 2 / fx.U for b in B]
    # linearised upper bound: sum_k w_k (vhi_k + sum_j sup(G_kj * D_j)), D_j in [-rad_j, rad_j]
    # Use the LP: minimise t s.t. for all sign patterns... approximate with midpoints of G and
    # the radius of G added: sup(sum_k w_k G_kj D_j) <= |sum_k w_k gmid_kj| rad_j + sum_k w_k grad_kj rad_j
    # Linearise |.| with auxiliary variables a_j >= +-sum_k w_k gmid_kj.
    K = len(ks)
    nv = K + n  # w_k, a_j
    c = np.zeros(nv)
    A, b = [], []
    for idx, k in enumerate(ks):
        s = slopes[k]
        c[idx] += s[1][1] / fx.U
        for j in range(n):
            g = s[2][j] if j < len(s[2]) else fx.ZERO
            c[idx] += (g[1] - g[0]) / 2 / fx.U * rad[j]
    for j in range(n):
        c[K + j] = rad[j]
        row1 = np.zeros(nv); row2 = np.zeros(nv)
        for idx, k in enumerate(ks):
            s = slopes[k]
            g = s[2][j] if j < len(s[2]) else fx.ZERO
            gm = (g[0] + g[1]) / 2 / fx.U
            row1[idx] = gm; row2[idx] = -gm
        row1[K + j] = -1; row2[K + j] = -1
        A.append(row1); b.append(0); A.append(row2); b.append(0)
    # normalisation: sum w = 1
    Aeq = [np.concatenate([np.ones(K), np.zeros(n)])]
    beq = [1]
    try:
        res = linprog(c, A_ub=np.array(A), b_ub=np.array(b), A_eq=np.array(Aeq), b_eq=beq,
                      bounds=[(0, None)] * nv, method='highs')
    except Exception:
        return None
    if not res.success or res.fun >= 0:
        return None
    wts = res.x[:K]
    mx = max(wts)
    ws = []
    for idx, k in enumerate(ks):
        wi = int(round(wts[idx] / mx * (1 << 20)))
        if wi > 0:
            ws.append((k, wi))
    if not ws:
        return None
    # exact verification (mirror of combS + check byS)
    acc = expr.s_const(fx.ZERO)
    for k, wi in reversed(ws):
        acc = expr.s_add(expr.s_scale(wi, slopes[k]), acc)
    if expr.slope_hi(B, acc) < 0:
        return ws
    return None


def solve(prob, B, depth=0, stats=None, limit=10**7):
    """Depth-first; returns certificate tree or None (unresolved)."""
    if stats is None:
        stats = {'nodes': 0, 'leaves': 0, 'R': 0, 'S': 0, 'L': 0, 'fail': 0, 'maxdepth': 0}
    stack_cert = []
    # iterative DFS producing nested tuples
    import os
    XK = os.environ.get('XO_K')
    if XK is not None:
        import smaller as _sm
        _xs = [0.3196127, 0.050935, 1.1397991, 0.1021522, 0.7825397, 0.1008571]
        _h = 2.0 ** -int(XK)
        KB = [(int((x - _h * s) * fx.U), int((x + _h * s) * fx.U)) for x, s in zip(_xs, _sm.SCALES)]
    def rec(B, depth):
        stats['nodes'] += 1
        if XK is not None and all(KB[j][0] <= B[j][0] and B[j][1] <= KB[j][1] for j in range(len(B))):
            stats['K'] = stats.get('K', 0) + 1
            return ('K',)
        stats['maxdepth'] = max(stats['maxdepth'], depth)
        if stats['nodes'] > limit:
            raise RuntimeError('limit')
        if getattr(prob, 'contractors', None):
            cut = prob.find_cut(B)
            if cut is not None:
                frac, j, p, side, k = cut
                lo, hi = B[j]
                BL = list(B); BL[j] = (lo, p); BR = list(B); BR[j] = (p, hi)
                stats['leaves'] += 1; stats['R'] += 1; stats['cuts'] = stats.get('cuts', 0) + 1
                if side == 'hi':
                    return ('cut', j, p, rec(BL, depth), ('R', k))
                return ('cut', j, p, ('R', k), rec(BR, depth))
        v = prob.judge(B)
        if v is not None:
            stats['leaves'] += 1
            if v[0] == 'R':
                stats['R'] += 1
            elif len(v[1]) == 1:
                stats['S'] += 1
            else:
                stats['L'] += 1
            return v
        if depth >= prob.maxdepth:
            stats['fail'] += 1
            return ('FAIL', B)
        j = prob.split_axis(B)
        lo, hi = B[j]
        m = (lo + hi) >> 1
        BL = list(B); BL[j] = (lo, m)
        BR = list(B); BR[j] = (m, hi)
        return ('split', j, rec(BL, depth + 1), rec(BR, depth + 1))
    sys.setrecursionlimit(10000)
    c = rec(B, depth)
    return c, stats


def count_cost(cert, prob, costR, costS):
    if cert[0] == 'split':
        return count_cost(cert[2], prob, costR, costS) + count_cost(cert[3], prob, costR, costS)
    if cert[0] == 'R':
        return costR[cert[1]]
    if cert[0] == 'S':
        return sum(costS[k] for k, _ in cert[1])
    return 0
