"""Figure of Section 3: the vertex Hamiltonians and the singular clearance along the octagon.

fig-reduction-hamiltonians.pdf: along one period [0, t_f] of the smoothed octagon's trajectory
(word e2 e0 e1 e2, switching time t_sw), with its normal Pontryagin lift (lambda = -1), the three
vertex Hamiltonians H_0, H_1, H_2 (left), and the ratio Q/||P|| of the distance of the costate from
the singular locus to the norm of the extended covector, against the intrinsic bound c_oct^{-1}
(right).

The lift is the strong lift of the proof of Hales--Vajjha, Theorem 7.5.1:
Lambda_1(0) = l_1 Lambda_10, Lambda_R(0) = l_R [[0, y0^2], [1, 0]], with the explicit constants
l_1, l_R of that proof for lambda = -1. Lambda_1(t) = g(t)^{-1} Lambda_1(0) g(t),
and Lambda_R is integrated numerically from its costate equation, interval by interval. The asserts
check what the caption states: the costate equations close up with the twisted endpoint conditions
Lambda_1(T) = R^{-1} Lambda_1(0) R and Lambda_R(T) = R^{-1} Lambda_R(0) R; at every sample all three
vertex Hamiltonians are <= 0 and the largest is 0; the active one is 0 on its piece; the outgoing
and incoming ones vanish at the switches; and Q/||P|| > c_oct^{-1} throughout.
"""
import math
import os
import sys
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp

sys.dont_write_bytecode = True  # import scripts/figures/octagon.py without writing a cache there
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[2] / 'scripts' / 'figures'))

import octagon as oc  # noqa: E402
import paperstyle as ps  # noqa: E402

SQ3 = math.sqrt(3)
J = oc.J
R, R_INV = oc.R, oc.R_INV


def lift_constants(y0):
    """Lambda_10, l_1 and l_R of the strong lift (Hales--Vajjha, proof of Theorem 7.5.1, lambda = -1)."""
    ell = math.log(4 / (3 * y0 ** 2 + 1))
    L10 = np.array([[0.0, 4 * SQ3 * y0 ** 4],
                    [-(SQ3 * (1 + y0 ** 2) * (3 * y0 ** 2 - 1)), 0.0]]) / (2 * y0 ** 2 * (1 + 3 * y0 ** 2))
    l1 = -((1 + 3 * y0 ** 2) * (-3 - 6 * y0 ** 2 + (1 + 3 * y0 ** 2) * ell)) / (12 * SQ3 * y0 ** 4)
    lR = -(3 - 12 * y0 ** 2 - 9 * y0 ** 4 + 18 * y0 ** 6
           + (-1 + 3 * y0 ** 2 + 21 * y0 ** 4 + 9 * y0 ** 6) * ell) / (24 * y0 ** 6)
    return L10, l1, lR


def hamiltonian(lam, L1, LR, X, u):
    """H = <Lambda_1 - (3/2) lam J, X> - <Lambda_R, Z_u>/<X, Z_u>."""
    Z = oc.control_matrix(u)
    return oc.trace_form(L1 - 1.5 * lam * J, X) - oc.trace_form(LR, Z) / oc.trace_form(X, Z)


def frob(M):
    return float(np.sum(M * M))


def clearance_constant():
    """The cost-gap bound c_oct of Proposition `prop:clearance`."""
    area = oc.AREA_OCT
    budget = (2 * math.pi - area) / (3 * (math.pi - area))
    return math.hypot(budget, 1 + 3 * budget / math.sqrt(2))


def compute(n_per=400):
    P = oc.OCT
    lam = -1.0
    L10, l1, lR = lift_constants(P.y0)
    L1_0 = l1 * L10
    LR_0 = lR * np.array([[0.0, P.y0 ** 2], [1.0, 0.0]])

    def L1(t):
        g = P.g(t)
        return np.linalg.inv(g) @ L1_0 @ g

    ts, LRs = [], []
    y = LR_0.ravel().copy()
    for i in range(4):
        u = oc.vertex(P.interval_control(i))

        def rhs(t, w, u=u):
            LR = w.reshape(2, 2)
            X = P.X(t)
            Pm = oc.control_p(u, X)
            A = -L1(t) + 1.5 * lam * J
            d = (Pm @ LR - LR @ Pm) - oc.trace_form(LR, Pm) * (Pm @ X - X @ Pm) + (A @ X - X @ A)
            return d.ravel()

        a, b = i * P.tsw, (i + 1) * P.tsw
        # sample strictly inside the interval, where the control is the vertex of the interval
        t = a + (np.arange(n_per) + 0.5) / n_per * P.tsw
        sol = solve_ivp(rhs, (a, b), y, method='DOP853', rtol=1e-12, atol=1e-13, dense_output=True)
        assert sol.success
        ts.append(t)
        LRs.append(sol.sol(t).T.reshape(-1, 2, 2))
        y = sol.y[:, -1]
        if i == 0:
            LR_sw = y.reshape(2, 2).copy()
    LR_T = y.reshape(2, 2)
    T = P.tf
    # the twisted endpoint conditions of the lift
    assert np.allclose(LR_T, R_INV @ LR_0 @ R, atol=1e-9)
    assert np.allclose(L1(T - 1e-15), R_INV @ L1_0 @ R, atol=1e-9)
    # the strong transversality of Theorem 7.5.1 after one switching interval
    assert np.allclose(LR_sw, R_INV @ LR_0 @ R, atol=1e-9)
    ts = np.concatenate(ts)
    LRs = np.concatenate(LRs)
    H = np.empty((3, ts.size))
    ratio = np.empty(ts.size)
    for n, (t, LR) in enumerate(zip(ts, LRs)):
        X = P.X(t)
        L = L1(t)
        assert abs(np.trace(LR)) < 1e-9 and abs(oc.trace_form(LR, X)) < 1e-8
        for i in range(3):
            H[i, n] = hamiltonian(lam, L, LR, X, oc.vertex(i))
        Q2 = frob(L - 1.5 * lam * J) + frob(LR)
        P2 = lam ** 2 + frob(L) + frob(LR)
        ratio[n] = math.sqrt(Q2 / P2)
    # every vertex Hamiltonian <= 0, the largest = 0, and it is the active one
    active = np.array([P.control(t) for t in ts])
    assert np.all(H <= 1e-8)
    assert np.allclose(H.max(axis=0), 0, atol=1e-8)
    assert np.allclose(H[active, np.arange(ts.size)], 0, atol=1e-8)
    assert ratio.min() > 1 / clearance_constant()
    return P, ts, H, ratio


def make(out_dir):
    ps.setup()
    import matplotlib.pyplot as plt
    P, ts, H, ratio = compute()
    fig, (ax, bx) = plt.subplots(1, 2, figsize=(ps.FULL, 2.3), gridspec_kw={'width_ratios': [1.35, 1]})
    for i in range(3):
        ax.plot(ts / P.tsw, H[i], color=ps.CONTROL_COLORS[i], lw=1.2,
                label=r'$H_{%d}$' % i)
    for k in range(5):
        ax.axvline(k, color=ps.GRID, lw=0.6, zorder=0)
    for k in range(4):
        c = P.interval_control(k)
        ax.text(k + 0.5, 0.02 * abs(H.min()), r'$\mathbf{e}_{%d}$' % c, ha='center', va='bottom',
                color=ps.CONTROL_COLORS[c], fontsize=9)
    ax.axhline(0, color=ps.INK, lw=0.6)
    ax.set_xlim(0, 4)
    ax.set_ylim(H.min() * 1.35, 0.12 * abs(H.min()))
    ax.set_xticks(range(5))
    ax.set_xticklabels([r'$0$', r'$t_{\mathrm{sw}}$', r'$2t_{\mathrm{sw}}$', r'$3t_{\mathrm{sw}}$',
                        r'$4t_{\mathrm{sw}}=t_{\mathrm{f}}$'])
    ax.set_ylabel('vertex Hamiltonians')
    ax.legend(loc='lower center', frameon=False, ncol=3)
    bx.plot(ts / P.tsw, ratio, color=ps.BLUE, lw=1.2, label=r'$Q/\Vert\mathcal{P}\Vert$')
    bx.axhline(1 / clearance_constant(), color=ps.RED, lw=0.9, ls='--', label=r'$c_{\mathrm{oct}}^{-1}$')
    for k in range(5):
        bx.axvline(k, color=ps.GRID, lw=0.6, zorder=0)
    bx.set_xlim(0, 4)
    bx.set_yscale('log')
    bx.set_ylim(1e-3, 1)
    bx.set_xticks(range(5))
    bx.set_xticklabels([r'$0$', '', r'$2t_{\mathrm{sw}}$', '', r'$t_{\mathrm{f}}$'])
    bx.legend(loc='upper right', frameon=False)
    fig.tight_layout(w_pad=1.5)
    ps.save(fig, os.path.join(out_dir, 'fig-reduction-hamiltonians.pdf'))
    return {'min_ratio': float(ratio.min()), 'max_ratio': float(ratio.max()), 'min_H': float(H.min())}


if __name__ == '__main__':
    print(make(str(HERE)))
