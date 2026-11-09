"""Figure of Section 9 (the smaller-short window of class M2): what the gates S0-S6 control.

fig-smaller-short.pdf has three panels.

(a) The plane of the ratio x = C/a and the displacement delta = B/C - 1 of a smaller-short window.
    The gates S0 (x < 12/5), S1 (x > 2), S2 (x < 13/6) and S3 (delta < 1/19) cut the shapes down
    to the small box [2, 13/6] x [0, 1/19] on which S4-S6 work. The dots are points of the
    equal-secant locus Sec(1, x, beta) = Sec(alpha, beta, x) with 1 <= alpha < x (computed).
(b) On that box, the slope eta = (alpha - 1)/delta of the equal-secant locus, for x = 2, 25/12, 13/6:
    it lies between the strong lower order 1 + 4x(x + 1)/(7x + 1) >= 13/5 and the small-shape upper
    order 3 (Lemma "Orders of the bridge" of Section 9).
(c) The natural score gap c*pi/3 + sqrt(3)*B(u_star; R, T(e), delta) - A_oct
    of gate S6 at e = 13/5, over 1/3 <= R <= 7/19, 0 <= delta <= 1/19.
    The norm floor comes from a reciprocal integral and its weighted variance.

Every fact the caption states is checked by an assert. The functions are those of Section 9 and
its appendix: the secant (eq:ss-secant), the slope k_s of the strong order, and the bound B, the
floor u_star, the bounds Z_U, Z_L and the angle T of gate S6.
"""
import math
import os

import numpy as np
from scipy.optimize import brentq

import paperstyle as ps
from paperstyle import plt


# ---- the secant and the equal-secant locus ------------------------------------------------------

def sec(A, B, P):
    """Sec(A, B, P): the average of g_B(s) = 1 - Bs/(B + s)^2 over [A, P]."""
    if abs(A - P) < 1e-13:
        return 1 - A * B / (A + B) ** 2
    return 1 + B * B / ((A + B) * (P + B)) - B / (P - A) * math.log((P + B) / (A + B))


def alpha_of(x, d):
    """The alpha in [1, x) with Sec(1, x, beta) = Sec(alpha, beta, x), beta = x(1 + d), or None."""
    be = x * (1 + d)
    u = sec(1, x, be)
    f = lambda a: sec(a, be, x) - u
    lo, hi = 1.0, x * (1 - 1e-12)
    if f(lo) < 0 or f(hi) > 0:
        return None
    return brentq(f, lo, hi, xtol=1e-15, rtol=1e-15)


def ks(x):
    """The strong lower-order slope k_s(x) = 4(x + 1)/(7x + 1)."""
    return 4 * (x + 1) / (7 * x + 1)


# ---- the integral score bound of gate S6 --------------------------------------------------------

def ell6(z):
    return z - 161 / (54 * math.sqrt(3)) * math.atan(z / math.sqrt(3))


def u_star(R, d):
    return 0.75 + (1 + R) * R ** 3 / (6 * (2 * R + (1 + R) * d)) * (
        (1 + 3 * R / 4) ** -2 + 9 * R * R / (80 * (1 + R) ** 4))


def ZU(R, d):
    return 2 * R * R * (1 + R) / (3 - R) + (1 + 2 * R) / (3 * (1 - R)) * d - 1.5 * d * d


def ZL(R, d):
    return 2 * R * R * (1 + R) / (3 - R) * (1 + 11 * d / 2)


def T6(R, d, e):
    return (2 * R + ((e + 1) * R - (e - 1)) * d) / (2 + (e + 1 - (e - 1) * R) * d)


def B6(R, T, d, u):
    b1 = 1 - u / ((3 + R * R) / 4)
    b2 = 1 - u / ((3 + T * T) / 4)
    return (ell6(R) + ell6(T) - (b1 * R + b2 * T) / 2 - (b1 + b2) * ZU(R, d) / 8
            - 161 / 54 * ((3 + R * R) / (3 + T * T) - 1) ** 2 / (8 * ZL(R, d)))


OCTAGON_COST = 2 * math.sqrt(3) * (
    8 - 4 * math.sqrt(2) - math.log(2)) / (2 * math.sqrt(2) - 1)


def make(out_dir):
    ps.setup()
    fig, axes = plt.subplots(1, 3, figsize=(ps.FULL, 2.25),
                             gridspec_kw={'width_ratios': [1.15, 1.0, 1.1], 'wspace': 0.42})

    # (a) the gates in the (x, delta) plane
    ax = axes[0]
    X0, X1, D1 = 1.0, 2.8, 0.30
    ax.set_xlim(X0, X1)
    ax.set_ylim(0, D1)
    shade = dict(alpha=0.18, lw=0)
    ax.axvspan(X0, 2.0, color=ps.FAINT, **shade)
    ax.axvspan(12 / 5, X1, color=ps.ORANGE, **shade)
    ax.axvspan(13 / 6, 12 / 5, color=ps.PURPLE, **shade)
    ax.fill_between([2.0, 13 / 6], 1 / 19, D1, color=ps.GREEN, **shade)
    ax.add_patch(plt.Rectangle((2.0, 0), 13 / 6 - 2, 1 / 19, fc=ps.BLUE, ec=ps.BLUE, lw=0.8,
                               alpha=0.55))
    # points of the equal-secant locus
    pts = []
    for x in np.linspace(1.05, X1 - 0.02, 26):
        for d in np.linspace(0.004, D1 - 0.01, 22):
            a = alpha_of(x, d)
            if a is not None:
                assert 1 <= a < x
                pts.append((x, d))
    pts = np.array(pts)
    assert len(pts) > 100
    ax.plot(pts[:, 0], pts[:, 1], '.', ms=1.4, color=ps.INK, alpha=0.55)
    for xv in (2.0, 13 / 6, 12 / 5):
        ax.axvline(xv, color=ps.INK, lw=0.5)
    ax.text(1.5, 0.27, 'S1', ha='center', va='top')
    ax.text(2.6, 0.27, 'S0', ha='center', va='top')
    ax.text((13 / 6 + 12 / 5) / 2, 0.27, 'S2', ha='center', va='top')
    ax.text(2.0 + (13 / 6 - 2) / 2, 0.17, 'S3', ha='center', va='center')
    ax.annotate('S4–S6', xy=(2.08, 0.026), xytext=(1.32, 0.09), fontsize=8,
                arrowprops=dict(arrowstyle='-', lw=0.5, color=ps.INK))
    ax.set_xticks([1, 2, 13 / 6, 12 / 5])
    ax.set_xticklabels(['1', '2', r'$\frac{13}{6}$', r'$\frac{12}{5}$'])
    ax.set_yticks([0, 1 / 19, 0.1, 0.2, 0.3])
    ax.set_yticklabels(['0', r'$\frac{1}{19}$', '0.1', '0.2', '0.3'])
    ax.set_xlabel(r'$x=C/a$')
    ax.set_ylabel(r'$\delta=B/C-1$')
    ax.set_title('(a)', loc='left')

    # (b) the slope eta on the small box
    ax = axes[1]
    ds = np.linspace(1e-4, 1 / 19, 80)
    for x, c in zip((2.0, 25 / 12, 13 / 6), (ps.ORANGE, ps.PURPLE, ps.GREEN)):
        eta = np.array([(alpha_of(x, d) - 1) / d for d in ds])
        lower = 1 + x * ks(x)              # 1 + 4x(x + 1)/(7x + 1)
        assert np.all(eta >= lower - 1e-9) and np.all(eta <= 3)
        assert lower >= 13 / 5 - 1e-12
        ax.plot(ds, eta, color=c, lw=1.2, label=r'$x=%s$' % {2.0: '2', 25 / 12: r'\frac{25}{12}',
                                                             13 / 6: r'\frac{13}{6}'}[x])
        ax.plot([0, 1 / 19], [lower, lower], color=c, lw=0.7, ls='--')
    ax.axhline(3, color=ps.INK, lw=0.8)
    ax.axhline(13 / 5, color=ps.INK, lw=0.8)
    ax.set_xlim(0, 1 / 19)
    ax.set_ylim(2.55, 3.05)
    ax.set_xticks([0, 1 / 38, 1 / 19])
    ax.set_xticklabels(['0', r'$\frac{1}{38}$', r'$\frac{1}{19}$'])
    ax.set_yticks([13 / 5, 2.8, 3])
    ax.set_yticklabels([r'$\frac{13}{5}$', '2.8', '3'])
    ax.set_xlabel(r'$\delta$')
    ax.set_ylabel(r'$\eta=(\alpha-1)/\delta$')
    ax.legend(loc='upper right', frameon=False, handlelength=1.2, borderaxespad=0.1,
              fontsize=7)
    ax.set_title('(b)', loc='left')

    # (c) the S6 score gap at e = 13/5
    ax = axes[2]
    Rs = np.linspace(1 / 3, 7 / 19, 121)
    dd = np.linspace(0, 1 / 19, 121)
    for e in (13 / 5, 3):
        Z = np.array([[
            161 / 54 * math.pi / 3
            + math.sqrt(3) * B6(R, T6(R, d, e), d, u_star(R, d))
            - OCTAGON_COST for R in Rs] for d in dd])
        assert Z.min() > 0, (e, Z.min())
        if e == 13 / 5:
            Zp = Z
    im = ax.pcolormesh(Rs, dd, Zp * 1e3, shading='auto', cmap='Blues')
    cb = fig.colorbar(im, ax=ax, fraction=0.07, pad=0.03)
    cb.set_label(r'$(c\pi/3+\sqrt{3}\mathcal{B}-A_{\rm oct})\cdot10^3$', fontsize=7)
    cb.ax.tick_params(labelsize=7)
    ax.set_xticks([1 / 3, 0.35, 7 / 19])
    ax.set_xticklabels([r'$\frac{1}{3}$', '0.35', r'$\frac{7}{19}$'])
    ax.set_yticks([0, 1 / 38, 1 / 19])
    ax.set_yticklabels(['0', r'$\frac{1}{38}$', r'$\frac{1}{19}$'])
    ax.set_xlabel(r'$R=(x-1)/(x+1)$')
    ax.set_ylabel(r'$\delta$')
    ax.set_title(r'(c) $\eta=13/5$', loc='left')

    ps.save(fig, os.path.join(out_dir, 'fig-smaller-short.pdf'))


if __name__ == '__main__':
    make(os.path.dirname(os.path.abspath(__file__)))
