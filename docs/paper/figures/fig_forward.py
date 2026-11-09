"""Figure of Section 7 (class F): fig-forward-window.pdf.

Left: the cost N (sqrt3/4) G(a, a) of N equal edges of an all-forward period against a^2, for N = 4
and N = 7, with the octagon's point and the band 4/3 < a^2 < 20/11 of Lemmas 7.x (small forward
minimum, threshold). Right: on 11/5 <= nu <= 3, the common lower bound Phi for the two norm-sum vertices
of the Casimir estimate, against the competitive
cap (3 A_oct/pi - 3/2)^2/12 allowed by the spectral cost-Casimir bound.

Assertions check special values and plot consistency. The interval bounds are proved in sections/a05-forward.tex, whose G, e_0 and lower curve are used here.
"""
import math
import os
from fractions import Fraction

import numpy as np

import paperstyle as ps

SQ2, SQ3 = math.sqrt(2), math.sqrt(3)
A_OCT = math.sqrt(12) * (8 - 4 * SQ2 - math.log(2)) / (2 * SQ2 - 1)


def G(a, b):
    """The edge function G of Section 7."""
    return (3 * a * b - 4 - (a * a + b * b) * np.log(a + b)
            + (a * a * np.log(a * a + 4) + b * b * np.log(b * b + 4)) / 2)


def e0(nu):
    K = 1 + nu
    return 1 - K / 8 + 1 / K


def phi(nu):
    """The proved common curve after equalizing the two shapes."""
    K = 1 + nu
    shape = np.minimum(7 / 3, (5 * nu + 1) / 6)
    x = shape / 2 - 1
    log_floor = 2 * x ** 3 / (3 * (1 + x) * (2 + x))
    pairing = e0(nu) + shape / 32 - log_floor
    return K ** 2 * (75 / 32 - pairing ** 2) / (16 * nu ** 2)


def checks():
    # The octagon: N = 4, a^2 = 4/(2 sqrt2 - 1), sqrt3 G(a, a) = A_oct.
    a_oct = math.sqrt(4 / (2 * SQ2 - 1))
    assert abs(SQ3 * G(a_oct, a_oct) - A_OCT) < 1e-12
    # G(a, a) = 0 at a^2 = 4/3, and G(a, a) >= 0 for a^2 >= 4/3 (nu <= 3).
    a43 = math.sqrt(4 / 3)
    assert abs(G(a43, a43)) < 1e-12
    xs = np.linspace(4 / 3, 2.4, 400)
    assert np.all(G(np.sqrt(xs), np.sqrt(xs)) >= -1e-12)
    # The threshold: G(a0, a0) > 23/22 at a0^2 = 20/11, and seven such edges exceed A_oct.
    a0 = math.sqrt(20 / 11)
    assert G(a0, a0) > 23 / 22
    assert 7 * SQ3 / 4 * G(a0, a0) > A_OCT
    # Seven equal edges cost more than A_oct for every a^2 >= 20/11 (G(a, a) increases in a).
    ys = np.linspace(20 / 11, 2.4, 400)
    assert np.all(7 * SQ3 / 4 * G(np.sqrt(ys), np.sqrt(ys)) > A_OCT)
    # The common curve lies above the shared rational cap. Sampling checks
    # the plot; the manuscript proves the interval bound by convexity.
    nus = np.linspace(11 / 5, 3, 2001)
    target = Fraction(9193, 50000)
    assert np.all(phi(nus) > float(target))
    # Exact midpoint and completed-square comparison used in that proof.
    nu = Fraction(5, 2)
    K = 1 + nu
    x = (5 * nu - 11) / 12
    log_floor = 2 * x ** 3 / (3 * (1 + x) * (2 + x))
    log_slope = Fraction(5, 18) * (1 + 1 / (1 + x) ** 2 - 8 / (2 + x) ** 2)
    pairing = 1 - K / 8 + 1 / K + (5 * nu + 1) / 192 - log_floor
    pairing_slope = -Fraction(19, 192) - 1 / K ** 2 - log_slope
    weight = K ** 2 / (16 * nu ** 2)
    weight_slope = -K / (8 * nu ** 3)
    midpoint = weight * (Fraction(75, 32) - pairing ** 2)
    slope = weight_slope * (Fraction(75, 32) - pairing ** 2) - 2 * weight * pairing * pairing_slope
    assert slope < 0 and midpoint - 96 * slope ** 2 > target
    assert abs(phi(float(nu)) - float(midpoint)) < 1e-12
    # The cap follows from the spectral cost-Casimir bound.
    cap = (3 * A_OCT / math.pi - 1.5) ** 2 / 12
    assert cap < float(target)
    return a_oct, cap


def make(out_dir):
    ps.setup()
    import matplotlib.pyplot as plt
    a_oct, cap = checks()

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(ps.FULL, 2.55))
    fig.subplots_adjust(wspace=0.32)

    # Left: N equal edges.
    x = np.linspace(1.2, 2.4, 400)
    g = G(np.sqrt(x), np.sqrt(x))
    ax1.axvspan(4 / 3, 20 / 11, color=ps.FILL, lw=0)
    ax1.plot(x, 7 * SQ3 / 4 * g, color=ps.ORANGE, label=r'$N=7$')
    ax1.plot(x, 4 * SQ3 / 4 * g, color=ps.BLUE, label=r'$N=4$')
    ax1.axhline(A_OCT, color=ps.INK, lw=0.7)
    ax1.plot([a_oct ** 2], [A_OCT], 'o', color=ps.BLUE, ms=4, zorder=5)
    ax1.annotate('octagon', (a_oct ** 2, A_OCT), xytext=(a_oct ** 2 - 0.36, A_OCT + 1.1),
                 fontsize=8, arrowprops=dict(arrowstyle='-', lw=0.5, color=ps.FAINT))
    ax1.text(1.21, A_OCT + 0.12, r'$A_{\mathrm{oct}}$', fontsize=8, va='bottom')
    for xv, lab in ((4 / 3, r'$4/3$'), (20 / 11, r'$20/11$')):
        ax1.axvline(xv, color=ps.FAINT, lw=0.5, ls=':')
        ax1.text(xv + 0.02, 6.9, lab, fontsize=7.5, ha='left', va='top')
    ax1.set_xlim(1.2, 2.4)
    ax1.set_ylim(-0.4, 7.2)
    ax1.set_xlabel(r'$a^2$')
    ax1.set_ylabel(r'$N\,\frac{\sqrt{3}}{4}\,G(a,a)$')
    ax1.legend(loc='lower right', frameon=False, handlelength=1.6)

    # Right: excess above the exact competitive cap, in units of 1e-4.
    nu = np.linspace(11 / 5, 3, 600)
    ax2.plot(nu, 1e4 * (phi(nu) - cap), color=ps.ORANGE, label=r'$\Phi$')
    ax2.axhline(0, color=ps.RED, lw=0.9, ls='--')
    ax2.text(2.21, -0.2, 'competitive cap', fontsize=8, va='top', color=ps.RED)
    ax2.set_xlim(11 / 5, 3)
    ax2.set_ylim(-1.2, 18)
    ax2.set_xlabel(r'$\nu=4/a^2$')
    ax2.set_ylabel(r'$10^4\,(\gamma^2-\Gamma_{\mathrm{oct}})$')
    ax2.legend(loc='upper center', frameon=False, handlelength=1.6)

    ps.save(fig, os.path.join(out_dir, 'fig-forward-window.pdf'))


if __name__ == '__main__':
    make(os.path.dirname(os.path.abspath(__file__)))
