"""Figure of Section 7 (class F): fig-forward-window.pdf.

Left: the cost N (sqrt3/4) G(a, a) of N equal edges of an all-forward period against a^2, for N = 4
and N = 7, with the octagon's point and the band 4/3 < a^2 < 20/11 of Lemmas 7.x (small forward
minimum, threshold). Right: on 11/5 <= nu <= 3, the two vertex bounds phi_A, phi_B of Appendix C.6
(lower bounds for the Casimir under the norm bounds), against 23/125 and against the competitive
cap (3 A_oct/pi - 3/2)^2/12 allowed by the spectral cost-Casimir bound.

Every fact stated in the caption is checked by an assert. G, e_0 and the vertex bounds are those of
Section 7 and Appendix C (sections/07-forward.tex, sections/a3-forward-estimates.tex).
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


def phi_A(nu):
    """K^2 (327/140 - (e0 + s/35)^2)/(16 nu^2), s = min(7/3, (5 nu + 1)/6) (Appendix C.6)."""
    K = 1 + nu
    s = np.minimum(7 / 3, (5 * nu + 1) / 6)
    return K ** 2 * (327 / 140 - (e0(nu) + s / 35) ** 2) / (16 * nu ** 2)


def phi_B(nu):
    """The bound at the vertex B = (1/35 - 1/64, 1/64) (Appendix C.6)."""
    K = 1 + nu
    c, b = 1 / 35, 1 / 64
    s = np.where(nu <= 13 / 5, (c - b) * (2 + 5 * (nu - 1) / 3) + (2 * b - c) * 7 / 3, 7 / 3 * c)
    return K ** 2 * (4 * (3 / 4 + c - b) * (3 / 4 + b) - (e0(nu) + s) ** 2) / (16 * nu ** 2)


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
    assert 7 * SQ3 / 4 * G(a0, a0) > 3.1268 > A_OCT
    # Seven equal edges cost more than A_oct for every a^2 >= 20/11 (G(a, a) increases in a).
    ys = np.linspace(20 / 11, 2.4, 400)
    assert np.all(7 * SQ3 / 4 * G(np.sqrt(ys), np.sqrt(ys)) > A_OCT)
    # The vertex bounds stay above 23/125 on [11/5, 3]; the tightest value is phi_A(13/5).
    nus = np.linspace(11 / 5, 3, 2001)
    assert np.all(phi_A(nus) > 23 / 125) and np.all(phi_B(nus) > 23 / 125)
    nu = Fraction(13, 5)
    K = 1 + nu
    e = 1 - K / 8 + 1 / K
    exact = K ** 2 * (Fraction(327, 140) - (e + Fraction(7, 3) / 35) ** 2) / (16 * nu ** 2)
    assert exact == Fraction(348293, 1892800) == Fraction(23, 125) + Fraction(89, 9464000)
    assert abs(min(phi_A(nus)) - float(exact)) < 1e-9
    # The competitive cap from C >= (pi/3)(kappa + 3/2): gamma^2 <= (3 A_oct/pi - 3/2)^2/12.
    cap = (3 * A_OCT / math.pi - 1.5) ** 2 / 12
    assert cap < 0.18381 < 23 / 125
    kappa = 3 * 3.1268 / math.pi - 1.5
    assert kappa < 1.4859 and 1.4859 ** 2 / 12 < 23 / 125
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
    for xv, lab, ha in ((4 / 3, r'$a^2=4/3$', 'right'), (20 / 11, r'$a^2=20/11$', 'left')):
        ax1.axvline(xv, color=ps.FAINT, lw=0.5, ls=':')
        ax1.text(xv + (0.02 if ha == 'left' else -0.02), 6.9, lab, fontsize=7.5, ha=ha, va='top')
    ax1.set_xlim(1.2, 2.4)
    ax1.set_ylim(-0.4, 7.2)
    ax1.set_xlabel(r'$a^2$')
    ax1.set_ylabel(r'$N\,\frac{\sqrt{3}}{4}\,G(a,a)$')
    ax1.legend(loc='lower right', frameon=False, handlelength=1.6)

    # Right: the Casimir bounds, in units of 1e-4 above 23/125.
    nu = np.linspace(11 / 5, 3, 600)
    base = 23 / 125
    ax2.plot(nu, 1e4 * (phi_A(nu) - base), color=ps.ORANGE, label=r'$\phi_A$')
    ax2.plot(nu, 1e4 * (phi_B(nu) - base), color=ps.PURPLE, label=r'$\phi_B$')
    ax2.axhline(0, color=ps.INK, lw=0.7)
    ax2.axhline(1e4 * (cap - base), color=ps.RED, lw=0.9, ls='--')
    ax2.text(2.21, 0.6, r'$23/125$', fontsize=8, va='bottom')
    ax2.text(2.21, 1e4 * (cap - base) - 0.6, 'competitive cap', fontsize=8, va='top',
             color=ps.RED)
    ax2.set_xlim(11 / 5, 3)
    ax2.set_ylim(-4.5, 17)
    ax2.set_xlabel(r'$\nu=4/a^2$')
    ax2.set_ylabel(r'$10^4\,(\gamma^2-23/125)$')
    ax2.legend(loc='upper center', frameon=False, handlelength=1.6)

    ps.save(fig, os.path.join(out_dir, 'fig-forward-window.pdf'))


if __name__ == '__main__':
    make(os.path.dirname(os.path.abspath(__file__)))
