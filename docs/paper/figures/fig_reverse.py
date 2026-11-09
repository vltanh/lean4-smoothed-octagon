"""Figures of Sections 4 and 5 (vertex periods; classes R and M3).

fig-reverse-estimates.pdf, two panels:

(a) The three-arc lemma (Lemma lem:three-arc, growing case). On the middle piece of three pieces
    with labels i, i-1, i (active margin a, factor q, outer margin b = a_k at its start), the
    switching function of the outer label is
        chi(s) = 2 s (Y (s - 1) + (sqrt3 a / 2) F(s)),
        F(s) = (a + b) log s - (a + b)(s - 1) + a (s - 1)^2 / s,
    (Appendix app:reverse-estimates), and Y is fixed by chi(q) = 0, so that
        chi(s) / (sqrt3 a) = s (F(s) - F(q)(s - 1)/(q - 1)).
    For a factor with b q < a (equivalently a_k a_{k+2} < a_{k+1}^2) it can stay <= 0; for b q > a
    the end condition forces chi > 0 somewhere, which the maximum principle forbids.
(b) The cost-Casimir inequality (Proposition prop:cost-casimir): C >= 4 pi kappa/(2 kappa + 3),
    against C <= A_oct; the cap kappa < kappa* = 3 A_oct/(4 pi - 2 A_oct) and the value
    313/210 behind the cap gamma^2 <= 97969/529200 = (313/210)^2/12. The spectral bound
    (pi/3)(kappa + 3/2) of the forward case is drawn for comparison.

    python3 figures/fig_reverse.py      (from docs/paper; or through make_figures.py)
"""
import math
import os
import sys

import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import paperstyle as ps  # noqa: E402
import matplotlib.pyplot as plt  # noqa: E402

SQ2 = math.sqrt(2)
DELTA_OCT = (8 - 4 * SQ2 - math.log(2)) / (2 * SQ2 - 1)
A_OCT = math.sqrt(12) * DELTA_OCT


def F(s, a, b):
    return (a + b) * np.log(s) - (a + b) * (s - 1) + a * (s - 1) ** 2 / s


def chi_normalized(s, a, b, q):
    """chi(s)/(sqrt3 a) on the middle piece, with Y fixed by chi(q) = 0 (chi(1) = 0 always)."""
    return s * (F(s, a, b) - F(q, a, b) * (s - 1) / (q - 1))


def panel_three_arc(ax):
    a, b = 1.0, 0.5
    cases = [(1.3, ps.BLUE, r'$q=1.3$: $bq<a$'), (2.4, ps.RED, r'$q=2.4$: $bq>a$')]
    for q, color, label in cases:
        s = np.linspace(1.0, q, 801)
        y = chi_normalized(s, a, b, q)
        # the end values vanish
        assert abs(y[0]) < 1e-12 and abs(y[-1]) < 1e-12
        x = (s - 1) / (q - 1)
        scale = np.abs(y).max()
        ax.plot(x, y / scale, color=color, label=label)
        if b * q < a:
            assert y.max() <= 1e-12          # chi <= 0 on the piece: admissible
        else:
            assert y.max() > 1e-3            # chi > 0 inside the piece: excluded
            ax.fill_between(x, 0, y / scale, where=y > 0, color=color, alpha=0.15, lw=0)
            i = int(np.argmax(y))
            ax.text(x[i], 0.55, r'$\chi>0$', color=color, fontsize=8, ha='center')
    ax.axhline(0, color=ps.FAINT, lw=0.6)
    ax.set_xlim(0, 1)
    ax.set_ylim(-1.15, 1.15)
    ax.set_xlabel(r'position on the middle piece, $(s-1)/(q-1)$')
    ax.set_ylabel(r'$\chi(s)/\max|\chi|$')
    ax.set_title(r'(a) three-arc lemma, $a=1$, $b=1/2$')
    ax.legend(loc='lower left', frameon=False)


def panel_casimir(ax):
    kappa = np.linspace(0.0, 2.2, 600)
    lower = 4 * math.pi * kappa / (2 * kappa + 3)
    spectral = math.pi / 3 * (kappa + 1.5)
    # the spectral bound dominates, with equality only at kappa = 3/2 (value pi)
    assert np.all(spectral - lower >= -1e-12)
    assert abs(4 * math.pi * 1.5 / 6 - math.pi) < 1e-15
    k_star = 3 * A_OCT / (4 * math.pi - 2 * A_OCT)
    assert abs(4 * math.pi * k_star / (2 * k_star + 3) - A_OCT) < 1e-12
    assert 1.485 < k_star < 1.4877 < 313 / 210          # Corollary cor:casimir-cap uses kappa < 1.4877
    assert abs((313 / 210) ** 2 / 12 - 97969 / 529200) < 1e-15
    ax.plot(kappa, lower, color=ps.BLUE, label=r'$4\pi\kappa/(2\kappa+3)$')
    ax.plot(kappa, spectral, color=ps.PURPLE, ls='--', lw=1.0, label=r'$(\pi/3)(\kappa+3/2)$')
    ax.axhline(A_OCT, color=ps.ORANGE, lw=1.0)
    ax.text(0.05, A_OCT + 0.1, r'$A_{\mathrm{oct}}=3.1260\ldots$', color=ps.ORANGE, fontsize=8)
    ax.axvspan(k_star, kappa[-1], color=ps.RED, alpha=0.08, lw=0)
    ax.axvline(k_star, color=ps.RED, lw=0.8)
    ax.text(k_star + 0.04, 3.7, r'$\kappa_*$', color=ps.RED, fontsize=8)
    ax.text(k_star + 0.04, 0.3, 'excluded for\ncompetitive\nperiods', color=ps.RED, fontsize=7.5)
    ax.set_xlim(0, kappa[-1])
    ax.set_ylim(0, 4.0)
    ax.set_xlabel(r'Casimir $\kappa=\sqrt{\det\Lambda_1}=\sqrt{12\gamma^2}$')
    ax.set_ylabel(r'lower bound for the cost $\mathcal{C}$')
    ax.set_title(r'(b) cost--Casimir inequality')
    ax.legend(loc='lower right', frameon=False, bbox_to_anchor=(0.67, 0.0))


def make(out_dir):
    ps.setup()
    fig, axes = plt.subplots(1, 2, figsize=(ps.FULL, 2.6))
    panel_three_arc(axes[0])
    panel_casimir(axes[1])
    fig.tight_layout(w_pad=1.6)
    ps.save(fig, os.path.join(out_dir, 'fig-reverse-estimates.pdf'))


if __name__ == '__main__':
    make(os.path.dirname(os.path.abspath(__file__)))
