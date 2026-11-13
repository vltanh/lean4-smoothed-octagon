"""Figure for Section 8 (class M2): what the estimates control.

fig-mixed-domains.pdf, three panels:

(a) the lower bound G(rho) = (9/4 - B(rho)^2)/(16 (1 - rho)^2), B(rho) = 1 - rho + log(4 rho), for the
    Casimir at a reverse centre (Lemma lem:m2-scale), with the cap
    23/125; G increases on [3/20, 1/4) and G(3/20) > 23/125, so rho < 3/20, a^2 < 12/17;
(b) the (t, x) parameters of the scalar reverse exclusion (Proposition prop:m2-reverse-core): the necessary
    region 0 < t < 2/5, 0 < x < 7/3 - 10t/3, 1 < 2t + 2x + x^2, 29t^2/4 < 2t + 2x + x^2, coloured by
    the case of the proof (unit shape, order face, scale strip);
(c) the (t, j) parameters of a forward successor, j = 2t + x - 1, in 1/4 < t < 2/5, 0 < j < 1 - 2t,
    by the step that excludes them (Proposition prop:m2-forward-steps).

Every fact the caption states is checked by an assert.
"""
import math
import os

import numpy as np
from matplotlib.colors import ListedColormap
import matplotlib.pyplot as plt

import paperstyle as ps


def G(rho):
    B = 1 - rho + np.log(4 * rho)
    return (9 / 4 - B ** 2) / (16 * (1 - rho) ** 2)


def reverse_case(t, x):
    """The case of `nh_reverse_core` at (t, x): 1 unit shape, 2 order face, 3 scale strip, 0 outside
    the necessary region."""
    s = 2 * t + 2 * x + x ** 2
    region = (t > 0) & (t < 2 / 5) & (x > 0) & (x < 7 / 3 - 10 / 3 * t) & (s > 1) & (s > 29 / 4 * t ** 2)
    c1 = (t <= 3 / 8) & (x <= 1 - 2 * t)
    c2 = ~c1 & (2 * t + x >= 1) & (x > 1 / 4)
    case = np.where(c1, 1, np.where(c2, 2, 3))
    return np.where(region, case, 0)


def forward_case(t, j):
    """The step that excludes a forward successor at (t, j): 1 low ratio, 2 low-t large gap,
    3 high-ratio large gap, 4 small gap; 0 outside 1/4 < t < 2/5, 0 < j < 1 - 2t."""
    region = (t > 1 / 4) & (t < 2 / 5) & (j > 0) & (j < 1 - 2 * t)
    case = np.where(t <= 1 / 3, 1,
                    np.where(j >= 1 / 30, np.where(t <= 3 / 8, 2, 3), 4))
    return np.where(region, case, 0)


def check():
    # (a) G increases on [3/20, 1/4) and exceeds 23/125 there; 23/125 > 9193/50000.
    r = np.linspace(3 / 20, 1 / 4, 20001)[:-1]
    g = G(r)
    assert np.all(np.diff(g) > 0)
    assert G(3 / 20) > 23 / 125 > 9193 / 50000
    # rho = 3/20 is a^2 = 12/17.
    assert abs(4 * (3 / 20) / (1 - 3 / 20) - 12 / 17) < 1e-15
    # (b) every point of the necessary region is in one of the three cases, and the strip lies in
    # 3/8 < t < 2/5, x <= 1/4; above x = 1 every point of the region is in the order face.
    T, X = np.meshgrid(np.linspace(1e-4, 0.4 - 1e-4, 1201), np.linspace(1e-4, 2.4, 2401))
    case = reverse_case(T, X)
    assert np.all(np.isin(case, [0, 1, 2, 3]))
    strip = case == 3
    assert strip.any()
    assert np.all(T[strip] > 3 / 8) and np.all(X[strip] <= 1 / 4 + 1e-12)
    assert np.all(case[(X > 1) & (case > 0)] == 2)
    # (c) the four steps cover the region.
    T2, J2 = np.meshgrid(np.linspace(0.25 + 1e-5, 0.4 - 1e-5, 801), np.linspace(1e-5, 0.5, 801))
    fc = forward_case(T2, J2)
    inside = (T2 > 1 / 4) & (T2 < 2 / 5) & (J2 > 0) & (J2 < 1 - 2 * T2)
    assert np.all((fc > 0) == inside)
    assert np.all(fc[inside & (T2 > 1 / 3) & (J2 < 1 / 30)] == 4)


def make(out_dir):
    check()
    ps.setup()
    fig, axs = plt.subplots(1, 3, figsize=(ps.FULL, 2.25), gridspec_kw={'wspace': 0.5})

    # (a) the scale bound
    ax = axs[0]
    rho = np.linspace(0.06, 0.25 - 1e-6, 600)
    ax.axvspan(3 / 20, 1 / 4, color=ps.FILL, lw=0)
    ax.plot(rho, G(rho), color=ps.BLUE)
    ax.axhline(23 / 125, color=ps.RED, ls='--', lw=0.9)
    ax.axvline(3 / 20, color=ps.FAINT, lw=0.6)
    ax.set_xlim(0.06, 0.25)
    ax.set_ylim(0.17, 0.19)
    ax.set_xticks([0.1, 0.15, 0.2, 0.25])
    ax.set_xticklabels(['0.10', r'$\frac{3}{20}$', '0.20', r'$\frac{1}{4}$'])
    ax.set_yticks([0.17, 0.18, 0.19])
    ax.set_xlabel(r'$\rho=a^2/(a^2+4)$')
    ax.text(0.155, 0.1712, r'$a^2\geq\frac{12}{17}$' '\nexcluded', fontsize=7.5, color=ps.INK)
    ax.text(0.07, 0.1865, r'$G(\rho)$', color=ps.BLUE, fontsize=8)
    ax.text(0.07, 0.1806, r'$23/125$', color=ps.RED, fontsize=7.5)
    ax.set_title('(a) centre scale', loc='left')

    # (b) the reverse successor
    ax = axs[1]
    t = np.linspace(0, 0.4, 801)
    x = np.linspace(0, 1.1, 1101)
    T, X = np.meshgrid(t, x)
    case = reverse_case(T, X).astype(float)
    case[case == 0] = np.nan
    cmap = ListedColormap(['#f6d7b8', '#d7e6f7', '#cdebd8'])
    ax.pcolormesh(T, X, case, cmap=cmap, vmin=0.5, vmax=3.5, shading='auto', rasterized=True)
    ax.plot(t, 1 - 2 * t, color=ps.INK, lw=0.6)
    ax.plot(t[t >= 3 / 8], np.full((t >= 3 / 8).sum(), 1 / 4), color=ps.INK, lw=0.6)
    ax.axvline(3 / 8, color=ps.INK, lw=0.6, ymax=(1 - 26 / 35) / 1.1)
    ax.axhline(1 / 4, color=ps.FAINT, lw=0.5, ls=':')
    ax.set_xlim(0, 0.4)
    ax.set_ylim(0, 1.1)
    ax.set_xticks([0, 0.2, 0.4])
    ax.set_xticklabels(['0', '0.2', r'$\frac{2}{5}$'])
    ax.set_xlabel(r'$t=a/(a+c)$')
    ax.set_ylabel(r'$x=(d-a)/(a+c)$')
    ax.text(0.04, 0.16, r'$k=1$', fontsize=8)
    ax.text(0.15, 0.78, r'$k=2t+x$', fontsize=8)
    ax.annotate(r'$k=\frac{29}{4}t^2$', xy=(0.386, 0.15), xytext=(0.22, 0.04), fontsize=8,
                arrowprops=dict(arrowstyle='-', lw=0.5, color=ps.INK))
    ax.set_title('(b) reverse successor', loc='left')

    # (c) the forward successor
    ax = axs[2]
    t = np.linspace(0.25, 0.4, 601)
    j = np.linspace(0, 0.5, 1001)
    T2, J2 = np.meshgrid(t, j)
    fc = forward_case(T2, J2).astype(float)
    fc[fc == 0] = np.nan
    cmap = ListedColormap(['#f6d7b8', '#d7e6f7', '#e4dcf3', '#f7d0cc'])
    ax.pcolormesh(T2, J2, fc, cmap=cmap, vmin=0.5, vmax=4.5, shading='auto', rasterized=True)
    ax.plot(t, 1 - 2 * t, color=ps.INK, lw=0.6)
    ax.plot(t, 5 / 7 * (1 - 2 * t), color=ps.INK, lw=0.6, ls=':')
    ax.axvline(1 / 3, color=ps.INK, lw=0.6, ymax=(1 / 3) / 0.5)
    ax.axvline(3 / 8, color=ps.INK, lw=0.6, ymin=(1 / 30) / 0.5, ymax=(1 / 4) / 0.5)
    ax.plot([1 / 3, 0.4], [1 / 30, 1 / 30], color=ps.INK, lw=0.6)
    ax.set_xlim(0.25, 0.4)
    ax.set_ylim(0, 0.5)
    ax.set_xticks([0.25, 1 / 3, 0.4])
    ax.set_xticklabels([r'$\frac{1}{4}$', r'$\frac{1}{3}$', r'$\frac{2}{5}$'])
    ax.set_xlabel(r'$t$')
    ax.set_ylabel(r'$j=2t+x-1$')
    ax.text(0.262, 0.13, 'low\nratio', fontsize=7.5)
    ax.text(0.336, 0.21, 'large gap', fontsize=7.5)
    ax.annotate('small gap', xy=(0.37, 0.015), xytext=(0.345, 0.37), fontsize=7.5,
                arrowprops=dict(arrowstyle='-', lw=0.5, color=ps.INK))
    ax.set_title('(c) forward successor', loc='left')

    ps.save(fig, os.path.join(out_dir, 'fig-mixed-domains.pdf'))


if __name__ == '__main__':
    import sys
    make(sys.argv[1] if len(sys.argv) > 1 else os.path.dirname(os.path.abspath(__file__)))
