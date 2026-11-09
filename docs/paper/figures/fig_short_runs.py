"""Class M1: what the angle gap and the winding identity control.

fig-short-runs-gap.pdf has two panels.

Left: the reduced variables (S, z) of the angle gap (appendix on class M1). For a reverse centre with
cos(phi) >= 3/10 the merged switch-norm variable S and the scaled centre variable
z = 4 rho/(1 - S) satisfy

    E <= E_max(S, z) = (1 - S)(1 - z/4) + log z,     E >= (3/5) sqrt(Q),   Q = 3(3 + S^2)/16,

so (S, z) lies in the shaded region where E_max >= (3/5) sqrt(Q). On it the Gram identity gives
gamma^2 >= f(S, z) = (4Q - E_max^2)/(16 (1 - rho)^2), rho = (1 - S) z/4, and the colours show f.
The symmetric-minimum lemma locates the minimum at S=0 on the pairing constraint.
It is greater than 5/27, which bounds the competitive Casimir cap.
The level set f=5/27 (dashed) therefore does not meet the region.

Right: the angle budget. The winding identity forces the m centre angles of a (--+)^m period to
average (m + 1) pi/(3m); the angle gap forces each of them above 2 pi/5. For m = 5 the average is
exactly 2 pi/5 and for m > 5 it is smaller, so only m = 2 survives the angle count.
"""
import math

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap

import paperstyle as ps

CAP = 5 / 27


def reduced_casimir(S, z):
    Q = 3 * (3 + S ** 2) / 16
    Emax = (1 - S) * (1 - z / 4) + np.log(z)
    rho = (1 - S) * z / 4
    feasible = Emax >= 0.6 * np.sqrt(Q)
    f = (4 * Q - Emax ** 2) / (16 * (1 - rho) ** 2)
    return feasible, f


def make(out_dir):
    ps.setup()
    S = np.linspace(0.0, 0.45, 901)
    z = np.linspace(0.55, 1.0, 901)
    SS, ZZ = np.meshgrid(S, z)
    feas, f = reduced_casimir(SS, ZZ)

    # The facts the caption states.
    assert feas.any()
    fmin = f[feas].min()
    assert fmin > CAP, (fmin, CAP)                      # the core inequality on the grid
    assert abs(math.cos(2 * math.pi / 5) - (math.sqrt(5) - 1) / 4) < 1e-15
    assert math.cos(2 * math.pi / 5) > 3 / 10
    ms = [m for m in range(2, 30) if m % 3 == 2]
    for m in ms:
        avg = (m + 1) * math.pi / (3 * m)
        if m == 5:
            assert abs(avg - 2 * math.pi / 5) < 1e-15
        elif m > 5:
            assert avg < 2 * math.pi / 5
        else:
            assert avg > 2 * math.pi / 5

    fig, (ax, bx) = plt.subplots(1, 2, figsize=(ps.FULL, 2.7),
                                 gridspec_kw={'width_ratios': [1.15, 1]})

    # left panel
    cmap = LinearSegmentedColormap.from_list('cas', ['#fbe3c9', '#dbe9fb', '#7aa7e8'])
    fm = np.ma.masked_where(~feas, f)
    pc = ax.pcolormesh(SS, ZZ, fm, cmap=cmap, shading='auto', vmin=CAP, vmax=float(f[feas].max()),
                       rasterized=True)
    ax.contour(SS, ZZ, feas.astype(float), levels=[0.5], colors=ps.INK, linewidths=0.8)
    ax.contour(SS, ZZ, f, levels=[CAP], colors=ps.RED, linewidths=0.9, linestyles='--')
    i = np.argmin(np.where(feas, f, np.inf))
    ax.plot(SS.flat[i], ZZ.flat[i], 'o', ms=3, color=ps.INK)
    ax.annotate('symmetric minimum', (SS.flat[i], ZZ.flat[i]), xytext=(0.12, 0.6),
                fontsize=7.5, arrowprops=dict(arrowstyle='-', lw=0.5, color=ps.INK))
    ax.text(0.44, 0.71, r'$f=5/27$', color=ps.RED, fontsize=7.5, ha='right', va='top')
    ax.set_xlim(0, 0.45)
    ax.set_ylim(0.55, 1.0)
    ax.set_xlabel(r'$S$')
    ax.set_ylabel(r'$z=4\rho/(1-S)$')
    cb = fig.colorbar(pc, ax=ax, fraction=0.05, pad=0.02)
    cb.set_label(r'$f(S,z)$', fontsize=7.5)
    cb.ax.tick_params(labelsize=7)

    # right panel
    avg = [(m + 1) / (3 * m) for m in ms]
    bx.axhline(2 / 5, color=ps.RED, lw=0.9, ls='--')
    bx.text(ms[-1], 2 / 5 + 0.006, r'$2\pi/5$: lower bound for each $\varphi_j$', ha='right',
            va='bottom', color=ps.RED, fontsize=7.5)
    bx.plot(ms, avg, 'o', ms=3.5, color=ps.BLUE)
    bx.plot(ms[:1], avg[:1], 'o', ms=5.5, mfc='none', mec=ps.ORANGE, mew=1.0)
    bx.annotate(r'$m=2$: excluded by its cost', (2, avg[0]), xytext=(6, 0.47), fontsize=7.5,
                arrowprops=dict(arrowstyle='-', lw=0.5, color=ps.INK))
    bx.set_xlabel(r'number $m$ of centres')
    bx.set_ylabel(r'average centre angle $/\pi$')
    bx.set_xticks(ms[::2])
    bx.set_ylim(0.32, 0.52)
    for spine in ('top', 'right'):
        ax.spines[spine].set_visible(True)
        bx.spines[spine].set_visible(False)
    fig.tight_layout(w_pad=1.2)
    ps.save(fig, f'{out_dir}/fig-short-runs-gap.pdf')


if __name__ == '__main__':
    import os
    make(os.path.dirname(os.path.abspath(__file__)))
