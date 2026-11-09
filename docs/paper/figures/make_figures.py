#!/usr/bin/env python3
"""The figures of the paper, written to docs/paper/figures/ as PDF files.

    python3 figures/make_figures.py        (from docs/paper/; or `make figures`)

This script draws the six figures of Sections 1, 2 and 4 and then runs every module
figures/fig_*.py, which draws the figures of the estimates of the later sections.

- fig-octagon.pdf: Reinhardt's smoothed octagon and the construction of one corner;
- fig-packing.pdf: three densest lattice packings of the octagon from its one-parameter family;
- fig-contacts.pdf: the six arcs g(t)s_j, t in [0, t_f], the contact hexagons and the control word;
- fig-halfplane.pdf: the state z(t) of the octagon in the upper half-plane, with the star domain
  and the compact domain;
- fig-simplex.pdf: the control simplex, forward and reverse switches, and two switching words;
- fig-cases.pdf: the structure of the proof.

The smoothed octagon's trajectory comes from scripts/figures/octagon.py of the repository, which
computes it in closed form from the definitions of the control problem and checks the closed form
against a numerical integration of the state equations. Every fact that a caption states is checked
here by an `assert`.
"""
import importlib
import math
import pathlib
import sys

sys.dont_write_bytecode = True
HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parents[2] / 'scripts' / 'figures'))

import numpy as np  # noqa: E402
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch, Polygon  # noqa: E402

import octagon as oc  # noqa: E402
import paperstyle as ps  # noqa: E402
from paperstyle import plt  # noqa: E402

PI = math.pi
SQ2, SQ3 = math.sqrt(2), math.sqrt(3)
P = oc.OCT
CC = ps.CONTROL_COLORS


# ---- shared geometry -----------------------------------------------------------------------------

def side_normal(k):
    return np.array([math.cos(k * PI / 4), math.sin(k * PI / 4)])


def side_dist(k, pts):
    """d_k(x) = 1 - (x_0 cos(k pi/4) + x_1 sin(k pi/4)), the distance to the k-th side line."""
    return 1 - np.atleast_2d(pts) @ side_normal(k)


def in_reinhardt(pts, tol=1e-9):
    """Membership in Reinhardt's smoothed octagon, as in Definition 2.3 (with a tolerance)."""
    pts = np.atleast_2d(pts)
    ok = np.ones(len(pts), dtype=bool)
    for k in range(8):
        dk, dk1 = side_dist(k, pts), side_dist((k + 1) % 8, pts)
        prod = side_dist((k - 1) % 8, pts) * side_dist((k + 2) % 8, pts)
        ok &= dk >= -tol
        ok &= ~((dk + dk1 <= 1.5 - SQ2 - tol) & (prod < SQ2 / 4 - tol))
    return ok


def regular_frame():
    """The linear map A = diag(1, (2 sqrt2 - 1)/sqrt3) that carries the octagon K_H of the trajectory
    onto Reinhardt's octagon (Proposition 11.x)."""
    M = oc.regular_frame(P)
    A = np.diag([1.0, (2 * SQ2 - 1) / SQ3])
    assert np.allclose(M, A, atol=1e-12)
    return A


def boundary_kh(n_per=80):
    return P.boundary(n_per)


def color_of_label(i):
    return CC[i % 3]


# ---- Figure: the octagon ---------------------------------------------------------------------------

def fig_octagon(out):
    A = regular_frame()
    O = np.array([line for line in oc.edge_polygon(P)]) @ A.T     # the regular octagon
    pcs = [(pc[0], oc.piece_points(P, pc, 120) @ A.T) for pc in oc.pieces(P)]
    KB = boundary_kh(200) @ A.T
    # Reinhardt's octagon: every boundary point satisfies the definition, and pushing it out by 1%
    # leaves the set; its area is A_oct (A has determinant (2 sqrt2 - 1)/sqrt3, and K_H has area A_oct).
    assert in_reinhardt(KB, tol=1e-7).all() and not in_reinhardt(1.01 * KB, tol=0).any()
    assert abs(oc.shoelace(KB) - oc.AREA_OCT * np.linalg.det(A)) < 1e-6
    assert np.allclose(O, oc.regular_octagon(1.0)[[7, 0, 1, 2, 3, 4, 5, 6]], atol=1e-12)
    # The corner V = (1, sqrt2 - 1) between side 0 (x = 1) and side 1 (x + y = sqrt2); the next two
    # sides, y = 1 (side 2) and x - y = sqrt2 (side 7), are the asymptotes, meeting at C.
    V = np.array([1.0, SQ2 - 1])
    C = np.array([1 + SQ2, 1.0])
    T1, T2 = np.array([1.0, 1 - 1 / SQ2]), np.array([SQ2 - 0.5, 0.5])
    arc = [p for k, p in pcs if k == 'arc']
    arc0 = min(arc, key=lambda p: np.linalg.norm(p.mean(axis=0) - V))
    assert np.abs(side_dist(2, arc0) * side_dist(7, arc0) - SQ2 / 4).max() < 1e-9
    ends = sorted([arc0[0], arc0[-1]], key=lambda p: p[1])
    assert np.allclose(ends, [T1, T2], atol=1e-9)
    assert abs(side_dist(0, T1)[0]) < 1e-12 and abs(side_dist(1, T2)[0]) < 1e-12
    # The straight part kept of each side has length 2 - sqrt2 (the side has length 2(sqrt2 - 1)).
    for k, p in pcs:
        if k == 'edge':
            assert abs(np.linalg.norm(p[-1] - p[0]) - (2 - SQ2)) < 1e-9
    # The tangency points are where d_k + d_{k+1} = 3/2 - sqrt2.
    for T in (T1, T2):
        assert abs(side_dist(0, T)[0] + side_dist(1, T)[0] - (1.5 - SQ2)) < 1e-12

    ps.setup()
    fig, (ax0, ax1) = plt.subplots(1, 2, figsize=(ps.FULL, 2.9),
                                   gridspec_kw={'width_ratios': [1, 1.3]})
    Oc = np.vstack([O, O[:1]])
    ax0.fill(KB[:, 0], KB[:, 1], color=ps.FILL, lw=0)
    ax0.plot(Oc[:, 0], Oc[:, 1], color=ps.FAINT, lw=0.7, ls=(0, (3, 2)))
    for k, p in pcs:
        ax0.plot(p[:, 0], p[:, 1], color=ps.BLUE if k == 'edge' else ps.ORANGE, lw=1.6)
    ax0.plot([0], [0], 'o', color=ps.INK, ms=2)
    th = np.linspace(0, 2 * PI, 100)
    ax0.plot(V[0] + 0.2 * np.cos(th), V[1] + 0.2 * np.sin(th), color=ps.INK, lw=0.5)
    ax0.annotate('(b)', V + np.array([0.18, 0.16]), fontsize=7)
    ax0.set_xlim(-1.2, 1.35)
    ax0.set_ylim(-1.2, 1.2)
    ax0.set_aspect('equal')
    ax0.axis('off')
    ax0.set_title('(a) the smoothed octagon', y=-0.08)

    # (b) the corner, with the whole branch d_2 d_7 = sqrt2/4 in the window
    d1, d2 = np.array([1.0, 1.0]) / SQ2, np.array([1.0, 0.0])
    Bm = np.array([d1, d2]).T
    uv = np.linalg.solve(Bm, (arc0[len(arc0) // 2] - C))
    s = np.linspace(-5, 5, 3000)
    branch = C + np.outer(uv[0] * np.exp(s), d1) + np.outer(uv[1] * np.exp(-s), d2)
    assert np.abs(side_dist(2, branch) * side_dist(7, branch) - SQ2 / 4).max() < 1e-9
    xl, xr, yb, yt = 0.4, 2.7, -0.42, 1.22
    ax1.fill(KB[:, 0], KB[:, 1], color=ps.FILL, lw=0)
    xs = np.array([xl, xr])
    ax1.plot([1, 1], [V[1], yb], color=ps.BLUE, lw=0.6, ls=(0, (1, 1.5)))   # side 0 line
    ax1.plot([V[0], xl], [V[1], SQ2 - xl], color=ps.BLUE, lw=0.6, ls=(0, (1, 1.5)))  # side 1 line
    ax1.plot(xs, [1, 1], color=ps.FAINT, lw=0.7, ls=(0, (4, 2)))           # side 2, an asymptote
    ax1.plot(xs, xs - SQ2, color=ps.FAINT, lw=0.7, ls=(0, (4, 2)))         # side 7, an asymptote
    keep = (branch[:, 0] > xl) & (branch[:, 0] < xr) & (branch[:, 1] > yb) & (branch[:, 1] < yt)
    ax1.plot(branch[keep, 0], branch[keep, 1], color=ps.ORANGE, lw=0.6)
    for k, p in pcs:
        ax1.plot(p[:, 0], p[:, 1], color=ps.BLUE if k == 'edge' else ps.ORANGE, lw=1.8)
    for p, lab, off in ((V, '$V$', (0.035, 0.0)), (C, '$C$', (-0.02, 0.06)),
                        (T1, '$T_1$', (0.035, -0.06)), (T2, '$T_2$', (-0.03, 0.07))):
        ax1.plot(*p, 'o', color=ps.INK, ms=2.5)
        ax1.annotate(lab, p, xytext=(p[0] + off[0], p[1] + off[1]), fontsize=8)
    ax1.annotate('side $0$', (1.03, -0.38), fontsize=7, color=ps.BLUE)
    ax1.annotate('side $1$', (0.42, 1.06), fontsize=7, color=ps.BLUE)
    ax1.annotate('side $2$', (1.75, 1.04), fontsize=7, color=ps.FAINT)
    ax1.annotate('side $7$', (2.25, 0.62), fontsize=7, color=ps.FAINT)
    ax1.annotate('$d_7d_2=\\sqrt{2}/4$', (1.42, 0.12), fontsize=8, color=ps.ORANGE)
    ax1.set_xlim(xl, xr)
    ax1.set_ylim(yb, yt)
    ax1.set_aspect('equal')
    ax1.axis('off')
    ax1.set_title('(b) the corner $V$ between sides $0$ and $1$', y=-0.08)
    ps.save(fig, out / 'fig-octagon.pdf')


# ---- Figure: the densest packings ------------------------------------------------------------------

def fig_packing(out):
    A = regular_frame()
    KB = boundary_kh(80)
    gauge = oc.Gauge(KB)
    times = (0.0, P.tsw / 2, P.tsw)
    ps.setup()
    fig, axes = plt.subplots(1, 3, figsize=(ps.FULL, 2.3))
    for ax, t in zip(axes, times):
        s = np.array([P.curve(j, t) for j in range(6)])
        b0, b1 = 2 * s[0], 2 * s[1]
        # The lattice 2Z sigma_0(t) + 2Z sigma_1(t) has determinant sqrt12; its translates of K_H
        # touch K_H at the six contact points and do not overlap it: every nonzero lattice vector v
        # has gauge at least 2, with equality exactly at the six vectors 2 sigma_j(t).
        assert abs(oc.det2(b0, b1) - math.sqrt(12)) < 1e-9
        assert np.allclose(2 * s[2], b1 - b0, atol=1e-9)
        pts, co = oc.lattice_points(b0, b1, 3)
        g = gauge(pts)
        assert g.min() > 2 - 1e-6
        assert int(np.sum(g < 2 + 1e-6)) == 6
        assert np.abs(gauge(s) - 1).max() < 1e-6
        assert abs(oc.shoelace(boundary_kh(400)) / oc.det2(b0, b1) - oc.DELTA_OCT) < 1e-6
        assert abs(oc.shoelace(s) - 3 * SQ3 / 2) < 1e-9
        Kr = KB @ A.T
        for v in pts:
            if np.linalg.norm(v) < 4.2:
                w = A @ v
                fill = ps.FILL if np.linalg.norm(v) > 1e-9 else '#9ec3f5'
                ax.fill(Kr[:, 0] + w[0], Kr[:, 1] + w[1], color=fill, lw=0)
                ax.plot(Kr[:, 0] + w[0], Kr[:, 1] + w[1], color=ps.BLUE, lw=0.6)
        ax.fill(Kr[:, 0], Kr[:, 1], color='#9ec3f5', lw=0)
        ax.plot(Kr[:, 0], Kr[:, 1], color=ps.BLUE, lw=0.9)
        hexa = np.vstack([s, s[:1]]) @ A.T
        ax.plot(hexa[:, 0], hexa[:, 1], color=ps.INK, lw=0.6)
        ax.plot(hexa[:-1, 0], hexa[:-1, 1], 'o', color=ps.INK, ms=2.2)
        ax.set_xlim(-2.6, 2.6)
        ax.set_ylim(-2.6, 2.6)
        ax.set_aspect('equal')
        ax.axis('off')
    axes[0].set_title('$t=0$', y=-0.08)
    axes[1].set_title('$t=t_{\\mathrm{sw}}/2$', y=-0.08)
    axes[2].set_title('$t=t_{\\mathrm{sw}}$', y=-0.08)
    ps.save(fig, out / 'fig-packing.pdf')


# ---- Figure: the six arcs and the contact hexagons -------------------------------------------------

def fig_contacts(out):
    ts = np.linspace(0, P.tf, 801)
    arcs = [np.array([P.curve(j, t) for t in ts]) for j in range(6)]
    KB = boundary_kh(200)
    gauge = oc.Gauge(KB)
    for j, a in enumerate(arcs):
        # Each arc starts at the sixth root s_j and ends at s_{j+1}, on the boundary of K_H, and is
        # the arc sigma_0 traces on [j t_f, (j+1) t_f].
        assert np.allclose(a[0], oc.SIXTH[j], atol=1e-12)
        assert np.allclose(a[-1], oc.SIXTH[(j + 1) % 6], atol=1e-12)
        assert np.abs(gauge(a) - 1).max() < 1e-6
        assert np.allclose(a[::50], [P.curve(0, t + j * P.tf) for t in ts[::50]], atol=1e-12)
    # The control on [0, t_f] is e_2, e_0, e_1, e_2 on four intervals of length t_sw.
    assert [P.interval_control(i) for i in range(4)] == [2, 0, 1, 2]
    hex_times = (0.0, 0.5 * P.tsw, 1.5 * P.tsw)
    for t in hex_times:
        s = np.array([P.curve(j, t) for j in range(6)])
        assert abs(oc.shoelace(s) - 3 * SQ3 / 2) < 1e-9
        for j in range(6):
            assert abs(oc.det2(s[j], s[(j + 1) % 6]) - SQ3 / 2) < 1e-9
            assert np.allclose(s[(j + 3) % 6], -s[j], atol=1e-12)

    ps.setup()
    fig = plt.figure(figsize=(ps.FULL, 3.15))
    ax = fig.add_axes([0.0, 0.16, 0.5, 0.84])
    ax.fill(KB[:, 0], KB[:, 1], color=ps.FILL, lw=0)
    arc_cols = (ps.BLUE, ps.ORANGE, ps.GREEN, ps.PURPLE, ps.RED, '#5b6770')
    for j, a in enumerate(arcs):
        ax.plot(a[:, 0], a[:, 1], color=arc_cols[j], lw=1.8)
        mid = a[len(a) // 2]
        ax.annotate('', xy=a[len(a) // 2 + 8], xytext=mid,
                    arrowprops=dict(arrowstyle='-|>', color=arc_cols[j], lw=1.0, mutation_scale=7))
        ax.plot(*oc.SIXTH[j], 'o', mfc='white', mec=ps.INK, ms=4, mew=0.7)
        lab = 1.16 * oc.SIXTH[j]
        ax.annotate('$s_{%d}$' % j, lab, ha='center', va='center', fontsize=8)
    ax.set_xlim(-1.3, 1.3)
    ax.set_ylim(-1.3, 1.3)
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title('(a) the arcs $g(t)s_j$, $0\\leq t\\leq t_{\\mathrm{f}}$', y=-0.1)

    ax = fig.add_axes([0.5, 0.16, 0.5, 0.84])
    ax.fill(KB[:, 0], KB[:, 1], color=ps.FILL, lw=0)
    # the boundary coloured by the vertex control active when sigma_0 passes there
    for i in range(P.n_int):
        tt = np.linspace(i * P.tsw, (i + 1) * P.tsw, 40)
        pts = np.array([P.curve(0, t) for t in tt])
        ax.plot(pts[:, 0], pts[:, 1], color=color_of_label(P.interval_control(i)), lw=1.6)
    for t, ls in zip(hex_times, ('-', (0, (3, 1.5)), (0, (1, 1.2)))):
        s = np.array([P.curve(j, t) for j in range(6)])
        h = np.vstack([s, s[:1]])
        ax.plot(h[:, 0], h[:, 1], color=ps.INK, lw=0.7, ls=ls)
        ax.plot(s[:, 0], s[:, 1], 'o', color=ps.INK, ms=2.4)
    ax.set_xlim(-1.3, 1.3)
    ax.set_ylim(-1.3, 1.3)
    ax.set_aspect('equal')
    ax.axis('off')
    ax.set_title('(b) contact hexagons at $t=0,\\ t_{\\mathrm{sw}}/2,\\ 3t_{\\mathrm{sw}}/2$', y=-0.1)

    # the control word on [0, t_f]
    axb = fig.add_axes([0.2, 0.02, 0.6, 0.06])
    for i in range(4):
        c = P.interval_control(i)
        axb.add_patch(plt.Rectangle((i, 0), 1, 1, color=color_of_label(c), lw=0))
        axb.text(i + 0.5, 0.5, '$\\mathbf{e}_{%d}$' % c, ha='center', va='center', color='white',
                 fontsize=8)
    axb.set_xlim(0, 4)
    axb.set_ylim(0, 1)
    axb.set_xticks([0, 1, 2, 3, 4])
    axb.set_xticklabels(['$0$', '$t_{\\mathrm{sw}}$', '$2t_{\\mathrm{sw}}$', '$3t_{\\mathrm{sw}}$',
                         '$t_{\\mathrm{f}}$'], fontsize=7)
    axb.set_yticks([])
    for sp in axb.spines.values():
        sp.set_visible(False)
    ps.save(fig, out / 'fig-contacts.pdf')


# ---- Figure: the upper half-plane ------------------------------------------------------------------

def in_compact(x, y):
    """Hales--Vajjha's compact domain (Definition 2.x), as in Cited/HalesVajjha/CompactDomain.lean."""
    a3 = 1 / SQ3
    star = (y > 0) & (np.abs(x) < a3) & (x * x + y * y > 1 / 3)
    X = oc.Phi(x, y)
    r0, r1, r2 = oc.rho(X)
    return (star & (y <= 4.5) & (8 / 27 * y <= (x - a3) ** 2 + y ** 2)
            & (8 / 27 * y <= (x + a3) ** 2 + y ** 2)
            & (r0 >= 1 / 15) & (r1 >= 1 / 15) & (r2 >= 1 / 15))


def fig_halfplane(out):
    a3 = 1 / SQ3
    n_int = 3 * P.N                            # three periods: z returns to its start
    ts = P.times(80, n_int=n_int)
    z = P.z(ts)
    assert abs(z[0] - 1j * P.y0) < 1e-12
    zend = oc.z_of(P.X(np.array([3 * P.tf]))[0])
    assert abs(zend - z[0]) < 1e-9
    # The state of the octagon stays in the compact domain, hence in the star domain.
    assert in_compact(z.real, z.imag).all()
    # Its margins, which are 2 rho_{2-i}, are at least 2/15 there (Theorem 2.x).
    r = np.array(oc.rho(P.X(ts)))
    assert (2 * r).min() > 2 / 15
    ps.setup()
    fig, ax = plt.subplots(figsize=(ps.FULL * 0.62, 3.0))
    xg = np.linspace(-0.62, 0.62, 900)
    yg = np.linspace(0.005, 1.5, 900)
    XX, YY = np.meshgrid(xg, yg)
    star = (np.abs(XX) < a3) & (XX ** 2 + YY ** 2 > 1 / 3)
    comp = in_compact(XX, YY)
    ax.contourf(XX, YY, star.astype(float), levels=[0.5, 1.5], colors=['#eef3fb'])
    ax.contourf(XX, YY, comp.astype(float), levels=[0.5, 1.5], colors=[ps.FILL])
    ax.plot([-a3, -a3], [0, 1.5], color=ps.INK, lw=0.7)
    ax.plot([a3, a3], [0, 1.5], color=ps.INK, lw=0.7)
    th = np.linspace(0, PI, 400)
    ax.plot(a3 * np.cos(th), a3 * np.sin(th), color=ps.INK, lw=0.7)
    ax.plot([-0.62, 0.62], [0, 0], color=ps.INK, lw=0.7)
    for i in range(n_int):
        tt = np.linspace(i * P.tsw, (i + 1) * P.tsw, 60)
        zz = P.z(tt)
        ax.plot(zz.real, zz.imag, color=color_of_label(P.interval_control(i)), lw=1.6)
    ax.plot(0, P.y0, 'o', color=ps.INK, ms=3)
    ax.annotate('$z(0)=iy_0$', (0, P.y0), xytext=(-0.09, P.y0 - 0.12), fontsize=8)
    ax.annotate('$-1/\\sqrt{3}$', (-a3, 0), xytext=(-a3 - 0.05, -0.1), fontsize=7)
    ax.annotate('$1/\\sqrt{3}$', (a3, 0), xytext=(a3 - 0.05, -0.1), fontsize=7)
    ax.set_xlim(-0.66, 0.66)
    ax.set_ylim(-0.14, 1.5)
    ax.set_aspect('equal')
    ax.axis('off')
    ps.save(fig, out / 'fig-halfplane.pdf')


# ---- Figure: the control simplex and switching words -----------------------------------------------

def word_signs(labels):
    """The switch signs of a cyclic word read through the twist (the next period's labels are the
    labels plus one): +1 forward (label up by 1), -1 reverse (label down by 1)."""
    ext = list(labels) + [(labels[0] + 1) % 3]
    out = []
    for a, b in zip(ext, ext[1:]):
        d = (b - a) % 3
        assert d in (1, 2)
        out.append(1 if d == 1 else -1)
    return out


def fig_simplex(out):
    octw, fivew = [2, 0, 1, 2], [0, 1, 0, 2, 0]
    so, sf = word_signs(octw), word_signs(fivew)
    assert so == [1, 1, 1, 1] and sum(so) % 3 == 1
    assert sf == [1, -1, -1, 1, 1] and sum(sf) % 3 == 1
    ps.setup()
    fig = plt.figure(figsize=(ps.FULL, 2.2))
    ax = fig.add_axes([0.0, 0.0, 0.32, 1.0])
    V = {0: np.array([0.0, 1.0]), 1: np.array([-SQ3 / 2, -0.5]), 2: np.array([SQ3 / 2, -0.5])}
    tri = np.array([V[0], V[1], V[2], V[0]])
    ax.fill(tri[:, 0], tri[:, 1], color='#eef3fb', lw=0)
    ax.plot(tri[:, 0], tri[:, 1], color=ps.INK, lw=0.7)
    for i in range(3):
        ax.plot(*V[i], 'o', color=CC[i], ms=6)
        lab = 1.28 * V[i]
        ax.text(lab[0], lab[1], '$\\mathbf{e}_{%d}$' % i, ha='center', va='center', fontsize=9)
        a, b = V[i], V[(i + 1) % 3]
        m = (a + b) / 2
        nrm = m / np.linalg.norm(m)
        p0, p1 = a + 0.25 * (b - a) + 0.12 * nrm, a + 0.75 * (b - a) + 0.12 * nrm
        ax.add_patch(FancyArrowPatch(p0, p1, arrowstyle='-|>', mutation_scale=8, color=ps.BLUE,
                                     lw=0.9, connectionstyle='arc3,rad=-0.15'))
        q0, q1 = b + 0.25 * (a - b) - 0.12 * nrm, b + 0.75 * (a - b) - 0.12 * nrm
        ax.add_patch(FancyArrowPatch(q0, q1, arrowstyle='-|>', mutation_scale=8, color=ps.RED,
                                     lw=0.9, connectionstyle='arc3,rad=-0.15'))
    ax.text(0, -0.86, 'forward $i\\to i+1$', color=ps.BLUE, ha='center', fontsize=7)
    ax.text(0, -1.05, 'reverse $i\\to i-1$', color=ps.RED, ha='center', fontsize=7)
    ax.set_xlim(-1.3, 1.3)
    ax.set_ylim(-1.15, 1.45)
    ax.set_aspect('equal')
    ax.axis('off')

    ax = fig.add_axes([0.36, 0.0, 0.64, 1.0])

    def draw_word(y, labels, signs, title):
        n = len(labels)
        for rep in range(2):
            for k, lab in enumerate(labels):
                c = (lab + rep) % 3
                x = rep * n + k
                ax.add_patch(plt.Rectangle((x, y), 0.9, 0.5, color=CC[c], lw=0,
                                           alpha=1.0 if rep == 0 else 0.45))
                ax.text(x + 0.45, y + 0.25, '$%d$' % c, ha='center', va='center', color='white',
                        fontsize=8)
                sgn = signs[k]
                ax.text(x + 0.95, y + 0.68, '$+$' if sgn > 0 else '$-$', ha='center', va='center',
                        color=ps.BLUE if sgn > 0 else ps.RED, fontsize=8)
        ax.plot([n - 0.05, n - 0.05], [y - 0.12, y + 0.62], color=ps.INK, lw=0.6, ls=(0, (2, 1.5)))
        ax.text(-0.3, y + 0.25, title, ha='right', va='center', fontsize=8)

    draw_word(1.5, octw, so, 'octagon')
    draw_word(0.0, fivew, sf, 'five pieces')
    ax.text(4, 2.45, 'one period $|$ next period (labels $+1$)', ha='center', fontsize=7,
            color=ps.FAINT)
    ax.set_xlim(-2.2, 10.2)
    ax.set_ylim(-0.3, 2.6)
    ax.axis('off')
    ps.save(fig, out / 'fig-simplex.pdf')


# ---- Figure: the structure of the proof ------------------------------------------------------------

def fig_cases(out):
    ps.setup()
    fig, ax = plt.subplots(figsize=(ps.FULL, 4.0))
    ax.set_xlim(-1, 101.5)
    ax.set_ylim(4, 72)
    ax.axis('off')
    RED_FC, GREEN_FC, GREY_FC = '#fbeaea', '#e8f4ec', '#f6f8fa'

    def box(x, y, w, h, text, fc=GREY_FC, fs=7.0):
        ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle='round,pad=0.35',
                                    fc=fc, ec=ps.INK, lw=0.6))
        ax.text(x, y, text, ha='center', va='center', fontsize=fs, linespacing=1.3)

    def arrow(p, q, text=None, off=(0, 0)):
        ax.add_patch(FancyArrowPatch(p, q, arrowstyle='-|>', mutation_scale=7, color=ps.INK,
                                     lw=0.6, shrinkA=0, shrinkB=0))
        if text:
            ax.text((p[0] + q[0]) / 2 + off[0], (p[1] + q[1]) / 2 + off[1], text, fontsize=6.8,
                    ha='center', va='center')

    # first row: from the disk to a period
    box(13, 66, 22, 7, 'worst disk $K$\n(Section 2)')
    box(44, 66, 28, 7, 'global minimizer of the\ncontrol problem (Section 2)')
    box(80, 66, 30, 7, 'normal vertex period,\n$N$ pieces (Section 3)')
    arrow((24.4, 66), (29.6, 66))
    arrow((58.4, 66), (64.6, 66))
    # second row: the number of pieces
    box(85, 49, 24, 10, '$N\\leq5$ (Section 10):\ncost $\\geq A_{\\mathrm{oct}}$, equal\n'
        'only for the octagon', fc=GREEN_FC)
    box(38, 50, 36, 6, '$N\\geq6$: five sign classes (Section 4)')
    arrow((86, 62.2), (86, 54.4))
    arrow((72, 62.2), (50, 53.3))
    # third row: the five classes
    y3 = 32
    cls = ((9, 17, '$\\mathrm{R}$: every switch\nreverse (Sect. 5)'),
           (28.5, 19, '$\\mathrm{M3}$: a reverse run\nof length $\\neq 2$ (Sect. 5)'),
           (47.5, 16, '$\\mathrm{M1}$: word $(--+)^m$\n(Section 6)'),
           (65.5, 16, '$\\mathrm{F}$: every switch\nforward (Sect. 7)'),
           (86, 22, '$\\mathrm{M2}$: a forward run\nof length $\\geq 2$ (Sect. 8)'))
    for x, w, lab in cls:
        box(x, y3, w, 8, lab, fc=RED_FC, fs=6.3)
        arrow((38, 46.6), (x, y3 + 4.4))
    # fourth row: the three cases of M2
    y4 = 13
    m2 = ((46, 30, 'smaller turn on a short run:\ngates S0, S1, ..., S6\n(Section 9)'),
          (72, 18, 'nonshort,\nreverse successor\n(Section 8)'),
          (91, 18, 'nonshort,\nforward successor\n(Section 8)'))
    for x, w, lab in m2:
        box(x, y4, w, 10, lab, fc=RED_FC, fs=6.3)
        arrow((86, y3 - 4.4), (x, y4 + 5.4))
    ps.save(fig, out / 'fig-cases.pdf')


def main():
    out = HERE
    oc.verify(P)
    for f in (fig_octagon, fig_packing, fig_contacts, fig_halfplane, fig_simplex, fig_cases):
        f(out)
        print('wrote', f.__name__)
    for mod in sorted(HERE.glob('fig_*.py')):
        m = importlib.import_module(mod.stem)
        m.make(str(out))
        print('ran', mod.name)


if __name__ == '__main__':
    main()
