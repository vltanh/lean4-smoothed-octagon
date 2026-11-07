#!/usr/bin/env python3
"""The figures of the README and of docs/, written to docs/figures/:

- smoothed-octagon.svg: the smoothed octagon K of the library (circle representation), its image
  under the area-preserving map A, which is Reinhardt's regular picture, and one corner magnified;
- octagon-packing.svg: a patch of the densest lattice packing K + 2Λ, with the critical hexagon;
- multipoint.gif: the six contact points σ_j(t) moving around K over one period [0, t_f];
- upper-half-plane.svg: the state X(t) = Φ(z(t)) as a path in the upper half-plane;
- density-comparison.svg: the densities of the smoothed (6k+2)-gons, k = 1, …, 6, and of the disk.
- smoothed-octagon-plain.svg: Reinhardt's smoothed octagon alone, in its regular orientation, with
  the corners cut from the regular octagon as ghosts;
- octagon-construction.svg: how each corner is smoothed: the hyperbola, its asymptotes, the tangency
  points and the cut-off corner;
- octagon-tiling.svg: its densest (critical lattice) packing, cropped to a rectangle;
- packing-densities.svg: the disk, the regular octagon, the smoothed 14-gon and the smoothed octagon,
  of inradius 1, each with its densest lattice packing and its density;
- worst-packer.gif: the smoothed octagon's densest packing sliding through its one-parameter family
  of critical lattices (the balanced motion), for the top of the README; no lines, points or text.

    python3 scripts/figures/make_figures.py

Every figure is computed from the definitions of the library SmoothedPolygons (octagon.py), and the
facts that a caption states are checked by `assert`s.
"""
import math
import sys

sys.dont_write_bytecode = True  # leave scripts/figures/ as it is

import numpy as np  # noqa: E402

import octagon as oc  # noqa: E402
from reinhardt_figures import Figure, OUT, FAINT, COLORS, FILLS, INK, sb  # noqa: E402

PI = math.pi
SQ2 = math.sqrt(2)
BLUE, ORANGE, GREEN, PURPLE = COLORS[0], COLORS[1], COLORS[2], COLORS[3]
FLOOR = '#f3f4f6'
# The colours of the three vertex controls e₁, e₂, e₃ (Fin-index 0, 1, 2). Under e₁ the curve σ₀
# traces a hyperbolic arc, which is drawn in the same orange.
CONTROL_COLORS = (ORANGE, PURPLE, GREEN)
PIECE_COLORS = {'edge': BLUE, 'arc': ORANGE}
P = oc.OCT


# ---- shared pieces ------------------------------------------------------------------------------

def transform(pts, M=None, shift=(0.0, 0.0)):
    pts = np.asarray(pts, dtype=float)
    if M is not None:
        pts = pts @ np.asarray(M).T
    return pts + np.asarray(shift)


def boundary_pieces(M=None, shift=(0.0, 0.0), n_per=60):
    """The edges and arcs of ∂K, as (kind, points), mapped by p ↦ Mp + shift."""
    return [(pc[0], transform(oc.piece_points(P, pc, n_per), M, shift)) for pc in oc.pieces(P)]


def draw_k(f, M=None, shift=(0.0, 0.0), fill=FILLS[0], width=2.2, n_per=30, opacity=1):
    """K (or its image), filled, with its edges in blue and its hyperbolic arcs in orange."""
    f.polygon(transform(P.boundary(n_per), M, shift), fill=fill, stroke='none', width=0,
              opacity=opacity)
    for kind, pts in boundary_pieces(M, shift, n_per):
        f.polyline(pts, stroke=PIECE_COLORS[kind], width=width)


def runs_inside(pts, box):
    """The maximal runs of consecutive points inside the box (xmin, xmax, ymin, ymax)."""
    x0, x1, y0, y1 = box
    inside = (pts[:, 0] >= x0) & (pts[:, 0] <= x1) & (pts[:, 1] >= y0) & (pts[:, 1] <= y1)
    out, cur = [], []
    for p, ok in zip(pts, inside):
        if ok:
            cur.append(p)
        elif cur:
            out.append(np.array(cur))
            cur = []
    if cur:
        out.append(np.array(cur))
    return [r for r in out if len(r) > 1]


def clip_polygon(pts, box):
    """The polygon clipped to the box (xmin, xmax, ymin, ymax) (Sutherland–Hodgman)."""
    x0, x1, y0, y1 = box
    out = [np.asarray(p, dtype=float) for p in pts]
    for axis, bound, keep_le in ((0, x0, False), (0, x1, True), (1, y0, False), (1, y1, True)):
        inside = (lambda p: p[axis] <= bound) if keep_le else (lambda p: p[axis] >= bound)
        res = []
        for m, cur in enumerate(out):
            prev = out[m - 1]
            if inside(cur) != inside(prev):
                lam = (bound - prev[axis]) / (cur[axis] - prev[axis])
                res.append(prev + lam * (cur - prev))
            if inside(cur):
                res.append(cur)
        out = res
    return out


def hyperbola_branch(c, center, through, s_max=6.0, n=1500):
    """The branch through the point `through` of the hyperbola with coefficients c and centre
    `center`: center + u d₁ + v d₂ with uv constant (d₁, d₂ the asymptote directions)."""
    d1, d2 = oc.asymptote_directions(c)
    u0, v0 = np.linalg.solve(np.array([d1, d2]).T, through - center)
    s = np.linspace(-s_max, s_max, n)
    pts = center + np.outer(u0 * np.exp(s), d1) + np.outer(v0 * np.exp(-s), d2)
    assert np.abs(oc.conic_eval(c, pts)).max() < 1e-8 * max(1.0, np.abs(pts).max() ** 2)
    return pts


def rot(a):
    return np.array([[math.cos(a), -math.sin(a)], [math.sin(a), math.cos(a)]])


# ---- smoothed-octagon.svg -----------------------------------------------------------------------

def smoothed_octagon(facts):
    """Left: the library's K in circle representation, with the six points s_j* = σ_j(0) on the unit
    circle and the octagon O (dashed) of the lines of its edges. Middle: its image A K under the
    area-preserving map A, Reinhardt's smoothed octagon, inside the regular octagon A O. Right: one
    corner of A K, magnified: the hyperbolic arc (traced under e₁), its hyperbola (dotted) and the two
    edges (traced under e₃ and e₂)."""
    A = oc.classical_map(P)
    O = oc.edge_polygon(P)
    B = P.boundary(200)
    AB, AO = transform(B, A), transform(O, A)
    gK, gAK = oc.Gauge(B), oc.Gauge(AB)
    # Reinhardt's picture A K is invariant under the rotation by π/4; the library's K is not (it is
    # an affine image of it), and A is not a similarity.
    turned = AB @ rot(PI / 4).T
    assert 1 - 1e-6 < gAK(turned).min() and gAK(turned).max() < 1 + 1e-6
    assert gK(B @ rot(PI / 4).T).max() > 1.02
    assert abs(A[0, 0] - 0.97329) < 1e-5 and abs(A[1, 1] - 1.02744) < 1e-5 and A[0, 1] == A[1, 0] == 0
    # The arcs clip the corners of O by less than 3% of its inradius.
    gap = max(np.min(np.linalg.norm(B - v, axis=1)) for v in O)
    inradius = min(abs(oc.cross(d, -p)) for p, d in oc.edge_lines(P))
    assert 0.02 < gap < 0.03 * inradius, gap
    # The six points s_j* = σ_j(0) lie on the boundary of K and on the unit circle.
    assert np.allclose(np.linalg.norm(oc.SIXTH, axis=1), 1) and np.abs(gK(oc.SIXTH) - 1).max() < 1e-6

    # The arc traced on [t_sw, 2t_sw] (control e₁), between the edge x = 1 (traced under e₂, e₃) and
    # the next one (traced under e₂, e₃); its hyperbola, in the coordinates of A K.
    pc, c, center, _ = facts['hyperbolas'][0]
    assert pc[1] == 1 and [P.interval_control(i) for i in (0, 1, 2)] == [2, 0, 1]
    Ainv = np.linalg.inv(A)
    Q = Ainv.T @ np.array([[c[0], c[1] / 2], [c[1] / 2, c[2]]]) @ Ainv
    lin = Ainv.T @ c[3:5]
    cA = np.array([Q[0, 0], 2 * Q[0, 1], Q[1, 1], lin[0], lin[1], c[5]])
    ends = [A @ P.curve(0, P.tsw), A @ P.curve(0, 2 * P.tsw)]
    arc_mid = A @ P.curve(0, 1.5 * P.tsw)
    corner = AO[np.argmin(np.linalg.norm(AO - arc_mid, axis=1))]
    assert abs(math.degrees(math.atan2(corner[1], corner[0])) - 22.5) < 1e-9
    branch = hyperbola_branch(cA, A @ center, arc_mid, s_max=3.0)

    s, gapx = 1.18, 0.5
    mid_c = np.array([2 * s + gapx, 0.0])
    zoom_w, zoom_mag = 0.17, 3.5
    big = zoom_w * zoom_mag
    zoom_c = np.array([mid_c[0] + s + gapx + big, 0.0])
    f = Figure(-s - 0.05, zoom_c[0] + big + 0.05, -s - 0.1, s + 0.05, 118)
    # Left: K in circle representation.
    th = np.linspace(0, 2 * PI, 400)
    draw_k(f)
    f.polygon(O, stroke=INK, width=1.1, dash='5 4')
    f.polyline(np.c_[np.cos(th), np.sin(th)], stroke=FAINT, width=1.0, dash='2 3')
    for j, p in enumerate(oc.SIXTH):
        f.dot(p, r=3.4)
        q = 1.15 * p + (0, 0.12 if j in (0, 3) else 0)
        f.text(q, f's{"₀₁₂₃₄₅"[j]}*', size=14)
    f.text((0, 0.08), 'K', size=20, color=BLUE)
    f.text((0, -0.16), 'circle representation', size=12, italic=False)
    # The map A.
    f.line((s + 0.06, 0.0), (mid_c[0] - s - 0.04, 0.0), stroke=INK, width=1.3, arrow=True)
    f.text((s + gapx / 2 + 0.01, 0.1), 'A', size=16)
    # Middle: A K, Reinhardt's smoothed octagon, inside the regular octagon A O.
    draw_k(f, A, mid_c)
    f.polygon(AO + mid_c, stroke=INK, width=1.1, dash='5 4')
    f.text((mid_c[0], 0.08), 'A K', size=20, color=BLUE)
    f.text((mid_c[0], -0.16), 'Reinhardt’s octagon', size=12, italic=False)
    # The zoom window, centred between the ends of the arc, and its magnified copy.
    wc = (ends[0] + ends[1] + corner) / 3
    win = (wc[0] - zoom_w, wc[0] + zoom_w, wc[1] - zoom_w, wc[1] + zoom_w)
    assert all(win[0] < e[0] < win[1] and win[2] < e[1] < win[3] for e in ends + [corner])
    sq = np.array([(-1, -1), (1, -1), (1, 1), (-1, 1)], dtype=float)
    f.polygon(wc + mid_c + zoom_w * sq, stroke=INK, width=0.9)
    f.polygon(zoom_c + big * sq, fill='#ffffff', stroke=INK, width=0.9)
    for sy in (-1, 1):
        f.line(wc + mid_c + (zoom_w, sy * zoom_w), zoom_c + (-big, sy * big), stroke=FAINT,
               width=0.8, dash='3 3')

    def mag(pts):
        return (np.asarray(pts) - wc) * zoom_mag + zoom_c

    n_v = len(AO)
    k_c = int(np.argmin(np.linalg.norm(AO - corner, axis=1)))
    seg = np.concatenate([np.linspace(AO[(k_c - 1) % n_v], AO[k_c], 800),
                          np.linspace(AO[k_c], AO[(k_c + 1) % n_v], 800)])
    f.polygon(mag(clip_polygon(AB, win)), fill=FILLS[0], stroke='none', width=0)
    for run in runs_inside(branch, win):
        f.polyline(mag(run), stroke=ORANGE, width=1.3, dash='1.5 3')
    for run in runs_inside(seg, win):
        f.polyline(mag(run), stroke=INK, width=1.1, dash='5 4')
    for kind, pts in boundary_pieces(A, n_per=400):
        for run in runs_inside(pts, win):
            f.polyline(mag(run), stroke=PIECE_COLORS[kind], width=2.6)
    for e in ends:
        f.dot(mag(e), r=3.4)
    # The labels sit off the curves: the edges' halves next to the arc, on their outer side.
    out_v, out_d = np.array([1.0, 0.0]), np.array([1.0, 1.0]) / math.sqrt(2)
    f.text(mag(arc_mid) + (-0.16, -0.05), 'e₁', size=15, color=ORANGE)
    f.text(mag(ends[0] + (0, -0.03)) + 0.12 * out_v, 'e₃', size=15, color=BLUE)
    f.text(mag(ends[1] + 0.03 * np.array([-1.0, 1.0]) / math.sqrt(2)) + 0.12 * out_d, 'e₂',
           size=15, color=BLUE)
    f.text(zoom_c + (0, -big - 0.13), f'one corner, ×{zoom_mag:g}', size=12, italic=False)
    return f.save('smoothed-octagon',
                  'The smoothed octagon K of the library, in circle representation (left): its 8 '
                  'straight edges (blue) alternate with 8 hyperbolic arcs (orange), inside the octagon O '
                  'of the edge lines (dashed); the six points s_j* = σ_j(0) lie on the unit circle. The '
                  'area-preserving map A = diag(0.973, 1.027) takes it to Reinhardt’s smoothed octagon '
                  '(middle), inside a regular octagon. Right: one corner magnified; σ₀ traces the edge '
                  'under e₃, the arc under e₁ and the next edge under e₂, and the hyperbola of the arc '
                  '(dotted) is tangent to both edges')


# ---- octagon-packing.svg -------------------------------------------------------------------------

def lattice_patch(rings=2):
    """The centres 2(a s₀* + b s₁*) of the copies of K within `rings` steps of the origin."""
    b0, b1 = 2 * P.curve(0, 0.0), 2 * P.curve(1, 0.0)
    pts, _ = oc.lattice_points(b0, b1, rings)
    keep = np.linalg.norm(pts, axis=1) < 2 * rings + 1e-9
    return np.vstack([[0.0, 0.0], pts[keep]]), b0, b1


def octagon_packing():
    """A patch of the lattice packing K + 2Λ, Λ = Z s₀* + Z s₁*, of density area(K)/√12 = δ_oct, with
    the critical hexagon s₀* … s₅* of the central copy, where it touches its six neighbours."""
    centres, b0, b1 = lattice_patch()
    B = P.boundary(200)
    gK = oc.Gauge(B)
    assert len(centres) == 19
    # The lattice 2Λ has covolume √12, so the packing has density area(K)/√12 = δ_oct.
    assert abs(oc.det2(b0, b1) - math.sqrt(12)) < 1e-12
    assert abs(oc.shoelace(P.boundary(400)) / abs(oc.det2(b0, b1)) - oc.DELTA_OCT) < 1e-6
    # The copies have disjoint interiors: ‖v - w‖_K ≥ 2 for any two centres, with equality exactly for
    # neighbours, which touch at the midpoint of their centres.
    nbrs = {tuple(np.round(v, 9)) for v in (b0, b1, b1 - b0, -b0, -b1, b0 - b1)}
    for m, v in enumerate(centres):
        for w in centres[m + 1:]:
            d = gK(v - w)[0]
            assert d > 2 - 1e-6
            assert (d < 2 + 1e-6) == (tuple(np.round(v - w, 9)) in nbrs or
                                      tuple(np.round(w - v, 9)) in nbrs)
    # The central copy touches its six neighbours K + 2s_j* at the vertices s_j* of the critical
    # hexagon, a regular hexagon of area 3√3/2 inscribed in K.
    hexagon = oc.SIXTH
    assert np.abs(gK(hexagon) - 1).max() < 1e-6
    assert abs(oc.shoelace(hexagon) - 3 * oc.SQRT3 / 2) < 1e-12
    assert all(np.abs(gK(hexagon[j] - 2 * hexagon[j]) - 1).max() < 1e-6 for j in range(6))

    f = Figure(-5.15, 5.15, -5.25, 4.62, 54)
    for v in centres[1:]:
        draw_k(f, shift=v, width=1.2, opacity=0.5, n_per=8)
    draw_k(f, width=1.8, n_per=24)
    f.polygon(hexagon, stroke=INK, width=1.3)
    for v, label, dx, dy in ((b0, '2s₀*', 0.0, -0.3), (b1, '2s₁*', 0.36, 0.0)):
        f.line((0, 0), v, stroke=INK, width=1.2, arrow=True)
        f.text(v * 0.7 + (dx, dy), label, size=14)
    for p in hexagon:
        f.dot(p, r=3.6)
    f.dot((0, 0), r=2.4)
    f.text((-0.45, -0.38), 'K', size=17, color=BLUE)
    f.text((0, -4.95), 'δ = area(K)/√12 = (8 − 4√2 − ln 2)/(2√2 − 1) ≈ 0.902414', size=15, italic=False)
    return f.save('octagon-packing',
                  'A patch of the densest lattice packing of the smoothed octagon K: the copies K + 2Λ, '
                  'Λ = Z s₀* + Z s₁*, of covolume √12 and density area(K)/√12 = (8 − 4√2 − ln 2)/(2√2 − 1) '
                  '≈ 0.902414. The central copy touches its six neighbours at the vertices s_j* of its '
                  'critical hexagon (black), a hexagon of area 3√3/2 inscribed in K')


# ---- multipoint.gif ----------------------------------------------------------------------------

def multipoint_gif(name='multipoint.gif', n_frames=60, width=520):
    """The balanced motion: as t runs over [0, t_f], the six points σ_j(t) move around the boundary of
    K, the hexagon σ₀(t) … σ₅(t) stays inscribed with area 3√3/2, and the six copies K + 2σ_j(t) touch
    K at σ_j(t) without overlapping it; at t_f the picture is that of t = 0 with σ_j in the place of
    σ_{j+1}. The timeline shows the control e₃, e₁, e₂, e₃."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import Polygon
    from PIL import Image
    plt.rcParams.update({'mathtext.fontset': 'dejavuserif'})

    B = P.boundary(200)
    gK = oc.Gauge(B)
    ts = np.linspace(0, P.tf, n_frames, endpoint=False)
    for t in ts:
        S = np.array([P.curve(j, t) for j in range(6)])
        # The six neighbours touch K at σ_j(t), and no two of the seven copies overlap.
        assert np.abs(gK(S) - 1).max() < 1e-6
        cs = np.vstack([[0.0, 0.0], 2 * S])
        assert min(gK(v - w)[0] for m, v in enumerate(cs) for w in cs[m + 1:]) > 2 - 1e-6
        assert abs(oc.shoelace(S) - 3 * oc.SQRT3 / 2) < 1e-12
        # Off the switching times, exactly two opposite points lie on hyperbolic arcs.
        if (t / P.tsw) % 1 > 1e-9:
            bent = [j for j in range(6) if P.bending(j, t) > 1e-6]
            assert len(bent) == 2 and (bent[1] - bent[0]) == 3, bent
    # The motion closes up after t_f, with the indices shifted by one.
    assert all(np.allclose(P.curve(j, P.tf), oc.SIXTH[(j + 1) % 6], atol=1e-12) for j in range(6))

    lim, bottom = 3.3, -4.25
    w_in = width / 100
    h_in = w_in * (lim - bottom) / (2 * lim)
    pieces = [(kind, pts) for kind, pts in boundary_pieces(n_per=40)]
    Kpts = P.boundary(40)
    th = np.linspace(0, 2 * PI, 200)
    t_x0, t_x1, t_y = -2.6, 2.6, -3.78
    labels = ('e₃', 'e₁', 'e₂', 'e₃')
    images = []
    for t in ts:
        S = np.array([P.curve(j, t) for j in range(6)])
        fig = plt.figure(figsize=(w_in, h_in), dpi=100)
        ax = fig.add_axes([0, 0, 1, 1])
        ax.set_xlim(-lim, lim)
        ax.set_ylim(bottom, lim)
        ax.set_aspect('equal')
        ax.axis('off')
        for v in 2 * S:
            ax.add_patch(Polygon(Kpts + v, closed=True, facecolor='#eef0f3', edgecolor=FAINT, lw=1.0))
        ax.add_patch(Polygon(Kpts, closed=True, facecolor=FILLS[0], edgecolor='none'))
        for kind, pts in pieces:
            ax.plot(pts[:, 0], pts[:, 1], color=PIECE_COLORS[kind], lw=2.2, solid_capstyle='butt')
        ax.add_patch(Polygon(S, closed=True, facecolor='none', edgecolor=INK, lw=1.1))
        ax.plot(oc.SIXTH[:, 0], oc.SIXTH[:, 1], 'o', ms=6.5, mfc='white', mec=FAINT, mew=1.1)
        ax.plot(S[:, 0], S[:, 1], 'o', ms=6.5, color=INK)
        q = S[0] * 1.2
        ax.text(q[0], q[1], 'σ₀', fontsize=13, family='serif', style='italic', color=INK,
                ha='center', va='center')
        # The timeline [0, t_f], coloured by the control.
        for m in range(4):
            a = t_x0 + (t_x1 - t_x0) * m / 4
            b = t_x0 + (t_x1 - t_x0) * (m + 1) / 4
            c = CONTROL_COLORS[P.interval_control(m)]
            ax.plot([a + 0.03, b - 0.03], [t_y, t_y], color=c, lw=5, solid_capstyle='butt')
            ax.text((a + b) / 2, t_y + 0.27, labels[m], fontsize=12, family='serif', color=c,
                    ha='center', va='center')
        x = t_x0 + (t_x1 - t_x0) * t / P.tf
        ax.plot([x], [t_y], 'o', ms=9, color=INK)
        ax.text(t_x0 - 0.12, t_y, '0', fontsize=12, family='serif', ha='right', va='center', color=INK)
        ax.text(t_x1 + 0.12, t_y, r'$t_\mathrm{f}$', fontsize=13, ha='left', va='center', color=INK)
        fig.canvas.draw()
        rgba = np.asarray(fig.canvas.buffer_rgba())
        images.append(Image.fromarray(rgba[:, :, :3].copy()))
        plt.close(fig)
    # One palette for all frames, from a frame of the middle, with pure white kept; each frame is
    # mapped to its nearest colours (Pillow's own mapping is coarser and greys the background).
    pal = images[n_frames // 3].quantize(colors=63, method=Image.Quantize.MEDIANCUT)
    rgb = np.vstack([[255, 255, 255], np.array(pal.getpalette()[:3 * 63]).reshape(-1, 3)])
    frames_q = []
    for im in images:
        a = np.asarray(im).reshape(-1, 3).astype(int)
        cols, inv = np.unique(a, axis=0, return_inverse=True)
        near = ((cols[:, None, :] - rgb[None, :, :]) ** 2).sum(axis=2).argmin(axis=1)
        q = Image.fromarray(near[inv.ravel()].reshape(im.size[1], im.size[0]).astype(np.uint8), 'P')
        q.putpalette(rgb.ravel().tolist())
        frames_q.append(q)
    path = OUT / name
    path.parent.mkdir(parents=True, exist_ok=True)
    frames_q[0].save(path, save_all=True, append_images=frames_q[1:], duration=70, loop=0,
                     optimize=True, disposal=1)
    assert path.stat().st_size < 2 * 1024 * 1024
    return path


# ---- upper-half-plane.svg ------------------------------------------------------------------------

def fit_line_through(pts, q):
    """The largest distance of the points from the line through q and the first point."""
    d = pts[-1] - q
    return np.abs([oc.cross(d, p - q) for p in pts]).max() / np.linalg.norm(d)


def fit_circle(pts):
    """The circle x² + y² + Dx + Ey + F = 0 through the points (least squares): centre, radius,
    largest residual."""
    M = np.c_[pts[:, 0], pts[:, 1], np.ones(len(pts))]
    rhs = -(pts[:, 0] ** 2 + pts[:, 1] ** 2)
    (D, E, F), *_ = np.linalg.lstsq(M, rhs, rcond=None)
    c = np.array([-D / 2, -E / 2])
    r = math.sqrt(c @ c - F)
    return c, r, np.abs(np.linalg.norm(pts - c, axis=1) - r).max()


def upper_half_plane():
    """The state X(t) = Φ(z(t)) of the smoothed octagon as a path z(t) in the upper half-plane, for t
    in [0, t_f]: it stays in the star domain ρ₀, ρ₁, ρ₂ > 0, the ideal triangle with vertices -1/√3,
    1/√3, ∞ (shaded). Under e₃ it moves along a line through -1/√3, under e₁ along a circle through
    ±1/√3, under e₂ along a line through 1/√3 (Lemma 7.2.1); the fourth arc, under e₃ again, retraces
    the first, so that z(t_f) = z(t_sw) = R⁻¹·z(0): the twisted boundary condition X(t_f) = R⁻¹X(0)R."""
    a3 = 1 / oc.SQRT3
    arcs = [P.z(np.linspace(i * P.tsw, (i + 1) * P.tsw, 200)) for i in range(4)]
    pts = [np.c_[z.real, z.imag] for z in arcs]
    z0 = complex(P.z(0.0))
    allz = np.concatenate(arcs)
    # The star domain: ρ₀ > 0 ⟺ x > -1/√3, ρ₁ > 0 ⟺ x < 1/√3, ρ₂ > 0 ⟺ x² + y² > 1/3.
    for xy in ((0.3, 0.9), (-0.5, 0.4), (0.1, 0.5)):
        r0, r1, r2 = oc.rho(oc.Phi(*xy))
        x, y = xy
        assert (r0 > 0) == (x > -a3) and (r1 > 0) == (x < a3) and (r2 > 0) == (x * x + y * y > 1 / 3)
    assert np.all(np.abs(allz.real) < a3 - 0.05) and np.all(np.abs(allz) ** 2 > 1 / 3 + 0.05)
    # The arcs and their generalized circles (Lemma 7.2.1).
    assert [P.interval_control(i) for i in range(4)] == [2, 0, 1, 2]
    assert fit_line_through(pts[0], np.array([-a3, 0.0])) < 1e-12
    assert fit_line_through(pts[2], np.array([a3, 0.0])) < 1e-12
    c1, r1, res = fit_circle(pts[1])
    assert res < 1e-10 and abs(c1[0]) < 1e-9
    assert abs(np.linalg.norm(c1 - (a3, 0)) - r1) < 1e-9 and abs(np.linalg.norm(c1 + (a3, 0)) - r1) < 1e-9
    # The fourth arc retraces the first (R³ = -I acts trivially); the endpoints.
    assert np.abs(arcs[3] - arcs[0]).max() < 1e-12
    assert abs(arcs[0][-1] - oc.mobius(oc.R_INV, z0)) < 1e-12
    assert abs(arcs[1][-1] - oc.mobius(oc.R_INV @ oc.R_INV, z0)) < 1e-12
    assert abs(arcs[2][-1] - z0) < 1e-12 and abs(arcs[3][-1] - oc.mobius(oc.R_INV, z0)) < 1e-12
    # R fixes i and rotates the ideal triangle: R⁻¹ sends -1/√3 to 1/√3, and 1/√3 to ∞.
    assert abs(oc.mobius(oc.R, 1j) - 1j) < 1e-15
    assert abs(oc.mobius(oc.R_INV, -a3) - a3) < 1e-12 and abs(oc.R_INV[1, 0] * a3 + oc.R_INV[1, 1]) < 1e-15

    xmin, xmax, ymin, ymax = -0.86, 0.86, -0.17, 1.72
    f = Figure(xmin, xmax, ymin, ymax, 290)
    phi = np.linspace(PI, 0, 200)
    semi = np.c_[a3 * np.cos(phi), a3 * np.sin(phi)]
    dom = np.vstack([[(-a3, ymax)], semi, [(a3, ymax)]])
    f.polygon(dom, fill=FLOOR, stroke='none', width=0)
    f.line((xmin + 0.02, 0), (xmax - 0.02, 0), stroke=INK, width=1.1)
    f.line((-a3, 0), (-a3, ymax), stroke=FAINT, width=1.2)
    f.line((a3, 0), (a3, ymax), stroke=FAINT, width=1.2)
    f.polyline(semi, stroke=FAINT, width=1.2)
    # The generalized circles of the three arcs, dashed.
    top = ymax - 0.02
    for q, arc, col in ((-a3, pts[0], GREEN), (a3, pts[2], PURPLE)):
        d = arc[-1] - np.array([q, 0.0])
        lam = top / d[1]
        f.line((q, 0), (q + lam * d[0], top), stroke=col, width=1.0, dash='4 4')
    beta = math.asin(c1[1] / r1)                  # the circle meets the real axis at ±1/√3
    assert c1[1] > 0
    ang = np.linspace(-beta, PI + beta, 400)
    circ = c1 + r1 * np.c_[np.cos(ang), np.sin(ang)]
    f.polyline(circ, stroke=ORANGE, width=1.0, dash='4 4')
    # The path, each arc with an arrow at its middle.
    for i in range(3):
        col = CONTROL_COLORS[P.interval_control(i)]
        a = pts[i]
        h = len(a) // 2
        f.polyline(a[:h + 1], stroke=col, width=3.0, arrow=True)
        f.polyline(a[h:], stroke=col, width=3.0)
    z1, z2 = arcs[0][-1], arcs[1][-1]
    for z in (z0, z1, z2):
        f.dot((z.real, z.imag), r=4.2)
    f.dot((0, 1), r=2.6, fill=FAINT)
    f.text((0.035, 1.0), 'i', size=15, color=FAINT, anchor='start')
    f.text((z0.real + 0.03, z0.imag - 0.06), sb('z(0) = i y', '0', size=14), size=14, anchor='start')
    f.text((z1.real + 0.07, z1.imag + 0.03), sb('z(t', 'f', ') = R', size=14) + '<tspan dy="-4.8" '
           'font-size="9.5">−1</tspan><tspan dy="4.8">·z(0)</tspan>', size=14, anchor='start')
    f.text((z2.real - 0.07, z2.imag + 0.015), 'R<tspan dy="-4.8" font-size="9.5">−2</tspan>'
           '<tspan dy="4.8">·z(0)</tspan>', size=14, anchor='end')
    m0, m1, m2 = pts[0][100], pts[1][100], pts[2][100]
    f.text(m0 + (0.06, -0.04), 'e₃', size=16, color=GREEN, italic=False, anchor='start')
    f.text(m1 + (0.0, 0.07), 'e₁', size=16, color=ORANGE, italic=False)
    f.text(m2 + (-0.06, -0.04), 'e₂', size=16, color=PURPLE, italic=False, anchor='end')
    f.text((-a3, -0.08), '−1/√3', size=14, italic=False)
    f.text((a3, -0.08), '1/√3', size=14, italic=False)
    f.text((0, -0.08), '0', size=14, italic=False, color=FAINT)
    f.text((-a3 + 0.02, 1.62), sb('ρ', '0', ' = 0', size=13), size=13, anchor='start', color=FAINT)
    f.text((a3 - 0.02, 1.62), sb('ρ', '1', ' = 0', size=13), size=13, anchor='end', color=FAINT)
    f.text((0, a3 - 0.06), sb('ρ', '2', ' = 0', size=13), size=13, color=FAINT)
    f.text((0, 1.5), 'star domain', size=14, italic=False, color=INK)
    return f.save('upper-half-plane',
                  'The state X(t) = Φ(z(t)) of the smoothed octagon for t in [0, t_f], as a path in the '
                  'upper half-plane inside the star domain ρ₀, ρ₁, ρ₂ > 0 (shaded), the ideal triangle '
                  'with vertices −1/√3, 1/√3 and ∞. From z(0) = i y₀ it runs along a line through −1/√3 '
                  'under e₃ (green), a circle through ±1/√3 under e₁ (orange), a line through 1/√3 under '
                  'e₂ (purple), and the first line again under e₃: z(t_f) = R⁻¹·z(0), the twisted '
                  'boundary condition X(t_f) = R⁻¹X(0)R. R fixes i')


# ---- density-comparison.svg ----------------------------------------------------------------------

def density_comparison(facts):
    """The densities area/√12 of the smoothed (6k+2)-gons, k = 1, …, 6, computed as the cost of their
    trajectories: they increase with k towards π/√12, the density of the disk; the smoothed octagon
    (k = 1) has the least, δ_oct ≈ 0.902414, below the regular octagon's (4 + 4√2)/(5 + 4√2)."""
    dens = facts['densities']
    assert len(dens) == 6 and abs(dens[0] - oc.DELTA_OCT) < 1e-12
    assert all(a < b for a, b in zip(dens, dens[1:])) and dens[-1] < oc.DELTA_DISK
    assert dens[0] < dens[1] < oc.DELTA_REGULAR_OCTAGON < dens[2] < oc.DELTA_DISK
    assert oc.DELTA_DISK - dens[-1] < 1e-4

    W, H = 640, 340
    left, right, top, bottom = 78, 190, 22, 62
    y_lo, y_hi = 0.90175, 0.9072
    f = Figure(0, W, 0, H, 1, pad=0)

    def X(k):
        return left + (k - 0.5) / 6 * (W - left - right)

    def Y(v):
        return bottom + (v - y_lo) / (y_hi - y_lo) * (H - top - bottom)

    for v in np.arange(0.902, 0.90701, 0.001):
        f.line((left, Y(v)), (W - right + 10, Y(v)), stroke='#e5e7eb', width=1)
        f.text((left - 8, Y(v)), f'{v:.3f}', size=12, italic=False, anchor='end', color='#6b7280')
    f.line((left, bottom), (W - right + 10, bottom), stroke=FAINT, width=1)
    for k in range(1, 7):
        f.text((X(k), bottom - 16), str(k), size=13, italic=False, color='#6b7280')
        f.text((X(k), bottom - 31), f'({6 * k + 2})', size=11, italic=False, color='#9ca3af')
    f.text(((left + W - right) / 2, bottom - 50), 'k  (the smoothed (6k + 2)-gon)', size=13,
           italic=False, color='#6b7280')
    f.text((18, (bottom + H - top) / 2), 'δ', size=16, color='#6b7280')
    # The disk.
    yd = Y(oc.DELTA_DISK)
    f.line((left, yd), (W - right + 10, yd), stroke=INK, width=1.3, dash='5 4')
    f.text((W - right + 16, yd + 8), 'disk', size=13, italic=False, anchor='start')
    f.text((W - right + 16, yd - 8), f'π/√12 = {oc.DELTA_DISK:.6f}', size=12, italic=False,
           anchor='start', color='#6b7280')
    # The regular octagon, for comparison.
    yr = Y(oc.DELTA_REGULAR_OCTAGON)
    f.add(f'<g><title>regular octagon: (4 + 4√2)/(5 + 4√2) = {oc.DELTA_REGULAR_OCTAGON:.6f}</title>'
          f'<circle cx="{f.p(X(1), yr)[0]:.1f}" cy="{f.p(X(1), yr)[1]:.1f}" r="5" fill="#ffffff" '
          f'stroke="{INK}" stroke-width="1.5"/></g>')
    f.text((X(1), yr - 18), 'regular octagon', size=12, italic=False, color='#6b7280')
    f.text((X(1), yr - 32), f'{oc.DELTA_REGULAR_OCTAGON:.6f}', size=12, italic=False, color='#6b7280')
    for k, d in enumerate(dens, start=1):
        col = ORANGE if k == 1 else BLUE
        x, y = f.p(X(k), Y(d))
        f.add(f'<g><title>k = {k}, smoothed {6 * k + 2}-gon: δ = {d:.6f}</title>'
              f'<circle cx="{x:.1f}" cy="{y:.1f}" r="6" fill="{col}" stroke="#ffffff" '
              f'stroke-width="2"/></g>')
    f.text((X(1) + 12, Y(dens[0]) + 1), 'smoothed octagon', size=13, italic=False, anchor='start')
    f.text((X(1) + 12, Y(dens[0]) - 15), sb('δ', 'oct', f' = {dens[0]:.6f}', size=12), size=12,
           italic=False, anchor='start', color='#6b7280')
    f.text((X(6), Y(dens[5]) - 16), f'{dens[5]:.6f}', size=12, italic=False, color='#6b7280')
    return f.save('density-comparison',
                  'The packing densities area/√12 of the smoothed (6k + 2)-gons for k = 1, …, 6 '
                  '(the area computed as the cost of the trajectory): they increase with k towards '
                  'the density π/√12 of the disk (dashed). The smoothed octagon (k = 1, orange) has '
                  'the least, δ_oct ≈ 0.902414, below the regular octagon’s (4 + 4√2)/(5 + 4√2) ≈ 0.906164')


# ---- plain figures: smoothed-octagon-plain.svg, octagon-tiling.svg, packing-densities.svg ------

PLAIN_FILL, PLAIN_STROKE = FILLS[0], BLUE
CUT_FILL = '#fed7aa'               # the corners cut from the regular octagon
CENTRAL_TINT = '#c8dbfb'          # the one copy that stays put in worst-packer.gif


def clip_begin(f, box, cid):
    """Start a group clipped to the box (xmin, xmax, ymin, ymax) of data coordinates."""
    (x0, y1), (x1, y0) = f.p(box[0], box[2]), f.p(box[1], box[3])
    f.add(f'<clipPath id="{cid}"><rect x="{x0:.1f}" y="{y0:.1f}" width="{x1 - x0:.1f}" '
          f'height="{y1 - y0:.1f}"/></clipPath>')
    f.add(f'<g clip-path="url(#{cid})">')


def clip_end(f):
    f.add('</g>')


def copies_in(box, b0, b1, reach, m=10):
    """The points a b0 + b b1 (|a|, |b| ≤ m) whose copy, of circumradius `reach`, meets the box."""
    out = []
    for a in range(-m, m + 1):
        for b in range(-m, m + 1):
            v = a * b0 + b * b1
            if box[0] - reach < v[0] < box[1] + reach and box[2] - reach < v[1] < box[3] + reach:
                out.append(v)
    return np.array(out)


def regular_k(n_per=200):
    """The boundary of A K: Reinhardt's smoothed octagon, area-preserving, edges horizontal and
    vertical."""
    return transform(P.boundary(n_per), oc.classical_map(P))


def corner_regions(K_pieces, O):
    """The corners cut from the polygon O by the arcs: each arc closed up by the vertex it replaces."""
    out = []
    for kind, pts in K_pieces:
        if kind == 'arc':
            v = O[np.argmin(np.linalg.norm(O - pts[len(pts) // 2], axis=1))]
            out.append((np.vstack([pts, [v]]), v))
    return out


SOFT_GRADIENT = ('<defs><radialGradient id="soft" cx="50%" cy="42%" r="62%">'
                 '<stop offset="0%" stop-color="#f5f9ff"/><stop offset="100%" stop-color="#d4e4fd"/>'
                 '</radialGradient></defs>')


def smoothed_octagon_plain():
    """Reinhardt's smoothed octagon A K alone, in its regular orientation: a soft fill, its 8 straight
    edges in blue and its 8 hyperbolic arcs in orange, and the 8 corners cut from the regular octagon
    as faint ghosts."""
    A = oc.classical_map(P)
    AB = regular_k()
    g = oc.Gauge(AB)
    AO = transform(oc.edge_polygon(P), A)
    pcs = boundary_pieces(A, n_per=60)
    ghosts = corner_regions(pcs, AO)
    # A K is A applied to the library's K, with det A = 1, so its area is √12 δ_oct; it is centrally
    # symmetric about the origin and invariant under the rotation by π/4, and the lines of its edges
    # bound a regular octagon A O with horizontal and vertical edges.
    assert abs(np.linalg.det(A) - 1) < 1e-14
    assert abs(oc.shoelace(AB) - oc.AREA_OCT) < 1e-6
    assert np.abs(g(-AB) - 1).max() < 1e-6 and np.abs(g(AB @ rot(PI / 4).T) - 1).max() < 1e-6
    assert np.allclose(AO / A[0, 0], oc.regular_octagon(1.0)[[7, 0, 1, 2, 3, 4, 5, 6]], atol=1e-12)
    # The ghosts are exactly what was cut away: 8 congruent corners whose areas add up to
    # area(A O) - area(A K); each side keeps a straight middle part of 1/√2 of its length.
    assert len(ghosts) == 8
    areas = [abs(oc.shoelace(q)) for q, _ in corner_regions(boundary_pieces(A, n_per=2000), AO)]
    assert np.ptp(areas) < 1e-9 and abs(sum(areas) - (oc.shoelace(AO) - oc.AREA_OCT)) < 1e-7
    side = np.linalg.norm(AO[1] - AO[0])
    for kind, pts in pcs:
        if kind == 'edge':
            assert abs(np.linalg.norm(pts[-1] - pts[0]) / side - 1 / SQ2) < 1e-12
    r = np.abs(AO).max() + 0.05
    f = Figure(-r, r, -r, r, 190)
    f.add(SOFT_GRADIENT)
    for q, v in ghosts:
        f.polygon(q, fill=CUT_FILL, stroke='none', width=0)
        f.polyline([q[0], v, q[-2]], stroke='#fb923c', width=1.3, dash='2.5 2')
    f.polygon(AB, fill='url(#soft)', stroke='none', width=0)
    for kind, pts in pcs:
        f.polyline(pts, stroke=PIECE_COLORS[kind], width=3.4 if kind == 'arc' else 3.0)
    return f.save('smoothed-octagon-plain', 'Reinhardt’s smoothed octagon')


def octagon_construction():
    """How the corners are smoothed, in the regular frame (inradius 1): each corner of the regular
    octagon (faint) is replaced by an arc of the hyperbola that is tangent to the two sides at the corner
    and has the lines of the next two sides as asymptotes. For the corner (1, tan π/8): the hyperbola's
    branch (dashed), its asymptotes y = 1 and x - y = √2 (dashed) meeting at its centre C = (1 + √2, 1),
    the tangency points T₁, T₂ and the cut-off corner (shaded); right, the corner magnified."""
    M = oc.regular_frame(P)
    O = transform(oc.edge_polygon(P), M)
    KB = transform(P.boundary(200), M)
    pcs = boundary_pieces(M, n_per=80)
    t8 = math.tan(PI / 8)
    m = 1
    V = O[m]
    C, d1, d2, kappa, T1, T2 = oc.corner_hyperbola(O, m)
    arc = transform(oc.piece_points(P, oc.pieces(P)[1], 200), M)
    # The octagon: regular, inradius 1; the corner (1, tan π/8) joins side 0 (x = 1) and side 1
    # (x + y = √2); the next sides are side 7 (x - y = √2) and side 2 (y = 1).
    assert np.allclose(O, oc.regular_octagon(1.0)[[7, 0, 1, 2, 3, 4, 5, 6]], atol=1e-12)
    assert np.allclose(V, (1, t8), atol=1e-12)
    assert np.allclose(O[[0, 1], 0], 1) and np.allclose(O[[1, 2]].sum(axis=1), SQ2)
    assert np.allclose(O[[7, 0], 0] - O[[7, 0], 1], SQ2) and np.allclose(O[[2, 3], 1], 1)
    # The asymptotes are those two lines, meeting at C = (1 + √2, 1).
    assert np.allclose(C, (1 + SQ2, 1), atol=1e-12)
    assert abs(oc.cross(d1, (1, 1))) < 1e-12 and abs(oc.cross(d2, (1, 0))) < 1e-12
    # The library's arc (traced by σ₀ under e₁ on [t_sw, 2t_sw]) is that hyperbola's: u v = κ along it.
    u, v = oc.hyperbola_uv(C, d1, d2, arc).T
    assert np.abs(u * v / kappa - 1).max() < 1e-10
    # The tangency points: T₁ = (1, 1 - 1/√2) on side 0 and T₂ = (√2 - 1/2, 1/2) on side 1, at
    # (3√2 - 4)/2 from the corner; the arc meets the sides there with a common tangent (C¹), and the
    # straight middle part of each side is 2 - √2, 1/√2 of the side.
    assert np.allclose(T1, (1, 1 - 1 / SQ2), atol=1e-12) and np.allclose(T2, (SQ2 - 0.5, 0.5), atol=1e-12)
    assert np.allclose(arc[[0, -1]], [T1, T2], atol=1e-9)
    for T in (T1, T2):
        assert abs(np.linalg.norm(T - V) - (3 * SQ2 - 4) / 2) < 1e-12
    for t, side in ((P.tsw, O[1] - O[0]), (2 * P.tsw, O[2] - O[1])):
        left, right = M @ P.curve_d(0, t - 1e-13), M @ P.curve_d(0, t + 1e-13)
        assert np.linalg.norm(left - right) < 1e-9 and abs(oc.cross(left, side)) < 1e-9
    side = np.linalg.norm(O[1] - O[0])
    assert abs(side - 2 * (SQ2 - 1)) < 1e-12 and abs((side - 2 * np.linalg.norm(T1 - V)) - (2 - SQ2)) < 1e-12
    # The cut-off corner is an eighth of area(O) - area(K).
    cut = np.vstack([arc, [V]])
    fine = np.vstack([transform(oc.piece_points(P, oc.pieces(P)[1], 4000), M), [V]])
    assert abs(abs(oc.shoelace(fine)) - (oc.shoelace(O) - oc.AREA_OCT * np.linalg.det(M)) / 8) < 1e-9
    # The branch through the arc, for drawing.
    um, vm = oc.hyperbola_uv(C, d1, d2, arc[len(arc) // 2])[0]
    sgrid = np.linspace(-4, 4, 3000)
    branch = C + np.outer(um * np.exp(sgrid), d1) + np.outer(vm * np.exp(-sgrid), d2)

    xl, xr, yb, yt = -1.22, 2.78, -1.22, 1.32
    zoom_w, zoom_mag = 0.15, 4.0
    big = zoom_w * zoom_mag
    zoom_c = np.array([xr + 0.35 + big, 0.1])
    f = Figure(xl, zoom_c[0] + big + 0.05, yb, yt, 112)
    main = (xl, xr, yb, yt)
    f.polygon(KB, fill=FILLS[0], stroke='none', width=0)
    f.polygon(cut, fill=CUT_FILL, stroke='none', width=0)
    f.polygon(O, stroke=FAINT, width=1.2)
    for p0, d in ((O[7], d1), (O[2], d2)):
        line = p0 + np.outer(np.linspace(-6, 6, 400), d)
        for run in runs_inside(line, main):
            f.polyline(run, stroke=INK, width=1.0, dash='6 4')
    for run in runs_inside(branch, main):
        f.polyline(run, stroke=ORANGE, width=1.4, dash='4 3')
    for kind, pts in pcs:
        f.polyline(pts, stroke=PIECE_COLORS[kind], width=2.4 if kind == 'edge' else 2.8)
    for q in (T1, T2):
        f.dot(q, r=3.4)
    f.dot(C, r=3.4)
    f.text(C + (-0.13, 0.1), 'C', size=15)
    f.text((xl + 0.05, 1.09), 'y = 1', size=13, anchor='start', color=INK, italic=False)
    f.text((0.55, -1.12), 'x − y = √2', size=13, anchor='start', color=INK, italic=False)
    # The zoom window and its magnified copy.
    wc = (T1 + T2 + V) / 3
    win = (wc[0] - zoom_w, wc[0] + zoom_w, wc[1] - zoom_w, wc[1] + zoom_w)
    assert all(win[0] + 0.02 < q[0] < win[1] - 0.02 and win[2] + 0.02 < q[1] < win[3] - 0.02
               for q in (T1, T2, V))
    sq = np.array([(-1, -1), (1, -1), (1, 1), (-1, 1)], dtype=float)
    f.polygon(wc + zoom_w * sq, stroke=INK, width=0.9)
    f.polygon(zoom_c + big * sq, fill='#ffffff', stroke=INK, width=0.9)
    for sy in (-1, 1):
        f.line(wc + (zoom_w, sy * zoom_w), zoom_c + (-big, sy * big), stroke=FAINT, width=0.8,
               dash='3 3')

    def mag(pts):
        return (np.asarray(pts) - wc) * zoom_mag + zoom_c

    f.polygon(mag(clip_polygon(KB, win)), fill=FILLS[0], stroke='none', width=0)
    f.polygon(mag(clip_polygon(cut, win)), fill=CUT_FILL, stroke='none', width=0)
    corner = np.concatenate([np.linspace(O[0], O[1], 600), np.linspace(O[1], O[2], 600)])
    for run in runs_inside(corner, win):
        f.polyline(mag(run), stroke=FAINT, width=1.2)
    for run in runs_inside(branch, win):
        f.polyline(mag(run), stroke=ORANGE, width=1.4, dash='4 3')
    for kind, pts in pcs:
        for run in runs_inside(pts, win):
            f.polyline(mag(run), stroke=PIECE_COLORS[kind], width=2.6 if kind == 'edge' else 3.0)
    for q, lab, off in ((T1, sb('T', '1', size=15), (0.12, -0.02)), (T2, sb('T', '2', size=15), (-0.13, -0.1))):
        f.dot(mag(q), r=3.8)
        f.text(mag(q) + off, lab, size=15)
    f.text(zoom_c + (0, -big - 0.13), f'the corner, ×{zoom_mag:g}', size=12, italic=False)
    return f.save('octagon-construction',
                  'How the corners are smoothed: each corner of the regular octagon (grey) is replaced by '
                  'an arc of the hyperbola that is tangent to the two sides at the corner and has the '
                  'lines of the next two sides as asymptotes. For the upper right corner: the hyperbola '
                  '(dashed orange), its asymptotes y = 1 and x − y = √2 meeting at its centre C, the '
                  'tangency points T₁ and T₂ and the cut-off corner (shaded); the straight part left of '
                  'each side is 1/√2 of it')


def octagon_tiling():
    """The densest lattice packing of A K: the copies A K + 2AΛ, Λ = Z s₀* + Z s₁*, cropped to a
    rectangle. Each copy touches six neighbours: the two beside it share a vertical edge, the four
    above and below touch it at single points; elsewhere thin gaps remain."""
    A = oc.classical_map(P)
    AB = regular_k()
    g = oc.Gauge(AB)
    b0, b1 = 2 * A @ oc.SIXTH[0], 2 * A @ oc.SIXTH[1]
    # The lattice 2AΛ has covolume √12 (det A = 1), so the density is area(A K)/√12 = δ_oct.
    assert abs(oc.det2(b0, b1) - math.sqrt(12)) < 1e-12
    assert abs(oc.shoelace(AB) / oc.det2(b0, b1) - oc.DELTA_OCT) < 1e-6
    # AΛ is critical for A K: its determinant √3/2 is the least det(p, q) over the affinely regular
    # hexagons inscribed in A K, and it has no nonzero point inside A K.
    crit, _, _ = oc.critical_determinant(g)
    assert abs(crit - oc.SQRT3 / 2) < 1e-6
    ok, on = oc.is_admissible(g, b0 / 2, b1 / 2, tol=1e-6)
    assert ok and on == 6
    # Neighbouring copies touch, and no others: ‖v‖ = 2 for the six neighbours ±b0, ±b1, ±(b1 - b0),
    # more for any other lattice vector.
    nb = [b0, b1, b1 - b0, -b0, -b1, b0 - b1]
    assert all(abs(g(v)[0] - 2) < 1e-6 for v in nb)
    pts, _ = oc.lattice_points(b0, b1, 4)
    far = [v for v in pts if min(np.linalg.norm(v - w) for w in nb) > 1e-9]
    assert g(np.array(far)).min() > 2.3
    # The copies beside each other share a whole vertical edge; the others touch at one point.
    assert abs(b0[1]) < 1e-15 and abs(b0[0] - 2 * A[0, 0]) < 1e-12
    edge = [pts_ for kind, pts_ in boundary_pieces(A) if kind == 'edge'][0]   # the edge x = a₀₀
    assert np.allclose(edge[:, 0], A[0, 0]) and np.allclose(edge[0], -edge[-1] * (-1, 1))
    for v in (b1, b1 - b0):
        c = v / 2                                            # the contact point
        assert np.abs(AB - c).sum(axis=1).min() < 1e-9
        assert min(np.linalg.norm(pts_[[0, -1]] - c, axis=1).min()
                   for kind, pts_ in boundary_pieces(A) if kind == 'edge') < 1e-12

    box = (-5.6, 5.6, -3.55, 3.55)
    f = Figure(*box, 56, pad=10)
    clip_begin(f, box, 'tiling')
    shape = regular_k(n_per=12)
    for v in copies_in(box, b0, b1, 1.1):
        f.polygon(shape + v, fill=PLAIN_FILL, stroke=PLAIN_STROKE, width=1.4)
    clip_end(f)
    return f.save('octagon-tiling',
                  'The densest packing of Reinhardt’s smoothed octagon, a lattice packing of density '
                  '(8 − 4√2 − ln 2)/(2√2 − 1) ≈ 0.902414: each copy shares a vertical edge with the '
                  'copies beside it and touches the four above and below at single points')


def packing_densities():
    """The disk, the regular octagon, the smoothed 14-gon and the smoothed octagon, all of inradius 1,
    in the order of decreasing packing density, each in front of a patch of its densest lattice
    packing, with its density."""
    th = np.linspace(0, 2 * PI, 4000, endpoint=False)
    disk = np.c_[np.cos(th), np.sin(th)]
    octa = oc.regular_octagon(1.0)
    P2 = oc.SmoothedPolygon(2)
    M1, M2 = oc.regular_frame(P), oc.regular_frame(P2)
    oct_s = transform(P.boundary(400), M1)
    gon14 = transform(P2.boundary(400), M2)
    # In the regular frames the edge lines of the smoothed polygons are regular polygons of inradius 1
    # with a vertical edge at x = 1 (the edge through σ₀(0) = s₀*).
    assert np.allclose(oc.edge_polygon(P) @ M1.T, octa[[7, 0, 1, 2, 3, 4, 5, 6]], atol=1e-12)
    E14 = oc.edge_polygon(P2) @ M2.T
    assert len(E14) == 14 and np.ptp(np.linalg.norm(E14, axis=1)) < 1e-12
    assert abs(np.linalg.norm(E14[0]) - 1 / math.cos(PI / 14)) < 1e-12
    shapes = [('disk', disk, oc.disk_gauge, 'π/√12 = '),
              ('regular octagon', octa, oc.Gauge(octa), '(4 + 4√2)/(5 + 4√2) = '),
              ('smoothed 14-gon', gon14, oc.Gauge(gon14), ''),
              ('smoothed octagon', oct_s, oc.Gauge(oct_s), '(8 − 4√2 − log 2)/(2√2 − 1) = ')]
    closed = [oc.DELTA_DISK, oc.DELTA_REGULAR_OCTAGON, P2.density(), oc.DELTA_OCT]
    assert abs(oc.DELTA_REGULAR_OCTAGON - (12 - 4 * SQ2) / 7) < 1e-15
    assert [f'{d:.6f}' for d in closed] == ['0.906900', '0.906164', '0.906052', '0.902414']
    # The lattices: the hexagonal one for the disk; for each smoothed polygon the image of
    # Λ = Z s₀* + Z s₁* under its regular frame, which serves the regular octagon as well.
    lat = [(np.array([1.0, 0.0]), np.array([0.5, oc.SQRT3 / 2])),
           (M1 @ oc.SIXTH[0], M1 @ oc.SIXTH[1]),
           (M2 @ oc.SIXTH[0], M2 @ oc.SIXTH[1]),
           (M1 @ oc.SIXTH[0], M1 @ oc.SIXTH[1])]
    assert np.allclose(lat[1][0], (1, 0)) and np.allclose(lat[1][1], (0.5, SQ2 - 0.5))
    dens = []
    for (name, pts, g, _), (b0, b1), d in zip(shapes, lat, closed):
        # Inradius 1: the least radial distance 1/‖u‖ over the unit vectors u is 1 (the directions
        # include those of the edge midpoints).
        assert abs(1 / g(disk[::5]).max() - 1) < 1e-6, name
        # Critical: det(b0, b1) is the critical determinant, the least det(p, q) over the inscribed
        # affinely regular hexagons, and the lattice is admissible with six points on the boundary.
        crit, _, _ = oc.critical_determinant(g)
        assert abs(oc.det2(b0, b1) - crit) < 1e-6, (name, crit)
        ok, on = oc.is_admissible(g, b0, b1, tol=1e-6)
        assert ok and on == 6, (name, on)
        # The density, computed independently as area / covolume of the packing lattice 2(Zb0 + Zb1).
        dens.append(oc.shoelace(pts) / (4 * crit))
        assert abs(dens[-1] - d) < 2e-6, (name, dens[-1], d)
    assert dens[0] > dens[1] > dens[2] > dens[3]
    assert abs(oc.critical_determinant(shapes[1][2])[0] - (SQ2 - 0.5)) < 1e-9

    w, gap, text_h = 2.3, 0.55, 1.05
    cols = [0.0, 2 * w + gap]
    rows = [0.0, -(2 * w + text_h + 0.3)]
    f = Figure(-w, cols[1] + w, rows[1] - w - text_h, w, 50)
    for i, ((name, pts, _, formula), (b0, b1), d) in enumerate(zip(shapes, lat, closed)):
        c = np.array([cols[i % 2], rows[i // 2]])
        clip_begin(f, (c[0] - w, c[0] + w, c[1] - w, c[1] + w), f'panel{i}')
        step = max(1, len(pts) // 700)
        for v in copies_in((-w, w, -w, w), 2 * b0, 2 * b1, 1.1):
            if np.linalg.norm(v) > 1e-9:
                f.polygon(pts[::step] + v + c, fill=PLAIN_FILL, stroke=PLAIN_STROKE, width=1.0,
                          opacity=0.45, stroke_opacity=0.45)
        f.polygon(pts[::step] + c, fill=PLAIN_FILL, stroke=PLAIN_STROKE, width=2.2)
        clip_end(f)
        f.text((c[0], c[1] - w - 0.33), name, size=15, italic=False)
        f.text((c[0], c[1] - w - 0.7), f'{formula}{d:.6f}', size=13, italic=False, color='#4b5563')
    return f.save('packing-densities',
                  'The disk, the regular octagon, the smoothed 14-gon and the smoothed octagon, all of '
                  'inradius 1, each in front of its densest lattice packing, in the order of decreasing '
                  'packing density: π/√12 = 0.906900, (4 + 4√2)/(5 + 4√2) = 0.906164, 0.906052 and '
                  '(8 − 4√2 − log 2)/(2√2 − 1) = 0.902414')


# ---- worst-packer.gif ------------------------------------------------------------------------------

def worst_packer_gif(name='worst-packer.gif', n_frames=120, ms=60, width=600, height=340, scale=78):
    """Reinhardt's smoothed octagon A K in its densest packing A K + 2AΛ_t, Λ_t = Z σ₀(t) + Z σ₁(t), as
    t runs over one period [0, t_f): every Λ_t is a critical lattice, so the copies slide around the
    central one (tinted a little deeper), keeping their orientation and their contacts: the octagon has
    a continuum of densest packings. Λ_{t_f} = Λ₀, so the loop is seamless. No lines, points or text."""
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    from matplotlib.patches import Polygon
    from PIL import Image

    A = oc.classical_map(P)
    AB = regular_k()
    g = oc.Gauge(AB)
    shape = regular_k(n_per=16)
    ts = np.linspace(0, P.tf, n_frames, endpoint=False)
    w, h = width / scale / 2, height / scale / 2
    box = (-w, w, -h, h)
    lattices = []
    for t in ts:
        b0, b1 = A @ P.curve(0, t), A @ P.curve(1, t)
        # Every frame is a densest packing: covolume √12, density δ_oct, no overlaps, six contacts.
        assert abs(oc.det2(2 * b0, 2 * b1) - math.sqrt(12)) < 1e-12
        ok, on = oc.is_admissible(g, b0, b1, tol=1e-6)
        assert ok and on == 6
        lattices.append((b0, b1))
    assert abs(oc.shoelace(AB) / math.sqrt(12) - oc.DELTA_OCT) < 1e-6
    # The lattice at t_f is Λ₀ again: its basis (s₁*, s₂*) is a unimodular integer change of (s₀*, s₁*).
    e0, e1 = A @ P.curve(0, P.tf), A @ P.curve(1, P.tf)
    U = np.linalg.solve(np.array([A @ oc.SIXTH[0], A @ oc.SIXTH[1]]).T, np.array([e0, e1]).T)
    assert np.allclose(U, np.round(U), atol=1e-12) and abs(abs(np.linalg.det(U)) - 1) < 1e-12
    # Smooth enough and short enough for the top of the README.
    # (GIF stores durations in hundredths of a second.)
    assert ms % 10 == 0 and 1000 / ms >= 15 and 6000 <= n_frames * ms <= 10000

    images = []
    for t, (b0, b1) in zip(ts, lattices):
        fig = plt.figure(figsize=(width / 100, height / 100), dpi=100)
        ax = fig.add_axes([0, 0, 1, 1])
        ax.set_xlim(-w, w)
        ax.set_ylim(-h, h)
        ax.set_aspect('equal')
        ax.axis('off')
        for v in copies_in(box, 2 * b0, 2 * b1, 1.1, m=8):
            tint = CENTRAL_TINT if np.linalg.norm(v) < 1e-9 else PLAIN_FILL
            ax.add_patch(Polygon(shape + v, closed=True, facecolor=tint, edgecolor=PLAIN_STROKE,
                                 lw=1.1))
        fig.canvas.draw()
        images.append(Image.fromarray(np.asarray(fig.canvas.buffer_rgba())[:, :, :3].copy()))
        plt.close(fig)
    path = OUT / name
    save_gif(images, path, ms)
    assert path.stat().st_size < 2 * 1024 * 1024
    return path


def save_gif(images, path, ms, colors=31):
    """Write the frames as a looping GIF with one palette (from a frame of the middle, with pure white
    kept), each frame mapped to its nearest colours."""
    from PIL import Image
    pal = images[len(images) // 3].quantize(colors=colors, method=Image.Quantize.MEDIANCUT)
    rgb = np.vstack([[255, 255, 255], np.array(pal.getpalette()[:3 * colors]).reshape(-1, 3)])
    frames = []
    for im in images:
        a = np.asarray(im).reshape(-1, 3).astype(int)
        cols, inv = np.unique(a, axis=0, return_inverse=True)
        near = ((cols[:, None, :] - rgb[None, :, :]) ** 2).sum(axis=2).argmin(axis=1)
        q = Image.fromarray(near[inv.ravel()].reshape(im.size[1], im.size[0]).astype(np.uint8), 'P')
        q.putpalette(rgb.ravel().tolist())
        frames.append(q)
    path.parent.mkdir(parents=True, exist_ok=True)
    frames[0].save(path, save_all=True, append_images=frames[1:], duration=ms, loop=0, optimize=True,
                   disposal=1)


def main():
    facts = oc.verify()
    for path in (smoothed_octagon(facts), octagon_packing(), upper_half_plane(),
                 density_comparison(facts), smoothed_octagon_plain(), octagon_construction(),
                 octagon_tiling(),
                 packing_densities(), worst_packer_gif(), multipoint_gif()):
        print(f'wrote {path.relative_to(OUT.parents[1])} ({path.stat().st_size // 1024} KiB)')


if __name__ == '__main__':
    main()
