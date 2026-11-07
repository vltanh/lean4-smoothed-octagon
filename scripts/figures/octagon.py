#!/usr/bin/env python3
"""Reinhardt's smoothed octagon, computed from the definitions of the library SmoothedPolygons.

The sources are in .lake/packages/SmoothedPolygons/SmoothedPolygons/:

- Defs.lean: the trace form ⟨X, Y⟩ = tr(XY), J, the rotation R = exp(Jπ/3), the control matrix Z_u
  (`controlMatrix`), Φ(x + iy), the star functions ρ₀, ρ₁, ρ₂, P = Z_u/⟨Z_u, X⟩ (`controlP`), the state
  equations g' = gX, X' = [P, X] (`IsStateTrajectory`), the cost -(3/2) ∫₀^{t_f} ⟨J, X⟩
  (`reinhardtCost`), θ_k, y₀, t_sw, t_f = (3k + 1) t_sw, the control e₃, e₁, e₂, e₃, … (`polygonControl`:
  the vertex with Fin-index (2 + ⌊t/t_sw⌋) mod 3), the sixth roots s_j* (`sixthRoot`) and the multi-point
  conditions (`IsMultiPoint`);
- Ch7/Polygon.lean: the e₃-trajectory from z₀ = i y₀ in closed form (`segX_eq`, `segG_eq`) and the
  spline `polygonX`, `polygonG`, which conjugates it by R⁻ⁱ on the i-th switching interval;
- Ch7/SmoothedPolygonDisk.lean: the spline extended with period 6 t_f (`smoothedPolygonG`,
  `smoothedPolygonX`), the curves σ_j(t) = g(t) s_j* (`smoothedPolygonCurve`) and the disk K, the region
  swept from the origin by σ₀ over [0, 6 t_f] (`smoothedPolygonDisk`), whose area ½ ∫ det(σ₀, σ₀') is
  the cost (`smoothedPolygonDisk_volume`).

The trajectory is computed twice, from the closed forms and by integrating the state equations
(scipy), and `verify` checks with `assert`s that the two agree and every fact that the figures state.

    python3 scripts/figures/octagon.py
"""
import math

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq

SQRT2, SQRT3 = math.sqrt(2), math.sqrt(3)
J = np.array([[0.0, -1.0], [1.0, 0.0]])
R = np.array([[0.5, -SQRT3 / 2], [SQRT3 / 2, 0.5]])
R_INV = np.array([[0.5, SQRT3 / 2], [-SQRT3 / 2, 0.5]])
SIXTH = np.array([[math.cos(math.pi * j / 3), math.sin(math.pi * j / 3)] for j in range(6)])

# The density of the smoothed octagon and its area √12 δ_oct (`smoothedOctagon_volume`).
DELTA_OCT = (8 - 4 * SQRT2 - math.log(2)) / (2 * SQRT2 - 1)
AREA_OCT = math.sqrt(12) * DELTA_OCT
DELTA_DISK = math.pi / math.sqrt(12)
# The packing density of the regular octagon (Fejes Tóth), for comparison.
DELTA_REGULAR_OCTAGON = (4 + 4 * SQRT2) / (5 + 4 * SQRT2)
CONTROL_NAMES = ('e₁', 'e₂', 'e₃')        # Fin-index 0, 1, 2


# ---- the definitions of Defs.lean ---------------------------------------------------------------

def vertex(i):
    """The vertex e_{i+1} = Pi.single i 1 of the control simplex U_T."""
    u = np.zeros(3)
    u[i] = 1.0
    return u


def control_matrix(u):
    """Z_u = [[(u₁ - u₂)/√3, (u₀ - 2u₁ - 2u₂)/3], [u₀, (u₂ - u₁)/√3]] (`controlMatrix`)."""
    return np.array([[(u[1] - u[2]) / SQRT3, (u[0] - 2 * u[1] - 2 * u[2]) / 3],
                     [u[0], (u[2] - u[1]) / SQRT3]])


def trace_form(A, B):
    return float(np.trace(A @ B))


def control_p(u, X):
    """P = Z_u/⟨Z_u, X⟩ (`controlP`)."""
    Z = control_matrix(u)
    return Z / trace_form(Z, X)


def Phi(x, y):
    """Φ(x + iy) = [[x/y, -(x² + y²)/y], [1/y, -x/y]], vectorized over x and y."""
    x, y = np.broadcast_arrays(np.asarray(x, dtype=float), np.asarray(y, dtype=float))
    out = np.empty(x.shape + (2, 2))
    out[..., 0, 0], out[..., 0, 1] = x / y, -(x ** 2 + y ** 2) / y
    out[..., 1, 0], out[..., 1, 1] = 1 / y, -x / y
    return out


def z_of(X):
    """The point z = x + iy of the upper half-plane with Φ(z) = X: y = 1/c, x = a/c."""
    return X[..., 0, 0] / X[..., 1, 0] + 1j / X[..., 1, 0]


def rho(X):
    """The star functions (ρ₀, ρ₁, ρ₂) of X = [[a, b], [c, -a]] (Corollary 3.1.6)."""
    a, b, c = X[..., 0, 0], X[..., 0, 1], X[..., 1, 0]
    return (c + SQRT3 * a) / SQRT3, (c - SQRT3 * a) / SQRT3, -(3 * b + c) / (2 * SQRT3)


def mobius(M, z):
    """The action (az + b)/(cz + d) of a 2 × 2 matrix on the upper half-plane; Φ(M·z) = M Φ(z) M⁻¹."""
    return (M[0, 0] * z + M[0, 1]) / (M[1, 0] * z + M[1, 1])


def det2(v, w):
    """det(v, w) = v₀w₁ - v₁w₀, vectorized over the leading axes."""
    return v[..., 0] * w[..., 1] - v[..., 1] * w[..., 0]


def shoelace(pts):
    P = np.asarray(pts, dtype=float)
    return 0.5 * float(np.dot(P[:, 0], np.roll(P[:, 1], -1)) - np.dot(P[:, 1], np.roll(P[:, 0], -1)))


# ---- the smoothed (6k+2)-gon (Polygon.lean, SmoothedPolygonDisk.lean) --------------------------

class SmoothedPolygon:
    """The trajectory (g, X) of the smoothed (6k+2)-gon on ℝ, with period 6 t_f, in closed form."""

    def __init__(self, k):
        self.k, self.N = k, 3 * k + 1
        self.theta = math.pi * k / (3 * k + 1)                               # θ_k
        self.y0 = math.sqrt((2 / math.cos(self.theta) - 1) / 3)              # y₀
        self.tsw = math.log(4 / (3 * self.y0 ** 2 + 1)) / (SQRT3 * self.y0)  # t_sw
        self.tf = self.N * self.tsw                                          # t_f
        self.period = 6 * self.tf
        self.n_int = 6 * self.N                  # switching intervals in a period
        self.g_sw = self.seg_g(self.tsw)
        self.h = self.g_sw @ R_INV                # g(t + t_sw) = h g(t) R
        pw = lambda M: np.array([np.linalg.matrix_power(M, i) for i in range(self.n_int + 1)])
        self.h_pow, self.r_pow, self.rinv_pow = pw(self.h), pw(R), pw(R_INV)

    # The e₃-trajectory from z₀ = i y₀ (`segX_eq`, `segG_eq`), W = exp(√3 y₀ s).
    def seg_x(self, s):
        W = np.exp(SQRT3 * self.y0 * np.asarray(s, dtype=float))
        return Phi((W - 1) / SQRT3, self.y0 * W)

    def seg_g(self, s):
        W = np.exp(SQRT3 * self.y0 * np.asarray(s, dtype=float))
        y2 = self.y0 ** 2
        out = np.empty(W.shape + (2, 2))
        out[..., 0, 0], out[..., 0, 1] = 1.0, -(W - 1) / SQRT3
        out[..., 1, 0] = (1 - 1 / W) / (SQRT3 * y2)
        out[..., 1, 1] = 1 - (W - 2 + 1 / W) / (3 * y2)
        return out

    def split(self, t):
        """t reduced mod 6 t_f (`oct_red`), its switching interval i = ⌊t/t_sw⌋ and s = t - i t_sw."""
        t = np.mod(np.asarray(t, dtype=float), self.period)
        i = np.clip(np.floor(t / self.tsw).astype(int), 0, self.n_int - 1)
        return i, t - i * self.tsw

    def g(self, t):
        """g(t) = (g_sw R⁻¹)ⁱ g₀(s) Rⁱ (`polygonG`, `smoothedPolygonG`)."""
        i, s = self.split(t)
        return self.h_pow[i] @ self.seg_g(s) @ self.r_pow[i]

    def X(self, t):
        """X(t) = R⁻ⁱ X(z₀, s) Rⁱ (`polygonX`, `smoothedPolygonX`)."""
        i, s = self.split(t)
        return self.rinv_pow[i] @ self.seg_x(s) @ self.r_pow[i]

    def control(self, t):
        """The Fin-index (2 + ⌊t/t_sw⌋) mod 3 of the vertex control (`polygonControl`)."""
        return (2 + self.split(t)[0]) % 3

    def interval_control(self, i):
        return (2 + i) % 3

    def z(self, t):
        return z_of(self.X(t))

    def Xdot(self, t):
        """X' = [P, X] with the control of the interval of t (one-sided at the switching times)."""
        X = self.X(t)
        u = np.array([vertex(c) for c in np.atleast_1d(self.control(t))]).reshape(X.shape[:-2] + (3,))
        Z = np.array([control_matrix(v) for v in u.reshape(-1, 3)]).reshape(X.shape)
        P = Z / np.trace(Z @ X, axis1=-2, axis2=-1)[..., None, None]
        return P @ X - X @ P

    def curve(self, j, t):
        """σ_j(t) = g(t) s_j* (`smoothedPolygonCurve`)."""
        return self.g(t) @ SIXTH[j % 6]

    def curve_d(self, j, t):
        """σ_j' = g X s_j*."""
        return self.g(t) @ self.X(t) @ SIXTH[j % 6]

    def curve_dd(self, j, t):
        """σ_j'' = g (X² + X') s_j*."""
        X = self.X(t)
        return self.g(t) @ (X @ X + self.Xdot(t)) @ SIXTH[j % 6]

    def bending(self, j, t):
        """det(σ_j', σ_j''), which is ≥ 0 almost everywhere (`IsBalancedPair`, item 4)."""
        return det2(self.curve_d(j, t), self.curve_dd(j, t))

    def cost_primitive(self, t):
        """An antiderivative of ⟨J, X(z₀, t)⟩ (`poly_costPrimitive`)."""
        y0, c = self.y0, SQRT3 * self.y0
        return -((1 + 3 * y0 ** 2) * math.exp(c * t) / c - 2 * t - 4 * math.exp(-c * t) / c) / (3 * y0)

    def cost(self):
        """-(3/2) ∫₀^{t_f} ⟨J, X⟩ = -(3/2) (3k + 1) ∫₀^{t_sw} ⟨J, X(z₀, t)⟩ (`poly_integral_J`)."""
        return -1.5 * self.N * (self.cost_primitive(self.tsw) - self.cost_primitive(0.0))

    def cost_quad(self):
        """-(3/2) ∫₀^{t_f} ⟨J, X⟩ by quadrature on each switching interval (`reinhardtCost`)."""
        f = lambda t: float(np.trace(J @ self.X(t)))
        return -1.5 * sum(quad(f, i * self.tsw, (i + 1) * self.tsw, epsabs=1e-13, epsrel=1e-13)[0]
                          for i in range(self.N))

    def area_quad(self):
        """½ ∫₀^{6 t_f} det(σ₀, σ₀') by quadrature: the area of the radial hull (`volume_radialHull`)."""
        f = lambda t: float(det2(self.curve(0, t), self.curve_d(0, t)))
        return 0.5 * sum(quad(f, i * self.tsw, (i + 1) * self.tsw, epsabs=1e-13, epsrel=1e-13)[0]
                         for i in range(self.n_int))

    def times(self, n_per=60, t0=0.0, n_int=None):
        """n_per sample times on each of n_int switching intervals from t0, the knots included once."""
        n_int = self.n_int if n_int is None else n_int
        ts = [t0 + (i + np.linspace(0, 1, n_per, endpoint=False)) * self.tsw for i in range(n_int)]
        return np.concatenate(ts)

    def boundary(self, n_per=60):
        """σ₀ on [0, 6 t_f): the boundary of K, counterclockwise from σ₀(0) = s₀* = (1, 0)."""
        return self.curve(0, self.times(n_per))

    def density(self):
        return self.cost() / math.sqrt(12)


OCT = SmoothedPolygon(1)


# ---- the state equations, integrated numerically ------------------------------------------------

def integrate(P, n_int=None, n_per=40, rtol=1e-12, atol=1e-13):
    """Solve g' = gX, X' = [P, X], P = Z_u/⟨Z_u, X⟩ (`IsStateTrajectory`) from g(0) = I,
    X(0) = Φ(i y₀), switching the control e₃, e₁, e₂, … at the multiples of t_sw. Returns the sample
    times (those of P.times) and g, X there."""
    n_int = P.n_int if n_int is None else n_int
    y = np.concatenate([np.eye(2).ravel(), Phi(0.0, P.y0).ravel()])
    ts, gs, Xs = [], [], []
    for i in range(n_int):
        u = vertex(P.interval_control(i))

        def rhs(_, w, u=u):
            g, X = w[:4].reshape(2, 2), w[4:].reshape(2, 2)
            Pm = control_p(u, X)
            return np.concatenate([(g @ X).ravel(), (Pm @ X - X @ Pm).ravel()])

        a, b = i * P.tsw, (i + 1) * P.tsw
        sol = solve_ivp(rhs, (a, b), y, method='DOP853', rtol=rtol, atol=atol, dense_output=True)
        assert sol.success
        t = a + np.linspace(0, 1, n_per, endpoint=False) * P.tsw
        w = sol.sol(t).T
        ts.append(t)
        gs.append(w[:, :4].reshape(-1, 2, 2))
        Xs.append(w[:, 4:].reshape(-1, 2, 2))
        y = sol.y[:, -1]
    return np.concatenate(ts), np.concatenate(gs), np.concatenate(Xs)


# ---- the boundary: straight edges and hyperbolic arcs -------------------------------------------

def pieces(P, j=0, tol=1e-9):
    """The pieces of the boundary traced by σ_j over one period: maximal runs of switching intervals
    on which det(σ_j', σ_j'') vanishes ('edge') or not ('arc'), merged cyclically, in counterclockwise
    order from the piece through σ_j(0). Each piece is (kind, first interval, number of intervals,
    controls)."""
    mids = (np.arange(P.n_int) + 0.5) * P.tsw
    kinds = ['arc' if abs(b) > tol else 'edge' for b in P.bending(j, mids)]
    start = 0
    while kinds[start - 1] == kinds[0] and start > -P.n_int + 1:
        start -= 1
    out, i = [], start
    while i < start + P.n_int:
        n = 1
        while n < P.n_int and kinds[(i + n) % P.n_int] == kinds[i % P.n_int]:
            n += 1
        out.append((kinds[i % P.n_int], i % P.n_int, n,
                    tuple(P.interval_control((i + m) % P.n_int) for m in range(n))))
        i += n
    return out


def piece_points(P, piece, n_per=60, j=0):
    """The points of σ_j on a piece, both ends included."""
    _, i0, n, _ = piece
    ts = np.linspace(i0 * P.tsw, (i0 + n) * P.tsw, n * n_per + 1)
    return P.curve(j, ts)


def line_intersection(p, d, q, e):
    lam = np.linalg.solve(np.array([d, -e]).T, q - p)
    return p + lam[0] * d


def edge_lines(P):
    """The lines (point, unit direction) of the straight edges of σ₀, in counterclockwise order."""
    out = []
    for pc in pieces(P):
        if pc[0] == 'edge':
            pts = piece_points(P, pc, 4)
            d = pts[-1] - pts[0]
            out.append((pts[0], d / np.linalg.norm(d)))
    return out


def edge_polygon(P):
    """The polygon bounded by the lines of the straight edges: consecutive lines meet at its vertices."""
    L = edge_lines(P)
    return np.array([line_intersection(*L[m - 1], *L[m]) for m in range(len(L))])


def conic_through(pts):
    """The conic Ax² + Bxy + Cy² + Dx + Ey + F = 0 nearest to the points (least squares, unit norm)
    and its relative residual."""
    x, y = pts[:, 0], pts[:, 1]
    M = np.array([x * x, x * y, y * y, x, y, np.ones_like(x)]).T
    _, sv, Vt = np.linalg.svd(M)
    return Vt[-1], sv[-1] / sv[0]


def conic_center(c):
    A, B, C, D, E, _ = c
    return np.linalg.solve(np.array([[2 * A, B], [B, 2 * C]]), -np.array([D, E]))


def conic_eval(c, p):
    A, B, C, D, E, F = c
    x, y = p[..., 0], p[..., 1]
    return A * x * x + B * x * y + C * y * y + D * x + E * y + F


def asymptote_directions(c):
    """The two directions d with A d₀² + B d₀d₁ + C d₁² = 0 (real exactly for a hyperbola)."""
    A, B, C = c[:3]
    if abs(A) > abs(C):
        ds = [np.array([1.0, r]) for r in np.roots([C, B, A])]
    else:
        ds = [np.array([r, 1.0]) for r in np.roots([A, B, C])]
    return [np.real(d) / np.linalg.norm(np.real(d)) for d in ds]


def cross(d, e):
    return d[0] * e[1] - d[1] * e[0]


def corner_hyperbola(O, m):
    """The classical construction of the arc at the corner O[m] of a convex polygon O (vertices
    counterclockwise; side k joins O[k] and O[k+1]): the hyperbola whose asymptotes are the lines of the
    two sides next to the sides at the corner (sides m - 2 and m + 1) and which is tangent to the side
    m - 1. It is {C + u d₁ + v d₂ : uv = κ}, C the meeting point of the asymptotes and d₁, d₂ their
    directions. Returns C, d₁, d₂, κ and the tangency points T₁ on side m - 1 and T₂ on side m (the
    second tangency is computed, not imposed)."""
    n = len(O)
    V = lambda k: np.asarray(O[k % n], dtype=float)
    d1, d2 = V(m - 1) - V(m - 2), V(m + 2) - V(m + 1)
    d1, d2 = d1 / np.linalg.norm(d1), d2 / np.linalg.norm(d2)
    C = line_intersection(V(m - 2), d1, V(m + 1), d2)
    B = np.array([d1, d2]).T

    def uv(p):
        return np.linalg.solve(B, np.asarray(p) - C)

    def tangency(a, b, kappa=None):
        # The points a + s(b - a) with u v = κ: (u₀ + s u₁)(v₀ + s v₁) = κ; tangency is a double root.
        u0, v0 = uv(a)
        u1, v1 = np.linalg.solve(B, b - a)
        lin, quad = u0 * v1 + u1 * v0, u1 * v1
        if kappa is None:
            kappa = u0 * v0 - lin ** 2 / (4 * quad)
        disc = lin ** 2 - 4 * quad * (u0 * v0 - kappa)
        return kappa, a + (-lin / (2 * quad)) * (b - a), disc

    kappa, T1, _ = tangency(V(m - 1), V(m))
    _, T2, disc2 = tangency(V(m), V(m + 1), kappa)
    assert abs(disc2) < 1e-12 * max(1.0, abs(kappa))      # also tangent to side m
    return C, d1, d2, kappa, T1, T2


def hyperbola_uv(C, d1, d2, pts):
    """The coordinates (u, v) of the points in the frame C, d₁, d₂."""
    return np.linalg.solve(np.array([d1, d2]).T, (np.atleast_2d(pts) - C).T).T


def classical_map(P):
    """The area-preserving linear map A = c diag(1/h₀₁, 1/sin θ_k), c = √(h₀₁ sin θ_k), in whose
    coordinates h = g_sw R⁻¹ is the rotation by -θ_k (`oct_hat`, rescaled to determinant 1), so that
    σ₀(t + 3 t_sw) = -h³ σ₀(t) is the rotation by π/(3k + 1)."""
    h01, s = P.h[0, 1], math.sin(P.theta)
    c = math.sqrt(h01 * s)
    return np.array([[c / h01, 0.0], [0.0, c / s]])


# ---- lattices and the gauge of K ---------------------------------------------------------------

class Gauge:
    """The gauge ‖w‖_K = max over the edges of ⟨w, n_e⟩/c_e of a convex polygon (counterclockwise,
    the origin inside) that approximates K from inside."""

    def __init__(self, pts):
        P = np.asarray(pts, dtype=float)
        Q = np.roll(P, -1, axis=0)
        d = Q - P
        self.n = np.stack([d[:, 1], -d[:, 0]], axis=1)       # outer normals
        self.c = np.einsum('ij,ij->i', self.n, P)
        assert np.all(self.c > 0)

    def __call__(self, w):
        w = np.atleast_2d(w)
        return (w @ self.n.T / self.c).max(axis=1)


def lattice_points(b0, b1, m=3):
    """The nonzero points a b0 + b b1 with |a|, |b| ≤ m, and their coefficients."""
    co = [(a, b) for a in range(-m, m + 1) for b in range(-m, m + 1) if (a, b) != (0, 0)]
    return np.array([a * b0 + b * b1 for a, b in co]), co


def inscribed_hexagon_det(P, gauge, phi, n_per=200):
    """For the boundary point p of K at the polar angle phi, the point q of ∂K with q - p ∈ ∂K and
    det(p, q) > 0 (the next vertex of the affinely regular hexagon p, q, q - p, -p, … inscribed in K),
    found on the sampled boundary; returns det(p, q)."""
    ts = P.times(n_per)
    B = P.curve(0, ts)
    ang = np.unwrap(np.arctan2(B[:, 1], B[:, 0]))
    t_p = np.interp(phi % (2 * math.pi), ang, ts)
    p = P.curve(0, t_p)
    f = lambda t: float(gauge(P.curve(0, t) - p)[0]) - 1.0
    # q lies about a sixth of a turn ahead of p.
    a, b = t_p + P.period / 12, t_p + P.period / 4
    t_q = brentq(f, a, b, xtol=1e-14)
    return float(det2(p, P.curve(0, t_q)))


def disk_gauge(w):
    """The gauge of the unit disk: the Euclidean norm."""
    return np.linalg.norm(np.atleast_2d(w), axis=1)


def regular_octagon(inradius=1.0):
    """The regular octagon with the given inradius and horizontal and vertical edges, counterclockwise
    from its vertex at the polar angle 22.5°."""
    R_c = inradius / math.cos(math.pi / 8)
    return np.array([[R_c * math.cos(math.pi / 8 + m * math.pi / 4),
                      R_c * math.sin(math.pi / 8 + m * math.pi / 4)] for m in range(8)])


def hexagon_det(gauge, phi):
    """For the boundary point p of a centrally symmetric convex disk (given by its gauge) at the polar
    angle phi, the next vertex q of the affinely regular hexagon p, q, q - p, -p, -q, p - q inscribed
    in it (q and q - p on the boundary, q counterclockwise from p by less than π); returns det(p, q),
    a third of the area of the hexagon, with p and q."""
    def radial(a):
        u = np.array([math.cos(a), math.sin(a)])
        return u / gauge(u)[0]
    p = radial(phi)
    a = brentq(lambda b: float(gauge(radial(b) - p)[0]) - 1.0, phi + 1e-9, phi + math.pi - 1e-9,
               xtol=1e-15)
    q = radial(a)
    return float(det2(p, q)), p, q


def critical_determinant(gauge, n=360):
    """The critical determinant Δ(K) of a centrally symmetric convex disk: the least determinant of a
    lattice with no nonzero point in the interior of K. By Reinhardt and Mahler it is the least
    det(p, q) over the affinely regular hexagons p, q, q - p, … inscribed in K, and the lattice Zp + Zq
    of a least one is critical. Minimized on a grid of n angles in [0, π), then refined; returns
    (Δ, p, q). Independent of the trajectory: it uses only the gauge."""
    from scipy.optimize import minimize_scalar
    grid = np.linspace(0, math.pi, n, endpoint=False)
    vals = [hexagon_det(gauge, a)[0] for a in grid]
    m = int(np.argmin(vals))
    step = math.pi / n
    res = minimize_scalar(lambda a: hexagon_det(gauge, a)[0], bounds=(grid[m] - step, grid[m] + step),
                          method='bounded', options={'xatol': 1e-12})
    d, p, q = hexagon_det(gauge, res.x)
    return min(d, vals[m]), p, q


def is_admissible(gauge, b0, b1, m=4, tol=1e-9):
    """No nonzero point of the lattice Z b0 + Z b1 lies in the interior of K; returns that and the
    number of lattice points on the boundary of K (within 1e-6)."""
    pts, _ = lattice_points(b0, b1, m)
    g = gauge(pts)
    return bool(g.min() > 1 - tol), int(np.sum(g < 1 + 1e-6))


def regular_frame(P=None):
    """The map K ↦ A K / a₀₀ that puts the smoothed octagon in Reinhardt's regular orientation with
    inradius 1: A is `classical_map`, and A O has inradius a₀₀ (its edge x = 1 goes to x = a₀₀)."""
    A = classical_map(OCT if P is None else P)
    return A / A[0, 0]


# ---- the checks --------------------------------------------------------------------------------

def verify(P=OCT, n_per=40):
    """Check every fact that the figures state about the smoothed octagon; return the numbers."""
    assert P.k == 1
    # The data of the octagon (`example7_5_smoothedOctagon`).
    assert abs(P.theta - math.pi / 4) < 1e-15
    assert abs(P.y0 - math.sqrt((math.sqrt(8) - 1) / 3)) < 1e-15
    assert abs(P.tsw - math.log(2) / (2 * math.sqrt(math.sqrt(8) - 1))) < 1e-15
    assert abs(P.tf - 4 * P.tsw) < 1e-15
    assert abs(np.trace(R_INV @ P.g_sw) - SQRT2) < 1e-12
    assert [P.interval_control(i) for i in range(4)] == [2, 0, 1, 2]       # e₃, e₁, e₂, e₃
    assert np.allclose(R_INV @ R, np.eye(2)) and np.allclose(np.linalg.matrix_power(R, 3), -np.eye(2))

    ts = P.times(n_per)
    g, X = P.g(ts), P.X(ts)
    # The closed forms against the state equations, integrated numerically over the whole period.
    t_ode, g_ode, X_ode = integrate(P, n_per=n_per)
    assert np.allclose(t_ode, ts, atol=1e-13)
    err_ode = max(np.abs(g_ode - g).max(), np.abs(X_ode - X).max())
    assert err_ode < 1e-8, err_ode
    # The state space: det g = 1, X traceless with det X = 1 and ρ₀, ρ₁, ρ₂ > 0 (`IsStarState`).
    assert np.abs(np.linalg.det(g) - 1).max() < 1e-12
    assert np.abs(np.trace(X, axis1=1, axis2=2)).max() < 1e-12
    assert np.abs(np.linalg.det(X) - 1).max() < 1e-12
    r0, r1, r2 = rho(X)
    rho_min = min(r0.min(), r1.min(), r2.min())
    assert rho_min > 0.05, rho_min
    # The initial and terminal conditions: g(0) = I, X(0) = Φ(i y₀), g(t_f) = R, X(t_f) = R⁻¹X(0)R.
    assert np.allclose(P.g(0.0), np.eye(2), atol=1e-15) and np.allclose(P.X(0.0), Phi(0.0, P.y0))
    assert np.abs(P.g(P.tf) - R).max() < 1e-12
    assert np.abs(P.X(P.tf) - R_INV @ P.X(0.0) @ R).max() < 1e-12
    # In the upper half-plane: z(0) = i y₀ and z(t_f) = R⁻¹ · z(0).
    z0 = complex(P.z(0.0))
    assert abs(z0 - 1j * P.y0) < 1e-15
    assert abs(complex(P.z(P.tf)) - mobius(R_INV, z0)) < 1e-12
    # Continuity at the switching times, and ⟨X, Z_u⟩ constant on each interval (Lemma 7.1.1).
    for i in range(1, P.n_int):
        t = i * P.tsw
        assert np.abs(P.g(t - 1e-12) - P.g(t)).max() < 1e-9
        assert np.abs(P.X(t - 1e-12) - P.X(t)).max() < 1e-9
        Z = control_matrix(vertex(P.interval_control(i)))
        vals = [trace_form(Z, P.X(t + s * P.tsw)) for s in (0.0, 0.3, 0.7, 0.999)]
        assert max(vals) - min(vals) < 1e-12
    # The cost and the area: -(3/2) ∫₀^{t_f} ⟨J, X⟩ = ½ ∫₀^{6t_f} det(σ₀, σ₀') = √12 δ_oct.
    cost, cost_q, area_q = P.cost(), P.cost_quad(), P.area_quad()
    B = P.boundary(400)
    area_poly = shoelace(B)
    assert abs(cost - AREA_OCT) < 1e-12, cost
    assert abs(cost_q - AREA_OCT) < 1e-10, cost_q
    assert abs(area_q - AREA_OCT) < 1e-10, area_q
    assert abs(area_poly - AREA_OCT) < 1e-6, area_poly
    assert abs(P.density() - DELTA_OCT) < 1e-12 and abs(DELTA_OCT - 0.902414) < 1e-6
    assert AREA_OCT < math.pi

    # The multi-curve: σ_j(0) = s_j*, and for every t the multi-point conditions det(σ_j, σ_{j+1}) =
    # √3/2, σ_j + σ_{j+2} + σ_{j+4} = 0, σ_{j+3} = -σ_j; σ_j(t + t_f) = σ_{j+1}(t); period 6 t_f.
    S = np.array([P.curve(j, ts) for j in range(6)])
    assert np.allclose(S[:, 0], SIXTH, atol=1e-15)
    for j in range(6):
        assert np.abs(det2(S[j], S[(j + 1) % 6]) - SQRT3 / 2).max() < 1e-12
        assert np.abs(S[j] + S[(j + 2) % 6] + S[(j + 4) % 6]).max() < 1e-12
        assert np.abs(S[(j + 3) % 6] + S[j]).max() < 1e-12
        assert np.abs(P.curve(j, ts + P.tf) - S[(j + 1) % 6]).max() < 1e-12
        assert np.abs(P.curve(j, ts + P.period) - S[j]).max() < 1e-12
        # The star condition σ_j' = α(σ_{j+1} - σ_j) + β σ_{j+1} with α, β > 0.
        D = P.curve_d(j, ts)
        A = np.stack([S[(j + 1) % 6] - S[j], S[(j + 1) % 6]], axis=-1)
        ab = np.linalg.solve(A, D[..., None])[..., 0]
        assert ab.min() > 0, ab.min()
        # The curvature condition det(σ_j', σ_j'') ≥ 0 (off the switching times).
        assert P.bending(j, ts[ts % P.tsw > 1e-9]).min() > -1e-12

    # σ₀ turns once around the origin with increasing phase: a simple closed curve (winding number 1).
    ang = np.unwrap(np.arctan2(B[:, 1], B[:, 0]))
    assert np.all(np.diff(ang) > 0) and abs(ang[-1] + (ang[1] - ang[0]) - ang[0] - 2 * math.pi) < 1e-3

    # Which curves bend under which control: e₁ bends σ₀, σ₃; e₂ bends σ₂, σ₅; e₃ bends σ₁, σ₄; the
    # others move along straight lines. So at each time two opposite contact points lie on arcs.
    mids = (np.arange(P.n_int) + 0.5) * P.tsw
    bend = np.array([P.bending(j, mids) for j in range(6)])          # (6, n_int)
    bent_by = {0: {0, 3}, 1: {2, 5}, 2: {1, 4}}
    for i in range(P.n_int):
        on_arc = {j for j in range(6) if bend[j, i] > 1e-6}
        assert on_arc == bent_by[P.interval_control(i)], (i, on_arc)
        assert all(abs(bend[j, i]) < 1e-12 for j in range(6) if j not in on_arc)

    # The boundary: 8 straight edges, each traced in 2 t_sw under e₂ then e₃ (switching at its
    # midpoint), alternating with 8 arcs, each traced in t_sw under e₁.
    pcs = pieces(P)
    assert [pc[0] for pc in pcs] == ['edge', 'arc'] * 8
    assert all(pc[2] == 2 and pc[3] == (1, 2) for pc in pcs if pc[0] == 'edge')
    assert all(pc[2] == 1 and pc[3] == (0,) for pc in pcs if pc[0] == 'arc')
    for pc in pcs:
        pts = piece_points(P, pc, 30)
        d = pts[-1] - pts[0]
        dev = np.abs(np.array([cross(d, p - pts[0]) for p in pts])).max() / np.linalg.norm(d)
        if pc[0] == 'edge':
            assert dev < 1e-12, dev
            mid = P.curve(0, (pc[1] + 1) * P.tsw)
            assert np.linalg.norm(mid - (pts[0] + pts[-1]) / 2) < 1e-12        # switch at the midpoint
        else:
            assert dev > 1e-3, dev
    # s₀* = σ₀(0) is the midpoint of the edge x = 1.
    first = pcs[[pc[1] for pc in pcs].index(P.n_int - 1)]
    assert first[0] == 'edge' and np.allclose(piece_points(P, first, 2)[[0, -1], 0], 1.0)

    # The lines of the 8 edges bound an octagon O; under the area-preserving map A it is a regular
    # octagon with horizontal and vertical edges: the smoothed octagon in circle representation is an
    # affine image of Reinhardt's.
    O = edge_polygon(P)
    A = classical_map(P)
    assert abs(np.linalg.det(A) - 1) < 1e-14
    AO = O @ A.T
    rad = np.linalg.norm(AO, axis=1)
    phase = np.degrees(np.arctan2(AO[:, 1], AO[:, 0])) % 360
    assert np.ptp(rad) < 1e-12
    assert np.allclose(np.sort(phase), 22.5 + 45 * np.arange(8), atol=1e-9)
    assert np.allclose(np.sort(np.abs(O[:, 0])), [SQRT2 - 1] * 4 + [1] * 4, atol=1e-12)
    # A conjugates the symmetry σ₀(t + 3t_sw) = -h³σ₀(t) to the rotation by π/4.
    M = A @ (-np.linalg.matrix_power(P.h, 3)) @ np.linalg.inv(A)
    c4 = math.cos(math.pi / 4)
    assert np.allclose(M, [[c4, -c4], [c4, c4]], atol=1e-12)
    assert np.abs(P.curve(0, ts + 3 * P.tsw) - (-np.linalg.matrix_power(P.h, 3) @ S[0].T).T).max() < 1e-12
    # O has area 3.139..., and packs with the same lattice at the packing density (4 + 4√2)/(5 + 4√2)
    # of the regular octagon; K lies inside O.
    area_O = shoelace(O)
    assert abs(area_O / math.sqrt(12) - DELTA_REGULAR_OCTAGON) < 1e-12
    gO = Gauge(O)
    assert gO(B).max() < 1 + 1e-12

    # Each arc is an arc of a hyperbola, tangent at its ends to the two edges that meet at the clipped
    # corner of O, whose asymptotes are the lines of the two edges flanking those.
    L = edge_lines(P)
    arcs = [pc for pc in pcs if pc[0] == 'arc']
    edge_index = {pc[1]: m for m, pc in enumerate(pc for pc in pcs if pc[0] == 'edge')}
    hyperbolas = []
    for pc in arcs:
        pts = piece_points(P, pc, 80)
        c, res = conic_through(pts)
        assert res < 1e-12, res
        assert c[1] ** 2 - 4 * c[0] * c[2] > 0.1              # a hyperbola
        prev_e = edge_index[(pc[1] - 2) % P.n_int]            # the edge before the arc
        nxt_e = (prev_e + 1) % 8
        for m, end in ((prev_e, pts[0]), (nxt_e, pts[-1])):
            p, d = L[m]
            assert abs(cross(d, end - p)) < 1e-12               # the arc ends on the edges
            assert abs(cross(d, P.curve_d(0, pc[1] * P.tsw if m == prev_e else
                                          (pc[1] + 1) * P.tsw))) < 1e-12   # tangent there
        center = conic_center(c)
        flank = [L[(prev_e - 1) % 8], L[(nxt_e + 1) % 8]]
        assert np.linalg.norm(center - line_intersection(*flank[0], *flank[1])) < 1e-9
        dirs = asymptote_directions(c)
        for p, d in flank:
            assert min(abs(cross(d, e)) for e in dirs) < 1e-9
        # The classical construction from the octagon O alone (asymptotes: the sides next to the sides
        # at the corner; tangent to one side at the corner) gives the same hyperbola, tangent to the
        # other side too, at the ends of the arc.
        m = int(np.argmin(np.linalg.norm(O - pts[len(pts) // 2], axis=1)))
        Cc, e1, e2, kappa, T1, T2 = corner_hyperbola(O, m)
        assert np.linalg.norm(Cc - center) < 1e-9
        u, v = hyperbola_uv(Cc, e1, e2, pts).T
        assert np.abs(u * v / kappa - 1).max() < 1e-10
        assert np.linalg.norm(T1 - pts[0]) < 1e-9 and np.linalg.norm(T2 - pts[-1]) < 1e-9
        hyperbolas.append((pc, c, center, flank))

    # In the regular frame of inradius 1 the sides lie on the lines ℓ_k: x cos(kπ/4) + y sin(kπ/4) = 1,
    # and the arc at the corner of ℓ_k and ℓ_{k+1} is the curve d_{k-1} d_{k+2} = √2/4, where
    # d_j(p) = 1 - ⟨p, n_j⟩ is the distance from p to ℓ_j: its asymptotes are ℓ_{k-1} and ℓ_{k+2}. It
    # touches ℓ_k and ℓ_{k+1} at (3√2 - 4)/2 from the corner, keeps a straight part 2 - √2 (1/√2 of the
    # side) of each side, and cuts the corner to the depth sec(π/8) - (1 - 2^(-3/4))/sin(π/8).
    Mreg = regular_frame(P)
    normals = np.array([[math.cos(k * math.pi / 4), math.sin(k * math.pi / 4)] for k in range(8)])
    Oreg = O @ Mreg.T
    for m in range(8):                                   # side m of edge_polygon lies on ℓ_m
        assert np.abs(Oreg[[m, (m + 1) % 8]] @ normals[m] - 1).max() < 1e-12
    depth = 1 / math.cos(math.pi / 8) - (1 - 2 ** -0.75) / math.sin(math.pi / 8)
    for pc in arcs:
        pts = piece_points(P, pc, 400) @ Mreg.T
        mid = pts[len(pts) // 2]
        k = int(round((math.atan2(mid[1], mid[0]) * 8 / math.pi - 1) / 2)) % 8
        dA, dB = 1 - pts @ normals[(k - 1) % 8], 1 - pts @ normals[(k + 2) % 8]
        assert dA.min() > 0 and dB.min() > 0
        assert np.abs(dA * dB - SQRT2 / 4).max() < 1e-10
        V = Oreg[(k + 1) % 8]                            # the corner of ℓ_k and ℓ_{k+1}
        assert abs(1 - pts[0] @ normals[k]) < 1e-12 and abs(1 - pts[-1] @ normals[(k + 1) % 8]) < 1e-12
        for T in (pts[0], pts[-1]):
            assert abs(np.linalg.norm(T - V) - (3 * SQRT2 - 4) / 2) < 1e-12
        assert abs(np.linalg.norm(pts - V, axis=1).min() - depth) < 1e-6
    assert abs(depth - 0.0230402) < 1e-7

    # The densest lattice packing: the lattice Λ_t = Z σ₀(t) + Z σ₁(t) has determinant √3/2, no nonzero
    # point inside K and exactly six on its boundary, σ_j(t); the copies K + 2Λ_t pack the plane with
    # density area(K)/√12 = δ_oct, for every t (the balanced motion).
    gK = Gauge(B)
    for t in np.linspace(0, P.tf, 13):
        b0, b1 = P.curve(0, t), P.curve(1, t)
        assert abs(det2(b0, b1) - SQRT3 / 2) < 1e-12
        pts, _ = lattice_points(b0, b1)
        nv = gK(pts)
        assert nv.min() > 1 - 1e-6
        assert np.sum(nv < 1 + 1e-6) == 6
        on = pts[nv < 1 + 1e-6]
        assert all(min(np.linalg.norm(on - P.curve(j, t), axis=1)) < 1e-12 for j in range(6))
    assert abs(AREA_OCT / (4 * SQRT3 / 2) - DELTA_OCT) < 1e-15
    # Every affinely regular hexagon inscribed in K has area 3√3/2 (det(p, q) = √3/2), so the
    # critical determinant of K is √3/2 and Λ_t is critical.
    dets = [inscribed_hexagon_det(P, gK, phi) for phi in np.linspace(0, 2 * math.pi, 37)[:-1] + 0.05]
    assert max(abs(d - SQRT3 / 2) for d in dets) < 1e-6, dets

    # The smoothed (6k+2)-gons for k = 1, …, 6: the cost is the area (by quadrature), and the
    # densities increase with k towards that of the disk, π/√12; the octagon's is the least.
    dens = []
    for k in range(1, 7):
        Pk = OCT if k == 1 else SmoothedPolygon(k)
        assert abs(np.trace(Pk.h) - 2 * math.cos(Pk.theta)) < 1e-12
        assert np.abs(Pk.g(Pk.tf) - R).max() < 1e-12                           # g(t_f) = R
        assert abs(Pk.cost() - Pk.area_quad()) < 1e-9
        assert abs(Pk.cost() - shoelace(Pk.boundary(80))) < 1e-5
        assert len(pieces(Pk)) == 2 * (6 * k + 2)          # 6k + 2 edges and 6k + 2 arcs
        dens.append(Pk.density())
    assert all(a < b for a, b in zip(dens, dens[1:])) and dens[-1] < DELTA_DISK
    assert abs(dens[0] - DELTA_OCT) < 1e-12

    return {'err_ode': err_ode, 'cost': cost, 'area': area_q, 'area_polygon': area_poly,
            'rho_min': rho_min, 'area_O': area_O, 'densities': dens, 'hyperbolas': hyperbolas}


if __name__ == '__main__':
    P = OCT
    print(f'y0 = {P.y0:.12f}, t_sw = {P.tsw:.12f}, t_f = {P.tf:.12f}')
    out = verify()
    print(f"closed form vs ODE: max difference {out['err_ode']:.2e}")
    print(f"cost {out['cost']:.12f}, area {out['area']:.12f}, sqrt(12) delta_oct {AREA_OCT:.12f}")
    print(f"area of the octagon of the edge lines {out['area_O']:.9f}")
    print('densities k = 1..6:', ', '.join(f'{d:.7f}' for d in out['densities']),
          f'(disk {DELTA_DISK:.7f})')
