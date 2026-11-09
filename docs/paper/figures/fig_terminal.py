"""The terminal comparison (Section 10 and its appendix): the four-piece and five-piece densities.

Every curve is computed from the closed-cycle data of Section 10 (labels def:term-cycle,
eq:term-tri, eq:term-arc, eq:term-rawarc), the parametrizations lem:four-param and lem:five-param,
and the densities eq:four-density and eq:five-density. Before drawing, the module checks with
`assert`s that the parametrized factors satisfy the tangent closure, that the forced initial
margins close up under the twist and lie on the quadric, that the raw cost of the cycle is 8 times
the density, and every fact that the captions state.

    python3 docs/paper/figures/fig_terminal.py
"""
import math
import os

import numpy as np

import paperstyle as ps

SQ2 = math.sqrt(2.0)
LOG2 = math.log(2.0)
DELTA_OCT = (8 - 4 * SQ2 - LOG2) / (2 * SQ2 - 1)
TSTAR = SQ2 - 1                                   # t* of the five-piece envelope
R_TRI = np.array([[0.0, 1.0], [-1.0, 1.0]])       # R in triangular coordinates


# ---- closed cycles (def:term-cycle) ---------------------------------------------------------------

def tri_factor(i, q):
    """The tangent factor T_i(q) in triangular coordinates, eq:term-tri."""
    if i == 0:
        return np.array([[q, 0.0], [0.0, 1 / q]])
    if i == 1:
        return np.array([[1 / q, q - 1 / q], [0.0, q]])
    return np.array([[1 / q, 0.0], [1 / q - q, q]])


def raw_arc(a, b, c, q):
    """a((a + b)(q - 1) + (a + c)(1 - 1/q) - a log q), eq:term-rawarc."""
    return a * ((a + b) * (q - 1) + (a + c) * (1 - 1 / q) - a * math.log(q))


def run_cycle(labels, factors, m0):
    """Apply the one-arc margin map along the word; return the margins at every switch, the raw
    cost, and the closure product."""
    m = [np.array(m0, dtype=float)]
    cost = 0.0
    prod = np.eye(2)
    for i, q in zip(labels, factors):
        cur = m[-1]
        a, b, c = cur[i], cur[(i + 1) % 3], cur[(i - 1) % 3]
        cost += raw_arc(a, b, c, q)
        nxt = cur.copy()
        nxt[(i + 1) % 3] = (a + b) * q - a
        nxt[(i - 1) % 3] = (a + c) / q - a
        m.append(nxt)
        prod = prod @ tri_factor(i, q)
    return m, cost, prod


def check_cycle(labels, factors, m0):
    m, cost, prod = run_cycle(labels, factors, m0)
    assert np.allclose(prod, R_TRI, atol=1e-11), prod                    # tangent closure
    for mk in m:
        assert np.all(mk > 0)                                            # strict star states
        assert abs(mk[0] * mk[1] + mk[1] * mk[2] + mk[2] * mk[0] - 4) < 1e-10
    # the twist: m_N(j) = m_0(j - 1)
    assert np.allclose(m[-1], [m[0][2], m[0][0], m[0][1]], atol=1e-10)
    for k in range(len(labels)):                                         # neighbouring labels
        nxt = labels[k + 1] if k + 1 < len(labels) else (labels[0] + 1) % 3
        assert nxt != labels[k]
    return cost


# ---- four pieces (lem:four-param, thm:four-density, app:four-density) ----------------------------

def four_density(a, b):
    """delta(a, b) = [4s(s - 1) + 2(1 + a)(1 - b) log a + 2(1 - a)(1 + b) log b]/((s - 1)(s + 3))."""
    s = a + b
    return (4 * s * (s - 1) + 2 * (1 + a) * (1 - b) * np.log(a)
            + 2 * (1 - a) * (1 + b) * np.log(b)) / ((s - 1) * (s + 3))


def four_cycle(a, b):
    """The word 2 0 1 2 with factors (1/a, 1/b, 1/a, 1/b) and the forced initial margins."""
    s = a + b
    N = (s - 1) * (s + 3)
    m0 = np.array([2 * (s - 1), 2 * (1 - a + b), 2 * (1 + a - b)]) / math.sqrt(N)
    return [2, 0, 1, 2], [1 / a, 1 / b, 1 / a, 1 / b], m0


def weight(x, c):
    """(2x + c) log x/(1 - x), monotone on (0, 1) for c >= 2 (lem:four-weight)."""
    return (2 * x + c) * np.log(x) / (1 - x)


# ---- five pieces (lem:five-param, thm:five-density, app:five-density) ----------------------------

def five_F(t):
    """The function F of the five-piece density, eq:five-density."""
    return (((1 + t) / (1 - t)) ** 2 * np.log((1 + t ** 2) / (2 * t))
            + np.log((1 + t ** 2) / (1 - t ** 2)) / t ** 2 + np.log(2 * t / (1 - t ** 2)))


def five_density(u, v):
    """delta(u, v) = [2(d + 2) - (d/2)(F(u) + F(v))]/(4 - d), d = (1 - u)(1 - v)."""
    d = (1 - u) * (1 - v)
    return (2 * (d + 2) - d / 2 * (five_F(u) + five_F(v))) / (4 - d)


def five_cycle(u, v):
    """The word 0 1 0 2 0 with factors (P(u), Q(u), r, Q(v), P(v)) and the forced margins."""
    P = lambda t: (1 + t * t) / (2 * t)
    Q = lambda t: (1 + t * t) / (1 - t * t)
    r = 4 * u * v / ((1 - u * u) * (1 - v * v))
    d = (1 - u) * (1 - v)
    N = d * (4 - d)
    m0 = 2 * np.array([(1 + u) * (1 - v), d, (1 - u) * (1 + v)]) / math.sqrt(N)
    return [0, 1, 0, 2, 0], [P(u), Q(u), r, Q(v), P(v)], m0


def five_h(t):
    """h(t) = -2t log t/(1 - t) - log(1 + t) (lem:five-h)."""
    return -2 * t * np.log(t) / (1 - t) - np.log(1 + t)


ENVELOPE_MAX = (3 + 2 * SQ2) * LOG2 + 2 * math.log(2 - SQ2)


# ---- the checks --------------------------------------------------------------------------------

def verify():
    rng = np.random.default_rng(20261108)
    # Four pieces: closure, forced state, cost; the minimum and its equality case.
    for th in rng.uniform(0.02, math.pi / 2 - 0.02, 40):
        a, b = math.cos(th), math.sin(th)
        cost = check_cycle(*four_cycle(a, b))
        assert abs(cost - 8 * four_density(a, b)) < 1e-9
    th = np.linspace(1e-3, math.pi / 2 - 1e-3, 20001)
    vals = four_density(np.cos(th), np.sin(th))
    k = int(np.argmin(vals))
    assert abs(th[k] - math.pi / 4) < 1e-3
    assert abs(four_density(SQ2 / 2, SQ2 / 2) - DELTA_OCT) < 1e-13
    assert np.all(vals[np.abs(th - math.pi / 4) > 1e-3] > DELTA_OCT)
    # the octagon's switch data: active margin 2/sqrt(2 sqrt2 - 1), third margin (sqrt2 - 1) times it
    _, _, m0 = four_cycle(SQ2 / 2, SQ2 / 2)
    act = 2 / math.sqrt(2 * SQ2 - 1)
    assert np.allclose(m0, [(SQ2 - 1) * act, act, act])
    # the octagon's duration (a/2) log q = log 2/(2 sqrt(2 sqrt2 - 1))
    assert abs(act / 2 * math.log(SQ2) - LOG2 / (2 * math.sqrt(2 * SQ2 - 1))) < 1e-15
    # The weight (2x + c) log x/(1 - x) is increasing for c >= 2.
    x = np.linspace(1e-3, 1 - 1e-3, 4001)
    for c in (2.0, 2.5, 3.0, 4.0):
        assert np.all(np.diff(weight(x, c)) > 0)
    # Five pieces: closure, forced state, cost.
    n = 0
    while n < 40:
        u, v = rng.uniform(0.01, 0.99, 2)
        if u + v + u * v <= 1:
            continue
        cost = check_cycle(*five_cycle(u, v))
        assert abs(cost - 8 * five_density(u, v)) < 1e-8 * max(1.0, abs(cost))
        n += 1
    # The envelope F(t) + 2 log(1 - t) <= its value at t* = sqrt2 - 1, and the identity (22).
    t = np.linspace(1e-3, 1 - 1e-3, 20001)
    env = five_F(t) + 2 * np.log(1 - t)
    assert np.all(env <= ENVELOPE_MAX + 1e-12)
    assert abs(t[int(np.argmax(env))] - TSTAR) < 1e-3
    assert abs(five_F(TSTAR) - (3 + 2 * SQ2) * LOG2) < 1e-12
    al, be = 2 * t / (1 + t * t), (1 - t * t) / (1 + t * t)
    assert np.allclose(env, LOG2 + five_h(al) + five_h(be), atol=1e-10)
    assert abs(LOG2 + 2 * five_h(SQ2 / 2) - ENVELOPE_MAX) < 1e-13
    # x -> h(sqrt x) is concave: second differences are negative.
    xs = np.linspace(1e-3, 1 - 1e-3, 4001)
    assert np.all(np.diff(five_h(np.sqrt(xs)), 2) < 0)
    # d = (1 - u)(1 - v) < d* = (2 - sqrt2)^2 on the domain, and the boundary value B(d*) = delta_oct.
    dstar = (2 - SQ2) ** 2
    K = (3 + 2 * SQ2) * LOG2
    assert abs((2 * dstar + 4 - K * dstar) / (4 - dstar) - DELTA_OCT) < 1e-14
    assert K > 3 + DELTA_OCT
    # The five-piece density exceeds delta_oct on the domain, with infimum at (t*, t*) on its edge.
    U, V = np.meshgrid(np.linspace(0.005, 0.995, 600), np.linspace(0.005, 0.995, 600))
    inside = U + V + U * V > 1 + 1e-9
    D = five_density(U[inside], V[inside])
    assert np.all((1 - U[inside]) * (1 - V[inside]) < dstar)
    assert np.all(D > DELTA_OCT)
    e = 1e-6
    assert five_density(TSTAR + e, TSTAR + e) - DELTA_OCT < 1e-4
    return {'four_min_theta': th[k], 'five_min': float(D.min())}


# ---- the figures --------------------------------------------------------------------------------

def make(out_dir):
    ps.setup()
    import matplotlib.pyplot as plt
    verify()

    # Figure 1: the two densities.
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(ps.FULL, 2.6),
                                   gridspec_kw={'width_ratios': [1.05, 1]})
    th = np.linspace(0.012, math.pi / 2 - 0.012, 1200)
    vals = four_density(np.cos(th), np.sin(th))
    ax1.plot(np.degrees(th), vals, color=ps.BLUE)
    ax1.axhline(DELTA_OCT, color=ps.FAINT, lw=0.8, ls='--')
    ax1.plot([45], [DELTA_OCT], 'o', color=ps.ORANGE, ms=4, zorder=3)
    ax1.annotate(r'$a=b=1/\sqrt{2}$', (45, DELTA_OCT), xytext=(52, DELTA_OCT + 0.008),
                 fontsize=8, color=ps.INK,
                 arrowprops=dict(arrowstyle='-', color=ps.FAINT, lw=0.6))
    ax1.text(88, DELTA_OCT - 0.0035, r'$\delta_{\mathrm{oct}}$', ha='right', va='top', fontsize=8,
             color=ps.FAINT)
    ax1.set_xlim(0, 90)
    ax1.set_ylim(DELTA_OCT - 0.008, 0.96)
    ax1.set_xticks([0, 15, 30, 45, 60, 75, 90])
    ax1.set_xlabel(r'$\theta$ (degrees), $a=\cos\theta$, $b=\sin\theta$')
    ax1.set_ylabel(r'$\delta(a,b)$')
    ax1.set_title('four pieces: the word $2\\,0\\,1\\,2$', fontsize=9)

    n = 500
    u = np.linspace(0.002, 0.998, n)
    U, V = np.meshgrid(u, u)
    inside = U + V + U * V > 1
    Z = np.full(U.shape, np.nan)
    Z[inside] = five_density(U[inside], V[inside]) - DELTA_OCT
    levels = [0.001, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1]
    assert np.nanmax(Z) < 0.1                    # delta(u, v) < 1 on the domain: d > 0
    cs = ax2.contourf(U, V, np.log10(Z), levels=np.log10(levels), cmap='Blues_r', extend='min')
    ax2.contour(U, V, np.log10(Z), levels=np.log10(levels[:-1]), colors=ps.INK, linewidths=0.3)
    uu = np.linspace(0, 1, 400)
    ax2.plot(uu, (1 - uu) / (1 + uu), color=ps.INK, lw=0.9)
    ax2.plot([TSTAR], [TSTAR], 'o', color=ps.ORANGE, ms=4, zorder=3)
    ax2.annotate(r'$(t_*,t_*)$', (TSTAR, TSTAR), xytext=(0.58, 0.08), fontsize=8,
                 arrowprops=dict(arrowstyle='-', color=ps.FAINT, lw=0.6))
    ax2.text(0.03, 0.30, r'$u+v+uv\leq 1$', fontsize=7.5, color=ps.FAINT)
    ax2.set_xlim(0, 1)
    ax2.set_ylim(0, 1)
    ax2.set_aspect('equal')
    ax2.set_xlabel('$u$')
    ax2.set_ylabel('$v$')
    ax2.set_title('five pieces: the word $0\\,1\\,0\\,2\\,0$', fontsize=9)
    cb = fig.colorbar(cs, ax=ax2, fraction=0.046, pad=0.04)
    ticks = [0.001, 0.01, 0.1]
    cb.set_ticks(np.log10(ticks))
    cb.set_ticklabels(['0.001', '0.01', '0.1'])
    cb.set_label(r'$\delta(u,v)-\delta_{\mathrm{oct}}$', fontsize=8)
    cb.ax.tick_params(labelsize=7)
    fig.tight_layout(w_pad=1.5)
    ps.save(fig, os.path.join(out_dir, 'fig-terminal-densities.pdf'))

    # Figure 2: the envelope of the five-piece density.
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(ps.FULL, 2.3))
    t = np.linspace(0.004, 0.996, 1500)
    ax1.plot(t, five_F(t) + 2 * np.log(1 - t), color=ps.BLUE)
    ax1.axhline(ENVELOPE_MAX, color=ps.FAINT, lw=0.8, ls='--')
    ax1.plot([TSTAR], [ENVELOPE_MAX], 'o', color=ps.ORANGE, ms=4, zorder=3)
    ax1.annotate(r'$t_*=\sqrt{2}-1$', (TSTAR, ENVELOPE_MAX), xytext=(0.5, ENVELOPE_MAX - 0.9),
                 fontsize=8, arrowprops=dict(arrowstyle='-', color=ps.FAINT, lw=0.6))
    ax1.set_xlim(0, 1)
    ax1.set_ylim(ENVELOPE_MAX - 3.0, ENVELOPE_MAX + 0.4)
    ax1.set_xlabel('$t$')
    ax1.set_ylabel(r'$F(t)+2\log(1-t)$')
    ax1.set_title('the envelope of the five-piece density', fontsize=9)
    x = np.linspace(0.002, 0.998, 1500)
    ax2.plot(x, five_h(np.sqrt(x)), color=ps.BLUE)
    a2 = (2 * TSTAR / (1 + TSTAR ** 2)) ** 2
    pts = np.array([0.18, 0.82])
    ax2.plot(pts, five_h(np.sqrt(pts)), 'o-', color=ps.GREEN, ms=3.5, lw=0.8)
    ax2.plot([0.5], [five_h(math.sqrt(0.5))], 'o', color=ps.ORANGE, ms=4, zorder=3)
    ax2.plot([0.5], [five_h(np.sqrt(pts)).mean()], 'o', color=ps.GREEN, ms=3.5, mfc='white')
    assert abs(a2 - 0.5) < 1e-12               # alpha^2 = beta^2 = 1/2 exactly at t = t*
    ax2.set_xlim(0, 1)
    ax2.set_xlabel('$x$')
    ax2.set_ylabel(r'$h(\sqrt{x})$')
    ax2.set_title(r'$x\mapsto h(\sqrt{x})$ is concave', fontsize=9)
    fig.tight_layout(w_pad=2.0)
    ps.save(fig, os.path.join(out_dir, 'fig-terminal-envelope.pdf'))


if __name__ == '__main__':
    make(os.path.dirname(os.path.abspath(__file__)))
    print('fig_terminal: checks passed, figures written')
