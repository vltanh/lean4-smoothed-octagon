"""The residuals of SmoothedOctagon/Certificates/Nonshort.lean, transcribed definition by
definition (same association order), for chart 1 (l0,l1,l2) = (0,1,ell) and chart 2 (0,ell,1)."""
from fractions import Fraction as Fr
from expr import var, C, hlog, log, name


def ccp(a, c, eps, l0, l1, l2):
    cx0 = a ** 2
    cx1 = a * c
    cx2 = 2 * cx1
    cx3 = cx0 + cx2 - 4
    cx4 = c * l1
    cx5 = l2 ** 3
    cx6 = cx0 + 4
    cx7 = a + c
    cx8 = l1 ** 3
    cx9 = c * cx8
    cx10 = cx7 * cx9
    cx11 = l1 ** 2
    cx12 = cx3 * l0
    cx13 = l2 ** 2
    cx14 = 2 * cx12
    cx15 = cx7 * l2
    cx16 = a * l1
    cx17 = 6 * cx12 * cx15 * cx16
    cx18 = 4 * a
    cx19 = 3 * cx0
    cx20 = l0 ** 2
    cx21 = cx20 * l2
    cx22 = 8 * cx1
    cx23 = cx13 * cx16
    cx24 = a ** 3
    cx25 = 4 * c
    cx26 = c * cx19 + cx25
    cx27 = cx16 * cx20
    cx28 = 12 * c
    cx29 = c ** 2
    cx30 = 8 * cx29
    cx31 = c * cx0
    cx32 = cx11 * l2
    cx33 = cx29 + 4
    cx34 = 3 * a
    cx35 = 2 * c
    cx36 = cx25 + cx34
    cx37 = a * cx14
    cx38 = 5 * cx24
    cx39 = 12 * a
    cx40 = l1 * l2
    cx41 = a * cx40
    cx42 = 8 * c
    cx43 = a * cx29
    cx44 = 10 * a ** 4
    cx45 = c ** 3
    cx46 = 8 * a
    cx47 = c * cx24
    cx48 = cx0 * cx29
    cx49 = cx27 * cx6
    cx50 = cx25 + cx38
    cx51 = cx21 * cx6
    cx52 = cx11 * cx15
    C2 = -cx3 * (a * (l0 + l2) + cx4) ** 2
    C3 = (-c * cx32 * (a * cx30 - 16 * a + 6 * cx24 - cx28 + 15 * cx31) - cx0 * cx13 * cx14
          - cx0 * cx21 * (c * cx18 + cx19 - 4) + cx0 * cx5 * cx6 - cx10 * (cx1 + 4)
          - cx11 * cx12 * cx2 - cx17 - cx23 * cx7 * (5 * cx0 + cx22 - 12)
          - cx27 * (-cx18 + cx24 + cx26))
    C4 = (a * cx5 * l1 * (cx26 + cx38 + cx39) - cx1 * cx11 * cx20 * cx6
          - cx1 * cx33 * l1 ** 4
          - cx11 * cx13 * (-12 * cx0 - 24 * cx1 - cx30 + cx44 + cx45 * cx46 + 30 * cx47 + 29 * cx48)
          - 2 * cx13 * cx20 * cx24 * cx7 - cx14 * cx23 * (cx34 + cx35)
          - cx20 * cx41 * (cx18 + cx28 + 7 * cx31 + cx38) - cx32 * cx36 * cx37
          - cx9 * l2 * (7 * cx24 + 18 * cx31 + cx42 + 9 * cx43))
    C5 = cx40 * (a * cx13 * l1 * (cx0 * cx28 + 10 * cx24 + cx29 * cx34 + cx39 + cx42)
                 - cx11 * cx37 * cx7 - cx15 * cx18 * cx20 * (cx0 + 2) - cx17
                 - cx32 * (13 * a * cx45 - 4 * cx0 - cx22 + 4 * cx29 + cx44 + 33 * cx47 + 38 * cx48)
                 - cx36 * cx49 - cx9 * (11 * cx31 + 7 * cx43 + cx46 + cx50))
    C6 = cx52 * (a * cx13 * l1 * (10 * cx0 + cx22 + cx33) - 3 * cx1 * cx7 * cx8
                 - cx14 * cx41 - cx32 * (14 * cx31 + 10 * cx43 + cx50) - cx34 * cx51 - cx49)
    C7 = a * cx15 * cx8 * (-cx10 + cx13 * cx7 * l1 * (5 * a + cx35) - cx51
                           - cx52 * (a + cx25))
    C8 = a * cx13 * cx7 ** 2 * l1 ** 5 * (-cx4 + cx7 * l2)
    return ((((((C8 * eps + C7) * eps + C6) * eps + C5) * eps + C4) * eps + C3) * eps + C2)


def build(chart, branch=0):
    a, c, eps, ell = var(0), var(1), var(2), var(3)
    l0 = C(0)
    if chart == 1:
        l1, l2 = C(1), ell
    else:
        l1, l2 = ell, C(1)
    z0 = eps * l0
    z1 = name('z1', eps * l1)
    z2 = name('z2', eps * l2)
    K = name('K', a ** 2 + 4)
    T0 = name('T0', a + c)
    S = name('S', K / (T0 * (1 + z0)))
    d = name('d', a + T0 * z1)
    W = name('W', T0 * (1 + z1))
    Q = name('Q', d ** 2 + 4)
    q = name('q', 1 + z2)
    Z = name('Z', Q * q / W)
    r = name('r', Z - d)
    Y = name('Y', W ** 2 - T0 ** 2)
    N = name('N', d * W - q * Y)
    H0 = hlog(z0)
    H1 = name('H1', hlog(z1))
    H2 = name('H2', hlog(z2))
    Bv = name('Bv', c * (4 - a ** 2) + 8 * a + a * z1 * (c ** 2 + 4)
              + z2 * T0 * (z1 + 2) * (K + a * T0 * z1 * (z1 + 2)))
    cpc = name('cpc', ccp(a, c, eps, l0, l1, l2))
    base = name('base', cpc / (2 * a * Q * (1 + z1) ** 2 * q))
    phi = name('phi', base - eps * K * N * l0 ** 3 * H0 / (Q * W)
               + eps * c * T0 * l1 ** 3 * Bv * H1 / (a * Q * W)
               - eps * d * l2 ** 3 * H2)
    D1 = name('D1', K ** 2 / (a * Q * W * (1 + z0))
              * (a * (l0 + l2) + c * l1 + a * eps * l0 * l2
                 + T0 * eps * l1 * l2 * (2 + eps * l1)))
    shift = name('shift', eps * phi / D1)
    rr = name('rr', a * T0 / K)
    tt = name('tt', a / T0)
    rho = name('rho', a ** 2 / K)
    xc = name('xc', c / T0)
    u0 = name('u0', 1 - rr + rr ** 2)
    v0 = name('v0', 1 - tt + tt ** 2)
    h0 = name('h0', K * (-1 + 2 * (rr + tt) - rho) / 16)
    du = name('du', (2 * rr ** 2 - rr) * z0 + rr ** 2 * z0 ** 2 + shift)
    dv = name('dv', z1 * (xc / 2 - xc ** 2) + z1 ** 2 * (xc ** 2 / (1 + z1) - xc * H1))
    dh = name('dh', K * (2 * rr * z0 - log(1 + z0) + dv / tt + S / a * shift) / 16)
    u = name('u', u0 + du)
    v = name('v', v0 + dv)
    h = name('h', h0 + dh)
    excess = name('excess', Fr(7, 2000) + K ** 2 * (v0 * du + u0 * dv + du * dv) / 64
                  - 2 * h0 * dh - dh ** 2)
    hd = name('hd', h + v * Y / 8)
    w = name('w', (u * K ** 2 + 16 * h * Y + v * Y ** 2) / Q ** 2)
    Kr = name('Kr', r ** 2 + 4)
    tn = name('tn', (Q ** 2 * v - 16 * hd * Z ** 2 + w * (Z ** 2) ** 2) / Kr ** 2)
    L2 = name('L2', 1 - z2 / 2 + z2 ** 2 * H2)
    Fend = name('Fend', 1 + (d / W) ** 2 * q - d / W * q * L2)
    turn = name('turn', Fr(1, 2) - (1 - xc + z1) / (1 + z1) ** 2 - z1 * H1)
    upperTurn = name('upperTurn', xc - Fr(1, 2) - z1 * (xc / (1 + z1) - H1))
    g = [
        c - a,
        K - T0 ** 2 * (1 + z0),
        12 - 17 * a ** 2,
        4 - c * d - Fr(2, 15) * W,
        c - Fr(2, 15) - (d + Fr(2, 15)) * z2,
        4 - a ** 2 - 2 * a * c - T0 ** 2 * z1 + Q * z2,
        c - a * (1 + z1),
        -phi,
        upperTurn,
        turn,
        v - Fend,
        8 - d,
        8 - r,
        T0 - Fr(1, 2),
        W - Fr(1, 2),
        Z - Fr(1, 2),
    ]
    gnames = [f'g{i}' for i in range(16)]
    if chart == 2:
        g.append(c - a - T0 * z1)
        gnames.append('g16')
    tau = name('tau', tn - Fr(3, 4))
    g.append(tau)
    gnames.append('tau')
    if branch == 0:
        g.append(-excess)
        gnames.append('negExcess')
    else:
        Bq = name('B', Z ** 3 * (4 - d * r) / (d * Kr ** 2))
        Gp = name('Gprime', Q ** 2 * v / 64 - hd * Q * Z / (8 * d))
        Cq = name('C', Q ** 2 * Z ** 2 / (256 * d ** 2))
        ee = name('endpointExcess', Bq ** 2 * excess + Bq * Gp * tau - Cq * tau ** 2)
        g.append(-ee)
        gnames.append('negEndpointExcess')
    return g, gnames


def root_box():
    import fx
    U = fx.U
    a = (fx.ofRat(1, 2)[0], fx.ofRat(17, 20)[1])
    c = (fx.ofRat(2, 15)[0], 2 * U)
    e = (fx.ofRat(1, 32)[0], 15 * U)
    l = (0, U)
    return [a, c, e, l]
