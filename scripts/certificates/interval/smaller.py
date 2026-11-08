"""The residuals of SmoothedOctagon/Certificates/SmallerShort.lean, definition by definition."""
from fractions import Fraction as Fr
from expr import var, C, sqrt, atan, logdiv, name


def build(clamp=False):
    r, delta, al, rho, v, E = (var(i) for i in range(6))
    x = name('x', 1 / r - 1)
    be = name('be', (1 + delta) * x)
    S = name('S', 1 + x)
    A = name('A', al + be)
    B = name('B', be + x)
    xi = name('xi', 1 - r)
    h = name('h', xi * (2 + delta))
    u = name('u', 1 + xi / (2 + delta) - xi * logdiv(h))
    ax = name('ax', al * r / (1 - r))
    ha = name('ha', (2 + delta) / (1 + delta + ax))
    xa = name('xa', (1 + delta) / (1 + delta + ax))
    ua = name('ua', 1 + xa ** 2 / ha - xa * logdiv(ha))
    Eupperpoly = name('Eupperpoly', r * (u + v - 2) + 2 * r * r ** 2 - rho * r ** 2 + rho - r ** 2 * E)
    gam = name('gam', (4 * u * v - E ** 2) / (16 * (1 - rho) ** 2))
    D = name('D', al ** 2 + 2 * al * be + 1 + 2 * x - 2 * be * x)
    lam = name('lam', 1 / (1 + rho * (al ** 2 - 1)))
    ed = name('ed', rho * D)
    w = name('w', lam ** 2 * (v - ed * E + ed ** 2 * u))
    EL = name('EL', lam * (2 * ed * u - E))
    rhoA = name('rhoA', al ** 2 * lam * rho)
    ti = name('ti', lam * rho * al * A)
    TB = name('TB', A / al)
    zeta = name('zeta', (1 - 2 * ti) / (1 + 2 * ti))
    m0 = name('m0', 2 * (1 + zeta) + Fr(2, 3) * zeta * (1 + zeta) ** 2)
    Rbar = name('Rbar', m0 * (w - Fr(3, 4)) + (u - 1) * TB + 1 + 1 / TB - rhoA - EL - 2 * zeta
                - Fr(2, 3) * zeta * zeta ** 2)
    gap1 = name('gap1', (1 - rho - v) * r ** 2 + rho * (E - 1 + rho) * r + rho * (1 - rho - u))
    pmid = name('pmid', be ** 2 * rho * x ** 2 - be ** 2 * rho + be ** 2 - 4 * be * rho * x ** 2
                - 4 * be * rho * x + 2 * be * x + 3 * rho * x ** 2 + 4 * rho * x + rho + x ** 2)
    fmid = name('fmid', (1 - rho) * (be ** 2 * rho + be * rho * x + rho * x ** 2 - rho + 1) - v
                - rho * E * (be * x - 2 * x - 1) - rho * u * pmid)
    ra = name('ra', al / A)
    fouter = name('fouter', (1 - rhoA - w) * ra ** 2 + rhoA * (EL - 1 + rhoA) * ra
                  + rhoA * (1 - rhoA - u))
    kap = name('kap', sqrt(12 * gam))
    Uq = name('U', (1 - rho) / rho)
    N = name('N', (Uq - x) / S)
    Z = name('Z', (Uq - al * be) / A)
    P00 = name('P00', -N - 2); P01 = name('P01', x + 2); P10 = N; P11 = x
    Qi00 = name('Qi00', -al / (2 * Uq)); Qi01 = name('Qi01', (al + 2 * be) / (2 * Uq))
    Qi10 = name('Qi10', Z / (2 * Uq)); Qi11 = name('Qi11', (Z + 2 * be) / (2 * Uq))
    F00 = name('F00', S / A); F01 = C(0)
    F10 = name('F10', (S ** 2 - B ** 2) / (S * A)); F11 = name('F11', A / S)
    PF00 = name('PF00', P00 * F00 + P01 * F10); PF01 = name('PF01', P00 * F01 + P01 * F11)
    PF10 = name('PF10', P10 * F00 + P11 * F10); PF11 = name('PF11', P10 * F01 + P11 * F11)
    m00 = name('m00', PF00 * Qi00 + PF01 * Qi10); m01 = name('m01', PF00 * Qi01 + PF01 * Qi11)
    m10 = name('m10', PF10 * Qi00 + PF11 * Qi10); m11 = name('m11', PF10 * Qi01 + PF11 * Qi11)
    h11 = name('h11', E * (r - rho * S) - u * (1 - (rho * S) ** 2) + v * (1 - r ** 2))
    h12 = name('h12', u * (1 + rho * S) ** 2 + v * (1 + r) ** 2 - E * (1 + r) * (1 + rho * S))
    h21 = name('h21', -u * (1 - rho * S) ** 2 - v * (1 - r) ** 2 - E * (1 - r) * (1 - rho * S))
    Tk = name('Tk', 2 * kap * (1 - rho) ** 2)
    AA = name('AA', Tk * (m00 + m11) + h12 * m11 - h11 * (m01 + 3 * m10) - 3 * h21 * m00)
    BB = name('BB', h11 * (m11 - m00) + h12 * m10 + h21 * m01 + Tk / 3 * (3 * m10 - m01))
    s3 = sqrt(C(3))
    cost = name('cost', s3 * (rho * u / (1 - rho) * (2 * be * x - x - al * be)
                             + (be * x - al) / (S * A)))
    thetaC = name('thetaCentered', atan((3 * BB - AA) / (s3 * (AA + BB))))
    excess = name('excess', cost + (kap + Fr(3, 2)) * (Fr(6283, 12000) - thetaC) - Fr(2501, 800))
    f = [u - ua, 1 - r + r ** 2 - u, r ** 2 * (1 - v) - rho * r + rho ** 2, A ** 2 * (1 - u) - al * be,
         gam - Fr(27, 256), Fr(23, 125) - gam, w - Fr(3, 4), 1 - ti + ti ** 2 - w, Rbar,
         Fr(3, 20) - rhoA, 3 * rhoA - EL, gap1, Eupperpoly, 3 * rho - E, fmid, fouter,
         r ** 2 - rho, x - al, al - 1 - delta * (1 + 2 * x / 7), 1 - rho * (al ** 2 + 2 * al * be + 1),
         1 - rho * (1 + be * x), (u - 1) * (2 + delta) ** 2 + (1 + delta), Fr(13, 16) - u,
         AA - 2 * Tk, BB, AA - BB, AA + BB - 4 * Tk, -excess]
    return f, [f'f{i}' for i in range(28)]


def root_box():
    import fx
    U = fx.U
    return [(fx.ofRat(1, 10)[0], fx.ofRat(1, 2)[1]), (0, 2 * U), (U, fx.ofRat(631, 100)[1]),
            (fx.ofRat(1, 226)[0], fx.ofRat(3, 20)[1]), (fx.ofRat(3, 4)[0], U),
            (fx.ofRat(-23, 16)[0], fx.ofRat(9, 20)[1])]


SCALES = [0.4, 2, 5.31, 0.15, 0.25, 1.9]
