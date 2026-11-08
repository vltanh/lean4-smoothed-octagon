"""Computations for `hs3_central_alpha` (DISPLACEMENT_CENTRAL_FACE §2), u frozen at a constant c."""
import sympy as sp, pickle, sys, os
from fractions import Fraction as Fr
from hh3_common import *

x, a, c, h, z = sp.symbols('x a c h z')
R = sp.Rational
LO, HI = R(3, 4), R(4, 5)
ZMAX = R(89, 72) - R(108, 95)


def F_noLog(i, x, be, al, u, q):
    S = 1 + x
    D = al**2 + 2 * al * be + 1 + 2 * x - 2 * be * x
    e = 1 - 1 / al**2; n_ = S / al**2; Dl = D / al**2
    E0 = S * (u - 1) + 1 / S
    A1 = 2 * e + n_ + Dl * E0
    A2 = e**2 + e * n_ + n_**2 + Dl**2 * u + Dl * e * E0 - Dl * (2 * S - 1) / al**2
    A3 = 2 * Dl * u + e * E0 - (2 * S - 1) / al**2
    Ws = 1 - q * A1 + q**2 * A2; ELs = -E0 + q * A3
    rA = al / (al + be); y = 2 * q / rA
    n = [2 + 4 * (4 - 3 * y) / (5 * al - 1), rA / q + 4 / (5 * al - 1)][i]
    return (u - 1) / rA + rA + 1 - q - ELs + n * (Ws - R(3, 4))


def slope(i, x, be, al, q):
    S = 1 + x
    D = al**2 + 2 * al * be + 1 + 2 * x - 2 * be * x
    rA = al / (al + be); y = 2 * q / rA
    n = [2 + 4 * (4 - 3 * y) / (5 * al - 1), rA / q + 4 / (5 * al - 1)][i]
    Dl = D / al**2; e = 1 - 1 / al**2
    return 1 / rA + S - q * (2 * Dl + e * S) + n * (-q * Dl * S + q**2 * (Dl**2 + Dl * e * S))


def compute():
    be = x + 25 * x / (15 * x + 36) * (a - 1)
    q = a**2 / (x * (x + 2) + a**2)
    K = x * (x + 2) + a**2; Z = 40 * a * x + 36 * a + 15 * x**2 + 11 * x; k = 5 * a - 1
    out = {}
    for i in (0, 1):
        Dp = (18 * (5 * x + 12)**3 * a * k * K**3 * Z) if i == 0 else (36 * (5 * x + 12)**2 * a * k * K**2 * Z)
        N = sp.cancel(sp.together(F_noLog(i, x, be, a, c, q) * Dp))
        num, den = sp.fraction(N)
        assert den == 1, den
        N = sp.expand(num)
        E = a * k * K * Z
        ED = sp.cancel(sp.diff(Dp, a) * E / Dp); assert sp.fraction(ED)[1] == 1
        ED = sp.expand(ED)
        EL = sp.cancel((1 / a + sp.diff(Z, a) / Z - sp.diff(K, a) / K) * E); assert sp.fraction(EL)[1] == 1
        EL = sp.expand(EL)
        Q = sp.expand(sp.diff(N, a) * E - N * ED + sp.expand(Dp) * EL)
        Pq = sp.expand(-Q)
        # certificates at c = LO, HI
        certs = {}
        PL = {}
        for cv in (LO, HI):
            d = to_dict(Pq.subs(c, cv).subs({x: 2 + h, a: R(108, 95) + z}, simultaneous=True), (h, z))
            ct = cert_a(d, Fr(1, 6)) if False else None
            ct = cert_c(d, Fr(1, 6), Fr(ZMAX.p, ZMAX.q))
            assert ct is not None
            print(i, cv, 'terms', len(d), 'res/p00', float(ct['res'] / d[(0, 0)]), file=sys.stderr)
            certs[cv] = ct; PL[cv] = d
        # slope
        sl = sp.factor(sp.together(slope(i, x, be, a, q)))
        snum, sden = sp.fraction(sl)
        snum = sp.expand(snum)
        sd = to_dict(snum.subs({x: 2 + h, a: R(108, 95) + z}, simultaneous=True), (h, z))
        sct = cert_c(sd, Fr(1, 6), Fr(ZMAX.p, ZMAX.q)); assert sct
        out[i] = dict(Dp=Dp, N=to_dict(N, (x, a, c)), E=E, ED=to_dict(ED, (x, a)), EL=to_dict(EL, (x, a)),
                      Pq=to_dict(Pq, (x, a, c)), PL=PL, certs=certs, snum=to_dict(snum, (x, a)), sden=sden,
                      sd=sd, sct=sct, Dexp=to_dict(sp.expand(Dp), (x, a)))
        print(i, 'N', len(out[i]['N']), 'Pq', len(out[i]['Pq']), 'ED', len(out[i]['ED']), 'EL', len(out[i]['EL']),
              'snum', len(out[i]['snum']), 'sden', sden, file=sys.stderr)
    return out


if __name__ == '__main__':
    out = compute()
    pickle.dump(out, open(os.path.join(os.environ.get('HH3_CACHE', '/tmp'), 'hh3_central.pkl'), 'wb'))
