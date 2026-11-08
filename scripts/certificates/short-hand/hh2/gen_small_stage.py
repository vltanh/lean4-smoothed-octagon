"""Staged clearing for the small outer face: Heavy/S2SmallLinkA, S2SmallLinkB (stage 2) and the
stage-1 strings used by gen_small_link.py. Run after gen_small.py."""
import re, os
import sympy as sp
from common import OUT, MOD, write, lean_expr
from shiftgen import nz_names
from leangen import nested_coeffs
from gen_small import polys

S, D, B, a, u = sp.symbols('S D B a u')
x, c = sp.symbols('x c')
GEN = 'gen_small_stage.py'

def templates(S_, D_, B_, a_, u_):
    M = f"(6 * {a_} ^ 2 + 1)"
    N = f"({M} * ({S_} * ({u_} - 1) + 1 / {S_}) + 2 * {S_} - 1)"
    W = f"({M} ^ 2 - {M} * {S_} + {S_} ^ 2 + {D_} ^ 2 * {u_} - {D_} * {N}) / (49 * {a_} ^ 4)"
    EL = f"(2 * {D_} * {u_} - {N}) / (7 * {a_} ^ 2)"
    k = f"(1 / 7 / ({a_} / {B_}))"
    cc = f"(({u_} - 1) / ({a_} / {B_}) + {a_} / {B_} + 1 - 1 / 7 - {EL})"
    LB = f"(-296 / 1029 + (4 * (2 * {k}) / 3 - 1) - (4 * (2 * {k}) / 3 - 1) ^ 2 / 2 + (4 * (2 * {k}) / 3 - 1) ^ 3 / 3)"
    G2 = f"({W} - 1) * 2 + 1 / 2 + {cc} + {LB} + (2 - 7 * 2 * {k} / 4) * ({W} - 3 / 4)"
    H1 = f"{G2} + (1 / {k} - 2) * ((1 - 7 * {k} / 4) * ({W} - 3 / 4))"
    return G2, H1

def sym_faces():
    Mm = 6 * a**2 + 1
    N = Mm * (S * (u - 1) + 1 / S) + 2 * S - 1
    W = (Mm**2 - Mm * S + S**2 + D**2 * u - D * N) / (49 * a**4)
    EL = (2 * D * u - N) / (7 * a**2)
    k = sp.Rational(1, 7) / (a / B)
    cc = (u - 1) / (a / B) + a / B + 1 - sp.Rational(1, 7) - EL
    tt = 4 * (2 * k) / 3 - 1
    LB = sp.Rational(-296, 1029) + tt - tt**2 / 2 + tt**3 / 3
    G2 = (W - 1) * 2 + sp.Rational(1, 2) + cc + LB + (2 - 7 * 2 * k / 4) * (W - sp.Rational(3, 4))
    H1 = G2 + (1 / k - 2) * ((1 - 7 * k / 4) * (W - sp.Rational(3, 4)))
    return G2, H1

def atoms_sub(e, S_, D_, B_, a_):
    s = lean_expr(e)
    for nm, v in [('S', S_), ('D', D_), ('B', B_), ('a', a_)]:
        s = re.sub(r'\b' + nm + r'\b', '(' + v + ')', s)
    return s

CON = dict(S_='1 + x', D_='hsDg x be al', B_='al + be', a_='al')
ABS = dict(S_='S', D_='D', B_='B', a_='a')
UdL = "(1200 * (1 + x) ^ 2 * (be - 1))"
UnL = "(900 * (1 + x) ^ 2 * (be - 1) + 85 * (x - 1) ^ 3 + (1 + x) ^ 2 * (be - x))"
KAPPA = {'H0': ("(1 + x)", 18522), 'H1': ("(al * (1 + x))", 37044)}

def stage1():
    G2, H1 = sym_faces()
    out = {}
    for nm, F in [('H0', G2), ('H1', H1)]:
        Pi = sp.expand(sp.cancel(F * a**5 * B * S))
        Pp = sp.Poly(Pi, u)
        out[nm] = (Pp.coeff_monomial(1), Pp.coeff_monomial(u))
    return out

def main():
    st = stage1()
    res = polys()
    be = x + c * (a - 1)
    subs = {S: 1 + x, B: a + be, D: a**2 + 2 * a * be + 1 + 2 * x - 2 * be * x}
    Ud = 1200 * (1 + x)**2 * (be - 1); Un = 900 * (1 + x)**2 * (be - 1) + 85 * (x - 1)**3 + (1 + x)**2 * (be - x)
    for nm, X, tag in [('H0', 'hh2SmQA', 'A'), ('H1', 'hh2SmQB', 'B')]:
        P0, P1 = st[nm]
        E = sp.expand(P0.subs(subs) * Ud + P1.subs(subs) * Un)
        kap, num = KAPPA[nm]
        kap_sym = (1 + x) if nm == 'H0' else a * (1 + x)
        assert sp.expand(E * num + kap_sym * (-res[nm][0])) == 0
        Qd = nested_coeffs(__import__('bern').from_sympy(-res[nm][0], (c, a, x)))
        names = [n for row in nz_names(X, Qd) for n in row if n]
        p0 = atoms_sub(P0, **CON); p1 = atoms_sub(P1, **CON)
        body = f'''/-- **Stage 2 for `{nm}`**: the atom polynomial of the small outer face in `(c, α, x)`. -/
theorem hh2_sm_stage2_{nm} (x al c be : ℝ) (hbe : be = x + c * (al - 1)) :
    ({p0}) * {UdL} + ({p1}) * {UnL} = -({kap} * {X} c al x / {num}) := by
  subst hbe
  unfold hsDg {X} {" ".join(names)}
  ring
'''
        write(f'S2SmallLink{tag}.lean', [MOD + 'S2SmallShift', MOD + 'S2Face'],
              f'small outer face, stage 2 for `{nm}`',
              f"The expansion of the stage-1 atom polynomial of `{nm}` (small outer face) in `(c, α, x)`, "
              f"`β = x + c(α - 1)`, `u_s = U_n/U_d`.", f"* `hh2_sm_stage2_{nm}`.", body, GEN)
    return st

if __name__ == '__main__':
    main()
