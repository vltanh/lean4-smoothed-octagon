"""Generator for `hs3_central_alpha` (DISPLACEMENT_CENTRAL_FACE §2): writes
`SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy/S3Central{A0,A1,B0,B1}.lean`.

Route (lighter than the note): the incoming norm is frozen at the endpoint value
`u₀ = ū(x, 20x/19)` (the test increases with u, and ū decreases along the path), so the
α-derivative of `F_i(x, α, b(x, α), u₀, q_c)` has no `u_b` term and is affine in `c = u₀`; its
cleared numerator `P_i(x, α, c)` (286 / 222 terms) is certified at `c = 3/4` and `c = 4/5` on
`[2, 13/6] × [108/95, 89/72]` by the crude corner bound (all adverse coefficients at the corner).
"""
import sympy as sp, pickle, sys, os
from fractions import Fraction as Fr
from hh3_common import *

x, a, c, h, z = sp.symbols('x a c h z')
R = sp.Rational
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../..'))
OUT = os.path.join(ROOT, 'SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy')
ZMAX = Fr(679, 6840)

NSTR = {0: "2 + 4 * (4 - 3 * (2 * hsQc x t / hsRA t (hs3b x t))) / (5 * t - 1)",
        1: "hsRA t (hs3b x t) / hsQc x t + 4 / (5 * t - 1)"}
DPROD = {0: "18 * (5 * x + 12) ^ 3 * t * (5 * t - 1) * (x * (x + 2) + t ^ 2) ^ 3 * (40 * t * x + 36 * t + 15 * x ^ 2 + 11 * x)",
         1: "36 * (5 * x + 12) ^ 2 * t * (5 * t - 1) * (x * (x + 2) + t ^ 2) ^ 2 * (40 * t * x + 36 * t + 15 * x ^ 2 + 11 * x)"}
SDEN = {0: "9 * t * (5 * t - 1) * (5 * x + 12) ^ 3 * (t ^ 2 + x ^ 2 + 2 * x) ^ 3",
        1: "9 * t * (5 * t - 1) * (5 * x + 12) ^ 2 * (t ^ 2 + x ^ 2 + 2 * x) ^ 2 * (40 * t * x + 36 * t + 15 * x ^ 2 + 11 * x)"}

HEADER = """module

public import {imp}

/-!
{doc}
-/

@[expose] public section

namespace SmoothedOctagon

open Real
"""


def coeff_lists(d3):
    """d3 keyed (x, a, c): list over powers of a of dicts keyed (x, c)."""
    da = max(k[1] for k in d3)
    out = []
    for e in range(da + 1):
        out.append({(kx, kc): v for (kx, ka, kc), v in d3.items() if ka == e})
    return out


def hor_list(lst, vars_):
    return "[" + ", ".join(horner(dct, vars_) if dct else "0" for dct in lst) + "]"


def emit_A(D, i):
    L = []
    Ncl = coeff_lists(D['N'])
    L.append(f"/-- The coefficients in `α` of the cleared central test `N_{i}(x, α, c)` (`u` frozen at `c`). -/\n"
             f"noncomputable def hh3C{i}Ns (x c : ℝ) : List ℝ :=\n  {hor_list(Ncl, ['x', 'c'])}\n")
    Dd = D['Dexp']
    da = max(k[1] for k in Dd)
    Dl = [{(kx,): v for (kx, ka), v in Dd.items() if ka == e} for e in range(da + 1)]
    L.append(f"/-- The coefficients in `α` of the clearing factor `D_{i}(x, α)`. -/\n"
             f"noncomputable def hh3C{i}Ds (x : ℝ) : List ℝ :=\n  {hor_list(Dl, ['x'])}\n")
    L.append(f"/-- `E D'/D` for `D_{i}` (`E = αkKZ`). -/\n"
             f"noncomputable def hh3C{i}ED (x a : ℝ) : ℝ :=\n  {poly_expanded(D['ED'], ['x', 'a'])}\n")
    L.append(f"/-- The cleared α-derivative `P_{i}(x, α, c) = -(N' E - N E D'/D + D E Λ'/Λ)`. -/\n"
             f"noncomputable def hh3C{i}P (x a c : ℝ) : ℝ :=\n  {horner_by(D['Pq'], ['x', 'a', 'c'], ['a', 'x', 'c'])}\n")
    L.append(f"/-- The numerator of the incoming-norm slope of `F_{i}` on the central path. -/\n"
             f"noncomputable def hh3C{i}S (x a : ℝ) : ℝ :=\n  {horner_by(D['snum'], ['x', 'a'], ['a', 'x'])}\n")
    if i == 0:
        L.append(f"""/-- `Λ = 2αZ/(3(5x + 12)K)`: numerator coefficients. -/
noncomputable def hh3CLs (x : ℝ) : List ℝ := [0, 2 * (15 * x ^ 2 + 11 * x), 2 * (40 * x + 36)]

/-- `Λ`: denominator coefficients. -/
noncomputable def hh3CLds (x : ℝ) : List ℝ := [3 * (5 * x + 12) * (x * (x + 2)), 0, 3 * (5 * x + 12)]

/-- `E = α(5α - 1)KZ`. -/
noncomputable def hh3CE (x a : ℝ) : ℝ :=
  a * (5 * a - 1) * (x * (x + 2) + a ^ 2) * (40 * a * x + 36 * a + 15 * x ^ 2 + 11 * x)

/-- `E Λ'/Λ`. -/
noncomputable def hh3CEL (x a : ℝ) : ℝ :=
  {poly_expanded(D['EL'], ['x', 'a'])}

theorem hh3_c_logarg (x t : ℝ) (hx : 0 < x) (ht : 0 < t) :
    2 * hsQc x t / hsRA t (hs3b x t) = hh3Hor (hh3CLs x) t / hh3Hor (hh3CLds x) t := by
  simp only [hh3CLs, hh3CLds, hh3Hor]
  unfold hsQc hsRA hs3b
  have h1 : 15 * x + 36 ≠ 0 := by positivity
  have h1x : x * 15 + 36 ≠ 0 := by positivity
  have h2 : x * (x + 2) + t ^ 2 ≠ 0 := by positivity
  have h3 : 3 * (5 * x + 12) * (x * (x + 2)) + t * (0 + t * (3 * (5 * x + 12) + t * 0)) ≠ 0 := by positivity
  have h4 : t * (15 * x + 36) + (x * (15 * x + 36) + 25 * x * (t - 1)) ≠ 0 := by nlinarith
  field_simp
  ring

theorem hh3_c_h2 (x t : ℝ) :
    (hh3HorD (hh3CLs x) t * hh3Hor (hh3CLds x) t - hh3Hor (hh3CLs x) t * hh3HorD (hh3CLds x) t) * hh3CE x t =
      hh3Hor (hh3CLs x) t * hh3Hor (hh3CLds x) t * hh3CEL x t := by
  simp only [hh3CLs, hh3CLds, hh3Hor, hh3HorD, hh3CE, hh3CEL]
  ring
""")
    L.append(f"""theorem hh3_c{i}_D (x t : ℝ) : hh3Hor (hh3C{i}Ds x) t = {DPROD[i]} := by
  simp only [hh3C{i}Ds, hh3Hor]
  ring

set_option maxRecDepth 20000 in
/-- **Clearing the central test** at fixed incoming norm `c`. -/
theorem hh3_c{i}_clear (x t c : ℝ) (hx : 1 < x) (ht : 1 < t) :
    hs3Fn x (hs3b x t) t c (hsQc x t) ({NSTR[i]}) 0 =
      hh3Hor (hh3C{i}Ns x c) t / hh3Hor (hh3C{i}Ds x) t := by
  rw [hh3_c{i}_D]
  simp only [hh3C{i}Ns, hh3Hor]
  unfold hs3Fn hsELs hsWs hsA1 hsA2 hsA3 hsE0 hsDg hsRA hs3b hsQc
  have h1 : 15 * x + 36 ≠ 0 := by positivity
  have h1x : x * 15 + 36 ≠ 0 := by positivity
  have h2 : x * (x + 2) + t ^ 2 ≠ 0 := by positivity
  have h3 : 5 * t - 1 ≠ 0 := by linarith
  have h3x : t * 5 - 1 ≠ 0 := by linarith
  have h5 : 5 * x + 12 ≠ 0 := by positivity
  have h6 : 40 * t * x + 36 * t + 15 * x ^ 2 + 11 * x ≠ 0 := by positivity
  have h7 : t * (15 * x + 36) + (x * (15 * x + 36) + 25 * x * (t - 1)) ≠ 0 := by nlinarith
  have h8 : 1 + x ≠ 0 := by positivity
  have h9 : t ≠ 0 := by positivity
  field_simp
  ring

set_option maxRecDepth 20000 in
theorem hh3_c{i}_h1 (x t : ℝ) :
    hh3HorD (hh3C{i}Ds x) t * hh3CE x t = hh3Hor (hh3C{i}Ds x) t * hh3C{i}ED x t := by
  simp only [hh3C{i}Ds, hh3Hor, hh3HorD, hh3CE, hh3C{i}ED]
  ring

set_option maxRecDepth 20000 in
theorem hh3_c{i}_Q (x t c : ℝ) :
    hh3HorD (hh3C{i}Ns x c) t * hh3CE x t - hh3Hor (hh3C{i}Ns x c) t * hh3C{i}ED x t +
      hh3Hor (hh3C{i}Ds x) t * hh3CEL x t = -hh3C{i}P x t c := by
  simp only [hh3C{i}Ns, hh3C{i}Ds, hh3Hor, hh3HorD, hh3CE, hh3C{i}ED, hh3CEL, hh3C{i}P]
  ring

set_option maxRecDepth 20000 in
theorem hh3_c{i}_P_aff (x t c : ℝ) :
    hh3C{i}P x t c = 20 * ((4 / 5 - c) * hh3C{i}P x t (3 / 4) + (c - 3 / 4) * hh3C{i}P x t (4 / 5)) := by
  unfold hh3C{i}P
  ring

set_option maxRecDepth 20000 in
/-- The incoming-norm slope of `F_{i}` on the central path, cleared. -/
theorem hh3_c{i}_slope_eq (x t : ℝ) (hx : 1 < x) (ht : 1 < t) :
    hh3Slope x (hs3b x t) t (hsQc x t) ({NSTR[i]}) =
      hh3C{i}S x t / ({SDEN[i]}) := by
  unfold hh3Slope hh3C{i}S hsDg hsRA hs3b hsQc
  have h1 : 15 * x + 36 ≠ 0 := by positivity
  have h1x : x * 15 + 36 ≠ 0 := by positivity
  have h2 : x * (x + 2) + t ^ 2 ≠ 0 := by positivity
  have h2' : t ^ 2 + x ^ 2 + 2 * x ≠ 0 := by positivity
  have h3 : 5 * t - 1 ≠ 0 := by linarith
  have h3x : t * 5 - 1 ≠ 0 := by linarith
  have h5 : 5 * x + 12 ≠ 0 := by positivity
  have h6 : 40 * t * x + 36 * t + 15 * x ^ 2 + 11 * x ≠ 0 := by positivity
  have h7 : t * (15 * x + 36) + (x * (15 * x + 36) + 25 * x * (t - 1)) ≠ 0 := by nlinarith
  have h9 : t ≠ 0 := by positivity
  field_simp
  ring
""")
    doc = f"""# Heavy leaf `hs3_central_alpha`: the cleared central test `F_{i}` at frozen incoming norm

Along the central boundary `β = b(x, α)`, `q = q_c(x, α)`, with the incoming norm frozen at a
constant `c`: `hh3_c{i}_clear` (`F_{i} - log(2q/r_A) = N/D`), `hh3_c_logarg` (`2q/r_A = Λ`),
`hh3_c{i}_h1`, `hh3_c_h2` (logarithmic derivatives of `D` and `Λ`), `hh3_c{i}_Q` (the cleared
α-derivative is `-P_{i}(x, α, c)`), `hh3_c{i}_P_aff` (affine in `c`) and `hh3_c{i}_slope_eq` (the
incoming-norm slope). Generated by `scripts/certificates/short-hand/hh3/hh3_central.py`.

## Main API

`hh3C{i}Ns`, `hh3C{i}Ds`, `hh3C{i}ED`, `hh3C{i}P`, `hh3C{i}S`{', `hh3CLs`, `hh3CLds`, `hh3CE`, `hh3CEL`' if i == 0 else ''}, and the identities above.
"""
    imp = "SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3Base" if i == 0 else \
        "SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3CentralA0"
    s = HEADER.format(imp=imp, doc=doc) + "\n" + "\n".join(L) + "\nend SmoothedOctagon\n"
    open(os.path.join(OUT, f'S3CentralA{i}.lean'), 'w').write(s)
    return len(s)


def pos_lemma(name, statement_fn, d, cert, hz_name='z'):
    pass


def emit_B(D, i):
    L = []
    zs = lnum(ZMAX)
    for tag, cv in (('lo', Fr(3, 4)), ('hi', Fr(4, 5))):
        key = [k for k in D['PL'] if Fr(int(k.p), int(k.q)) == cv][0]
        d = D['PL'][key]; ct = D['certs'][key]
        L.append(f"""set_option maxRecDepth 20000 in
theorem hh3_c{i}_P{tag}_hz (h z : ℝ) :
    hh3C{i}P (2 + h) (108 / 95 + z) {lnum(cv)} =
      {poly_expanded(d, ['h', 'z'])} := by
  unfold hh3C{i}P
  ring

set_option maxRecDepth 20000 in
theorem hh3_c{i}_P{tag}_pos {{x t : ℝ}} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ht : 108 / 95 ≤ t)
    (ht' : t ≤ 89 / 72) : 0 < hh3C{i}P x t {lnum(cv)} := by
  obtain ⟨h, rfl⟩ : ∃ h, x = 2 + h := ⟨x - 2, by ring⟩
  obtain ⟨z, rfl⟩ : ∃ z, t = 108 / 95 + z := ⟨t - 108 / 95, by ring⟩
  have h0 : 0 ≤ h := by linarith
  have h1 : h ≤ 1 / 6 := by linarith
  have v0 : 0 ≤ z := by linarith
  have v1 : z ≤ {zs} := by linarith
  rw [hh3_c{i}_P{tag}_hz]
""" + "\n".join(lean_cert(d, ct, hv=('h', 'z'))) + "\n")
    sd = D['sd']; sct = D['sct']
    L.append(f"""set_option maxRecDepth 20000 in
theorem hh3_c{i}_S_hz (h z : ℝ) :
    hh3C{i}S (2 + h) (108 / 95 + z) =
      {poly_expanded(sd, ['h', 'z'])} := by
  unfold hh3C{i}S
  ring

set_option maxRecDepth 20000 in
theorem hh3_c{i}_S_pos {{x t : ℝ}} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ht : 108 / 95 ≤ t)
    (ht' : t ≤ 89 / 72) : 0 < hh3C{i}S x t := by
  obtain ⟨h, rfl⟩ : ∃ h, x = 2 + h := ⟨x - 2, by ring⟩
  obtain ⟨z, rfl⟩ : ∃ z, t = 108 / 95 + z := ⟨t - 108 / 95, by ring⟩
  have h0 : 0 ≤ h := by linarith
  have h1 : h ≤ 1 / 6 := by linarith
  have v0 : 0 ≤ z := by linarith
  have v1 : z ≤ {zs} := by linarith
  rw [hh3_c{i}_S_hz]
""" + "\n".join(lean_cert(sd, sct, hv=('h', 'z'))) + "\n")
    doc = f"""# Heavy leaf `hs3_central_alpha`: certificates for the test `F_{i}`

`hh3_c{i}_Plo_pos`, `hh3_c{i}_Phi_pos`: the cleared α-derivative numerator `P_{i}(x, α, c)` is positive at
`c = 3/4` and `c = 4/5` on `[2, 13/6] × [108/95, 89/72]`; `hh3_c{i}_S_pos`: the incoming-norm slope
numerator is positive there. Each polynomial is expanded in `x = 2 + h`, `α = 108/95 + z` and bounded
below by its constant term minus all adverse terms at the corner `(1/6, 679/6840)`
(`linear_combination`). Generated by `scripts/certificates/short-hand/hh3/hh3_central.py`.

## Main API

`hh3_c{i}_Plo_pos`, `hh3_c{i}_Phi_pos`, `hh3_c{i}_S_pos`.
"""
    s = HEADER.format(imp=f"SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3CentralA{i}", doc=doc) + "\n" + "\n".join(L) + "\nend SmoothedOctagon\n"
    open(os.path.join(OUT, f'S3CentralB{i}.lean'), 'w').write(s)
    return len(s)


if __name__ == '__main__':
    pk = os.path.join(os.environ.get('HH3_CACHE', '/tmp'), 'hh3_central.pkl')
    if not os.path.exists(pk) or '--fresh' in sys.argv:
        import hh3_central_compute
        out = hh3_central_compute.compute()
        pickle.dump(out, open(pk, 'wb'))
    D = pickle.load(open(pk, 'rb'))
    for i in (0, 1):
        print('A', i, emit_A(D[i], i))
        print('B', i, emit_B(D[i], i))
