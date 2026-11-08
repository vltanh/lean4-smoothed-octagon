"""Writes Heavy/S2Small.lean (link identities and hs2_outer_sign_small_proof); run after gen_small.py."""
import re, os
from common import OUT
from gen_small_stage import stage1, templates, atoms_sub, ABS, CON, UdL, UnL, KAPPA
ST = stage1()
G2abs, H1abs = templates('S', 'D', 'B', 'a', 'u')
P = {nm: (atoms_sub(ST[nm][0], **ABS), atoms_sub(ST[nm][1], **ABS)) for nm in ST}
def dnames(f,X):
    return re.findall(r'^noncomputable def ('+X+r'_d[0-9_]+)', open(os.path.join(OUT,f)).read(), re.M)
dA=" ".join(dnames('S2SmallShift.lean','hh2SmQA')); dB=" ".join(dnames('S2SmallShift.lean','hh2SmQB'))
u="hsUs x be"
W=f"hsWs x be al ({u}) (1 / 7)"
EL=f"hsELs x be al ({u}) (1 / 7)"
rA="hsRA al be"
k=f"(1 / 7 / {rA})"
cc=f"(({u} - 1) / {rA} + {rA} + 1 - 1 / 7 - {EL})"
def G2(l): return f"({W} - 1) * 2 + 1 / 2 + {cc} + {l} + (2 - 7 * 2 * {k} / 4) * ({W} - 3 / 4)"
A=f"((1 - 7 * {k} / 4) * ({W} - 3 / 4))"
def H1(l): return f"{G2(l)} +\n      (1 / {k} - 2) * {A}"
LB=f"(-296 / 1029 + (4 * (2 * {k}) / 3 - 1) - (4 * (2 * {k}) / 3 - 1) ^ 2 / 2 + (4 * (2 * {k}) / 3 - 1) ^ 3 / 3)"
hyps="""{x al c be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : (36 * x + 25) / 84 ≤ al)
    (hal' : al ≤ 3 / 2) (hc1 : 5 / 8 ≤ c) (hc2 : c ≤ (24 * x + 51) / 128) (hbe : be = x + c * (al - 1))
    (ℓ : ℝ) (hℓ : ℓ ≤ """+LB+")"
def proof(X,dn,den,expr_l,nm):
    kap,num=KAPPA[nm]
    return f"""  calc _ ≤ {expr_l} := by gcongr
    _ < 0 := by
      have hP := {X}_pos c al x hx hx2 hal hal' hc1 hc2
      have hal0 : 0 < al := by linarith
      have hbe1 : 0 < be - 1 := by
        rw [hbe]
        have : 0 ≤ c * (al - 1) := mul_nonneg (by linarith) (by linarith)
        linarith
      have hB : 0 < al + be := by linarith
      have hS : (0 : ℝ) < 1 + x := by linarith
      rw [hh2_Ws_outer _ _ _ _ hal0.ne' hS.ne', hh2_ELs_outer _ _ _ _ hal0.ne' hS.ne']
      unfold hsRA
      exact hh2_combine1 (M := al ^ 5 * (al + be) * (1 + x)) (Ud := {UdL}) (by positivity) (by positivity)
        (hh2_sm_stage1_{nm} (1 + x) (hsDg x be al) (al + be) al (hsUs x be) hS.ne' hal0.ne' hB.ne')
        (hh2_sm_us x be hS.ne' hbe1.ne') (hh2_sm_stage2_{nm} x al c be hbe)
        (by have : 0 < {kap} * {X} c al x := by positivity
            linarith)
"""
txt=f'''module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2Face
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2SmallLinkA
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2SmallLinkB

/-!
# S2 heavy face signs: the outer face for small `α`

`hs2_outer_sign_small_proof` proves the statement of `hs2_outer_sign_small`
(`OUTER_RATIO_HAND_SIGN` §§4-5, (13), (16); inventory HS-S2 R24): for `13/6 ≤ x ≤ 12/5`,
`1 ≤ α ≤ 3/2`, `α ≤ x`, `x(x + 2) ≤ 6α²`, `β` in the strip, `q = 1/7`, `u = u_s(x, β)` and
`2 ≤ τ ≤ 7r_A`, `G_τ < 0`.

Proof: `hh2_hsF_face` and `hh2_tau_outer` reduce to `H₀ = G₂ < 0` and
`H₁ = G₂ + (T - 2)A < 0`; the log majorant `hh2_log_le_bound` makes both rational; on the enlarged
set `α ≥ a_f(x) = (36x + 25)/84` (`OUTER_RATIO_HAND_SIGN` (7)) and
`5/8 ≤ c ≤ c₊(x) = (24x + 51)/128` (`CENTRAL_RATIO_HAND_SIGN` (6)), `c = (β - x)/(α - 1)`, their
cleared numerators are `hh2SmQA`, `hh2SmQB`, positive by `Heavy/S2SmallShift`.

Denominators are cleared in two stages: `hh2_sm_stage1_*` (the face in abstract atoms) and
`hh2_sm_stage2_*` (`Heavy/S2SmallLinkA`, `-B`: the expansion of the atom polynomials).

Route: the notes' monotonicities in `α` (App. A, `A₀`, `A₁`) and `c` (`C₀`, `C₁`) and the terminal
univariate signs (App. B) are replaced by nested Bernstein certificates in `(c, s, x)`,
`s = α - a_f(x)`, on two `x`-boxes (`H₀`) and one box (`H₁`).

## Main API

* `hh2_af_le`, `hh2_strip_cplus`: the enlarged coordinates.
* `hh2_small_H0`, `hh2_small_H1`: the two duration-free signs.
* `hs2_outer_sign_small_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `a_f(x) = (36x + 25)/84 ≤ α` when `x(x + 2) ≤ 6α²` (`OUTER_RATIO_HAND_SIGN` (7):
`84²x(x + 2) - 6(36x + 25)² = -720x² + 3312x - 3750 > 0` on `[13/6, 12/5]`). -/
theorem hh2_af_le {{x al : ℝ}} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : x * (x + 2) ≤ 6 * al ^ 2) : (36 * x + 25) / 84 ≤ al := by
  have h1 : 6 * ((36 * x + 25) / 84) ^ 2 ≤ x * (x + 2) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
  have h2 : ((36 * x + 25) / 84) ^ 2 ≤ al ^ 2 := by linarith
  have h3 : 0 ≤ (36 * x + 25) / 84 := by positivity
  nlinarith [sq_nonneg ((36 * x + 25) / 84 - al), sq_nonneg ((36 * x + 25) / 84 + al)]

/-- The strip coordinate with the upper end `c₊(x) = (24x + 51)/128` (`CENTRAL_RATIO_HAND_SIGN` (6):
`96x³ - 428x² + 457x + 51 > 0`). -/
theorem hh2_strip_cplus {{x al be : ℝ}} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 < al)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ∃ c : ℝ, 5 / 8 ≤ c ∧ c ≤ (24 * x + 51) / 128 ∧ be = x + c * (al - 1) := by
  have ha : 0 < al - 1 := by linarith
  refine ⟨(be - x) / (al - 1), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ ha]
    have h1 : 5 / 8 * (al - 1) ≤ 8 * x * (al - 1) / (9 * x + 8) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  · rw [div_le_iff₀ ha]
    have h1 : x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ (24 * x + 51) / 128 * (al - 1) := by
      rw [div_le_iff₀ (by positivity)]
      have hq : 0 ≤ (24 * x + 51) * (4 * x ^ 2 + 11 * x + 1) - 128 * x * (7 * x + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2), sq_nonneg (x - 9 / 4),
          mul_nonneg (mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx)) (sub_nonneg.2 hx)]
      nlinarith [mul_nonneg ha.le hq]
    linarith
  · field_simp
    ring

/-- **Stage 1 for `H₀`** (abstract atoms `S, D, B, α, u`): `H₀ · α⁵BS = Π₀ + uΠ₁`. -/
theorem hh2_sm_stage1_H0 (S D B a u : ℝ) (hS : S ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) :
    ({G2abs}) * (a ^ 5 * B * S) =
      {P['H0'][0]} + u * ({P['H0'][1]}) := by
  field_simp
  ring

/-- **Stage 1 for `H₁`**: `H₁ · α⁵BS = Π₀ + uΠ₁`. -/
theorem hh2_sm_stage1_H1 (S D B a u : ℝ) (hS : S ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) :
    ({H1abs}) * (a ^ 5 * B * S) =
      {P['H1'][0]} + u * ({P['H1'][1]}) := by
  field_simp
  ring

/-- `u_s · U_d = U_n`. -/
theorem hh2_sm_us (x be : ℝ) (hS : 1 + x ≠ 0) (hb : be - 1 ≠ 0) :
    hsUs x be * {UdL} = {UnL} := by
  unfold hsUs
  field_simp
  ring

/-- **Recombination**: `E · M = Π₀ + uΠ₁`, `uU_d = U_n` and `Π₀U_d + Π₁U_n = R < 0` give `E < 0`. -/
theorem hh2_combine1 {{E M Ud u Un P0 P1 R : ℝ}} (hM : 0 < M) (hUd : 0 < Ud)
    (hG : E * M = P0 + u * P1) (hu : u * Ud = Un) (h2 : P0 * Ud + P1 * Un = R) (hR : R < 0) : E < 0 := by
  have key : E * (M * Ud) = -(-R) := by linear_combination Ud * hG + P1 * hu + h2
  exact hh2_neg_of_mul (by positivity) (by linarith) key

/-- The small outer face: `H₀ = G₂ < 0` for any `ℓ` below the log majorant (`hh2SmQA_pos`). -/
theorem hh2_small_H0 {hyps} :
    {G2("ℓ")} < 0 := by
{proof("hh2SmQA",dA,"",G2(LB),"H0")}
/-- The small outer face: `H₁ = G₂ + (T - 2)A < 0` for any `ℓ` below the log majorant
(`hh2SmQB_pos`). -/
theorem hh2_small_H1 {hyps} :
    {H1("ℓ")} < 0 := by
{proof("hh2SmQB",dB,"",H1(LB),"H1")}
/-- **The outer sharp-ratio face, small `α`** (`hs2_outer_sign_small`). -/
theorem hs2_outer_sign_small_proof {{x al be τ : ℝ}} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hal' : al ≤ 3 / 2) (_hax : al ≤ x) (hqc : x * (x + 2) ≤ 6 * al ^ 2)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    hsF x be al (hsUs x be) (1 / 7) τ (log (τ * (1 / 7) / hsRA al be))
      (2 - 7 * τ * (1 / 7) / (4 * hsRA al be)) < 0 := by
  have haf := hh2_af_le hx hx2 hal hqc
  obtain ⟨c, hc1, hc2, hbe⟩ := hh2_strip_cplus hx hx2 (by linarith) hb hb'
  have hal0 : 0 < al := by linarith
  have hB : 0 < al + be := by rw [hbe]; nlinarith
  have hrA : 0 < hsRA al be := by unfold hsRA; positivity
  have hk : 0 < 1 / 7 / hsRA al be := by positivity
  have hτk : τ * (1 / 7 / hsRA al be) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hrA]
    linarith
  rw [hh2_hsF_face]
  have hl := hh2_log_le_bound (y := 2 * (1 / 7 / hsRA al be)) (by positivity)
  refine lt_of_le_of_lt (hh2_tau_outer hk hτ hτk) (max_lt ?_ ?_)
  · exact hh2_small_H0 hx hx2 haf hal' hc1 hc2 hbe _ hl
  · exact hh2_small_H1 hx hx2 haf hal' hc1 hc2 hbe _ hl

end SmoothedOctagon
'''
open(os.path.join(OUT,'S2Small.lean'),'w').write(txt)
print('S2Small.lean',len(txt))
