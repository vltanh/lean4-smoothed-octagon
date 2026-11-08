module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenBeta
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenX
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenTerm

/-!
# S2 hand signs: the central face

`hs2_central_sign_proof` proves the statement of `hs2_central_sign`: the duration tangent at
`t(a) = max(2, 20/3 - 4a)` (`hl2c_tangent`) bounds `G_τ` by the two tests `F₀`, `F₁`; both
increase in `β` up to `b_+(x, a)` (`hl2c_beta`), decrease in `x` along `β = b_+`
(`hl2c_xmono`), and are negative at `x = 13/6` (`hl2c_term`).

## Main API

* `hs2_central_sign_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- **The central sharp-ratio face** (the statement of `hs2_central_sign`). -/
theorem hs2_central_sign_proof {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ * hsQc x al ≤ hsRA al be) :
    hsF x be al (hsUC x be) (hsQc x al) τ (log (τ * hsQc x al / hsRA al be))
      (2 - 7 * τ * hsQc x al / (4 * hsRA al be)) < 0 := by
  obtain ⟨hal', hxb, hbp⟩ := hl2c_strip hx hx2 hal hqc hb hb'
  have hal0 : 0 < al := by linarith
  have hx0 : 0 < x := by linarith
  have hB : 0 < al + be := by linarith
  have hK : 0 < hl2cK x al := by unfold hl2cK; positivity
  have hk : 0 < hl2ck x al be := by unfold hl2ck; positivity
  have hkq : hsQc x al / hsRA al be = hl2ck x al be := by
    unfold hsQc hsRA hl2ck hl2cK; field_simp
  have hτk : τ * hl2ck x al be ≤ 1 := by
    have hrA : 0 < hsRA al be := by unfold hsRA; positivity
    rw [← hkq, mul_div_assoc', div_le_one hrA]
    exact hτT
  set t := max 2 (20 / 3 - 4 * al) with htdef
  have ht : 2 ≤ t := le_max_left _ _
  have ht2 : t ≤ 8 / 3 := max_le (by norm_num) (by linarith)
  rw [hl2c_face hal0 hB hx0]
  refine lt_of_le_of_lt (hl2c_tangent (t := t) hk ht hτ hτk) (max_lt ?_ ?_)
  · have h1 := (hl2c_beta hx hx2 hal hal' ht hxb hbp le_rfl).1
    have h2 := (hl2c_xmono hx hx2 hal hal' ht ht2).1
    have h3 := (hl2c_term hal hal').1
    rw [← htdef] at h3
    have e : hl2cF0 t x al be (hsUC x be) = hl2cR x al be (hsUC x be) +
        (4 - 7 * hl2ck x al be / 2) * (hl2cw x al be (hsUC x be) - 3 / 4) + 4 / t - 2 / t ^ 2 -
        3 / 2 + log (t * hl2ck x al be) := rfl
    rw [← e]
    linarith
  · have h1 := (hl2c_beta hx hx2 hal hal' ht hxb hbp le_rfl).2
    have h2 := (hl2c_xmono hx hx2 hal hal' ht ht2).2
    have h3 := (hl2c_term hal hal').2
    rw [← htdef] at h3
    have e : hl2cF1 t x al be (hsUC x be) = hl2cR x al be (hsUC x be) +
        (1 / hl2ck x al be + 1 / 4) * (hl2cw x al be (hsUC x be) - 3 / 4) +
        1 / hl2ck x al be * ((t - 1) / t ^ 2 - 1 / 4) + 2 / t - 1 + log (t * hl2ck x al be) := rfl
    rw [← e]
    linarith

end SmoothedOctagon
