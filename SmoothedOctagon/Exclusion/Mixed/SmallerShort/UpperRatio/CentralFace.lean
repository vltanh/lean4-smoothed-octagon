module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Beta
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Ratio
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Terminal

/-!
# Smaller-short window, upper ratio: the central face

`ur_central_sign_proof` proves the statement of `ur_central_sign`: the duration tangent at
`t(a) = max(2, 20/3 - 4a)` (`urc_tangent`) bounds `G_τ` by the two tests `F₀`, `F₁`; both
increase in `β` up to `b_+(x, a)` (`urc_beta`), decrease in `x` along `β = b_+`
(`urc_xmono`), and are negative at `x = 13/6` (`urc_term`).

## Main API

* `ur_central_sign_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- **The central sharp-ratio face** (the statement of `ur_central_sign`). -/
theorem ur_central_sign_proof {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ * ssQc x al ≤ ssRA al be) :
    ssF x be al (ssUC x be) (ssQc x al) τ (log (τ * ssQc x al / ssRA al be))
      (2 - 7 * τ * ssQc x al / (4 * ssRA al be)) < 0 := by
  obtain ⟨hal', hxb, hbp⟩ := urc_strip hx hx2 hal hqc hb hb'
  have hal0 : 0 < al := by linarith
  have hx0 : 0 < x := by linarith
  have hB : 0 < al + be := by linarith
  have hK : 0 < urcK x al := by unfold urcK; positivity
  have hk : 0 < urck x al be := by unfold urck; positivity
  have hkq : ssQc x al / ssRA al be = urck x al be := by
    unfold ssQc ssRA urck urcK; field_simp
  have hτk : τ * urck x al be ≤ 1 := by
    have hrA : 0 < ssRA al be := by unfold ssRA; positivity
    rw [← hkq, mul_div_assoc', div_le_one hrA]
    exact hτT
  set t := max 2 (20 / 3 - 4 * al) with htdef
  have ht : 2 ≤ t := le_max_left _ _
  have ht2 : t ≤ 8 / 3 := max_le (by norm_num) (by linarith)
  rw [urc_face hal0 hB hx0]
  refine lt_of_le_of_lt (urc_tangent (t := t) hk ht hτ hτk) (max_lt ?_ ?_)
  · have h1 := (urc_beta hx hx2 hal hal' ht hxb hbp le_rfl).1
    have h2 := (urc_xmono hx hx2 hal hal' ht ht2).1
    have h3 := (urc_term hal hal').1
    rw [← htdef] at h3
    have e : urcF0 t x al be (ssUC x be) = urcR x al be (ssUC x be) +
        (4 - 7 * urck x al be / 2) * (urcw x al be (ssUC x be) - 3 / 4) + 4 / t - 2 / t ^ 2 -
        3 / 2 + log (t * urck x al be) := rfl
    rw [← e]
    linarith
  · have h1 := (urc_beta hx hx2 hal hal' ht hxb hbp le_rfl).2
    have h2 := (urc_xmono hx hx2 hal hal' ht ht2).2
    have h3 := (urc_term hal hal').2
    rw [← htdef] at h3
    have e : urcF1 t x al be (ssUC x be) = urcR x al be (ssUC x be) +
        (1 / urck x al be + 1 / 4) * (urcw x al be (ssUC x be) - 3 / 4) +
        1 / urck x al be * ((t - 1) / t ^ 2 - 1 / 4) + 2 / t - 1 + log (t * urck x al be) := rfl
    rw [← e]
    linarith

end SmoothedOctagon
