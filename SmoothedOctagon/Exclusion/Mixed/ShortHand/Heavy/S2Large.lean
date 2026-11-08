module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2Face
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2LargeCertA
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2LargeCertB

/-!
# S2 heavy face signs: the outer face for large `α`

`hs2_outer_sign_large_proof` proves the statement of `hs2_outer_sign_large`
(`OUTER_RATIO_HAND_SIGN` §6, (17)-(18); inventory HS-S2 R24): for `13/6 ≤ x ≤ 12/5`,
`3/2 ≤ α ≤ x`, `β` in the strip, `q = 1/7`, `u = V̄(x)` and `2 ≤ τ ≤ 7r_A`, `G_τ < 0`.

Proof: `hh2_hsF_face` and `hh2_tau_outer` reduce to `H₀ = G₂ < 0` and
`H₁ = G₂ + (T - 2)A < 0`; the log majorant `hh2_log_le_bound` makes both rational; in the strip
coordinate `c = (β - x)/(α - 1) ∈ [5/8, 7/8]` (the enlarged set (17), with `α ≤ 12/5`) their
cleared numerators are the certificate polynomials `hh2LgA`, `hh2LgB` (`Heavy/S2LargeCertA`, `-B`).

Route: the notes' Bernstein expansion in `α` with coefficient-norm bounds in `(x, c)` is replaced
by a nested Bernstein certificate in `(c, α, x)` on the whole box (no subdivision).

## Main API

* `hh2_strip_c`: the strip coordinate `c`.
* `hh2_large_H0`, `hh2_large_H1`: the two duration-free signs.
* `hs2_outer_sign_large_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- The strip coordinate: `β = x + c(α - 1)` with `5/8 ≤ c ≤ 7/8` (`OUTER_RATIO_HAND_SIGN` (7)-(8)). -/
theorem hh2_strip_c {x al be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 < al)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ∃ c : ℝ, 5 / 8 ≤ c ∧ c ≤ 7 / 8 ∧ be = x + c * (al - 1) := by
  have ha : 0 < al - 1 := by linarith
  refine ⟨(be - x) / (al - 1), ?_, ?_, ?_⟩
  · rw [le_div_iff₀ ha]
    have h1 : 5 / 8 * (al - 1) ≤ 8 * x * (al - 1) / (9 * x + 8) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  · rw [div_le_iff₀ ha]
    have h1 : x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ 7 / 8 * (al - 1) := by
      rw [div_le_iff₀ (by positivity)]
      have hq : 0 ≤ 7 * (4 * x ^ 2 + 11 * x + 1) - 8 * x * (7 * x + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx2)]
      nlinarith [mul_nonneg ha.le hq]
    linarith
  · field_simp
    ring

/-- The large outer face: `H₀ = G₂ < 0` for any `ℓ` below the log majorant (`hh2LgA_pos`). -/
theorem hh2_large_H0 {x al c be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 3 / 2 ≤ al)
    (hal' : al ≤ 12 / 5) (hc1 : 5 / 8 ≤ c) (hc2 : c ≤ 7 / 8) (hbe : be = x + c * (al - 1))
    (ℓ : ℝ) (hℓ : ℓ ≤ (-296 / 1029 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) - (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 3 / 3)) :
    (hsWs x be al (hsVbar x) (1 / 7) - 1) * 2 + 1 / 2 + ((hsVbar x - 1) / hsRA al be + hsRA al be + 1 - 1 / 7 - hsELs x be al (hsVbar x) (1 / 7)) + ℓ + (2 - 7 * 2 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsVbar x) (1 / 7) - 3 / 4) < 0 := by
  calc _ ≤ (hsWs x be al (hsVbar x) (1 / 7) - 1) * 2 + 1 / 2 + ((hsVbar x - 1) / hsRA al be + hsRA al be + 1 - 1 / 7 - hsELs x be al (hsVbar x) (1 / 7)) + (-296 / 1029 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) - (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 3 / 3) + (2 - 7 * 2 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsVbar x) (1 / 7) - 3 / 4) := by gcongr
    _ < 0 := by
      subst hbe
      have hP := hh2LgA_pos c al x hc1 hc2 hal hal' hx hx2
      have hal0 : 0 < al := by linarith
      have hB : 0 < al * c + al - c + x := by nlinarith
      have hden : 0 < 222264 * al ^ 5 * (x + 1) * (35 * x + 13) * (al * c + al - c + x) := by positivity
      refine hh2_neg_of_mul hden hP ?_
      rw [hh2_Ws_outer _ _ _ _ hal0.ne' (by positivity), hh2_ELs_outer _ _ _ _ hal0.ne' (by positivity)]
      have hB' : al + (x + c * (al - 1)) ≠ 0 := by nlinarith
      have hS : x + 1 ≠ 0 := by positivity
      have hV : 35 * x + 13 ≠ 0 := by positivity
      have hS' : 1 + x ≠ 0 := by positivity
      unfold hsVbar hsRA hsDg hh2LgA
      unfold hh2LgA_d0_0 hh2LgA_d0_1 hh2LgA_d0_2 hh2LgA_d0_3 hh2LgA_d0_4 hh2LgA_d0_5 hh2LgA_d0_6 hh2LgA_d1_0 hh2LgA_d1_1 hh2LgA_d1_2 hh2LgA_d1_3 hh2LgA_d1_4 hh2LgA_d1_5 hh2LgA_d1_6 hh2LgA_d2_0 hh2LgA_d2_1 hh2LgA_d2_2 hh2LgA_d2_3 hh2LgA_d2_4 hh2LgA_d2_5 hh2LgA_d2_6 hh2LgA_d3_0 hh2LgA_d3_1 hh2LgA_d3_2 hh2LgA_d3_3 hh2LgA_d3_4 hh2LgA_d3_5 hh2LgA_d3_6 hh2LgA_d4_0 hh2LgA_d4_1 hh2LgA_d4_2 hh2LgA_d4_3 hh2LgA_d4_4 hh2LgA_d4_5 hh2LgA_d4_6
      field_simp
      ring

/-- The large outer face: `H₁ = G₂ + (T - 2)A < 0` for any `ℓ` below the log majorant
(`hh2LgB_pos`). -/
theorem hh2_large_H1 {x al c be : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 3 / 2 ≤ al)
    (hal' : al ≤ 12 / 5) (hc1 : 5 / 8 ≤ c) (hc2 : c ≤ 7 / 8) (hbe : be = x + c * (al - 1))
    (ℓ : ℝ) (hℓ : ℓ ≤ (-296 / 1029 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) - (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 3 / 3)) :
    (hsWs x be al (hsVbar x) (1 / 7) - 1) * 2 + 1 / 2 + ((hsVbar x - 1) / hsRA al be + hsRA al be + 1 - 1 / 7 - hsELs x be al (hsVbar x) (1 / 7)) + ℓ + (2 - 7 * 2 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsVbar x) (1 / 7) - 3 / 4) +
      (1 / (1 / 7 / hsRA al be) - 2) * ((1 - 7 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsVbar x) (1 / 7) - 3 / 4)) < 0 := by
  calc _ ≤ (hsWs x be al (hsVbar x) (1 / 7) - 1) * 2 + 1 / 2 + ((hsVbar x - 1) / hsRA al be + hsRA al be + 1 - 1 / 7 - hsELs x be al (hsVbar x) (1 / 7)) + (-296 / 1029 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) - (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 2 / 2 + (4 * (2 * (1 / 7 / hsRA al be)) / 3 - 1) ^ 3 / 3) + (2 - 7 * 2 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsVbar x) (1 / 7) - 3 / 4) +
      (1 / (1 / 7 / hsRA al be) - 2) * ((1 - 7 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al (hsVbar x) (1 / 7) - 3 / 4)) := by gcongr
    _ < 0 := by
      subst hbe
      have hP := hh2LgB_pos c al x hc1 hc2 hal hal' hx hx2
      have hal0 : 0 < al := by linarith
      have hB : 0 < al * c + al - c + x := by nlinarith
      have hden : 0 < 444528 * al ^ 4 * (x + 1) * (35 * x + 13) * (al * c + al - c + x) := by positivity
      refine hh2_neg_of_mul hden hP ?_
      rw [hh2_Ws_outer _ _ _ _ hal0.ne' (by positivity), hh2_ELs_outer _ _ _ _ hal0.ne' (by positivity)]
      have hB' : al + (x + c * (al - 1)) ≠ 0 := by nlinarith
      have hS : x + 1 ≠ 0 := by positivity
      have hV : 35 * x + 13 ≠ 0 := by positivity
      have hS' : 1 + x ≠ 0 := by positivity
      unfold hsVbar hsRA hsDg hh2LgB
      unfold hh2LgB_d0_0 hh2LgB_d0_1 hh2LgB_d0_2 hh2LgB_d0_3 hh2LgB_d0_4 hh2LgB_d0_5 hh2LgB_d1_0 hh2LgB_d1_1 hh2LgB_d1_2 hh2LgB_d1_3 hh2LgB_d1_4 hh2LgB_d1_5 hh2LgB_d2_0 hh2LgB_d2_1 hh2LgB_d2_2 hh2LgB_d2_3 hh2LgB_d2_4 hh2LgB_d2_5 hh2LgB_d3_0 hh2LgB_d3_1 hh2LgB_d3_2 hh2LgB_d3_3 hh2LgB_d3_4 hh2LgB_d3_5 hh2LgB_d4_1 hh2LgB_d4_2 hh2LgB_d4_3 hh2LgB_d4_4 hh2LgB_d4_5
      field_simp
      ring

/-- **The outer sharp-ratio face, large `α`** (`hs2_outer_sign_large`). -/
theorem hs2_outer_sign_large_proof {x al be τ : ℝ} (hx : 13 / 6 ≤ x) (hx2 : x ≤ 12 / 5)
    (hal : 3 / 2 ≤ al) (hax : al ≤ x) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    hsF x be al (hsVbar x) (1 / 7) τ (log (τ * (1 / 7) / hsRA al be))
      (2 - 7 * τ * (1 / 7) / (4 * hsRA al be)) < 0 := by
  obtain ⟨c, hc1, hc2, hbe⟩ := hh2_strip_c hx hx2 (by linarith) hb hb'
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
  · exact hh2_large_H0 hx hx2 hal (by linarith) hc1 hc2 hbe _ hl
  · exact hh2_large_H1 hx hx2 hal (by linarith) hc1 hc2 hbe _ hl

end SmoothedOctagon
