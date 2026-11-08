module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CSteps
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CUni

/-!
# Gate S1: the central low-ratio face

`hs1_central_face_proof` proves the heavy leaf `hs1_central_face`
(`LOW_RATIO_CENTRAL_HAND_SIGN` (6); inventory HS-S01 D-R15): on the central face `q = q_c ≤ 1/7`
the corrected envelope exceeds `9193/50000` for every duration `τ ∈ [2, T]`.

Proof: the duration reduction `hh1c_face_red` leaves the two tests `F₀`, `F₁`
(D-R6, D-R7). For `F₀`: raise `u` to `u_ℓ(x, β)` (`hh1c_stepU0`), `β` to `x + (10/13)(α - 1)` along
the ceiling (`hh1c_stepB0`), `α` to `a_U(x) ≥ α` (`hh1c_stepA0`, D-R9 (ii)), and conclude by the
one-variable sign `hh1c_uni_h0`. For `F₁`: raise `u` to `V̄(x) ≥ u_ℓ` (`hh1c_stepU1`), `β` at fixed
norm (`hh1c_stepB1`), `x` to `2` at fixed `α` (`hh1c_stepX1`), and conclude by `hh1c_uni_k1`.
Route: the notes eliminate `α` in `F₁` by concavity and keep the β-dependent norm; here `F₁` uses the
β-independent ceiling `V̄` and the `x`-monotonicity instead (all derivative signs are generated
termwise certificates, `S1CClaim*`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The central low-ratio face** (`LOW_RATIO_CENTRAL_HAND_SIGN` (6); inventory HS-S01 D-R15): for
`1 < x ≤ 2`, `1 ≤ α`, `6α² ≤ x(x + 2)` (`q_c ≤ 1/7`), the strip
`x + 8x(α - 1)/(9x + 8) ≤ β ≤ x + x(7x + 1)(α - 1)/(4x² + 11x + 1)`, `3/4 ≤ u ≤ u_ℓ(x, β)` and
every `τ ∈ [2, T]`, `T = r_A/q_c`: `Γ_*(q_c) - (7/96)R*_τ(q_c) > 9193/50000`. -/
theorem hs1_central_face_proof {x al be u τ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hqc : 6 * al ^ 2 ≤ x * (x + 2)) (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hu : 3 / 4 ≤ u)
    (hul : u ≤ hsUl x be) (hτ : 2 ≤ τ) (hτT : τ * hsQc x al ≤ hsRA al be) :
    9193 / 50000 < hsGs x al u (hsQc x al) - 7 / 96 * hsRs x be al u (hsQc x al) τ := by
  have hx6 : 6 ≤ x * (x + 2) := by nlinarith
  have hx0 : 329 / 200 ≤ x := by nlinarith
  have hx85 : 8 / 5 ≤ x := by linarith
  have haU : al ≤ (1013 * x + 676) / 2340 := by
    have h1 : al ^ 2 ≤ ((1013 * x + 676) / 2340) ^ 2 := by nlinarith [sq_nonneg (337 * x - 676)]
    have h2 : 0 ≤ (1013 * x + 676) / 2340 := by positivity
    nlinarith [sq_nonneg (al - (1013 * x + 676) / 2340), sq_nonneg (al + (1013 * x + 676) / 2340)]
  have ha76 : al ≤ 7 / 6 := by linarith
  have ha1351 : al ≤ 1351 / 1170 := by linarith
  have hal1 : 0 ≤ al - 1 := by linarith
  have hbe0 : x + 1 / 2 * (al - 1) ≤ be := by
    have : 1 / 2 * (al - 1) ≤ 8 * x * (al - 1) / (9 * x + 8) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hbe1 : be ≤ x + 10 / 13 * (al - 1) := by
    have : x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ 10 / 13 * (al - 1) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hal1 (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 - x) (by linarith : (0 : ℝ) ≤ 51 * x + 5))]
    linarith
  have hxbe : x ≤ be := by nlinarith
  have hβ1 : x + 10 / 13 * (al - 1) ≤ x + 4 / 5 * (al - 1) := by nlinarith
  have hβ0 : x + 1 / 2 * (al - 1) ≤ x + 10 / 13 * (al - 1) := by nlinarith
  have hred := hh1c_face_red (u := u) (by linarith) hal (by linarith) hτ hτT
  suffices h : 0 < hh1cF0 x al be u ∧ 0 < hh1cF1 x al be u by
    have := lt_min h.1 h.2
    linarith
  constructor
  · have h1 := hh1c_stepU0 hx85 hx2 hal ha76 hbe0 (by linarith) hu hul
    have h2 := hh1c_stepB0 hx85 hx2 hal ha76 hbe0 hbe1 hβ1
    have h3 := hh1c_stepA0 hx0 hx2 hal haU le_rfl
    have h4 := hh1c_uni_h0 hx0 hx2 rfl rfl rfl
    linarith
  · have hV := (hh1_Ul_le_Vbar hx hxbe)
    obtain ⟨hV0, hV1⟩ := hh1_Vbar_bounds hx hx2
    have h1 := hh1c_stepU1 hx85 hx2 hal ha76 hbe0 (by linarith) hu (hul.trans hV)
    have h2 := hh1c_stepB1 hx85 hx2 hal ha76 hbe0 hbe1 hβ1 hV0 hV1
    have h3 := hh1c_stepX1 hx85 hx2 le_rfl hal ha76
    have h4 := hh1c_uni_k1 hal ha1351 rfl rfl
    linarith

end SmoothedOctagon
