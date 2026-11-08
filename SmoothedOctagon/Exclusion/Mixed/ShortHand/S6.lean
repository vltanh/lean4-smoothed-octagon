module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs6.Angle
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs6.Concave
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs6.Shear
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S6Defs
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Hand

/-!
# Hand proof of the smaller-short case, gate S6: the completion cost is too large

`MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION` (1)-(31), with `SHEAR_COST_REDUCTION`,
`ROOT_AND_ANGLE_REDUCTION` §§3-5, `SCALE_ANGLE_BARRIER` §§4-5, `CENTRAL_COST_SHAPE_BOUNDS`;
inventory HS-S567 Part III (SH.1-SH.5, AC.1, AB1, AB2, AL, CS.1-CS.3, SB.1-SB.3, S6.1-S6.8), on its
recommended route (no critical-angle classification; the barrier is applied pointwise along the
continuation in the angle `δ`). On the small-shape domain with `Γ > 1829/10000`, `h < 0`,
`-hR > 5A/2`: the window cost plus completion `C_br + (κ + 3/2)(π/3 - θ_br)` is at least the
central-scale score `𝓕_c` (`HsData.hs6_continuation`), `𝓕_c > cπ/3 + √3𝓑(u_q) - 1/800000`
(`hs6_Fc_gt`), `𝓑(u_q) > b*` (`hs6_B_concave`, `hs6_B_endpoint`, heavy), and the constants
(`hs6_constants`) give `> A_oct`, contradicting the window defect.

## Main API

* Central-scale objects: `hs6J0`, `hs6K`, `hs6psi`, `hs6Z`, `hs6omega`, `hs6Cc`, `hs6Fc`; the
  polynomial bound `hs6B` with `hs6uq`, `hs6ZU`, `hs6ZL`, `hs6T`, `hs6L`; `hs6bstar`.
* Stable scalar leaves: `hs6_kappa`, `hs6_shape`, `hs6_u_bounds`, `hs6_central_shear`,
  `hs6_tangent_inv`, `hs6_tangent_anti`, `hs6_score_deriv`, `hs6_barrier_sin`, `hs6_barrier`,
  `hs6_Fc_gt`, `hs6_T_eq`, `hs6_B_concave`, `hs6_constants`.
* Stable actual-data leaves: `HsData.hs6_angle` (AL), `HsData.hs6_continuation` (S6.2).
* Heavy: `hs6_B_endpoint` (`SMALL_SHAPE_COST_EXCLUSION` (20)-(31)), proved by hand in
  `Heavy/S6Hand*` (`archive/lighter-proofs/SHORT_COST_CONCAVITY.md`).
* Gate: `HsData.s6`, `M2Short.hs_S6`.
* Helper modules: `Hs6.Angle` (the rotated trace identity, AB1-AB2), `Hs6.Concave` (concavity of
  `𝓑` in `T`, S6.5), `Hs6.Shear` (the central shear bounds, CS.3).
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real Certificates.SmallerShort

/-! ### Scalar leaves -/

/-- **Lowering `κ`** (`SMALL_SHAPE_COST_EXCLUSION` §2; inventory HS-S567 S6.1):
`12·1829/10000 - (40/27)² = 23/1822500 > 0`, so `Γ > 1829/10000 ⇒ √(12Γ) > 40/27`.
Status: stable. -/
theorem hs6_kappa {Γ : ℝ} (hΓ : 1829 / 10000 < Γ) : 40 / 27 < √(12 * Γ) := by
  rw [Real.lt_sqrt (by norm_num)]
  linarith

/-- **The angle coordinates** (`CENTRAL_COST_SHAPE_BOUNDS` (3)-(4); inventory HS-S567 CS.1): on
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`, `β = x(1 + δ)`: `1/3 ≤ R ≤ 7/19`,
`9/31 ≤ T_s ≤ R`, `0 ≤ A < 1/100`, and `(βx - α)((x + 2)α + (2x + 1)β)/(S²K_A) = R + (1 + A)T_s`.
Status: stable.
Route: `A = (R² - T²)/(3 + T²) ≤ (R² - T_min²)/3` with `T ≥ T_min = (10x - 11)/(10x + 11)` and one
quartic in `x` (`3(x + 1)²(10x + 11)² - 400x(10x² - 11) > 0`), instead of the monotone `a(x)`. -/
theorem hs6_shape {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    1 / 3 ≤ hsRr x ∧ hsRr x ≤ 7 / 19 ∧ 9 / 31 ≤ hsTs al (x * (1 + δ)) ∧
      hsTs al (x * (1 + δ)) ≤ hsRr x ∧ 0 ≤ hsAn x (x * (1 + δ)) al ∧
      hsAn x (x * (1 + δ)) al < 1 / 100 ∧
      (x * (1 + δ) * x - al) * ((x + 2) * al + (2 * x + 1) * (x * (1 + δ))) /
          ((1 + x) ^ 2 * (al ^ 2 + al * (x * (1 + δ)) + (x * (1 + δ)) ^ 2)) =
        hsRr x + (1 + hsAn x (x * (1 + δ)) al) * hsTs al (x * (1 + δ)) := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x + 1 := by linarith
  have hal0 : 0 < al := by linarith
  have hδ1 : 0 < 1 + δ := by linarith
  have hbe0 : 2 * (1 + δ) ≤ x * (1 + δ) := mul_le_mul_of_nonneg_right hx hδ1.le
  have hbex : x ≤ x * (1 + δ) := by nlinarith
  have hsum : 0 < x * (1 + δ) + al := by linarith
  -- `β ≤ αx` and `11β ≥ 10xα`
  have hord : x * (1 + δ) ≤ al * x := by nlinarith
  have hord2 : 10 * x * al ≤ 11 * (x * (1 + δ)) := by nlinarith
  have hKA : 0 < al ^ 2 + al * (x * (1 + δ)) + (x * (1 + δ)) ^ 2 := by positivity
  -- `A = (R² - T²)/(3 + T²)`
  have hAid : hsAn x (x * (1 + δ)) al = (hsRr x ^ 2 - hsTs al (x * (1 + δ)) ^ 2) /
      (3 + hsTs al (x * (1 + δ)) ^ 2) := by
    unfold hsAn hsRr hsTs
    have : 0 < (x * (1 + δ) + al) ^ 2 * 3 + (x * (1 + δ) - al) ^ 2 := by positivity
    rw [div_eq_div_iff (by positivity) (by field_simp; positivity)]
    field_simp
    ring
  have hT0 : 9 / 31 ≤ hsTs al (x * (1 + δ)) := by
    unfold hsTs; rw [le_div_iff₀ hsum]; nlinarith
  have hTR : hsTs al (x * (1 + δ)) ≤ hsRr x := by
    unfold hsTs hsRr; rw [div_le_div_iff₀ hsum hx0]; nlinarith
  have hTmin : (10 * x - 11) / (10 * x + 11) ≤ hsTs al (x * (1 + δ)) := by
    unfold hsTs; rw [div_le_div_iff₀ (by linarith) hsum]; nlinarith
  refine ⟨?_, ?_, hT0, hTR, ?_, ?_, ?_⟩
  · unfold hsRr; rw [le_div_iff₀ hx0]; linarith
  · unfold hsRr; rw [div_le_iff₀ hx0]; linarith
  · unfold hsAn
    apply div_nonneg (mul_nonneg (by nlinarith) (by linarith)) (by positivity)
  · rw [hAid]
    have hTm0 : 0 ≤ (10 * x - 11) / (10 * x + 11) := div_nonneg (by linarith) (by linarith)
    have hT2 : ((10 * x - 11) / (10 * x + 11)) ^ 2 ≤ hsTs al (x * (1 + δ)) ^ 2 :=
      pow_le_pow_left₀ hTm0 hTmin 2
    have hRT : hsRr x ^ 2 - ((10 * x - 11) / (10 * x + 11)) ^ 2 < 3 / 100 := by
      have e : hsRr x ^ 2 - ((10 * x - 11) / (10 * x + 11)) ^ 2 =
          4 * x * (10 * x ^ 2 - 11) / ((x + 1) ^ 2 * (10 * x + 11) ^ 2) := by
        unfold hsRr; field_simp; ring
      rw [e, div_lt_iff₀ (by positivity)]
      have h0 : 0 ≤ x - 2 := by linarith
      have h1 : 0 ≤ 13 / 6 - x := by linarith
      nlinarith [mul_nonneg h0 h1, mul_nonneg (mul_nonneg h0 h0) h1, mul_nonneg h0 (mul_nonneg h0 h0)]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · unfold hsRr hsTs hsAn
    field_simp
    ring

/-- The Padé-type logarithm majorant behind the incoming floor (`CENTRAL_COST_SHAPE_BOUNDS`
(7)-(8)): `log(1 + R) < R(3R⁴ + 80R³ + 320R² + 480R + 240)/(30(R + 1)(R + 2)³)` for `R > 0`
(derivative of the difference `R⁶/(10(R + 1)²(R + 2)⁴)`).
Route: replaces the integral representation of `V(x) - 3/4` in the notes. -/
private lemma hs6_log_lt {R : ℝ} (hR : 0 < R) :
    log (1 + R) < R * (3 * R ^ 4 + 80 * R ^ 3 + 320 * R ^ 2 + 480 * R + 240) /
      (30 * (R + 1) * (R + 2) ^ 3) := by
  have h := ss_lt_of_deriv
    (f := fun t => (3 * t ^ 5 + 80 * t ^ 4 + 320 * t ^ 3 + 480 * t ^ 2 + 240 * t) /
      (30 * t ^ 4 + 210 * t ^ 3 + 540 * t ^ 2 + 600 * t + 240) - log (1 + t))
    (f' := fun t => t ^ 6 / (10 * (t + 1) ^ 2 * (t + 2) ^ 4)) hR (fun t ht => ?_) (fun t ht => by
      have : 0 < t := ht.1
      positivity)
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
      zero_div, add_zero, log_one, sub_zero] at h
    have e : R * (3 * R ^ 4 + 80 * R ^ 3 + 320 * R ^ 2 + 480 * R + 240) /
        (30 * (R + 1) * (R + 2) ^ 3) = (3 * R ^ 5 + 80 * R ^ 4 + 320 * R ^ 3 + 480 * R ^ 2 + 240 * R) /
        (30 * R ^ 4 + 210 * R ^ 3 + 540 * R ^ 2 + 600 * R + 240) := by
      congr 1 <;> ring
    rw [e]; linarith
  have ht0 : 0 ≤ t := ht.1
  have hD : 0 < 30 * t ^ 4 + 210 * t ^ 3 + 540 * t ^ 2 + 600 * t + 240 := by positivity
  have hN : HasDerivAt (fun t : ℝ => 3 * t ^ 5 + 80 * t ^ 4 + 320 * t ^ 3 + 480 * t ^ 2 + 240 * t)
      (15 * t ^ 4 + 320 * t ^ 3 + 960 * t ^ 2 + 960 * t + 240) t := by
    have := (((((hasDerivAt_pow 5 t).const_mul 3).add ((hasDerivAt_pow 4 t).const_mul 80)).add
      ((hasDerivAt_pow 3 t).const_mul 320)).add ((hasDerivAt_pow 2 t).const_mul 480)).add
      ((hasDerivAt_id' t).const_mul 240)
    convert this using 1; push_cast; ring
  have hDd : HasDerivAt (fun t : ℝ => 30 * t ^ 4 + 210 * t ^ 3 + 540 * t ^ 2 + 600 * t + 240)
      (120 * t ^ 3 + 630 * t ^ 2 + 1080 * t + 600) t := by
    have := (((((hasDerivAt_pow 4 t).const_mul 30).add ((hasDerivAt_pow 3 t).const_mul 210)).add
      ((hasDerivAt_pow 2 t).const_mul 540)).add ((hasDerivAt_id' t).const_mul 600)).add_const 240
    convert this using 1; push_cast; ring
  have hL : HasDerivAt (fun t : ℝ => log (1 + t)) (1 / (1 + t)) t := by
    have := ((hasDerivAt_id' t).const_add 1).log (by linarith)
    convert this using 1
  refine ((hN.div hDd hD.ne').sub hL).congr_deriv ?_
  have : 0 < 1 + t := by linarith
  field_simp
  ring

/-- **The incoming norm, two-sided** (`CENTRAL_COST_SHAPE_BOUNDS` (5)-(8); inventory HS-S567 CS.2):
on the box of `hs6_shape`, `u_q(R, δ) < Sec(1, x, β) ≤ 3/4 + R²/12`. Status: stable.
Route: the floor uses the Padé-type majorant `hs6_log_lt` of `log(1 + R)` (derivative of the
difference `R⁶/(10(R + 1)²(R + 2)⁴)`) instead of the integral representation of `V - 3/4`. -/
theorem hs6_u_bounds {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    hs6uq (hsRr x) δ < m2Sec 1 x (x * (1 + δ)) ∧
      m2Sec 1 x (x * (1 + δ)) ≤ 3 / 4 + hsRr x ^ 2 / 12 := by
  have _ := hx2
  have _ := hal
  have _ := hal'
  have hx1 : 1 < x := by linarith only [hx]
  have hx0 : 0 < x := by linarith only [hx]
  have hδ1 : 0 < 1 + δ := by linarith only [hδ]
  have hbex : x ≤ x * (1 + δ) := by nlinarith only [hx0, hδ]
  have hbe1 : 1 < x * (1 + δ) := by linarith only [hx1, hbex]
  -- the split `(β - 1)u = (x - 1)V + (β - x)Sec(x, x, β)`
  have hsplit := ss_sec_add (A := 1) (B := x) (M := x) (P := x * (1 + δ)) one_pos hx0 hx0
    (by linarith only [hbe1])
  have hT34 : 3 / 4 ≤ m2Sec x x (x * (1 + δ)) := ss_sec_ge_34 hx0 hx0 (by linarith only [hbe1])
  have hR2 : hsRr x ^ 2 = (x - 1) ^ 2 / (x + 1) ^ 2 := by rw [hsRr, div_pow]
  have hR9 : 1 / 108 ≤ hsRr x ^ 2 / 12 := by
    rw [hR2, div_div, le_div_iff₀ (by positivity)]; nlinarith only [hx, hx2]
  constructor
  · -- the floor: `V - 3/4 > R²H_R/(15(2 + R)³)` and the weight `(x - 1)/(β - 1) = 1/(1 + z)`
    have hR0 : 0 < hsRr x := by
      unfold hsRr; exact div_pos (by linarith only [hx1]) (by linarith only [hx1])
    have hlog := hs6_log_lt hR0
    have hV : m2Sec 1 x x = 1 + x ^ 2 / ((1 + x) * (x + x)) -
        x / (x - 1) * log (1 + hsRr x) := by
      rw [m2Sec_of_ne (by linarith only [hx1])]
      congr 3
      unfold hsRr; field_simp; ring
    set B := hsRr x ^ 2 * (3 * hsRr x ^ 2 + 10 * hsRr x + 10) / (15 * (2 + hsRr x) ^ 3) with hB
    have hB0 : 0 < B := by rw [hB]; positivity
    have hxR1 : x / (x - 1) = (1 + hsRr x) / (2 * hsRr x) := by
      unfold hsRr; field_simp; ring
    have hxR2 : x ^ 2 / ((1 + x) * (x + x)) = (1 + hsRr x) / 4 := by
      unfold hsRr; field_simp; ring
    have eR : (1 + hsRr x) / 4 + 1 / 4 - B = (1 + hsRr x) / (2 * hsRr x) *
        (hsRr x * (3 * hsRr x ^ 4 + 80 * hsRr x ^ 3 + 320 * hsRr x ^ 2 + 480 * hsRr x + 240) /
          (30 * (hsRr x + 1) * (hsRr x + 2) ^ 3)) := by
      rw [hB]; field_simp; ring
    have hVB : B < m2Sec 1 x x - 3 / 4 := by
      have hpos : 0 < (1 + hsRr x) / (2 * hsRr x) := by positivity
      have := mul_lt_mul_of_pos_left hlog hpos
      rw [hV, hxR1, hxR2]
      linarith only [this, eR]
    set z := x * δ / (x - 1) with hz
    have hz0 : 0 ≤ z := by rw [hz]; positivity
    have hz2 : z ≤ 2 / 19 := by
      rw [hz, div_le_iff₀ (by linarith only [hx1])]; nlinarith only [hδ, hδ2, hx, hx2]
    have hβ : x * (1 + δ) - 1 = (x - 1) * (1 + z) := by rw [hz]; field_simp; ring
    have huq : hs6uq (hsRr x) δ = 3 / 4 + B * (1 - z + 19 / 21 * z ^ 2) := by
      rw [hB, hz]; unfold hs6uq hsRr; field_simp; ring
    have hw : (1 - z + 19 / 21 * z ^ 2) * (1 + z) ≤ 1 := by
      have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg z) (by linarith only [hz2] : 19 * z - 2 ≤ 0)
      linarith only [this]
    rw [huq]
    have hmain : (x - 1) * B < (x * (1 + δ) - 1) * (m2Sec 1 x (x * (1 + δ)) - 3 / 4) := by
      have h1 := mul_lt_mul_of_pos_left hVB (by linarith only [hx1] : (0 : ℝ) < x - 1)
      have h2 := mul_nonneg (by linarith only [hbex] : (0 : ℝ) ≤ x * (1 + δ) - x)
        (by linarith only [hT34] : (0 : ℝ) ≤ m2Sec x x (x * (1 + δ)) - 3 / 4)
      linarith only [h1, h2, hsplit]
    have hlow : (x * (1 + δ) - 1) * (B * (1 - z + 19 / 21 * z ^ 2)) ≤ (x - 1) * B := by
      rw [hβ]
      have := mul_le_mul_of_nonneg_left hw (mul_nonneg (by linarith only [hx1] : (0 : ℝ) ≤ x - 1) hB0.le)
      linarith only [this]
    have h3 : (x * (1 + δ) - 1) * (B * (1 - z + 19 / 21 * z ^ 2)) <
        (x * (1 + δ) - 1) * (m2Sec 1 x (x * (1 + δ)) - 3 / 4) := by linarith only [hmain, hlow]
    have := lt_of_mul_lt_mul_left h3 (by linarith only [hbe1])
    linarith only [this]
  · -- the ceiling: both pieces have mean at most `R²/12`
    have hV := hs_V_le_U0 hx1
    have hT := hs_sec_tail_le hx0 hbex
    have hU0 : hsU0 x = 3 / 4 + hsRr x ^ 2 / 12 := by
      rw [hsU0, hR2]; field_simp
    have hTt : (x * (1 + δ) - x) ^ 2 / (48 * x ^ 2) ≤ hsRr x ^ 2 / 12 := by
      have e : (x * (1 + δ) - x) ^ 2 / (48 * x ^ 2) = δ ^ 2 / 48 := by field_simp; ring
      rw [e]
      have : δ ^ 2 ≤ (1 / 19) ^ 2 := pow_le_pow_left₀ hδ hδ2 2
      linarith only [this, hR9]
    rw [hU0] at hV
    have h1 : (x * (1 + δ) - 1) * m2Sec 1 x (x * (1 + δ)) ≤
        (x * (1 + δ) - 1) * (3 / 4 + hsRr x ^ 2 / 12) := by
      rw [hsplit]
      have hT' : m2Sec x x (x * (1 + δ)) ≤ 3 / 4 + hsRr x ^ 2 / 12 := by linarith only [hT, hTt]
      have h2 := mul_le_mul_of_nonneg_left hV (by linarith only [hx1] : (0 : ℝ) ≤ x - 1)
      have h3 := mul_le_mul_of_nonneg_left hT' (by linarith only [hbex] : (0 : ℝ) ≤ x * (1 + δ) - x)
      linarith only [h2, h3]
    exact le_of_mul_le_mul_left h1 (by linarith only [hbe1])

/-- **The central shear bounds** (`CENTRAL_COST_SHAPE_BOUNDS` (9)-(13); inventory HS-S567 CS.3): on the
box of `hs6_shape`, `1/9 ≤ Z_L ≤ Z ≤ Z_U < 1/5`. Status: stable.
Route: `Z_U - Z` and `Z - Z_L` are `d·N/D` exactly, with explicit numerators bounded on the box
(`Hs6.Shear`), instead of the Taylor bound in `d` and the concavity in `η` of the notes. -/
theorem hs6_central_shear {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    1 / 9 ≤ hs6ZL (hsRr x) δ ∧ hs6ZL (hsRr x) δ ≤ hs6Z x (x * (1 + δ)) al ∧
      hs6Z x (x * (1 + δ)) al ≤ hs6ZU (hsRr x) δ ∧ hs6ZU (hsRr x) δ < 1 / 5 := by
  have hR1 : 1 / 3 ≤ hsRr x := by unfold hsRr; rw [le_div_iff₀ (by linarith)]; linarith
  have hR2 : hsRr x ≤ 7 / 19 := by unfold hsRr; rw [div_le_iff₀ (by linarith)]; linarith
  have h3R : 0 < 3 - hsRr x := by linarith
  have hZ0 : 1 / 9 ≤ 2 * hsRr x ^ 2 * (1 + hsRr x) / (3 - hsRr x) := by
    rw [le_div_iff₀ h3R]
    have : (1 / 3) ^ 2 ≤ hsRr x ^ 2 := pow_le_pow_left₀ (by norm_num) hR1 2
    nlinarith
  -- `α = 1 + ηδ` with `13/5 ≤ η ≤ 3`
  obtain ⟨η, hη1, hη2, hη⟩ : ∃ η : ℝ, 13 / 5 ≤ η ∧ η ≤ 3 ∧ al = 1 + η * δ := by
    rcases hδ.lt_or_eq with hpos | hzero
    · refine ⟨(al - 1) / δ, ?_, ?_, ?_⟩
      · rw [le_div_iff₀ hpos]; linarith
      · rw [div_le_iff₀ hpos]; linarith
      · field_simp; ring
    · refine ⟨13 / 5, le_rfl, by norm_num, ?_⟩
      rw [← hzero] at hal hal' ⊢
      linarith
  subst hη
  obtain ⟨hL, hU⟩ := hs6_shear_core hx hx2 hδ hδ2 hη1 hη2
  refine ⟨?_, hL, hU, ?_⟩
  · show 1 / 9 ≤ 2 * hsRr x ^ 2 * (1 + hsRr x) / (3 - hsRr x) * (1 + 11 * δ / 2)
    have : 1 ≤ 1 + 11 * δ / 2 := by linarith
    nlinarith
  · show 2 * hsRr x ^ 2 * (1 + hsRr x) / (3 - hsRr x) + (1 + 2 * hsRr x) / (3 * (1 - hsRr x)) * δ -
      3 / 2 * δ ^ 2 < 1 / 5
    have h1R : 0 < 1 - hsRr x := by linarith
    have e1 : 2 * hsRr x ^ 2 * (1 + hsRr x) / (3 - hsRr x) ≤ 2548 / 18050 := by
      rw [div_le_iff₀ h3R]
      have : hsRr x ^ 2 ≤ (7 / 19) ^ 2 := pow_le_pow_left₀ (by linarith) hR2 2
      have : hsRr x ^ 3 ≤ (7 / 19) ^ 3 := pow_le_pow_left₀ (by linarith) hR2 3
      nlinarith
    have e2 : (1 + 2 * hsRr x) / (3 * (1 - hsRr x)) ≤ 11 / 12 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have e3 : (1 + 2 * hsRr x) / (3 * (1 - hsRr x)) * δ ≤ 11 / 12 * (1 / 19) :=
      mul_le_mul e2 hδ2 hδ (by norm_num)
    nlinarith [sq_nonneg δ]

/-- The double angle of an arctangent: `cos(2 arctan y) = (1 - y²)/(1 + y²)`,
`sin(2 arctan y) = 2y/(1 + y²)`. -/
private lemma hs6_two_arctan (y : ℝ) :
    cos (2 * arctan y) = (1 - y ^ 2) / (1 + y ^ 2) ∧ sin (2 * arctan y) = 2 * y / (1 + y ^ 2) := by
  have h1 : 0 < 1 + y ^ 2 := by positivity
  constructor
  · rw [cos_two_mul, cos_sq_arctan]
    field_simp
    ring
  · rw [sin_two_mul, sin_arctan, cos_arctan]
    have hs : √(1 + y ^ 2) ^ 2 = 1 + y ^ 2 := Real.sq_sqrt h1.le
    have hs0 : 0 < √(1 + y ^ 2) := Real.sqrt_pos.2 h1
    field_simp
    rw [hs]

/-- The square-root form of the tangent curve: for `0 ≤ A < K`, `0 < δ < π`,
`K sin δ + h̃ cos δ = (K - 𝒟 cos δ)/sin δ = √(h̃² + A²)`. -/
private lemma hs6_tangent_sqrt {A K δ : ℝ} (hA : 0 ≤ A) (hK : A < K) (h0 : 0 < δ) (hπ : δ < π) :
    K * sin δ + (K * cos δ - √(K ^ 2 - A ^ 2)) / sin δ * cos δ =
        (K - √(K ^ 2 - A ^ 2) * cos δ) / sin δ ∧
      (K - √(K ^ 2 - A ^ 2) * cos δ) / sin δ =
        √(((K * cos δ - √(K ^ 2 - A ^ 2)) / sin δ) ^ 2 + A ^ 2) := by
  have hs : 0 < sin δ := sin_pos_of_pos_of_lt_pi h0 hπ
  have hK0 : 0 < K := lt_of_le_of_lt hA hK
  have hKA : 0 ≤ K ^ 2 - A ^ 2 := sub_nonneg.2 (pow_le_pow_left₀ hA hK.le 2)
  have hD2 : √(K ^ 2 - A ^ 2) ^ 2 = K ^ 2 - A ^ 2 := Real.sq_sqrt hKA
  have hD0 : 0 ≤ √(K ^ 2 - A ^ 2) := Real.sqrt_nonneg _
  have hDK : √(K ^ 2 - A ^ 2) ≤ K := by
    rw [Real.sqrt_le_left hK0.le]; linarith [sq_nonneg A]
  have hc1 : cos δ ≤ 1 := cos_le_one δ
  have hsc : sin δ ^ 2 + cos δ ^ 2 = 1 := sin_sq_add_cos_sq δ
  have hnum : 0 ≤ K - √(K ^ 2 - A ^ 2) * cos δ := by
    linarith [mul_le_mul_of_nonneg_left hc1 hD0]
  have key : (K * cos δ - √(K ^ 2 - A ^ 2)) ^ 2 + A ^ 2 * sin δ ^ 2 =
      (K - √(K ^ 2 - A ^ 2) * cos δ) ^ 2 := by
    linear_combination sin δ ^ 2 * hD2 + (K ^ 2 - √(K ^ 2 - A ^ 2) ^ 2) * hsc
  constructor
  · field_simp
    linear_combination K * hsc
  · have heq : ((K * cos δ - √(K ^ 2 - A ^ 2)) / sin δ) ^ 2 + A ^ 2 =
        ((K - √(K ^ 2 - A ^ 2) * cos δ) / sin δ) ^ 2 := by
      rw [div_pow, div_pow]
      field_simp
      linear_combination key
    rw [heq, Real.sqrt_sq (by positivity)]

/-- The derivative of the tangent curve: `h̃'(δ) = (𝒟 cos δ - K)/sin²δ`. -/
private lemma hs6_ht_deriv {A K δ : ℝ} (h0 : 0 < δ) (hπ : δ < π) :
    HasDerivAt (fun s => (K * cos s - √(K ^ 2 - A ^ 2)) / sin s)
      ((√(K ^ 2 - A ^ 2) * cos δ - K) / sin δ ^ 2) δ := by
  have hs : 0 < sin δ := sin_pos_of_pos_of_lt_pi h0 hπ
  have h := (((hasDerivAt_cos δ).const_mul K).sub_const (√(K ^ 2 - A ^ 2))).div
    (hasDerivAt_sin δ) hs.ne'
  refine h.congr_deriv ?_
  have hsc : sin δ ^ 2 + cos δ ^ 2 = 1 := sin_sq_add_cos_sq δ
  field_simp
  linear_combination (-K) * hsc

/-- `K - 𝒟 cos δ > 0` on `(0, π)` for `0 ≤ A < K`. -/
private lemma hs6_K_sub_pos {A K δ : ℝ} (hA : 0 ≤ A) (hK : A < K) (h0 : 0 < δ) (hπ : δ < π) :
    0 < K - √(K ^ 2 - A ^ 2) * cos δ := by
  have hs : 0 < sin δ := sin_pos_of_pos_of_lt_pi h0 hπ
  have hK0 : 0 < K := lt_of_le_of_lt hA hK
  have hD0 : 0 ≤ √(K ^ 2 - A ^ 2) := Real.sqrt_nonneg _
  have hDK : √(K ^ 2 - A ^ 2) ≤ K := by
    rw [Real.sqrt_le_left hK0.le]; linarith [sq_nonneg A]
  have hsc : sin δ ^ 2 + cos δ ^ 2 = 1 := sin_sq_add_cos_sq δ
  have hc1 : cos δ < 1 := by
    have h2 : cos δ ^ 2 < 1 := by linarith [pow_pos hs 2]
    exact (abs_lt.1 (sq_lt_one_iff_abs_lt_one _ |>.1 h2)).2
  rcases le_or_gt 0 (cos δ) with hc | hc
  · linarith [mul_le_mul_of_nonneg_right hDK hc, mul_pos hK0 (sub_pos.2 hc1)]
  · linarith [mul_nonneg hD0 (neg_nonneg.2 hc.le)]

/-- **The tangent curve inverts the half-angle formula** (`SHEAR_COST_REDUCTION` (8)-(10)(c);
inventory HS-S567 SH.4): for `A ≥ 0`, `K > A`, `𝒟 = √(K² - A²)` and `h < 0`, the angle
`δ = 2 arctan((√(h² + A²) - h)/(K + 𝒟))` lies in `(0, π)` and `(K cos δ - 𝒟)/sin δ = h`.
Status: stable. -/
theorem hs6_tangent_inv {A K h : ℝ} (hA : 0 ≤ A) (hK : A < K) (hh : h < 0) :
    0 < 2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2))) ∧
      2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2))) < π ∧
      (K * cos (2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2)))) - √(K ^ 2 - A ^ 2)) /
          sin (2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2)))) = h := by
  set D := √(K ^ 2 - A ^ 2) with hD
  set ρ := √(h ^ 2 + A ^ 2) with hρ
  have hK0 : 0 < K := lt_of_le_of_lt hA hK
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hD2 : D ^ 2 = K ^ 2 - A ^ 2 := Real.sq_sqrt (sub_nonneg.2 (pow_le_pow_left₀ hA hK.le 2))
  have hρ2 : ρ ^ 2 = h ^ 2 + A ^ 2 := Real.sq_sqrt (by positivity)
  have hKD : 0 < K + D := by linarith
  set y := (ρ - h) / (K + D) with hy
  have hy0 : 0 < y := div_pos (by linarith) hKD
  have hyK : y * (K + D) = ρ - h := by rw [hy]; field_simp
  refine ⟨by linarith [arctan_pos.2 hy0], by linarith [arctan_lt_pi_div_two y], ?_⟩
  obtain ⟨hc, hs⟩ := hs6_two_arctan y
  rw [hc, hs]
  have key : (K * (1 - y ^ 2) - D * (1 + y ^ 2) - 2 * h * y) * (K + D) = 0 := by
    linear_combination (-1 : ℝ) * hD2 - hρ2 - (ρ + y * (K + D) + h) * hyK
  have key' : K * (1 - y ^ 2) - D * (1 + y ^ 2) - 2 * h * y = 0 :=
    (mul_eq_zero.1 key).resolve_right hKD.ne'
  have h1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  field_simp
  linear_combination key'

/-- **The tangent curve is decreasing** (`SHEAR_COST_REDUCTION` (10)(a)-(b); inventory HS-S567 SH.4):
for `A ≥ 0`, `K > A`, `h̃(δ) = (K cos δ - 𝒟)/sin δ` is strictly decreasing on `(0, π)`
(`h̃' = (𝒟 cos δ - K)/sin²δ < 0`), and `K sin δ + h̃(δ) cos δ = √(h̃(δ)² + A²)`. Status: stable. -/
theorem hs6_tangent_anti {A K δ₁ δ₂ : ℝ} (hA : 0 ≤ A) (hK : A < K) (h1 : 0 < δ₁) (h12 : δ₁ < δ₂)
    (h2 : δ₂ < π) :
    (K * cos δ₂ - √(K ^ 2 - A ^ 2)) / sin δ₂ < (K * cos δ₁ - √(K ^ 2 - A ^ 2)) / sin δ₁ ∧
      K * sin δ₁ + (K * cos δ₁ - √(K ^ 2 - A ^ 2)) / sin δ₁ * cos δ₁ =
        √(((K * cos δ₁ - √(K ^ 2 - A ^ 2)) / sin δ₁) ^ 2 + A ^ 2) := by
  refine ⟨?_, ?_⟩
  · have h := ss_lt_of_deriv (f := fun s => -((K * cos s - √(K ^ 2 - A ^ 2)) / sin s))
      (f' := fun s => (K - √(K ^ 2 - A ^ 2) * cos s) / sin s ^ 2) h12
      (fun z hz => by
        have := (hs6_ht_deriv (A := A) (K := K) (δ := z) (by linarith [hz.1])
          (by linarith [hz.2])).const_mul (-1)
        convert this using 1
        · funext s; ring
        · ring)
      (fun z hz => by
        have h0 : 0 < z := by linarith [hz.1]
        have hπ : z < π := by linarith [hz.2]
        have := hs6_K_sub_pos hA hK h0 hπ
        have := sin_pos_of_pos_of_lt_pi h0 hπ
        positivity)
    linarith
  · obtain ⟨e1, e2⟩ := hs6_tangent_sqrt hA hK h1 (by linarith)
    rw [e1, e2]

/-- **The score derivative** (`SHEAR_COST_REDUCTION` (11)-(13); inventory HS-S567 SH.5): for
`A ≥ 0`, `K > A`, `J₀, c` real and `0 < δ < π`, `F̃(δ) = -J₀h̃(δ) - cδ` has derivative
`(J₀√(h̃(δ)² + A²) - c sin δ)/sin δ`. Status: stable. -/
theorem hs6_score_deriv {A K J₀ c δ : ℝ} (hA : 0 ≤ A) (hK : A < K) (h0 : 0 < δ) (hπ : δ < π) :
    HasDerivAt (fun s => -J₀ * ((K * cos s - √(K ^ 2 - A ^ 2)) / sin s) - c * s)
      ((J₀ * √(((K * cos δ - √(K ^ 2 - A ^ 2)) / sin δ) ^ 2 + A ^ 2) - c * sin δ) / sin δ) δ := by
  have hs : 0 < sin δ := sin_pos_of_pos_of_lt_pi h0 hπ
  have h := ((hs6_ht_deriv (A := A) (K := K) h0 hπ).const_mul (-J₀)).sub
    ((hasDerivAt_id' δ).const_mul c)
  refine h.congr_deriv ?_
  rw [← (hs6_tangent_sqrt hA hK h0 hπ).2]
  field_simp
  ring

/-- **The barrier criterion** (`SCALE_ANGLE_BARRIER` (21); inventory HS-S567 SB.2): with
`0 ≤ b₁ < 1`, `A ≥ 0`, `b₂ = b₁ - (1 - b₁)A`, `c > 3/2`, `3(b₁ + b₂)/2 < c`, `J₀ = 3(1 - b₁)/2`,
`K = A + 2 + 2(c - 3/2)/J₀`, `H > 0` and `δ = 2 arctan((√(H² + A²) + H)/(K + √(K² - A²)))`: if
`Q_c(H²) = J₀²H⁴ + (-3c(b₁ + b₂) + (9/2)(b₁² + b₂²))H² + A²(c - 3(b₁ + b₂)/2)² < 0` then
`J₀√(H² + A²) < c sin δ`. Status: stable. -/
theorem hs6_barrier_sin {b₁ A c H : ℝ} (hb₁ : 0 ≤ b₁) (hb₁1 : b₁ < 1) (hA : 0 ≤ A) (hc : 3 / 2 < c)
    (hcb : 3 * (b₁ + (b₁ - (1 - b₁) * A)) / 2 < c) (hH : 0 < H)
    (hQ : (3 * (1 - b₁) / 2) ^ 2 * (H ^ 2) ^ 2 +
        (-3 * c * (b₁ + (b₁ - (1 - b₁) * A)) + 9 / 2 * (b₁ ^ 2 + (b₁ - (1 - b₁) * A) ^ 2)) * H ^ 2 +
        A ^ 2 * (c - 3 * (b₁ + (b₁ - (1 - b₁) * A)) / 2) ^ 2 < 0) :
    3 * (1 - b₁) / 2 * √(H ^ 2 + A ^ 2) <
      c * sin (2 * arctan ((√(H ^ 2 + A ^ 2) + H) /
        ((A + 2 + 2 * (c - 3 / 2) / (3 * (1 - b₁) / 2)) +
          √((A + 2 + 2 * (c - 3 / 2) / (3 * (1 - b₁) / 2)) ^ 2 - A ^ 2)))) := by
  have _ := hb₁
  set J := 3 * (1 - b₁) / 2 with hJ
  set K := A + 2 + 2 * (c - 3 / 2) / J with hKdef
  set b₂ := b₁ - (1 - b₁) * A with hb₂
  have hJ0 : 0 < J := by rw [hJ]; linarith
  have hJK : J * K = 2 * c - 3 / 2 * (b₁ + b₂) := by
    rw [hKdef, hb₂]; field_simp; ring
  have hKA : A < K := by
    have : 0 < 2 * (c - 3 / 2) / J := div_pos (by linarith) hJ0
    rw [hKdef]; linarith
  set D := √(K ^ 2 - A ^ 2) with hD
  set ρ := √(H ^ 2 + A ^ 2) with hρ
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hD2 : D ^ 2 = K ^ 2 - A ^ 2 := Real.sq_sqrt (sub_nonneg.2 (pow_le_pow_left₀ hA hKA.le 2))
  have hρ2 : ρ ^ 2 = H ^ 2 + A ^ 2 := Real.sq_sqrt (by positivity)
  obtain ⟨hδ0, hδπ, hδh⟩ := hs6_tangent_inv hA hKA (neg_lt_zero.2 hH)
  have e : √((-H) ^ 2 + A ^ 2) - -H = ρ + H := by rw [neg_sq]; ring
  rw [e, ← hD] at hδ0 hδπ hδh
  set δ := 2 * arctan ((ρ + H) / (K + D)) with hδ
  have hs : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ0 hδπ
  obtain ⟨e1, e2⟩ := hs6_tangent_sqrt hA hKA hδ0 hδπ
  rw [← hD, hδh, neg_sq, ← hρ] at e2
  rw [← hD, hδh] at e1
  have hlin1 : K * cos δ - D = -H * sin δ := by
    rw [← hδh]; field_simp
  have hlin2 : K * sin δ - H * cos δ = ρ := by rw [← e2, ← e1]; ring
  have hsin : sin δ * (K ^ 2 + H ^ 2) = K * ρ + D * H := by
    linear_combination K * hlin2 + H * hlin1
  have hKH : 0 < K ^ 2 + H ^ 2 := by positivity
  have hc0 : 0 < c := by linarith
  have hP : 0 ≤ ρ * (K * (J * K - c) + J * H ^ 2) := by
    have : 0 < J * K - c := by rw [hJK]; linarith
    have : 0 < K := by linarith
    positivity
  have hcDH : 0 ≤ c * D * H := by positivity
  have hid : (c * D * H) ^ 2 - (ρ * (K * (J * K - c) + J * H ^ 2)) ^ 2 =
      -((K ^ 2 + H ^ 2) * (J ^ 2 * (H ^ 2) ^ 2 +
        (-3 * c * (b₁ + b₂) + 9 / 2 * (b₁ ^ 2 + b₂ ^ 2)) * H ^ 2 +
        A ^ 2 * (c - 3 * (b₁ + b₂) / 2) ^ 2)) := by
    rw [hJ, hb₂] at hJK ⊢
    linear_combination 3 * (A ^ 2 + H ^ 2) * (H ^ 2 + K ^ 2) *
      (A * b₁ - A + K * b₁ - K + 2 * b₁) / 2 * hJK -
      (K * (3 * (1 - b₁) / 2 * K - c) + 3 * (1 - b₁) / 2 * H ^ 2) ^ 2 * hρ2 +
      c ^ 2 * H ^ 2 * hD2
  have hsq : (ρ * (K * (J * K - c) + J * H ^ 2)) ^ 2 < (c * D * H) ^ 2 := by
    have := mul_pos hKH (neg_pos.2 hQ)
    linarith
  have hlt : ρ * (K * (J * K - c) + J * H ^ 2) < c * D * H := lt_of_pow_lt_pow_left₀ 2 hcDH hsq
  have : J * ρ * (K ^ 2 + H ^ 2) < c * sin δ * (K ^ 2 + H ^ 2) := by
    rw [mul_assoc c, hsin]; linarith
  exact lt_of_mul_lt_mul_right this hKH.le

/-- The barrier quotient `Q = Q_c(H²)/H²` with `A = tH`, `v = b₁` (`SCALE_ANGLE_BARRIER` (25),
expanded): `(9/4)(1 - v)²H² - 6cv + 9v² + 3(1 - v)tH(c - 3v) + (9/2)(1 - v)²t²H² +
(t(c - 3v + (3/2)(1 - v)tH))²`. -/
private noncomputable def hs6Qb (v t H c : ℝ) : ℝ :=
  9 / 4 * (1 - v) ^ 2 * H ^ 2 - 6 * c * v + 9 * v ^ 2 + 3 * (1 - v) * t * H * (c - 3 * v) +
    9 / 2 * (1 - v) ^ 2 * t ^ 2 * H ^ 2 + (t * (c - 3 * v + 3 / 2 * (1 - v) * t * H)) ^ 2

/-- The `v`-derivative of `hs6Qb`, in a form with signed terms. -/
private noncomputable def hs6Qbv (v t H c : ℝ) : ℝ :=
  -(9 / 2 * (1 - v) * H ^ 2) + (-6 * c + 18 * v) - 3 * t * H * ((c - 3 * v) + 3 * (1 - v)) -
    9 * (1 - v) * t ^ 2 * H ^ 2 -
      2 * t ^ 2 * (c - 3 * v + 3 / 2 * (1 - v) * t * H) * (3 + 3 / 2 * t * H)

/-- `hs6Qb` is quadratic in `v`: its increment is the derivative at the midpoint. -/
private lemma hs6Qb_v (v w t H c : ℝ) :
    hs6Qb w t H c - hs6Qb v t H c = (w - v) * hs6Qbv ((v + w) / 2) t H c := by
  unfold hs6Qb hs6Qbv; ring

/-- The derivative is negative: every term but `-6c + 18v` is nonpositive. -/
private lemma hs6Qbv_neg {m t H c : ℝ} (hm : m ≤ 1) (ht : 0 ≤ t) (hH : 0 ≤ H)
    (hc : 18 * m < 6 * c) : hs6Qbv m t H c < 0 := by
  unfold hs6Qbv
  generalize ha : 1 - m = a
  have ha0 : 0 ≤ a := by rw [← ha]; linarith
  generalize he : c - 3 * m = e
  have he0 : 0 ≤ e := by rw [← he]; linarith
  have : 0 ≤ 9 / 2 * a * H ^ 2 + 3 * t * H * (e + 3 * a) + 9 * a * t ^ 2 * H ^ 2 +
      2 * t ^ 2 * (e + 3 / 2 * a * t * H) * (3 + 3 / 2 * t * H) := by positivity
  linarith

/-- **The barrier lemma** (`SCALE_ANGLE_BARRIER` (24)-(30); inventory HS-S567 SB.3): for
`0 < R ≤ 7/17`, `v₀ = 2R²/(3(3 + R²)) ≤ b₁ ≤ 49/916`, `0 ≤ A ≤ R²/3`, `b₂ = b₁ - (1 - b₁)A ≥ 0`,
`21/8 ≤ c ≤ 3`, `0 < H < 7R²/6`, `HR ≥ 5A/2`: `Q_c(H²) < 0`. Status: stable.
Route: as in the notes, but every term of the `v`-derivative of `Q` is nonpositive outright, so the
step `v ↦ v₀` needs neither `b₂ ≥ 0` nor `A ≤ R²/3` (both hypotheses are unused). -/
theorem hs6_barrier {R b₁ A c H : ℝ} (hR : 0 < R) (hR7 : R ≤ 7 / 17)
    (hb₁ : 2 * R ^ 2 / (3 * (3 + R ^ 2)) ≤ b₁) (hb₁' : b₁ ≤ 49 / 916) (hA : 0 ≤ A)
    (hA' : A ≤ R ^ 2 / 3) (hb₂ : 0 ≤ b₁ - (1 - b₁) * A) (hc : 21 / 8 ≤ c) (hc' : c ≤ 3) (hH : 0 < H)
    (hH' : H < 7 * R ^ 2 / 6) (hHR : 5 / 2 * A ≤ H * R) :
    (3 * (1 - b₁) / 2) ^ 2 * (H ^ 2) ^ 2 +
        (-3 * c * (b₁ + (b₁ - (1 - b₁) * A)) + 9 / 2 * (b₁ ^ 2 + (b₁ - (1 - b₁) * A) ^ 2)) * H ^ 2 +
        A ^ 2 * (c - 3 * (b₁ + (b₁ - (1 - b₁) * A)) / 2) ^ 2 < 0 := by
  have _ := hA'
  have _ := hb₂
  set b₂ := b₁ - (1 - b₁) * A with hb₂def
  have hb₁0 : 0 ≤ b₁ := le_trans (by positivity) hb₁
  have hR2 : R ^ 2 ≤ 49 / 289 := by
    have := pow_le_pow_left₀ hR.le hR7 2
    norm_num at this ⊢; linarith
  -- `A = tH` with `0 ≤ t ≤ 2R/5`
  set t := A / H with htdef
  have hAt : A = t * H := by rw [htdef]; field_simp
  have ht0 : 0 ≤ t := div_nonneg hA hH.le
  have ht1 : t ≤ 2 * R / 5 := by
    rw [htdef, div_le_iff₀ hH]; linarith
  have hQ : (3 * (1 - b₁) / 2) ^ 2 * (H ^ 2) ^ 2 +
      (-3 * c * (b₁ + b₂) + 9 / 2 * (b₁ ^ 2 + b₂ ^ 2)) * H ^ 2 +
      A ^ 2 * (c - 3 * (b₁ + b₂) / 2) ^ 2 = H ^ 2 * hs6Qb b₁ t H c := by
    rw [hb₂def, hAt]; unfold hs6Qb; ring
  rw [hQ]
  refine mul_neg_of_pos_of_neg (by positivity) ?_
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 2 * R / 5 := ⟨_, rfl⟩
  obtain ⟨H₁, hH₁⟩ : ∃ H₁ : ℝ, H₁ = 7 * R ^ 2 / 6 := ⟨_, rfl⟩
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : ℝ, v₀ = 2 * R ^ 2 / (3 * (3 + R ^ 2)) := ⟨_, rfl⟩
  rw [← hd] at ht1
  rw [← hH₁] at hH'
  rw [← hv₀] at hb₁
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  have hc3 : 0 ≤ c - 3 * b₁ := by linarith
  have ha : 0 ≤ 1 - b₁ := by linarith
  -- (i) raise `t` to `d`
  have s1 : hs6Qb b₁ t H c ≤ hs6Qb b₁ d H c := by
    unfold hs6Qb
    have : 0 ≤ c - 3 * b₁ + 3 / 2 * (1 - b₁) * t * H := by positivity
    gcongr
  -- (ii) raise `H` to `H₁`
  have s2 : hs6Qb b₁ d H c ≤ hs6Qb b₁ d H₁ c := by
    unfold hs6Qb
    have : 0 ≤ c - 3 * b₁ + 3 / 2 * (1 - b₁) * d * H := by positivity
    gcongr
  -- (iii) lower `v` to `v₀`
  have s3 : hs6Qb b₁ d H₁ c ≤ hs6Qb v₀ d H₁ c := by
    have h := hs6Qb_v v₀ b₁ d H₁ c
    have hv0 : 0 ≤ v₀ := by rw [hv₀]; positivity
    have hneg := hs6Qbv_neg (m := (v₀ + b₁) / 2) (t := d) (H := H₁) (c := c)
      (by linarith) hd0 (by linarith) (by linarith)
    have := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hb₁) hneg.le
    linarith
  -- (iv) the chord in `c`
  have s4 : hs6Qb v₀ d H₁ c * (3 / 8) ≤
      (3 - c) * hs6Qb v₀ d H₁ (21 / 8) + (c - 21 / 8) * hs6Qb v₀ d H₁ 3 := by
    have e : hs6Qb v₀ d H₁ c * (3 / 8) - ((3 - c) * hs6Qb v₀ d H₁ (21 / 8) +
        (c - 21 / 8) * hs6Qb v₀ d H₁ 3) = -(3 / 8 * (d ^ 2 * (c - 21 / 8) * (3 - c))) := by
      unfold hs6Qb; ring
    have := mul_nonneg (mul_nonneg (sq_nonneg d) (sub_nonneg.2 hc)) (sub_nonneg.2 hc')
    linarith
  -- (v) the two endpoint polynomials
  have hp : ∀ k : ℕ, R ^ k ≤ (7 / 17) ^ k := fun k => pow_le_pow_left₀ hR.le hR7 k
  have hR3 : 0 < 3 + R ^ 2 := by positivity
  have e1 : hs6Qb v₀ d H₁ (21 / 8) * (90000 * (R ^ 2 + 3) ^ 2) = R ^ 2 *
      (784 * R ^ 10 + 23912 * R ^ 8 + 4200 * R ^ 7 + 270529 * R ^ 6 + 116970 * R ^ 5 +
        1350675 * R ^ 4 + 1043280 * R ^ 3 + 2037375 * R ^ 2 + 2976750 * R - 1941975) := by
    rw [hv₀, hd, hH₁]; unfold hs6Qb; field_simp; ring
  have e2 : hs6Qb v₀ d H₁ 3 * (90000 * (R ^ 2 + 3) ^ 2) = R ^ 2 *
      (784 * R ^ 10 + 23912 * R ^ 8 + 6720 * R ^ 7 + 270529 * R ^ 6 + 162960 * R ^ 5 +
        1359450 * R ^ 4 + 1300320 * R ^ 3 + 2019825 * R ^ 2 + 3402000 * R - 2073600) := by
    rw [hv₀, hd, hH₁]; unfold hs6Qb; field_simp; ring
  have p1 : 784 * R ^ 10 + 23912 * R ^ 8 + 4200 * R ^ 7 + 270529 * R ^ 6 + 116970 * R ^ 5 +
      1350675 * R ^ 4 + 1043280 * R ^ 3 + 2037375 * R ^ 2 + 2976750 * R - 1941975 < 0 := by
    linarith [hp 10, hp 8, hp 7, hp 6, hp 5, hp 4, hp 3, hp 2]
  have p2 : 784 * R ^ 10 + 23912 * R ^ 8 + 6720 * R ^ 7 + 270529 * R ^ 6 + 162960 * R ^ 5 +
      1359450 * R ^ 4 + 1300320 * R ^ 3 + 2019825 * R ^ 2 + 3402000 * R - 2073600 < 0 := by
    linarith [hp 10, hp 8, hp 7, hp 6, hp 5, hp 4, hp 3, hp 2]
  have hD : 0 < 90000 * (R ^ 2 + 3) ^ 2 := by positivity
  have q1 : hs6Qb v₀ d H₁ (21 / 8) < 0 := by
    have : hs6Qb v₀ d H₁ (21 / 8) * (90000 * (R ^ 2 + 3) ^ 2) < 0 := by
      rw [e1]; exact mul_neg_of_pos_of_neg (by positivity) p1
    exact neg_of_mul_neg_left this hD.le
  have q2 : hs6Qb v₀ d H₁ 3 < 0 := by
    have : hs6Qb v₀ d H₁ 3 * (90000 * (R ^ 2 + 3) ^ 2) < 0 := by
      rw [e2]; exact mul_neg_of_pos_of_neg (by positivity) p2
    exact neg_of_mul_neg_left this hD.le
  have m1 := mul_le_mul_of_nonneg_left (le_max_left (hs6Qb v₀ d H₁ (21 / 8)) (hs6Qb v₀ d H₁ 3))
    (sub_nonneg.2 hc')
  have m2 := mul_le_mul_of_nonneg_left (le_max_right (hs6Qb v₀ d H₁ (21 / 8)) (hs6Qb v₀ d H₁ 3))
    (sub_nonneg.2 hc)
  have hmax : max (hs6Qb v₀ d H₁ (21 / 8)) (hs6Qb v₀ d H₁ 3) < 0 := max_lt q1 q2
  linarith

/-- The cost-shear identity in the atoms of `HsData.hs6_continuation`: with `J₀ = 3u/(2U₁)` and
`Z = 2U₁Q₀w₀ - P`, `C_br = C_c + J₀h_c - J₀h_a` (`SHEAR_COST_REDUCTION` (7) at the two scales). -/
private lemma hs6_cost_id {u M Q w w0 P E Z J : ℝ} (hM : M ≠ 0) (hJ : J = 3 * u / (2 * M))
    (hZ : Z = 2 * M * Q * w0 - P) :
    √3 * (w * u * Q + E) =
      √3 * (u * Q * w0 + E) + J * -(Z / √3) - J * (√3 / 3 * (P - 2 * M * Q * w)) := by
  have hinv : Z / √3 = √3 / 3 * Z := by
    have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
    have hs0 : √3 ≠ 0 := by positivity
    rw [← mul_div_mul_right Z √3 hs0, h3]; ring
  rw [hinv, hJ, hZ]
  field_simp
  ring

/-- **The continuation core** (`SHEAR_COST_REDUCTION` (10)-(13) on the recommended route): for
`0 ≤ A < K` and shears `h_c < h_a < 0`, if `J₀√(h² + A²) < c sin δ(h)` for every `h ∈ [h_c, h_a]`,
then `δ_a = δ(h_a)` and `δ_c = δ(h_c)` satisfy `0 < δ_a < δ_c` and the score
`F̃(δ) = -J₀h̃(δ) - cδ` decreases from `δ_a` to `δ_c`: `-J₀h_c - cδ_c ≤ -J₀h_a - cδ_a`. -/
private lemma hs6_cont_core {A K J₀ c ha hc : ℝ} (hA : 0 ≤ A) (hK : A < K) (hca : hc < ha)
    (ha0 : ha < 0)
    (hbar : ∀ h, hc ≤ h → h ≤ ha → J₀ * √(h ^ 2 + A ^ 2) <
      c * sin (2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2))))) :
    0 < 2 * arctan ((√(ha ^ 2 + A ^ 2) - ha) / (K + √(K ^ 2 - A ^ 2))) ∧
      2 * arctan ((√(ha ^ 2 + A ^ 2) - ha) / (K + √(K ^ 2 - A ^ 2))) <
        2 * arctan ((√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2))) ∧
      -J₀ * hc - c * (2 * arctan ((√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2)))) ≤
        -J₀ * ha - c * (2 * arctan ((√(ha ^ 2 + A ^ 2) - ha) / (K + √(K ^ 2 - A ^ 2)))) := by
  obtain ⟨a0, aπ, aeq⟩ := hs6_tangent_inv hA hK ha0
  obtain ⟨c0, cπ, ceq⟩ := hs6_tangent_inv hA hK (hca.trans ha0)
  generalize 2 * arctan ((√(ha ^ 2 + A ^ 2) - ha) / (K + √(K ^ 2 - A ^ 2))) = δa at a0 aπ aeq ⊢
  generalize 2 * arctan ((√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2))) = δc at c0 cπ ceq ⊢
  have hanti : ∀ s t, 0 < s → s < t → t < π →
      (K * cos t - √(K ^ 2 - A ^ 2)) / sin t < (K * cos s - √(K ^ 2 - A ^ 2)) / sin s :=
    fun s t h1 h2 h3 => (hs6_tangent_anti hA hK h1 h2 h3).1
  have hac : δa < δc := by
    rcases lt_trichotomy δa δc with h | h | h
    · exact h
    · exfalso; rw [h] at aeq; linarith
    · exfalso; have := hanti δc δa c0 h aπ; linarith
  refine ⟨a0, hac, ?_⟩
  have key := ss_le_of_deriv
    (f := fun s => -(-J₀ * ((K * cos s - √(K ^ 2 - A ^ 2)) / sin s) - c * s))
    (f' := fun s => -((J₀ * √(((K * cos s - √(K ^ 2 - A ^ 2)) / sin s) ^ 2 + A ^ 2) -
      c * sin s) / sin s)) hac.le
    (fun z hz => (hs6_score_deriv hA hK (by linarith [hz.1]) (by linarith [hz.2])).neg)
    (fun z hz => by
      have hz0 : 0 < z := by linarith [hz.1]
      have hzπ : z < π := by linarith [hz.2]
      have hs : 0 < sin z := sin_pos_of_pos_of_lt_pi hz0 hzπ
      have h1 := hanti δa z a0 hz.1 hzπ
      have h2 := hanti z δc hz0 hz.2 cπ
      rw [aeq] at h1
      rw [ceq] at h2
      generalize hhz : (K * cos z - √(K ^ 2 - A ^ 2)) / sin z = h at h1 h2 ⊢
      obtain ⟨d0, dπ, deq⟩ := hs6_tangent_inv hA hK (h1.trans ha0)
      have hdz : 2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2))) = z := by
        generalize 2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2))) = d
          at d0 dπ deq ⊢
        rcases lt_trichotomy d z with hd | hd | hd
        · exfalso; have := hanti d z d0 hd hzπ; linarith
        · exact hd
        · exfalso; have := hanti z d hz0 hd dπ; linarith
      have hb := hbar h h2.le h1.le
      rw [hdz] at hb
      have : (J₀ * √(h ^ 2 + A ^ 2) - c * sin z) / sin z < 0 :=
        div_neg_of_neg_of_pos (by linarith) hs
      linarith)
  beta_reduce at key
  rw [aeq, ceq] at key
  linarith

/-- The alternating `arctan` majorant: `arctan y ≤ y - y³/3 + y⁵/5` for `y ≥ 0`
(`SMALL_SHAPE_COST_EXCLUSION` (13); derivative of the difference `y⁶/(1 + y²)`). -/
private lemma hs6_arctan_quintic {y : ℝ} (hy : 0 ≤ y) : arctan y ≤ y - y ^ 3 / 3 + y ^ 5 / 5 := by
  have h := ss_le_of_deriv (f := fun t => t - t ^ 3 / 3 + t ^ 5 / 5 - arctan t)
    (f' := fun t => t ^ 6 / (1 + t ^ 2)) hy (fun t _ => ?_) (fun t _ => by positivity)
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_zero,
      add_zero, arctan_zero] at h
    linarith
  have := ((((hasDerivAt_id' t).sub ((hasDerivAt_pow 3 t).div_const 3)).add
    ((hasDerivAt_pow 5 t).div_const 5)).sub (hasDerivAt_arctan t))
  refine this.congr_deriv ?_
  have : 0 < 1 + t ^ 2 := by positivity
  field_simp
  push_cast
  ring

/-- **The central angle bound** (`SMALL_SHAPE_COST_EXCLUSION` (9)): for `0 ≤ A < 1/100`, `K > 4`,
`H > 0`: `2 arctan((√(H² + A²) + H)/(K + √(K² - A²))) ≤ (150001/150000)(2H + A²/(2H))/K`. -/
private lemma hs6_omega_le {A K H : ℝ} (hA : 0 ≤ A) (hA1 : A < 1 / 100) (hK : 4 < K) (hH : 0 < H) :
    2 * arctan ((√(H ^ 2 + A ^ 2) + H) / (K + √(K ^ 2 - A ^ 2))) ≤
      150001 / 150000 * (2 * H + A ^ 2 / (2 * H)) / K := by
  have hK0 : 0 < K := by linarith
  have hN0 : 0 < 2 * H + A ^ 2 / (2 * H) := by positivity
  have hnum : √(H ^ 2 + A ^ 2) + H ≤ 2 * H + A ^ 2 / (2 * H) := by
    have : √(H ^ 2 + A ^ 2) ≤ H + A ^ 2 / (2 * H) := by
      rw [Real.sqrt_le_left (by positivity)]
      have e : (H + A ^ 2 / (2 * H)) ^ 2 = H ^ 2 + A ^ 2 + (A ^ 2 / (2 * H)) ^ 2 := by
        field_simp; ring
      rw [e]; nlinarith [sq_nonneg (A ^ 2 / (2 * H))]
    linarith
  have hA2 : A ^ 2 < 1 / 10000 := by nlinarith
  have hKA : A ^ 2 / K < K := by rw [div_lt_iff₀ hK0]; nlinarith
  have hden : 2 * K - A ^ 2 / K ≤ K + √(K ^ 2 - A ^ 2) := by
    have : K - A ^ 2 / K ≤ √(K ^ 2 - A ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      have e : (K - A ^ 2 / K) ^ 2 = K ^ 2 - 2 * A ^ 2 + (A ^ 2 / K) ^ 2 := by field_simp; ring
      rw [e]
      have : (A ^ 2 / K) ^ 2 ≤ A ^ 2 := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        have hAK : A ^ 2 ≤ K ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hAK (sq_nonneg A)]
      linarith
    linarith
  have hD0 : 0 < 2 * K - A ^ 2 / K := by linarith
  have hy0 : 0 ≤ (√(H ^ 2 + A ^ 2) + H) / (K + √(K ^ 2 - A ^ 2)) := by positivity
  have hy : (√(H ^ 2 + A ^ 2) + H) / (K + √(K ^ 2 - A ^ 2)) ≤
      (2 * H + A ^ 2 / (2 * H)) / (2 * K - A ^ 2 / K) :=
    div_le_div₀ hN0.le hnum hD0 hden
  have hfin : 2 * ((2 * H + A ^ 2 / (2 * H)) / (2 * K - A ^ 2 / K)) ≤
      150001 / 150000 * (2 * H + A ^ 2 / (2 * H)) / K := by
    rw [mul_div_assoc', div_le_div_iff₀ hD0 hK0]
    have e : 150001 / 150000 * (2 * H + A ^ 2 / (2 * H)) * (2 * K - A ^ 2 / K) -
        2 * (2 * H + A ^ 2 / (2 * H)) * K =
        (2 * H + A ^ 2 / (2 * H)) * (2 * K ^ 2 - 150001 * A ^ 2) / (150000 * K) := by
      field_simp; ring
    have : 0 ≤ (2 * H + A ^ 2 / (2 * H)) * (2 * K ^ 2 - 150001 * A ^ 2) / (150000 * K) := by
      apply div_nonneg (mul_nonneg hN0.le (by nlinarith)) (by positivity)
    linarith
  linarith [arctan_le_self hy0]

/-- The anisotropy in the angle coordinates: `A = (R² - T²)/(3 + T²)`, i.e. `(1 + A)U₂ = U₁`. -/
private lemma hs6_An_eq {x be al : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    (1 + hsAn x be al) * ((3 + hsTs al be ^ 2) / 4) = (3 + hsRr x ^ 2) / 4 := by
  unfold hsAn hsRr hsTs
  have : 0 < al ^ 2 + al * be + be ^ 2 := by positivity
  field_simp
  ring

/-- **The central score against the polynomial bound** (`SMALL_SHAPE_COST_EXCLUSION` (6)-(15);
inventory HS-S567 S6.3, S6.4): on the box of `hs6_shape`, for `u_q(R, δ) ≤ u ≤ 3/4 + R²/12` with
`u ≤ U₂ = (3 + T_s²)/4`: `𝓕_c(u) > cπ/3 + √3·𝓑(u_q; R, T_s, δ) - 1/800000` (cancellation (8), the
bound (9)-(11) on `ω_c`, the `arctan` majorant, `𝓑_u > 0`). Status: stable. -/
theorem hs6_Fc_gt {x δ al u : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) (hu : hs6uq (hsRr x) δ ≤ u)
    (hu' : u ≤ 3 / 4 + hsRr x ^ 2 / 12) (hu2 : u ≤ (3 + hsTs al (x * (1 + δ)) ^ 2) / 4) :
    161 / 54 * π / 3 + √3 * hs6B (hsRr x) (hsTs al (x * (1 + δ))) δ (hs6uq (hsRr x) δ) -
        1 / 800000 < hs6Fc x (x * (1 + δ)) al u := by
  obtain ⟨hR1, hR2, hT1, hT2, hA0, hA1, -⟩ := hs6_shape hx hx2 hδ hδ2 hal hal'
  obtain ⟨hZL1, hZLZ, hZZU, hZU5⟩ := hs6_central_shear hx hx2 hδ hδ2 hal hal'
  have hx0 : 0 < x := by linarith only [hx]
  have hal0 : 0 < al := by linarith only [hal, hδ]
  have hbe0 : 0 < x * (1 + δ) := by positivity
  have hAeq := hs6_An_eq hx0 hal0 hbe0
  have hU1 : m2U (1 / (1 + x)) = (3 + hsRr x ^ 2) / 4 := by unfold m2U hsRr; field_simp; ring
  have hs3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs3' : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √3 := by positivity
  have hs3g : (17 / 10 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hs3l : √3 < 7 / 4 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hinv : ∀ y : ℝ, y / √3 = √3 * y / 3 := fun y => by
    rw [div_eq_div_iff hs0.ne' (by norm_num)]; linear_combination (-y) * hs3
  -- the fixed angle `ψ`, through the quintic `arctan` majorant
  have hq : ∀ z : ℝ, 0 ≤ z → arctan (z / √3) ≤ √3 * (z - z ^ 3 / 9 + z ^ 5 / 45) / 3 := by
    intro z hz
    have h := hs6_arctan_quintic (div_nonneg hz hs0.le)
    rw [hinv] at h ⊢
    have e : √3 * z / 3 - (√3 * z / 3) ^ 3 / 3 + (√3 * z / 3) ^ 5 / 5 =
        √3 * (z - z ^ 3 / 9 + z ^ 5 / 45) / 3 := by
      linear_combination (-(√3 * z ^ 3) / 81 + √3 * z ^ 5 * (√3 ^ 2 + 3) / 1215) * hs3'
    linarith only [h, e]
  have hψ : hs6psi x (x * (1 + δ)) al ≤ √3 * (hsRr x - hsRr x ^ 3 / 9 + hsRr x ^ 5 / 45 +
      (hsTs al (x * (1 + δ)) - hsTs al (x * (1 + δ)) ^ 3 / 9 + hsTs al (x * (1 + δ)) ^ 5 / 45)) / 3 := by
    rw [hs6psi]
    have h1 := hq (hsRr x) (by linarith only [hR1])
    have h2 := hq (hsTs al (x * (1 + δ))) (by linarith only [hT1])
    linarith only [h1, h2]
  -- the central angle `ω_c`
  have hZ0 : 0 < hs6Z x (x * (1 + δ)) al := by linarith only [hZL1, hZLZ]
  have hH0 : 0 < hs6Z x (x * (1 + δ)) al / √3 := div_pos hZ0 hs0
  have hR0 : 0 ≤ hsRr x := by linarith only [hR1]
  have hu0 : 0 < u := by
    have : 0 ≤ hs6uq (hsRr x) δ - 3 / 4 := by
      unfold hs6uq
      have e : hsRr x ^ 2 - hsRr x * (1 + hsRr x) * δ / 2 + 19 * (1 + hsRr x) ^ 2 * δ ^ 2 / 84 =
          (hsRr x - (1 + hsRr x) * δ / 4) ^ 2 + 55 / 336 * ((1 + hsRr x) * δ) ^ 2 := by ring
      have hb : 0 ≤ hsRr x ^ 2 - hsRr x * (1 + hsRr x) * δ / 2 +
          19 * (1 + hsRr x) ^ 2 * δ ^ 2 / 84 := by rw [e]; positivity
      have hf : 0 ≤ (3 * hsRr x ^ 2 + 10 * hsRr x + 10) / (15 * (2 + hsRr x) ^ 3) := by
        positivity
      have := mul_nonneg hf hb
      linarith only [this]
    linarith only [this, hu]
  have hJ0 : 0 < hs6J0 x u := by rw [hs6J0, hU1]; positivity
  have hJk : hs6J0 x u < 40 / 27 := by
    rw [hs6J0, hU1, div_lt_iff₀ (by positivity)]
    have : (1 / 3) ^ 2 ≤ hsRr x ^ 2 := pow_le_pow_left₀ (by norm_num) hR1 2
    linarith only [this, hu']
  have hK4 : 4 < hs6K x (x * (1 + δ)) al u := by
    rw [hs6K]
    have : 2 < 2 * (40 / 27) / hs6J0 x u := by rw [lt_div_iff₀ hJ0]; linarith only [hJk]
    linarith only [this, hA0]
  have hω := hs6_omega_le hA0 hA1 hK4 hH0
  have hωd : hs6omega x (x * (1 + δ)) al u = 2 * arctan ((√((hs6Z x (x * (1 + δ)) al / √3) ^ 2 +
      hsAn x (x * (1 + δ)) al ^ 2) + hs6Z x (x * (1 + δ)) al / √3) /
        (hs6K x (x * (1 + δ)) al u + √(hs6K x (x * (1 + δ)) al u ^ 2 -
          hsAn x (x * (1 + δ)) al ^ 2))) := rfl
  rw [← hωd] at hω
  -- the cost and the cancellation `J₀K = 2c - 3b/2`
  have hFc : hs6Fc x (x * (1 + δ)) al u = √3 * (u * ((2 * (x * (1 + δ)) * x - x - al * (x * (1 + δ))) /
      (x * (x + 2))) + (hsRr x + hsTs al (x * (1 + δ))) / 2) +
      161 / 54 * (π / 3 - hs6psi x (x * (1 + δ)) al - hs6omega x (x * (1 + δ)) al u) := by
    rw [hs6Fc, hs6Cc]; ring
  have hZd : hs6Z x (x * (1 + δ)) al = 2 * ((3 + hsRr x ^ 2) / 4) * ((2 * (x * (1 + δ)) * x - x -
      al * (x * (1 + δ))) / (x * (x + 2))) - hsRr x - (1 + hsAn x (x * (1 + δ)) al) *
        hsTs al (x * (1 + δ)) := by rw [hs6Z, hU1]; ring
  have hKd : hs6K x (x * (1 + δ)) al u = hsAn x (x * (1 + δ)) al + 2 + 2 * (40 / 27) / hs6J0 x u := rfl
  have hJd : hs6J0 x u = 3 * u / (2 * ((3 + hsRr x ^ 2) / 4)) := by rw [hs6J0, hU1]
  have hB : hs6B (hsRr x) (hsTs al (x * (1 + δ))) δ (hs6uq (hsRr x) δ) ≤
      hs6B (hsRr x) (hsTs al (x * (1 + δ))) δ u := by
    unfold hs6B
    have hU1p : 0 < (3 + hsRr x ^ 2) / 4 := by positivity
    have hU2p : 0 < (3 + hsTs al (x * (1 + δ)) ^ 2) / 4 := by positivity
    have hZU0 : 0 ≤ hs6ZU (hsRr x) δ := by linarith only [hZL1, hZLZ, hZZU]
    have e1 : hs6uq (hsRr x) δ / ((3 + hsRr x ^ 2) / 4) ≤ u / ((3 + hsRr x ^ 2) / 4) :=
      div_le_div_of_nonneg_right hu hU1p.le
    have e2 : hs6uq (hsRr x) δ / ((3 + hsTs al (x * (1 + δ)) ^ 2) / 4) ≤
        u / ((3 + hsTs al (x * (1 + δ)) ^ 2) / 4) := div_le_div_of_nonneg_right hu hU2p.le
    have e3 := mul_le_mul_of_nonneg_left e1 (by linarith only [hR1] : (0 : ℝ) ≤ hsRr x)
    have e4 := mul_le_mul_of_nonneg_left e2 (by linarith only [hT1] : (0 : ℝ) ≤ hsTs al (x * (1 + δ)))
    have e5 := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hZU0
    linarith only [e3, e4, e5]
  -- generalize to atoms
  rw [hFc]
  rw [hZd] at hZ0 hH0 hω hZLZ hZZU
  rw [hKd, hJd] at hω hK4
  rw [hJd] at hJ0 hJk
  have hAq : hsAn x (x * (1 + δ)) al = (3 + hsRr x ^ 2) / (3 + hsTs al (x * (1 + δ)) ^ 2) - 1 := by
    have : 0 < 3 + hsTs al (x * (1 + δ)) ^ 2 := by positivity
    field_simp; linarith only [hAeq]
  -- pass to atoms
  have hBu : hs6B (hsRr x) (hsTs al (x * (1 + δ))) δ u = hs6L (hsRr x) + hs6L (hsTs al (x * (1 + δ))) -
      ((1 - u / ((3 + hsRr x ^ 2) / 4)) * hsRr x + (1 - u / ((3 + hsTs al (x * (1 + δ)) ^ 2) / 4)) *
        hsTs al (x * (1 + δ))) / 2 - ((1 - u / ((3 + hsRr x ^ 2) / 4)) +
          (1 - u / ((3 + hsTs al (x * (1 + δ)) ^ 2) / 4))) * hs6ZU (hsRr x) δ / 8 -
      161 / 54 * hsAn x (x * (1 + δ)) al ^ 2 / (8 * hs6ZL (hsRr x) δ) := by
    rw [hs6B, hAq]
  rw [hBu] at hB
  clear hFc hZd hKd hJd hωd hBu hAeq
  generalize hs6psi x (x * (1 + δ)) al = ψ at *
  generalize hs6omega x (x * (1 + δ)) al u = ω at *
  generalize hs6B (hsRr x) (hsTs al (x * (1 + δ))) δ (hs6uq (hsRr x) δ) = Bq at *
  generalize (2 * (x * (1 + δ)) * x - x - al * (x * (1 + δ))) / (x * (x + 2)) = W at *
  generalize hs6ZU (hsRr x) δ = ZU at *
  generalize hs6ZL (hsRr x) δ = ZL at *
  generalize hsAn x (x * (1 + δ)) al = A at *
  generalize hsTs al (x * (1 + δ)) = T at *
  generalize hsRr x = R at *
  set Z := 2 * ((3 + R ^ 2) / 4) * W - R - (1 + A) * T with hZ
  set J := 3 * u / (2 * ((3 + R ^ 2) / 4)) with hJ
  set K := A + 2 + 2 * (40 / 27) / J with hK
  have hU1 : 0 < (3 + R ^ 2) / 4 := by positivity
  have hU2 : 0 < (3 + T ^ 2) / 4 := by positivity
  have hT3 : 0 < 3 + T ^ 2 := by positivity
  -- the cancellation `JK = 2c - 3b/2`
  have hJK : J * K = 161 / 27 - 3 / 2 * ((1 - u / ((3 + R ^ 2) / 4)) + (1 - u / ((3 + T ^ 2) / 4))) := by
    rw [hK, hJ, hAq]; field_simp; ring
  -- the cost split `C_c = (√3/2){(1 + a₁)R + (1 + a₂)T} + J·√3Z/3`
  have hC : √3 * (u * W + (R + T) / 2) = √3 / 2 * ((2 - (1 - u / ((3 + R ^ 2) / 4))) * R +
      (2 - (1 - u / ((3 + T ^ 2) / 4))) * T) + J * (√3 * Z / 3) := by
    rw [hJ, hZ, hAq]; field_simp; ring
  -- the angle `ω`, in the form `N = √3(2Z/3 + A²/(2Z))`
  have hZ0' : 0 < Z := by linarith only [hZL1, hZLZ]
  have hN : 2 * (Z / √3) + A ^ 2 / (2 * (Z / √3)) = √3 * (2 * Z / 3 + A ^ 2 / (2 * Z)) := by
    rw [hinv Z]; field_simp; linear_combination (-3 * A ^ 2) * hs3'
  rw [hN] at hω
  have hJ0' : 0 < J := hJ0
  have hK0 : 0 < K := by linarith only [hK4]
  -- the excess factor contributes less than `1/800000`
  have hN0 : 0 < 2 * Z / 3 + A ^ 2 / (2 * Z) := by positivity
  have hNub : √3 * (2 * Z / 3 + A ^ 2 / (2 * Z)) ≤ 7 / 4 * (2 / 15 + 9 / 20000) := by
    have h1 : A ^ 2 / (2 * Z) ≤ 9 / 20000 := by
      rw [div_le_iff₀ (by positivity)]
      have : A ^ 2 ≤ (1 / 100) ^ 2 := pow_le_pow_left₀ hA0 hA1.le 2
      linarith only [this, hZL1, hZLZ]
    have h2 : 2 * Z / 3 + A ^ 2 / (2 * Z) ≤ 2 / 15 + 9 / 20000 := by
      linarith only [h1, hZZU, hZU5]
    have := mul_le_mul hs3l.le h2 hN0.le (by norm_num)
    linarith only [this]
  have hexc : 161 / 54 * (√3 * (2 * Z / 3 + A ^ 2 / (2 * Z))) / (150000 * K) < 1 / 800000 := by
    rw [div_lt_iff₀ (by positivity)]
    linarith only [hNub, hK4]
  have hωK : 161 / 54 * ω ≤ 161 / 54 * (√3 * (2 * Z / 3 + A ^ 2 / (2 * Z))) / K +
      161 / 54 * (√3 * (2 * Z / 3 + A ^ 2 / (2 * Z))) / (150000 * K) := by
    have e : 161 / 54 * (150001 / 150000 * (√3 * (2 * Z / 3 + A ^ 2 / (2 * Z))) / K) =
        161 / 54 * (√3 * (2 * Z / 3 + A ^ 2 / (2 * Z))) / K +
          161 / 54 * (√3 * (2 * Z / 3 + A ^ 2 / (2 * Z))) / (150000 * K) := by
      field_simp; ring
    have := mul_le_mul_of_nonneg_left hω (by norm_num : (0 : ℝ) ≤ 161 / 54)
    linarith only [this, e]
  -- `J·√3Z/3 - c N/K = -(√3/K)(bZ/2 + cA²/(2Z)) ≥ -(√3/8)(bZ + cA²/Z)`
  set b := (1 - u / ((3 + R ^ 2) / 4)) + (1 - u / ((3 + T ^ 2) / 4)) with hb
  have hb0 : 0 ≤ b := by
    have h1 : u / ((3 + R ^ 2) / 4) ≤ 1 := by
      rw [div_le_one hU1]; linarith only [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 3) hR1 2, hu']
    have h2 : u / ((3 + T ^ 2) / 4) ≤ 1 := by rw [div_le_one hU2]; exact hu2
    rw [hb]; linarith only [h1, h2]
  have hcancel : J * (√3 * Z / 3) - 161 / 54 * (√3 * (2 * Z / 3 + A ^ 2 / (2 * Z))) / K =
      -(√3 / K * (b * Z / 2 + 161 / 54 * A ^ 2 / (2 * Z))) := by
    have e : J = (161 / 27 - 3 / 2 * b) / K := by rw [eq_div_iff hK0.ne']; exact hJK
    rw [e]; field_simp; ring
  have hX0 : 0 ≤ b * Z / 2 + 161 / 54 * A ^ 2 / (2 * Z) := by positivity
  have hdiv : √3 / K * (b * Z / 2 + 161 / 54 * A ^ 2 / (2 * Z)) ≤
      √3 / 4 * (b * Z / 2 + 161 / 54 * A ^ 2 / (2 * Z)) := by
    apply mul_le_mul_of_nonneg_right _ hX0
    exact div_le_div_of_nonneg_left hs0.le (by norm_num) hK4.le
  have hZb : b * Z ≤ b * ZU := mul_le_mul_of_nonneg_left hZZU hb0
  have hAZ : A ^ 2 / Z ≤ A ^ 2 / ZL := div_le_div_of_nonneg_left (sq_nonneg A) (by linarith only [hZL1]) hZLZ
  have hfin : √3 / 4 * (b * Z / 2 + 161 / 54 * A ^ 2 / (2 * Z)) ≤
      √3 / 8 * (b * ZU + 161 / 54 * (A ^ 2 / ZL)) := by
    have e : √3 / 4 * (b * Z / 2 + 161 / 54 * A ^ 2 / (2 * Z)) =
        √3 / 8 * (b * Z + 161 / 54 * (A ^ 2 / Z)) := by field_simp; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [hZb, hAZ]
  -- assemble
  have hψc : 161 / 54 * ψ ≤ 161 / 54 * (√3 * (R - R ^ 3 / 9 + R ^ 5 / 45 +
      (T - T ^ 3 / 9 + T ^ 5 / 45)) / 3) := by linarith only [hψ]
  have hL : √3 / 2 * ((2 - (1 - u / ((3 + R ^ 2) / 4))) * R + (2 - (1 - u / ((3 + T ^ 2) / 4))) * T) -
      161 / 54 * (√3 * (R - R ^ 3 / 9 + R ^ 5 / 45 + (T - T ^ 3 / 9 + T ^ 5 / 45)) / 3) -
      √3 / 8 * (b * ZU + 161 / 54 * (A ^ 2 / ZL)) =
      √3 * (hs6L R + hs6L T - ((1 - u / ((3 + R ^ 2) / 4)) * R +
        (1 - u / ((3 + T ^ 2) / 4)) * T) / 2 - b * ZU / 8 - 161 / 54 * A ^ 2 / (8 * ZL)) := by
    rw [hb]; unfold hs6L; field_simp; ring
  have hBq : √3 * Bq ≤ √3 * (hs6L R + hs6L T - ((1 - u / ((3 + R ^ 2) / 4)) * R +
      (1 - u / ((3 + T ^ 2) / 4)) * T) / 2 - b * ZU / 8 - 161 / 54 * A ^ 2 / (8 * ZL)) := by
    exact mul_le_mul_of_nonneg_left hB hs0.le
  rw [hC]
  set N := √3 * (2 * Z / 3 + A ^ 2 / (2 * Z)) with hNdef
  set S := R - R ^ 3 / 9 + R ^ 5 / 45 + (T - T ^ 3 / 9 + T ^ 5 / 45) with hSdef
  set X := b * Z / 2 + 161 / 54 * A ^ 2 / (2 * Z) with hXdef
  set Y := b * ZU + 161 / 54 * (A ^ 2 / ZL) with hYdef
  set P := √3 / 2 * ((2 - (1 - u / ((3 + R ^ 2) / 4))) * R + (2 - (1 - u / ((3 + T ^ 2) / 4))) * T)
    with hPdef
  have s2 : -(√3 / 8 * Y) ≤ J * (√3 * Z / 3) - 161 / 54 * N / K := by
    linarith only [hcancel, hdiv, hfin]
  have s3 : √3 * Bq ≤ P - 161 / 54 * (√3 * S / 3) - √3 / 8 * Y := by
    linarith only [hL, hBq]
  linarith only [hψc, hωK, hexc, s2, s3]

/-- The angle coordinate on the box in the variables `(R, δ, η)` (`SMALL_SHAPE_COST_EXCLUSION` (21)):
for `x > 1`, `δ ≥ 0`, `T_s(1 + ηδ, x(1 + δ)) = hs6T R δ η`, `R = (x - 1)/(x + 1)`. Status: stable. -/
theorem hs6_T_eq {x δ η : ℝ} (hx : 1 < x) (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    hsTs (1 + η * δ) (x * (1 + δ)) = hs6T (hsRr x) δ η := by
  have hx1 : 0 < x + 1 := by linarith
  have h1 : 0 < x * (1 + δ) + (1 + η * δ) := by nlinarith
  have h2 : hs6T (hsRr x) δ η = 2 * (x * (1 + δ) - (1 + η * δ)) / (x + 1) /
      (2 * (x * (1 + δ) + (1 + η * δ)) / (x + 1)) := by
    unfold hs6T hsRr
    congr 1 <;> field_simp <;> ring
  rw [h2, div_div_div_cancel_right₀ hx1.ne', hsTs, mul_div_mul_left _ _ (two_ne_zero)]

/-- **Concavity in `T` removes `η`** (`SMALL_SHAPE_COST_EXCLUSION` (16)-(19); inventory HS-S567
S6.5): for `1/3 ≤ R ≤ 7/19`, `0 ≤ δ ≤ 1/19`, `13/5 ≤ η ≤ 3`: `𝓑(u_q; R, T(η), δ) ≥
min{𝓑(u_q; R, T(13/5), δ), 𝓑(u_q; R, T(3), δ)}`. Status: stable. -/
theorem hs6_B_concave {R δ η : ℝ} (hR : 1 / 3 ≤ R) (hR' : R ≤ 7 / 19) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hη : 13 / 5 ≤ η) (hη' : η ≤ 3) :
    min (hs6B R (hs6T R δ (13 / 5)) δ (hs6uq R δ)) (hs6B R (hs6T R δ 3) δ (hs6uq R δ)) ≤
      hs6B R (hs6T R δ η) δ (hs6uq R δ) := by
  have hR0 : 0 < R := by linarith
  have hR1 : R < 1 := by linarith
  -- `T(e) = N(e)/D(e)` decreases in `e`, `9/31 ≤ T(3)`, `T(13/5) ≤ R`
  have hD : ∀ e : ℝ, 1 ≤ e → 0 < 2 + (e + 1 - (e - 1) * R) * δ := fun e he => by
    have : 0 ≤ (e - 1) * (1 - R) := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ (e + 1 - (e - 1) * R) * δ := mul_nonneg (by nlinarith) hδ
    linarith
  have hmono : ∀ a b : ℝ, 1 ≤ a → a ≤ b → hs6T R δ b ≤ hs6T R δ a := fun a b ha hab => by
    unfold hs6T
    rw [div_le_div_iff₀ (hD b (by linarith)) (hD a ha)]
    have : 0 ≤ 2 * δ * (1 - R) * (1 + R) * (b - a) * (1 + δ) := by
      have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ)
        (by linarith : (0 : ℝ) ≤ 1 - R)) (by linarith : (0 : ℝ) ≤ 1 + R)) (by linarith : (0 : ℝ) ≤ b - a))
        (by linarith : (0 : ℝ) ≤ 1 + δ)
      exact this
    nlinarith
  have hT3 : 9 / 31 ≤ hs6T R δ 3 := by
    unfold hs6T
    rw [le_div_iff₀ (hD 3 (by norm_num))]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 19 - δ) (by linarith : (0 : ℝ) ≤ 49 - 71 * R)]
  have hT13 : hs6T R δ (13 / 5) ≤ 7 / 19 := by
    unfold hs6T
    rw [div_le_iff₀ (hD (13 / 5) (by norm_num))]
    have : 0 ≤ δ * (1 - R) * (1 + R) * (13 / 5 - 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg hδ (by linarith)) (by linarith)) (by norm_num)
    nlinarith
  -- the incoming floor and the shear bounds at fixed `R, δ`
  have hu : 3 / 4 ≤ hs6uq R δ := by
    unfold hs6uq
    have e : R ^ 2 - R * (1 + R) * δ / 2 + 19 * (1 + R) ^ 2 * δ ^ 2 / 84 =
        (R - (1 + R) * δ / 4) ^ 2 + 55 / 336 * ((1 + R) * δ) ^ 2 := by ring
    have hb : 0 ≤ R ^ 2 - R * (1 + R) * δ / 2 + 19 * (1 + R) ^ 2 * δ ^ 2 / 84 := by
      rw [e]; positivity
    have hf : 0 ≤ (3 * R ^ 2 + 10 * R + 10) / (15 * (2 + R) ^ 3) := by positivity
    have := mul_nonneg hf hb
    linarith
  have hZL : 0 < hs6ZL R δ := by
    unfold hs6ZL
    have : 0 < 3 - R := by linarith
    positivity
  have hZU : 0 ≤ hs6ZU R δ := by
    unfold hs6ZU
    have h1 : 0 < 3 - R := by linarith
    have h2 : 0 < 1 - R := by linarith
    have h3 : 1 / 27 ≤ 2 * R ^ 2 * (1 + R) / (3 - R) := by
      rw [le_div_iff₀ h1]; nlinarith
    have h4 : 0 ≤ (1 + 2 * R) / (3 * (1 - R)) * δ := by positivity
    have h5 : δ ^ 2 ≤ (1 / 19) ^ 2 := pow_le_pow_left₀ hδ hδ2 2
    linarith
  have hconc := hs6_B_concaveOn hR hR' hu hZU hZL
  have hmem : ∀ e : ℝ, 13 / 5 ≤ e → e ≤ 3 → hs6T R δ e ∈ Icc (9 / 31 : ℝ) (7 / 19) := fun e h1 h2 =>
    ⟨hT3.trans (hmono e 3 (by linarith) h2), (hmono (13 / 5) e (by norm_num) h1).trans hT13⟩
  have h := hconc.min_le_of_mem_Icc (hmem 3 (by norm_num) le_rfl) (hmem (13 / 5) le_rfl (by norm_num))
    ⟨hmono η 3 (by linarith) hη', hmono (13 / 5) η (by norm_num) hη⟩
  rw [min_comm]
  exact h

/-- **The two endpoint polynomials** (`SMALL_SHAPE_COST_EXCLUSION` (20)-(31); inventory HS-S567
S6.6, S6.7): for `1/3 ≤ R ≤ 7/19`, `0 ≤ δ ≤ 1/19` and `e ∈ {13/5, 3}`:
`𝓑(u_q; R, T(e), δ) > b*`. Status: heavy, by hand (`Heavy/S6Hand`: concavity in `R`, then
monotonicity in `δ`, `SHORT_COST_CONCAVITY`). -/
theorem hs6_B_endpoint {R δ e : ℝ} (hR : 1 / 3 ≤ R) (hR' : R ≤ 7 / 19) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (he : e = 13 / 5 ∨ e = 3) :
    hs6bstar < hs6B R (hs6T R δ e) δ (hs6uq R δ) := by
  apply hs6_B_endpoint_proof <;> assumption

/-- **The constants** (`SMALL_SHAPE_COST_EXCLUSION` §7; inventory HS-S567 S6.8):
`A_oct < 3126055/10⁶`, `π > 314159265/10⁸`, `√3 > 989/571`. Status: stable. -/
theorem hs6_constants :
    octagonCost < 3126055 / 1000000 ∧ (314159265 / 100000000 : ℝ) < π ∧ (989 / 571 : ℝ) < √3 := by
  refine ⟨?_, by linarith [Real.pi_gt_d20], by rw [Real.lt_sqrt (by norm_num)]; norm_num⟩
  have h12 : √12 < 3464101616 / 1000000000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h32 : 5656854249 / 1000000000 < √32 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h8 : 2828427124 / 1000000000 < √8 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hl := Real.log_two_gt_d9
  have hD : 0 < √8 - 1 := by linarith
  have hN : 0 ≤ 8 - √32 - Real.log 2 := by
    have : √32 < 5.6569 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have := Real.log_two_lt_d9
    linarith
  rw [octagonCost, octagonDensity, mul_div_assoc', div_lt_iff₀ hD]
  have : √12 * (8 - √32 - Real.log 2) ≤ 3464101616 / 1000000000 * (8 - √32 - Real.log 2) :=
    mul_le_mul_of_nonneg_right h12.le hN
  nlinarith

/-! ### Actual-data leaves and gate S6 -/

namespace HsData

variable (H : HsData)

/-- The cover's incoming norm at the normalized point. -/
private lemma hs6_pt_u : H.pt.u = H.u := H.pt_u

/-- The cover's `x` at the normalized point. -/
private lemma hs6_pt_x : H.pt.x = H.x := by
  have := H.one_lt_x
  simp only [HsData.pt, Point.x]
  field_simp
  ring

/-- The cover's `β` at the normalized point. -/
private lemma hs6_pt_be : H.pt.be = H.be := by
  have := H.one_lt_x
  rw [Point.be, H.hs6_pt_x]
  simp only [HsData.pt]
  field_simp
  ring

/-- The cover's Casimir at the normalized point is `Γ`. -/
private lemma hs6_pt_gam : H.pt.gam = H.Γ := by
  rw [Point.gam, H.hs6_pt_u, H.Γ_eq, hsGam]
  rfl

/-- The window cost at the normalized point (`Point.cost`). -/
private lemma hs6_pt_cost : H.pt.cost = √3 * (H.rho * H.u / (1 - H.rho) *
    (2 * H.be * H.x - H.x - H.al * H.be) + (H.be * H.x - H.al) / ((1 + H.x) * (H.al + H.be))) := by
  rw [Point.cost, H.hs6_pt_u, Point.S, Point.A, H.hs6_pt_x, H.hs6_pt_be]
  rfl

/-- **The angle bound at `κ₀`** (`ROOT_AND_ANGLE_REDUCTION` (14)-(25), `MIXED_GENERAL_SHORT_DEFECT_INTERFACE`
(5)-(8); inventory HS-S567 AC.1, AB1, AB2, AL): for actual data with `40/27 ≤ κ = pt.kap`,
`K = A + 2 + 2κ₀/J₀`, `h` the actual shear, and `0 < δ < π/2 - ψ` with
`K sin δ + h cos δ ≥ √(A² + h²)`: `θ_br = arctan(√3ℬ/𝒜) ≤ ψ + δ`. Status: stable.
Route: the angle-circle comparison is replaced by the rotated trace identity and the
quadratic-in-`ξ` bound of `Hs6.Angle` (`hs6_angle_core`), as the inventory recommends. -/
theorem hs6_angle (hκ : 40 / 27 ≤ H.pt.kap) {δ : ℝ} (hδ : 0 < δ)
    (hδψ : δ < π / 2 - hs6psi H.x H.be H.al)
    (hsup : √(hsAn H.x H.be H.al ^ 2 + hsShear H.x H.be H.al H.rho ^ 2) ≤
      hs6K H.x H.be H.al H.u * sin δ + hsShear H.x H.be H.al H.rho * cos δ) :
    arctan (√3 * H.pt.BB / H.pt.AA) ≤ hs6psi H.x H.be H.al + δ := by
  have hx1 := H.one_lt_x
  have hal0 : 0 < H.al := by linarith [H.one_le_al]
  have hbe0 : 0 < H.be := by linarith [H.x_le_be]
  have hρ0 := H.rho_pos
  have hρ1 : H.rho < 1 := by linarith [H.rho_le]
  have hu0 : 0 < H.u := by linarith [H.u_ge_34]
  have hk0 : 0 < H.pt.kap := by linarith
  have halx := H.al_lt_x
  have hxbe := H.x_le_be
  -- `ψ = arctan(√3μ/n)`, `μ = βx - α`, `n = (2x + 1)α + (x + 2)β`
  set μ := H.be * H.x - H.al with hμ
  set n := (2 * H.x + 1) * H.al + (H.x + 2) * H.be with hn
  have hμ0 : 0 < μ := by rw [hμ]; nlinarith
  have hn0 : 0 < n := by rw [hn]; positivity
  have hs3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < √3 := by positivity
  have hR0 : 0 ≤ hsRr H.x := by unfold hsRr; exact div_nonneg (by linarith) (by linarith)
  have hR1 : hsRr H.x < 1 := by unfold hsRr; rw [div_lt_one (by linarith)]; linarith
  have hT0 : 0 ≤ hsTs H.al H.be := by unfold hsTs; exact div_nonneg (by linarith) (by linarith)
  have hT1 : hsTs H.al H.be < 1 := by unfold hsTs; rw [div_lt_one (by linarith)]; linarith
  have hRT : hsRr H.x * hsTs H.al H.be < 3 := by
    have := mul_le_mul hR1.le hT1.le hT0 (by norm_num)
    linarith
  have hprod : hsRr H.x / √3 * (hsTs H.al H.be / √3) = hsRr H.x * hsTs H.al H.be / 3 := by
    rw [div_mul_div_comm, hs3]
  have hψ : hs6psi H.x H.be H.al = arctan (√3 * μ / n) := by
    rw [hs6psi, arctan_add (by rw [hprod]; linarith)]
    congr 1
    have e1 : (hsRr H.x + hsTs H.al H.be) / (3 - hsRr H.x * hsTs H.al H.be) = μ / n := by
      unfold hsRr hsTs
      rw [hμ, hn]
      have h1 : 0 < H.x + 1 := by linarith
      have h2 : 0 < H.be + H.al := by linarith
      rw [div_eq_div_iff (by unfold hsRr hsTs at hRT; linarith) hn0.ne']
      field_simp
      ring
    have hsum : hsRr H.x / √3 + hsTs H.al H.be / √3 = √3 * (hsRr H.x + hsTs H.al H.be) / 3 := by
      rw [← add_div, div_eq_div_iff hs0.ne' (by norm_num)]
      linear_combination (-(hsRr H.x + hsTs H.al H.be)) * hs3
    rw [hprod, hsum]
    have h3 : (0 : ℝ) < 3 - hsRr H.x * hsTs H.al H.be := by linarith
    calc √3 * (hsRr H.x + hsTs H.al H.be) / 3 / (1 - hsRr H.x * hsTs H.al H.be / 3) =
        √3 * ((hsRr H.x + hsTs H.al H.be) / (3 - hsRr H.x * hsTs H.al H.be)) := by
          field_simp
      _ = √3 * μ / n := by rw [e1]; ring
  -- `0 < ψ`, `0 < δ < π/2`
  have hy0 : 0 < √3 * μ / n := by positivity
  have hψ0 : 0 < hs6psi H.x H.be H.al := by rw [hψ]; exact arctan_pos.2 hy0
  have hδπ : δ < π := by linarith [Real.pi_pos]
  have hsδ : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ hδπ
  -- raise `κ₀` to `κ` in the supporting line
  have hU0 : 0 < m2U (1 / (1 + H.x)) := by
    unfold m2U; have : 0 < 1 / (1 + H.x) := by positivity
    nlinarith [sq_nonneg (1 / (1 + H.x) - 1 / 2)]
  have hJ0 : 0 < 3 * H.u / (2 * m2U (1 / (1 + H.x))) := by positivity
  have hsup' : √(hsAn H.x H.be H.al ^ 2 + hsShear H.x H.be H.al H.rho ^ 2) ≤
      (hsAn H.x H.be H.al + 2 + 2 * H.pt.kap / (3 * H.u / (2 * m2U (1 / (1 + H.x))))) * sin δ +
        hsShear H.x H.be H.al H.rho * cos δ := by
    have h1 : 2 * (40 / 27) / (3 * H.u / (2 * m2U (1 / (1 + H.x)))) ≤
        2 * H.pt.kap / (3 * H.u / (2 * m2U (1 / (1 + H.x)))) :=
      div_le_div_of_nonneg_right (by linarith) hJ0.le
    have h2 := mul_le_mul_of_nonneg_right h1 hsδ.le
    have e : hs6K H.x H.be H.al H.u = hsAn H.x H.be H.al + 2 +
        2 * (40 / 27) / (3 * H.u / (2 * m2U (1 / (1 + H.x)))) := rfl
    rw [e] at hsup
    linarith
  have core : √3 * cos δ * (n * H.pt.BB - μ * H.pt.AA) - sin δ * (n * H.pt.AA + 3 * μ * H.pt.BB) ≤ 0 :=
    hs6_angle_core hx1 hal0 hbe0 hρ0 hρ1 hu0 H.pt_u hk0 hsδ hsup'
  -- the defect data
  obtain ⟨-, hB0, hBA, -, -⟩ : 2 * H.pt.Tk ≤ H.pt.AA ∧ 0 < H.pt.BB ∧ H.pt.BB < H.pt.AA ∧
      4 * H.pt.Tk ≤ H.pt.AA + H.pt.BB ∧
      H.pt.cost + (H.pt.kap + 3 / 2) * (π / 3 - arctan (√3 * H.pt.BB / H.pt.AA)) ≤ octagonCost :=
    H.defect
  have hA0 : 0 < H.pt.AA := hB0.trans hBA
  -- `√3ℬ cos(ψ + δ) ≤ 𝒜 sin(ψ + δ)`
  have hq : 0 < √(1 + (√3 * μ / n) ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hcos : 0 < cos (hs6psi H.x H.be H.al + δ) :=
    cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hkey : √3 * H.pt.BB * cos (hs6psi H.x H.be H.al + δ) ≤
      H.pt.AA * sin (hs6psi H.x H.be H.al + δ) := by
    rw [cos_add, sin_add, hψ, cos_arctan, sin_arctan]
    have e : √3 * H.pt.BB * (1 / √(1 + (√3 * μ / n) ^ 2) * cos δ -
        √3 * μ / n / √(1 + (√3 * μ / n) ^ 2) * sin δ) -
        H.pt.AA * (√3 * μ / n / √(1 + (√3 * μ / n) ^ 2) * cos δ +
          1 / √(1 + (√3 * μ / n) ^ 2) * sin δ) =
        (√3 * cos δ * (n * H.pt.BB - μ * H.pt.AA) - sin δ * (n * H.pt.AA + 3 * μ * H.pt.BB)) /
          (n * √(1 + (√3 * μ / n) ^ 2)) := by
      field_simp
      linear_combination (-(sin δ * μ * H.pt.BB)) * hs3
    have : (√3 * cos δ * (n * H.pt.BB - μ * H.pt.AA) - sin δ * (n * H.pt.AA + 3 * μ * H.pt.BB)) /
        (n * √(1 + (√3 * μ / n) ^ 2)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg core (by positivity)
    linarith
  have htan : √3 * H.pt.BB / H.pt.AA ≤ tan (hs6psi H.x H.be H.al + δ) := by
    rw [tan_eq_sin_div_cos, div_le_div_iff₀ hA0 hcos]
    linarith
  calc arctan (√3 * H.pt.BB / H.pt.AA) ≤ arctan (tan (hs6psi H.x H.be H.al + δ)) :=
        arctan_le_arctan_iff.2 htan
    _ = hs6psi H.x H.be H.al + δ := arctan_tan (by linarith) (by linarith)

/-- **The continuation to the central scale** (`SMALL_SHAPE_COST_EXCLUSION` (3)-(5); inventory HS-S567
S6.1, S6.2, recommended route): on the small-shape domain, with `Γ > 1829/10000`, `h < 0`,
`-hR > 5A/2`: `C_br + (κ + 3/2)(π/3 - θ_br) ≥ 𝓕_c(u)` (`hs6_kappa`, `hs6_angle` at `δ_a = δ(h)`,
`hs6_tangent_inv`, `hs6_tangent_anti`, the cost-shear identity `C_br = H₀ - J₀h`, `hs6_score_deriv`
with `hs6_barrier_sin`, `hs6_barrier` pointwise on `[δ_a, δ_c]` (`hs6_shape`, `hs6_u_bounds`,
`hs6_central_shear`, `q_le_qc`)). Status: stable.
Route: the inventory's recommended route (no critical-angle classification; the barrier holds
pointwise along `[δ_a, δ_c]` because `H ≤ H_c = Z/√3 < 7R²/6`), via `hs6_cont_core`; the outer
cap `ρ_A < 1/7` is not used. -/
theorem hs6_continuation (hS : H.SmallShape) (hΓ : 1829 / 10000 < H.Γ)
    (hh : hsShear H.x H.be H.al H.rho < 0)
    (hhR : 5 / 2 * hsAn H.x H.be H.al < -hsShear H.x H.be H.al H.rho * hsRr H.x) :
    hs6Fc H.x H.be H.al H.u ≤
      H.pt.cost + (H.pt.kap + 3 / 2) * (π / 3 - arctan (√3 * H.pt.BB / H.pt.AA)) := by
  have hx1 := H.one_lt_x
  have hal1 := H.one_le_al
  have halx := H.al_lt_x
  have hxbe := H.x_le_be
  have hρ0 := H.rho_pos
  have hρ320 := H.rho_le
  have hal0 : 0 < H.al := by linarith only [hal1]
  have hbe0 : 0 < H.be := by linarith only [hx1, hxbe]
  have hbe : H.x * (1 + H.δ) = H.be := by unfold HsData.δ; field_simp; ring
  obtain ⟨hx2, hx13, hδ0, hδ19, hal1', hal2'⟩ := hS
  have hal : 13 / 5 * H.δ ≤ H.al - 1 := by linarith only [hal1']
  have hal' : H.al - 1 ≤ 3 * H.δ := by linarith only [hal2']
  obtain ⟨hR1, hR2, hT1, hT2, hA0, hA1, hP⟩ := hs6_shape hx2 hx13 hδ0 hδ19 hal hal'
  obtain ⟨hu1, hu2⟩ := hs6_u_bounds hx2 hx13 hδ0 hδ19 hal hal'
  obtain ⟨hZL, hZLZ, -, hZU⟩ := hs6_central_shear hx2 hx13 hδ0 hδ19 hal hal'
  have hZU' := (hs6_central_shear hx2 hx13 hδ0 hδ19 hal hal').2.2.1
  rw [hbe] at hT1 hT2 hA0 hA1 hP hu1 hu2 hZLZ hZU'
  rw [← H.u_eq] at hu1 hu2
  have hZ1 : 1 / 9 ≤ hs6Z H.x H.be H.al := hZL.trans hZLZ
  have hZ5 : hs6Z H.x H.be H.al < 1 / 5 := lt_of_le_of_lt hZU' hZU
  have hu34 := H.u_ge_34
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3g : (17 / 10 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  -- the incident ceilings `u ≤ U₁`, `u(1 + A) ≤ U₁`
  have hU1 : m2U (1 / (1 + H.x)) = (3 + hsRr H.x ^ 2) / 4 := by
    unfold m2U hsRr; field_simp; ring
  have hU12 : (1 + hsAn H.x H.be H.al) * m2U (hsRA H.al H.be) = m2U (1 / (1 + H.x)) := by
    unfold m2U hsRA hsAn
    have : 0 < H.al ^ 2 + H.al * H.be + H.be ^ 2 :=
      add_pos (add_pos (pow_pos hal0 2) (mul_pos hal0 hbe0)) (pow_pos hbe0 2)
    have : 0 < H.al + H.be := by linarith only [hal0, hbe0]
    have : 0 < H.be + H.al := by linarith only [hal0, hbe0]
    field_simp; ring
  have huA : H.u * (1 + hsAn H.x H.be H.al) ≤ m2U (1 / (1 + H.x)) := by
    rw [← hU12]
    have := mul_le_mul_of_nonneg_left H.u_le_rA (by linarith only [hA0] : 0 ≤ 1 + hsAn H.x H.be H.al)
    linarith only [this]
  have huU := H.u_le_r
  -- the shear at the central scale `h_c = -Z/√3`, below the actual shear
  have hQ0 : 0 < 2 * H.be * H.x - H.x - H.al * H.be := by
    have hq1 := mul_pos (by linarith only [hx1] : (0 : ℝ) < H.x)
      (by linarith only [hx1, hxbe] : (0 : ℝ) < H.be - 1)
    have hq2 := mul_pos hbe0 (by linarith only [halx] : (0 : ℝ) < H.x - H.al)
    linarith only [hq1, hq2]
  have hscale : H.rho / (1 - H.rho) < 1 / (H.x * (H.x + 2)) := by
    have h1 := H.rho_lt_rt
    have h2 := H.t_le_r
    have h3 : H.rho < 1 / (1 + H.x) ^ 2 := by
      calc H.rho < 1 / (1 + H.x) * H.t := h1
        _ ≤ 1 / (1 + H.x) * (1 / (1 + H.x)) := by gcongr
        _ = 1 / (1 + H.x) ^ 2 := by field_simp
    rw [div_lt_div_iff₀ (by linarith only [hρ320]) (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at h3
    linarith only [h3]
  have hU0 : 0 < m2U (1 / (1 + H.x)) := by rw [hU1]; positivity
  have hU1' : (H.x ^ 2 + H.x + 1) / (1 + H.x) ^ 2 = m2U (1 / (1 + H.x)) := by
    unfold m2U; field_simp; ring
  have hZ : hs6Z H.x H.be H.al = 2 * m2U (1 / (1 + H.x)) * (2 * H.be * H.x - H.x - H.al * H.be) *
      (1 / (H.x * (H.x + 2))) - (H.be * H.x - H.al) * ((H.x + 2) * H.al + (2 * H.x + 1) * H.be) /
        ((1 + H.x) ^ 2 * (H.al ^ 2 + H.al * H.be + H.be ^ 2)) := by
    rw [hs6Z, hP]; ring
  have hsh : hsShear H.x H.be H.al H.rho = √3 / 3 * ((H.be * H.x - H.al) *
      ((H.x + 2) * H.al + (2 * H.x + 1) * H.be) / ((1 + H.x) ^ 2 * (H.al ^ 2 + H.al * H.be + H.be ^ 2)) -
      2 * m2U (1 / (1 + H.x)) * (2 * H.be * H.x - H.x - H.al * H.be) * (H.rho / (1 - H.rho))) := by
    rw [hsShear, hU1']
  have hERT : (H.be * H.x - H.al) / ((1 + H.x) * (H.al + H.be)) =
      (hsRr H.x + hsTs H.al H.be) / 2 := by
    unfold hsRr hsTs
    have : 0 < H.be + H.al := by linarith only [hal0, hbe0]
    have : 0 < H.al + H.be := by linarith only [hal0, hbe0]
    field_simp; ring
  -- the cost identity `C_br = C_c + J₀h_c - J₀h_a`
  have hcost : H.pt.cost = hs6Cc H.x H.be H.al H.u + hs6J0 H.x H.u * -(hs6Z H.x H.be H.al / √3) -
      hs6J0 H.x H.u * hsShear H.x H.be H.al H.rho := by
    rw [H.hs6_pt_cost, hs6Cc, hsh, hERT]
    have := hs6_cost_id (u := H.u) (Q := 2 * H.be * H.x - H.x - H.al * H.be)
      (w := H.rho / (1 - H.rho)) (E := (hsRr H.x + hsTs H.al H.be) / 2) (J := hs6J0 H.x H.u)
      hU0.ne' rfl hZ
    linear_combination this
  -- the shear at the central scale `h_c = -Z/√3`, below the actual shear
  have hcs : -(hs6Z H.x H.be H.al / √3) < hsShear H.x H.be H.al H.rho := by
    rw [hZ, hsh]
    generalize (H.be * H.x - H.al) * ((H.x + 2) * H.al + (2 * H.x + 1) * H.be) /
      ((1 + H.x) ^ 2 * (H.al ^ 2 + H.al * H.be + H.be ^ 2)) = P
    generalize m2U (1 / (1 + H.x)) = M at hU0 ⊢
    generalize 2 * H.be * H.x - H.x - H.al * H.be = Q at hQ0 ⊢
    generalize H.rho / (1 - H.rho) = w at hscale ⊢
    generalize 1 / (H.x * (H.x + 2)) = w0 at hscale ⊢
    have hinv : (2 * M * Q * w0 - P) / √3 = √3 / 3 * (2 * M * Q * w0 - P) := by
      have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
      have hs0 : √3 ≠ 0 := by positivity
      rw [← mul_div_mul_right (2 * M * Q * w0 - P) √3 hs0, h3]; ring
    rw [hinv]
    have : 2 * M * Q * w < 2 * M * Q * w0 := by
      have := mul_lt_mul_of_pos_left hscale (by positivity : 0 < 2 * M * Q)
      linarith only [this]
    have hs0 : 0 < √3 / 3 := by positivity
    have := mul_lt_mul_of_pos_left this hs0
    linarith only [this]
  -- the Casimir lower bound `κ ≥ κ₀`
  have hκ : 40 / 27 ≤ H.pt.kap := by
    rw [Point.kap, H.hs6_pt_gam]; exact (hs6_kappa hΓ).le
  -- the angle constants
  set A := hsAn H.x H.be H.al with hAdef
  set R := hsRr H.x with hRdef
  set J₀ := hs6J0 H.x H.u with hJdef
  set K := hs6K H.x H.be H.al H.u with hKdef
  set ha := hsShear H.x H.be H.al H.rho with hadef
  set hc := -(hs6Z H.x H.be H.al / √3) with hcdef
  have hu0 : 0 < H.u := by linarith only [hu34]
  have hJ0 : 0 < J₀ := by rw [hJdef, hs6J0]; positivity
  have hK2 : A + 2 ≤ K := by
    rw [hKdef, hs6K]; have : 0 < 2 * (40 / 27) / J₀ := by positivity
    linarith only [this]
  have hKA : A < K := by linarith only [hK2]
  -- the pointwise barrier on `[h_c, h_a]`
  have hKJ : K = A + 2 + 2 * (40 / 27) / J₀ := rfl
  have hω : hs6omega H.x H.be H.al H.u =
      2 * arctan ((√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2))) := by
    rw [hcdef, neg_sq, sub_neg_eq_add]; rfl
  have hFc : hs6Fc H.x H.be H.al H.u = hs6Cc H.x H.be H.al H.u +
      161 / 54 * (π / 3 - hs6psi H.x H.be H.al - hs6omega H.x H.be H.al H.u) := rfl
  clear_value A R J₀ K ha hc
  have hR9 : (1 / 3) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (by norm_num) hR1 2
  have hR49 : R ^ 2 ≤ (7 / 19) ^ 2 := pow_le_pow_left₀ (by linarith only [hR1]) hR2 2
  have hZs : -hc < 7 / 54 := by
    rw [hcdef, neg_neg, div_lt_iff₀ (by positivity)]; linarith only [hZ5, hs3g]
  have hbar : ∀ h, hc ≤ h → h ≤ ha → J₀ * √(h ^ 2 + A ^ 2) <
      161 / 54 * sin (2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2)))) := by
    intro h h1 h2
    set v := 1 - H.u / m2U (1 / (1 + H.x)) with hv
    have hvU : H.u / m2U (1 / (1 + H.x)) = 1 - v := by rw [hv]; ring
    have hJv : J₀ = 3 * (1 - v) / 2 := by
      rw [← hvU, hJdef, hs6J0]; field_simp
    have hKv : K = A + 2 + 2 * (161 / 54 - 3 / 2) / (3 * (1 - v) / 2) := by
      rw [hKJ, ← hJv]; norm_num
    have hv0 : 0 ≤ v := by
      rw [hv, sub_nonneg, div_le_one hU0]; exact huU
    have hv1 : v < 1 := by
      have : 0 < H.u / m2U (1 / (1 + H.x)) := by positivity
      rw [hv]; linarith only [this]
    have hvA : 0 ≤ v - (1 - v) * A := by
      rw [← hvU, hv]
      have : H.u / m2U (1 / (1 + H.x)) * (1 + A) ≤ 1 := by
        rw [div_mul_eq_mul_div, div_le_one hU0]; exact huA
      linarith only [this]
    have hv49 : v ≤ 49 / 916 := by
      have e1 : 867 / 916 * m2U (1 / (1 + H.x)) ≤ H.u := by
        rw [hU1]; linarith only [hu34, hR49]
      have e2 : 867 / 916 ≤ H.u / m2U (1 / (1 + H.x)) := by
        rw [le_div_iff₀ hU0]; linarith only [e1]
      rw [hv]; linarith only [e2]
    have hvv0 : 2 * R ^ 2 / (3 * (3 + R ^ 2)) ≤ v := by
      have e1 : H.u / m2U (1 / (1 + H.x)) ≤ (3 / 4 + R ^ 2 / 12) / m2U (1 / (1 + H.x)) :=
        div_le_div_of_nonneg_right hu2 hU0.le
      have e2 : (3 / 4 + R ^ 2 / 12) / m2U (1 / (1 + H.x)) = 1 - 2 * R ^ 2 / (3 * (3 + R ^ 2)) := by
        rw [hU1]; field_simp; ring
      rw [hv]; linarith only [e1, e2]
    have hH0 : 0 < -h := by linarith only [h2, hh]
    have hH7 : -h < 7 * R ^ 2 / 6 := by linarith only [h1, hZs, hR9]
    have hHR : 5 / 2 * A ≤ -h * R := by
      have := mul_le_mul_of_nonneg_right (neg_le_neg h2) (by linarith only [hR1] : (0 : ℝ) ≤ R)
      linarith only [this, hhR]
    have hvA' : 0 ≤ (1 - v) * A := mul_nonneg (by linarith only [hv1]) hA0
    have hQ := hs6_barrier (R := R) (b₁ := v) (A := A) (c := 161 / 54) (H := -h)
      (by linarith only [hR1]) (by linarith only [hR2]) hvv0 hv49 hA0 (by linarith only [hA1, hR9])
      hvA (by norm_num) (by norm_num) hH0 hH7 hHR
    have hb := hs6_barrier_sin hv0 hv1 hA0 (by norm_num) (by linarith only [hv49, hvA']) hH0 hQ
    rw [← hKv, ← hJv, neg_sq, ← sub_eq_add_neg] at hb
    exact hb
  -- the continuation from `δ_a` to `δ_c`
  obtain ⟨ha0', hac, hF⟩ := hs6_cont_core (J₀ := J₀) (c := 161 / 54) hA0 hKA hcs hh hbar
  -- the supporting-line hypothesis of the angle bound holds with equality at `δ_a`
  obtain ⟨-, haπ, aeq⟩ := hs6_tangent_inv hA0 hKA hh
  obtain ⟨e1, e2⟩ := hs6_tangent_sqrt hA0 hKA ha0' haπ
  rw [aeq] at e1 e2
  have hc0 : hc < 0 := hcs.trans hh
  have hD0 : 0 ≤ √(K ^ 2 - A ^ 2) := Real.sqrt_nonneg _
  have hnum : √(hc ^ 2 + A ^ 2) ≤ -hc + A := by
    rw [Real.sqrt_le_left (by linarith only [hc0, hA0])]
    have := mul_nonneg (neg_nonneg.2 hc0.le) hA0
    linarith only [this]
  have hy0 : 0 ≤ (√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2)) :=
    div_nonneg (by linarith only [Real.sqrt_nonneg (hc ^ 2 + A ^ 2), hc0])
      (by linarith only [hD0, hK2, hA0])
  have hhc : -hc < 2 / 17 := by
    rw [hcdef, neg_neg, div_lt_iff₀ (by positivity)]; linarith only [hZ5, hs3g]
  have hy : (√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2)) < 1 / 8 := by
    rw [div_lt_iff₀ (by linarith only [hD0, hK2, hA0])]
    linarith only [hnum, hhc, hA1, hD0, hK2, hA0]
  have hatc : 2 * arctan ((√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2))) < 1 / 4 := by
    linarith only [arctan_le_self hy0, hy]
  rw [← hω] at hac hF hatc
  generalize 2 * arctan ((√(ha ^ 2 + A ^ 2) - ha) / (K + √(K ^ 2 - A ^ 2))) = δa
    at ha0' hac hF haπ aeq e1 e2
  generalize hs6omega H.x H.be H.al H.u = δc at hac hF hatc hFc
  have hsup : √(A ^ 2 + ha ^ 2) ≤ K * sin δa + ha * cos δa := by rw [e1, e2, add_comm]
  -- `ψ + δ_a < π/2`
  have hψ : hs6psi H.x H.be H.al < 11 / 25 := by
    have hs0 : 0 < √3 := by positivity
    have hT0 : 0 ≤ hsTs H.al H.be := by linarith only [hT1]
    have h1 := arctan_le_self (div_nonneg (by linarith only [hR1] : (0 : ℝ) ≤ R) hs0.le)
    have h2 := arctan_le_self (div_nonneg hT0 hs0.le)
    have h3 : hsTs H.al H.be / √3 ≤ R / √3 := div_le_div_of_nonneg_right hT2 hs0.le
    have h4 : R / √3 < 11 / 50 := by rw [div_lt_iff₀ hs0]; linarith only [hR2, hs3g]
    rw [hs6psi, ← hRdef]
    linarith only [h1, h2, h3, h4]
  have hpi := Real.pi_gt_three
  have hδψ : δa < π / 2 - hs6psi H.x H.be H.al := by linarith only [hψ, hpi, hac, hatc]
  rw [hAdef, hKdef, hadef] at hsup
  have hθ := H.hs6_angle hκ ha0' hδψ hsup
  -- the window defect data: `0 < ℬ < 𝒜`, so `θ_br < π/3`
  obtain ⟨-, hB0, hBA, -, -⟩ : 2 * H.pt.Tk ≤ H.pt.AA ∧ 0 < H.pt.BB ∧ H.pt.BB < H.pt.AA ∧
      4 * H.pt.Tk ≤ H.pt.AA + H.pt.BB ∧
      H.pt.cost + (H.pt.kap + 3 / 2) * (π / 3 - arctan (√3 * H.pt.BB / H.pt.AA)) ≤ octagonCost :=
    H.defect
  have hθ3 : arctan (√3 * H.pt.BB / H.pt.AA) < π / 3 := by
    rw [← arctan_sqrt_three]
    apply arctan_strictMono
    rw [div_lt_iff₀ (by linarith only [hB0, hBA])]
    exact mul_lt_mul_of_pos_left hBA (by positivity)
  have hstep : 161 / 54 * (π / 3 - arctan (√3 * H.pt.BB / H.pt.AA)) ≤
      (H.pt.kap + 3 / 2) * (π / 3 - arctan (√3 * H.pt.BB / H.pt.AA)) :=
    mul_le_mul_of_nonneg_right (by linarith only [hκ]) (by linarith only [hθ3])
  rw [hFc, hcost]
  linarith only [hstep, hθ, hF]

/-- **Gate S6** (`SMALL_SHAPE_COST_EXCLUSION` (2); inventory HS-S567 S6.8): on the small-shape domain,
with `Γ > 1829/10000`, `h < 0`, `-hR > 5A/2`: `C_br + (κ + 3/2)(π/3 - θ_br) > A_oct`.
Proof plan: `hs6_continuation`; `hs6_Fc_gt` (with `hs6_u_bounds`, `u_le_rA`); `hs6_T_eq`,
`hs6_B_concave`, `hs6_B_endpoint` give `𝓑(u_q) > b* > 0`; `hs6_constants`:
`cπ/3 + √3𝓑 - 1/800000 > cπ₀/3 + ℓb* - 1/800000 = A₀ > A_oct`.
Status: assembly (to be proved from the leaves above). -/
theorem s6 (hS : H.SmallShape) (hΓ : 1829 / 10000 < H.Γ) (hh : hsShear H.x H.be H.al H.rho < 0)
    (hhR : 5 / 2 * hsAn H.x H.be H.al < -hsShear H.x H.be H.al H.rho * hsRr H.x) :
    octagonCost < H.pt.cost + (H.pt.kap + 3 / 2) * (π / 3 - arctan (√3 * H.pt.BB / H.pt.AA)) := by
  have hx1 := H.one_lt_x
  have hbe : H.x * (1 + H.δ) = H.be := by
    unfold HsData.δ; field_simp; ring
  have hcont := H.hs6_continuation hS hΓ hh hhR
  obtain ⟨hx2, hx13, hδ0, hδ19, hal1, hal2⟩ := hS
  have hal : 13 / 5 * H.δ ≤ H.al - 1 := by linarith
  have hal' : H.al - 1 ≤ 3 * H.δ := by linarith
  obtain ⟨hu1, hu2⟩ := hs6_u_bounds hx2 hx13 hδ0 hδ19 hal hal'
  rw [hbe, ← H.u_eq] at hu1 hu2
  have hu3 : H.u ≤ (3 + hsTs H.al H.be ^ 2) / 4 := by
    have h := H.u_le_rA
    have := H.one_le_al
    have := H.x_le_be
    have hpos : 0 < H.al + H.be := by linarith
    have hpos' : 0 < H.be + H.al := by linarith
    have : m2U (hsRA H.al H.be) = (3 + hsTs H.al H.be ^ 2) / 4 := by
      unfold m2U hsRA hsTs
      field_simp
      ring
    rwa [this] at h
  have hF := hs6_Fc_gt hx2 hx13 hδ0 hδ19 hal hal' (u := H.u)
    hu1.le hu2 (by rw [hbe]; exact hu3)
  rw [hbe] at hF
  have hB : hs6bstar < hs6B (hsRr H.x) (hsTs H.al H.be) H.δ (hs6uq (hsRr H.x) H.δ) := by
    obtain ⟨hR1, hR2, -⟩ := hs6_shape hx2 hx13 hδ0 hδ19 hal hal'
    obtain ⟨η, hη1, hη2, hη⟩ : ∃ η : ℝ, 13 / 5 ≤ η ∧ η ≤ 3 ∧ H.al = 1 + η * H.δ := by
      rcases hδ0.lt_or_eq with hpos | hzero
      · refine ⟨(H.al - 1) / H.δ, ?_, ?_, ?_⟩
        · rw [le_div_iff₀ hpos]; linarith
        · rw [div_le_iff₀ hpos]; linarith
        · field_simp; ring
      · refine ⟨13 / 5, le_rfl, by norm_num, ?_⟩
        rw [← hzero] at hal1 hal2 ⊢
        linarith
    rw [← hbe, hη, hs6_T_eq hx1 hδ0 (by linarith)]
    exact lt_of_lt_of_le (lt_min (hs6_B_endpoint hR1 hR2 hδ0 hδ19 (Or.inl rfl))
      (hs6_B_endpoint hR1 hR2 hδ0 hδ19 (Or.inr rfl))) (hs6_B_concave hR1 hR2 hδ0 hδ19 hη1 hη2)
  obtain ⟨hA, hpi, hs3⟩ := hs6_constants
  have hb0 : 0 < hs6bstar := by norm_num [hs6bstar]
  have hgap : 989 / 571 * hs6bstar <
      √3 * hs6B (hsRr H.x) (hsTs H.al H.be) H.δ (hs6uq (hsRr H.x) H.δ) := by
    nlinarith [mul_pos (sub_pos.2 hs3) hb0, Real.sqrt_nonneg 3]
  have hexact : (3126055 / 1000000 : ℝ) =
      161 / 54 * (314159265 / 100000000) / 3 + 989 / 571 * hs6bstar - 1 / 800000 := by
    norm_num [hs6bstar]
  linarith

end HsData

/-- **Gate S6 for the actual window** (`SMALL_SHAPE_COST_EXCLUSION` (2)): on the small-shape
domain, with `Γ > 1829/10000`, `h < 0`, `-hR > 5A/2`, the window cost and completion exceed
`A_oct`. -/
theorem M2Short.hs_S6 (D : M2Short) (h1 : 2 ≤ D.C / D.a) (h2 : D.C / D.a ≤ 13 / 6)
    (h3 : 0 ≤ D.B / D.C - 1) (h4 : D.B / D.C - 1 ≤ 1 / 19)
    (h5 : 1 + 13 / 5 * (D.B / D.C - 1) ≤ D.A / D.a) (h6 : D.A / D.a ≤ 1 + 3 * (D.B / D.C - 1))
    (hΓ : 1829 / 10000 < D.Γ)
    (hh : hsShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) < 0)
    (hhR : 5 / 2 * hsAn (D.C / D.a) (D.B / D.a) (D.A / D.a) <
      -hsShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) *
        hsRr (D.C / D.a)) :
    octagonCost <
      D.ss_pt.cost + (D.ss_pt.kap + 3 / 2) * (π / 3 - arctan (√3 * D.ss_pt.BB / D.ss_pt.AA)) := by
  rw [← D.toHs_x, ← D.toHs_be, ← D.toHs_al, ← D.toHs_rho] at hh hhR
  have h := D.toHs.s6 (D.hs_smallShape h1 h2 h3 h4 h5 h6) (by rwa [D.toHs_Γ]) hh hhR
  rwa [D.toHs_pt] at h

end SmoothedOctagon
