module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Interface
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Angle
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.ExactScore
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.ExactShape
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Continuation
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Defs
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Endpoint
public import SmoothedOctagon.Period.OctagonCost

/-!
# Smaller-short completion: continuation, the genuine norm floor and exact score
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set MeasureTheory

open SmallerShort

/-- **Lowering `κ`**:
`12·1829/10000 - (40/27)² = 23/1822500 > 0`, so `Γ > 1829/10000 ⇒ √(12Γ) > 40/27`. -/
theorem cost_kappa {Γ : ℝ} (hΓ : 1829 / 10000 < Γ) : 40 / 27 < √(12 * Γ) := by
  rw [Real.lt_sqrt (by norm_num)]
  linarith

/-- **The angle coordinates**: on
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`, `β = x(1 + δ)`: `1/3 ≤ R ≤ 7/19`,
`9/31 ≤ T_s ≤ R`, `0 ≤ A < 1/100`, and `(βx - α)((x + 2)α + (2x + 1)β)/(S²K_A) = R + (1 + A)T_s`.
Proof: `A = (R² - T²)/(3 + T²) ≤ (R² - T_min²)/3` with `T ≥ T_min = (10x - 11)/(10x + 11)` and one
quartic in `x` (`3(x + 1)²(10x + 11)² - 400x(10x² - 11) > 0`). -/
theorem cost_shape {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    1 / 3 ≤ ssRr x ∧ ssRr x ≤ 7 / 19 ∧ 9 / 31 ≤ ssTs al (x * (1 + δ)) ∧
      ssTs al (x * (1 + δ)) ≤ ssRr x ∧ 0 ≤ ssAn x (x * (1 + δ)) al ∧
      ssAn x (x * (1 + δ)) al < 1 / 100 ∧
      (x * (1 + δ) * x - al) * ((x + 2) * al + (2 * x + 1) * (x * (1 + δ))) /
          ((1 + x) ^ 2 * (al ^ 2 + al * (x * (1 + δ)) + (x * (1 + δ)) ^ 2)) =
        ssRr x + (1 + ssAn x (x * (1 + δ)) al) * ssTs al (x * (1 + δ)) := by
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
  have hAid : ssAn x (x * (1 + δ)) al = (ssRr x ^ 2 - ssTs al (x * (1 + δ)) ^ 2) /
      (3 + ssTs al (x * (1 + δ)) ^ 2) := by
    unfold ssAn ssRr ssTs
    have : 0 < (x * (1 + δ) + al) ^ 2 * 3 + (x * (1 + δ) - al) ^ 2 := by positivity
    rw [div_eq_div_iff (by positivity) (by field_simp; positivity)]
    field_simp
    ring
  have hT0 : 9 / 31 ≤ ssTs al (x * (1 + δ)) := by
    unfold ssTs; rw [le_div_iff₀ hsum]; nlinarith
  have hTR : ssTs al (x * (1 + δ)) ≤ ssRr x := by
    unfold ssTs ssRr; rw [div_le_div_iff₀ hsum hx0]; nlinarith
  have hTmin : (10 * x - 11) / (10 * x + 11) ≤ ssTs al (x * (1 + δ)) := by
    unfold ssTs; rw [div_le_div_iff₀ (by linarith) hsum]; nlinarith
  refine ⟨?_, ?_, hT0, hTR, ?_, ?_, ?_⟩
  · unfold ssRr; rw [le_div_iff₀ hx0]; linarith
  · unfold ssRr; rw [div_le_iff₀ hx0]; linarith
  · unfold ssAn
    apply div_nonneg (mul_nonneg (by nlinarith) (by linarith)) (by positivity)
  · rw [hAid]
    have hTm0 : 0 ≤ (10 * x - 11) / (10 * x + 11) := div_nonneg (by linarith) (by linarith)
    have hT2 : ((10 * x - 11) / (10 * x + 11)) ^ 2 ≤ ssTs al (x * (1 + δ)) ^ 2 :=
      pow_le_pow_left₀ hTm0 hTmin 2
    have hRT : ssRr x ^ 2 - ((10 * x - 11) / (10 * x + 11)) ^ 2 < 3 / 100 := by
      have e : ssRr x ^ 2 - ((10 * x - 11) / (10 * x + 11)) ^ 2 =
          4 * x * (10 * x ^ 2 - 11) / ((x + 1) ^ 2 * (10 * x + 11) ^ 2) := by
        unfold ssRr; field_simp; ring
      rw [e, div_lt_iff₀ (by positivity)]
      have h0 : 0 ≤ x - 2 := by linarith
      have h1 : 0 ≤ 13 / 6 - x := by linarith
      nlinarith [mul_nonneg h0 h1, mul_nonneg (mul_nonneg h0 h0) h1, mul_nonneg h0 (mul_nonneg h0 h0)]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · unfold ssRr ssTs ssAn
    field_simp
    ring

theorem cost_u_bounds {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    s6VarianceFloor (ssRr x) δ < m2Sec 1 x (x * (1 + δ)) ∧
      m2Sec 1 x (x * (1 + δ)) ≤ 3 / 4 + ssRr x ^ 2 / 12 := by
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
  have hR2 : ssRr x ^ 2 = (x - 1) ^ 2 / (x + 1) ^ 2 := by rw [ssRr, div_pow]
  have hR9 : 1 / 108 ≤ ssRr x ^ 2 / 12 := by
    rw [hR2, div_div, le_div_iff₀ (by positivity)]; nlinarith only [hx, hx2]
  refine ⟨s6_norm_gt_variance_floor hx1 hδ, ?_⟩
  have hV := ss_V_le_U0 hx1
  have hT := ss_sec_tail_le hx0 hbex
  have hU0 : ssU0 x = 3 / 4 + ssRr x ^ 2 / 12 := by
    rw [ssU0, hR2]; field_simp
  have hTt : (x * (1 + δ) - x) ^ 2 / (48 * x ^ 2) ≤ ssRr x ^ 2 / 12 := by
    have e : (x * (1 + δ) - x) ^ 2 / (48 * x ^ 2) = δ ^ 2 / 48 := by field_simp; ring
    rw [e]
    have : δ ^ 2 ≤ (1 / 19) ^ 2 := pow_le_pow_left₀ hδ hδ2 2
    linarith only [this, hR9]
  rw [hU0] at hV
  have h1 : (x * (1 + δ) - 1) * m2Sec 1 x (x * (1 + δ)) ≤
      (x * (1 + δ) - 1) * (3 / 4 + ssRr x ^ 2 / 12) := by
    rw [hsplit]
    have hT' : m2Sec x x (x * (1 + δ)) ≤ 3 / 4 + ssRr x ^ 2 / 12 := by linarith only [hT, hTt]
    have h2 := mul_le_mul_of_nonneg_left hV (by linarith only [hx1] : (0 : ℝ) ≤ x - 1)
    have h3 := mul_le_mul_of_nonneg_left hT' (by linarith only [hbex] : (0 : ℝ) ≤ x * (1 + δ) - x)
    linarith only [h2, h3]
  exact le_of_mul_le_mul_left h1 (by linarith only [hbe1])

theorem cost_central_shear {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    1 / 9 ≤ costZL (ssRr x) δ ∧ costZL (ssRr x) δ ≤ costZ x (x * (1 + δ)) al ∧
      costZ x (x * (1 + δ)) al ≤ costZU (ssRr x) δ ∧ costZU (ssRr x) δ < 1 / 5 := by
  have hR1 : 1 / 3 ≤ ssRr x := by unfold ssRr; rw [le_div_iff₀ (by linarith)]; linarith
  have hR2 : ssRr x ≤ 7 / 19 := by unfold ssRr; rw [div_le_iff₀ (by linarith)]; linarith
  have h3R : 0 < 3 - ssRr x := by linarith
  have hZ0 : 1 / 9 ≤ 2 * ssRr x ^ 2 * (1 + ssRr x) / (3 - ssRr x) := by
    rw [le_div_iff₀ h3R]
    have : (1 / 3) ^ 2 ≤ ssRr x ^ 2 := pow_le_pow_left₀ (by norm_num) hR1 2
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
  obtain ⟨hL, hU⟩ := cost_shear_core hx hx2 hδ hδ2 hη1 hη2
  refine ⟨?_, hL, hU, ?_⟩
  · show 1 / 9 ≤ 2 * ssRr x ^ 2 * (1 + ssRr x) / (3 - ssRr x) * (1 + 11 * δ / 2)
    have : 1 ≤ 1 + 11 * δ / 2 := by linarith
    nlinarith
  · show 2 * ssRr x ^ 2 * (1 + ssRr x) / (3 - ssRr x) + (1 + 2 * ssRr x) / (3 * (1 - ssRr x)) * δ -
      3 / 2 * δ ^ 2 < 1 / 5
    have h1R : 0 < 1 - ssRr x := by linarith
    have e1 : 2 * ssRr x ^ 2 * (1 + ssRr x) / (3 - ssRr x) ≤ 1 / 7 := by
      rw [div_le_iff₀ h3R]
      have : ssRr x ^ 2 ≤ (7 / 19) ^ 2 := pow_le_pow_left₀ (by linarith) hR2 2
      have : ssRr x ^ 3 ≤ (7 / 19) ^ 3 := pow_le_pow_left₀ (by linarith) hR2 3
      nlinarith
    have e2 : (1 + 2 * ssRr x) / (3 * (1 - ssRr x)) ≤ 11 / 12 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have e3 : (1 + 2 * ssRr x) / (3 * (1 - ssRr x)) * δ ≤ 11 / 12 * (1 / 19) :=
      mul_le_mul e2 hδ2 hδ (by norm_num)
    nlinarith [sq_nonneg δ]

/-- The double angle of an arctangent: `cos(2 arctan y) = (1 - y²)/(1 + y²)`,
`sin(2 arctan y) = 2y/(1 + y²)`. -/
private lemma cost_two_arctan (y : ℝ) :
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
private lemma cost_tangent_sqrt {A K δ : ℝ} (hA : 0 ≤ A) (hK : A < K) (h0 : 0 < δ) (hπ : δ < π) :
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
private lemma cost_ht_deriv {A K δ : ℝ} (h0 : 0 < δ) (hπ : δ < π) :
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
private lemma cost_K_sub_pos {A K δ : ℝ} (hA : 0 ≤ A) (hK : A < K) (h0 : 0 < δ) (hπ : δ < π) :
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

/-- **The tangent curve inverts the half-angle formula**:
for `A ≥ 0`, `K > A`, `𝒟 = √(K² - A²)` and `h < 0`, the angle
`δ = 2 arctan((√(h² + A²) - h)/(K + 𝒟))` lies in `(0, π)` and `(K cos δ - 𝒟)/sin δ = h`. -/
theorem cost_tangent_inv {A K h : ℝ} (hA : 0 ≤ A) (hK : A < K) (hh : h < 0) :
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
  obtain ⟨hc, hs⟩ := cost_two_arctan y
  rw [hc, hs]
  have key : (K * (1 - y ^ 2) - D * (1 + y ^ 2) - 2 * h * y) * (K + D) = 0 := by
    linear_combination (-1 : ℝ) * hD2 - hρ2 - (ρ + y * (K + D) + h) * hyK
  have key' : K * (1 - y ^ 2) - D * (1 + y ^ 2) - 2 * h * y = 0 :=
    (mul_eq_zero.1 key).resolve_right hKD.ne'
  have h1 : (0 : ℝ) < 1 + y ^ 2 := by positivity
  field_simp
  linear_combination key'

/-- **The tangent curve is decreasing**:
for `A ≥ 0`, `K > A`, `h̃(δ) = (K cos δ - 𝒟)/sin δ` is strictly decreasing on `(0, π)`
(`h̃' = (𝒟 cos δ - K)/sin²δ < 0`), and `K sin δ + h̃(δ) cos δ = √(h̃(δ)² + A²)`. -/
theorem cost_tangent_anti {A K δ₁ δ₂ : ℝ} (hA : 0 ≤ A) (hK : A < K) (h1 : 0 < δ₁) (h12 : δ₁ < δ₂)
    (h2 : δ₂ < π) :
    (K * cos δ₂ - √(K ^ 2 - A ^ 2)) / sin δ₂ < (K * cos δ₁ - √(K ^ 2 - A ^ 2)) / sin δ₁ ∧
      K * sin δ₁ + (K * cos δ₁ - √(K ^ 2 - A ^ 2)) / sin δ₁ * cos δ₁ =
        √(((K * cos δ₁ - √(K ^ 2 - A ^ 2)) / sin δ₁) ^ 2 + A ^ 2) := by
  refine ⟨?_, ?_⟩
  · have h := ss_lt_of_deriv (f := fun s => -((K * cos s - √(K ^ 2 - A ^ 2)) / sin s))
      (f' := fun s => (K - √(K ^ 2 - A ^ 2) * cos s) / sin s ^ 2) h12
      (fun z hz => by
        have := (cost_ht_deriv (A := A) (K := K) (δ := z) (by linarith [hz.1])
          (by linarith [hz.2])).const_mul (-1)
        convert this using 1
        · funext s; ring
        · ring)
      (fun z hz => by
        have h0 : 0 < z := by linarith [hz.1]
        have hπ : z < π := by linarith [hz.2]
        have := cost_K_sub_pos hA hK h0 hπ
        have := sin_pos_of_pos_of_lt_pi h0 hπ
        positivity)
    linarith
  · obtain ⟨e1, e2⟩ := cost_tangent_sqrt hA hK h1 (by linarith)
    rw [e1, e2]

/-- **The score derivative**: for
`A ≥ 0`, `K > A`, `J₀, c` real and `0 < δ < π`, `F̃(δ) = -J₀h̃(δ) - cδ` has derivative
`(J₀√(h̃(δ)² + A²) - c sin δ)/sin δ`. -/
theorem cost_score_deriv {A K J₀ c δ : ℝ} (hA : 0 ≤ A) (hK : A < K) (h0 : 0 < δ) (hπ : δ < π) :
    HasDerivAt (fun s => -J₀ * ((K * cos s - √(K ^ 2 - A ^ 2)) / sin s) - c * s)
      ((J₀ * √(((K * cos δ - √(K ^ 2 - A ^ 2)) / sin δ) ^ 2 + A ^ 2) - c * sin δ) / sin δ) δ := by
  have hs : 0 < sin δ := sin_pos_of_pos_of_lt_pi h0 hπ
  have h := ((cost_ht_deriv (A := A) (K := K) h0 hπ).const_mul (-J₀)).sub
    ((hasDerivAt_id' δ).const_mul c)
  refine h.congr_deriv ?_
  rw [← (cost_tangent_sqrt hA hK h0 hπ).2]
  field_simp
  ring

/-- The cost-shear identity in the atoms of `SmallerShortData.cost_continuation`: with `J₀ = 3u/(2U₁)` and
`Z = 2U₁Q₀w₀ - P`, `C_br = C_c + J₀h_c - J₀h_a` (the cost-shear identity `C = H₀ - J₀h` at the two
scales). -/
private lemma cost_cost_id {u M Q w w0 P E Z J : ℝ} (hM : M ≠ 0) (hJ : J = 3 * u / (2 * M))
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

/-- **The continuation core**: for
`0 ≤ A < K` and shears `h_c < h_a < 0`, if `J₀√(h² + A²) < c sin δ(h)` for every `h ∈ [h_c, h_a]`,
then `δ_a = δ(h_a)` and `δ_c = δ(h_c)` satisfy `0 < δ_a < δ_c` and the score
`F̃(δ) = -J₀h̃(δ) - cδ` decreases from `δ_a` to `δ_c`: `-J₀h_c - cδ_c ≤ -J₀h_a - cδ_a`. -/
private lemma cost_cont_core {A K J₀ c ha hc : ℝ} (hA : 0 ≤ A) (hK : A < K) (hca : hc < ha)
    (ha0 : ha < 0)
    (hbar : ∀ h, hc ≤ h → h ≤ ha → J₀ * √(h ^ 2 + A ^ 2) <
      c * sin (2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2))))) :
    0 < 2 * arctan ((√(ha ^ 2 + A ^ 2) - ha) / (K + √(K ^ 2 - A ^ 2))) ∧
      2 * arctan ((√(ha ^ 2 + A ^ 2) - ha) / (K + √(K ^ 2 - A ^ 2))) <
        2 * arctan ((√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2))) ∧
      -J₀ * hc - c * (2 * arctan ((√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2)))) ≤
        -J₀ * ha - c * (2 * arctan ((√(ha ^ 2 + A ^ 2) - ha) / (K + √(K ^ 2 - A ^ 2)))) := by
  obtain ⟨a0, aπ, aeq⟩ := cost_tangent_inv hA hK ha0
  obtain ⟨c0, cπ, ceq⟩ := cost_tangent_inv hA hK (hca.trans ha0)
  generalize 2 * arctan ((√(ha ^ 2 + A ^ 2) - ha) / (K + √(K ^ 2 - A ^ 2))) = δa at a0 aπ aeq ⊢
  generalize 2 * arctan ((√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2))) = δc at c0 cπ ceq ⊢
  have hanti : ∀ s t, 0 < s → s < t → t < π →
      (K * cos t - √(K ^ 2 - A ^ 2)) / sin t < (K * cos s - √(K ^ 2 - A ^ 2)) / sin s :=
    fun s t h1 h2 h3 => (cost_tangent_anti hA hK h1 h2 h3).1
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
    (fun z hz => (cost_score_deriv hA hK (by linarith [hz.1]) (by linarith [hz.2])).neg)
    (fun z hz => by
      have hz0 : 0 < z := by linarith [hz.1]
      have hzπ : z < π := by linarith [hz.2]
      have hs : 0 < sin z := sin_pos_of_pos_of_lt_pi hz0 hzπ
      have h1 := hanti δa z a0 hz.1 hzπ
      have h2 := hanti z δc hz0 hz.2 cπ
      rw [aeq] at h1
      rw [ceq] at h2
      generalize hhz : (K * cos z - √(K ^ 2 - A ^ 2)) / sin z = h at h1 h2 ⊢
      obtain ⟨d0, dπ, deq⟩ := cost_tangent_inv hA hK (h1.trans ha0)
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

theorem cost_Fc_gt {x δ al u : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13/6)
    (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/19)
    (hal : 13/5*δ ≤ al-1) (hal1 : al-1 ≤ 3*δ)
    (hu : s6VarianceFloor (ssRr x) δ ≤ u) (hu1 : u ≤ 3/4+ssRr x^2/12)
    (hu2 : u ≤ (3+ssTs al (x*(1+δ))^2)/4) :
    (161/54)*π/3+sqrt 3*costBExact (ssRr x) (ssTs al (x*(1+δ)))
      (s6VarianceFloor (ssRr x) δ) (costZU (ssRr x) δ) (costZL (ssRr x) δ) <
      costFc x (x*(1+δ)) al u := by
  obtain ⟨hR1,hR2,hT1,hT2,hA0,hA1,-⟩ := cost_shape hx hx2 hδ hδ2 hal hal1
  obtain ⟨hZL1,hZLZ,hZZU,hZU5⟩ := cost_central_shear hx hx2 hδ hδ2 hal hal1
  have hx0 : 0 < x := by linarith only [hx]
  have hal0 : 0 < al := by linarith only [hal,hδ]
  have hbe0 : 0 < x*(1+δ) := by positivity
  have hs : 0 < sqrt (3:ℝ) := by positivity
  have hs2 : (sqrt (3:ℝ))^2 = 3 := sq_sqrt (by norm_num)
  have hs1 : 1 < sqrt (3:ℝ) := by rw [lt_sqrt (by norm_num)]; norm_num
  have hZ0 : 0 < costZ x (x*(1+δ)) al := by linarith only [hZL1,hZLZ]
  have hH0 : 0 < costZ x (x*(1+δ)) al/sqrt 3 := div_pos hZ0 hs
  have hH1 : costZ x (x*(1+δ)) al/sqrt 3 < 1/5 := by
    rw [div_lt_iff₀ hs]
    linarith only [hZZU,hZU5,hs1]
  have hvar : 6*(ssAn x (x*(1+δ)) al)^2 < (costZ x (x*(1+δ)) al/sqrt 3)^2 := by
    have hA2 : (ssAn x (x*(1+δ)) al)^2 < (1/100)^2 := by nlinarith only [hA0,hA1]
    have hz : 1/9 ≤ costZ x (x*(1+δ)) al := hZL1.trans hZLZ
    have hZ2 : (1/9)^2 ≤ (costZ x (x*(1+δ)) al)^2 :=
      (sq_le_sq₀ (by norm_num) hZ0.le).2 hz
    rw [div_pow,hs2]
    nlinarith only [hA2,hZ2]
  have hfloor := s6_variance_floor_ge_three_quarters (R := ssRr x) (d := δ)
    (by linarith only [hR1]) hδ
  have hu0 : 0 < u := by linarith only [hfloor,hu]
  have hU1 : m2U (1/(1+x)) = (3+ssRr x^2)/4 := by unfold m2U ssRr; field_simp; ring
  have hJk : costJ0 x u < 40/27 := by
    rw [costJ0,hU1,div_lt_iff₀ (by positivity)]
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/3) hR1 2
    linarith only [hsq,hu1]
  have huU1 : u ≤ (3+ssRr x^2)/4 := by nlinarith only [hu1,sq_nonneg (ssRr x)]
  have hraw := s6_exact_raw_score hx0 hal0 hbe0 hu0 hJk hA0 huU1 hu2 hH0 hH1 hvar
  have hb : 0 ≤ (1-4*u/(3+ssRr x^2))+(1-4*u/(3+ssTs al (x*(1+δ))^2)) := by
    have hb1 : 4*u/(3+ssRr x^2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith only [huU1]
    have hb2 : 4*u/(3+ssTs al (x*(1+δ))^2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith only [hu2]
    linarith only [hb1,hb2]
  have hZL0 : 0 < costZL (ssRr x) δ := by linarith only [hZL1]
  have hZU0 : 0 ≤ costZU (ssRr x) δ := by linarith only [hZ0,hZZU]
  have hn := s6_exact_norm_mono (ZL := costZL (ssRr x) δ) (by linarith only [hR1] : 0 ≤ ssRr x)
    (by linarith only [hT1] : 0 ≤ ssTs al (x*(1+δ))) hZU0 hu
  have he := s6_exact_envelopes hb hZL0 hZLZ hZZU
  have hlow := mul_le_mul_of_nonneg_left (hn.trans he) hs.le
  linarith only [hlow,hraw]

/-- The angle coordinate on the box in the variables `(R, δ, η)`:
for `x > 1`, `δ ≥ 0`, `T_s(1 + ηδ, x(1 + δ)) = costT R δ η`, `R = (x - 1)/(x + 1)`. -/
theorem cost_T_eq {x δ η : ℝ} (hx : 1 < x) (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    ssTs (1 + η * δ) (x * (1 + δ)) = costT (ssRr x) δ η := by
  have hx1 : 0 < x + 1 := by linarith
  have h1 : 0 < x * (1 + δ) + (1 + η * δ) := by nlinarith
  have h2 : costT (ssRr x) δ η = 2 * (x * (1 + δ) - (1 + η * δ)) / (x + 1) /
      (2 * (x * (1 + δ) + (1 + η * δ)) / (x + 1)) := by
    unfold costT ssRr
    congr 1 <;> field_simp <;> ring
  rw [h2, div_div_div_cancel_right₀ hx1.ne', ssTs, mul_div_mul_left _ _ (two_ne_zero)]

/-- The exact octagon comparison transfers every score above the natural S6 threshold. -/
theorem cost_octagon_lt_exact_score {B : ℝ} (hB : 9/4000 < B) :
    octagonCost < (161/54)*π/3+sqrt 3*B := by
  have hs : 0 < sqrt (3:ℝ) := by positivity
  have hm := mul_lt_mul_of_pos_left hB hs
  have ho := octagonCost_lt_score
  linarith only [hm,ho]


namespace SmallerShortData
variable (H : SmallerShortData)

/-- The cover's incoming norm at the normalized point. -/
private lemma cost_pt_u : H.pt.u = H.u := H.pt_u

/-- The cover's `x` at the normalized point. -/
private lemma cost_pt_x : H.pt.x = H.x := by
  have := H.one_lt_x
  simp only [SmallerShortData.pt, Point.x]
  field_simp
  ring

/-- The cover's `β` at the normalized point. -/
private lemma cost_pt_be : H.pt.be = H.be := by
  have := H.one_lt_x
  rw [Point.be, H.cost_pt_x]
  simp only [SmallerShortData.pt]
  field_simp
  ring

/-- The cover's Casimir at the normalized point is `Γ`. -/
private lemma cost_pt_gam : H.pt.gam = H.Γ := by
  rw [Point.gam, H.cost_pt_u, H.Γ_eq, ssGam]
  rfl

/-- The window cost at the normalized point (`Point.cost`). -/
private lemma cost_pt_cost : H.pt.cost = √3 * (H.rho * H.u / (1 - H.rho) *
    (2 * H.be * H.x - H.x - H.al * H.be) + (H.be * H.x - H.al) / ((1 + H.x) * (H.al + H.be))) := by
  rw [Point.cost, H.cost_pt_u, Point.S, Point.A, H.cost_pt_x, H.cost_pt_be]
  rfl

/-- **The angle bound at `κ₀`**: for actual data with `40/27 ≤ κ = pt.kap`,
`K = A + 2 + 2κ₀/J₀`, `h` the actual shear, and `0 < δ < π/2 - ψ` with
`K sin δ + h cos δ ≥ √(A² + h²)`: `θ_br = arctan(√3ℬ/𝒜) ≤ ψ + δ`. Proof: the rotated trace
identity and the quadratic-in-`ξ` bound of `SmallerShort.Cost.Angle` (`cost_angle_core`). -/
theorem cost_angle (hκ : 40 / 27 ≤ H.pt.kap) {δ : ℝ} (hδ : 0 < δ)
    (hδψ : δ < π / 2 - costpsi H.x H.be H.al)
    (hsup : √(ssAn H.x H.be H.al ^ 2 + ssShear H.x H.be H.al H.rho ^ 2) ≤
      costK H.x H.be H.al H.u * sin δ + ssShear H.x H.be H.al H.rho * cos δ) :
    arctan (√3 * H.pt.BB / H.pt.AA) ≤ costpsi H.x H.be H.al + δ := by
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
  have hR0 : 0 ≤ ssRr H.x := by unfold ssRr; exact div_nonneg (by linarith) (by linarith)
  have hR1 : ssRr H.x < 1 := by unfold ssRr; rw [div_lt_one (by linarith)]; linarith
  have hT0 : 0 ≤ ssTs H.al H.be := by unfold ssTs; exact div_nonneg (by linarith) (by linarith)
  have hT1 : ssTs H.al H.be < 1 := by unfold ssTs; rw [div_lt_one (by linarith)]; linarith
  have hRT : ssRr H.x * ssTs H.al H.be < 3 := by
    have := mul_le_mul hR1.le hT1.le hT0 (by norm_num)
    linarith
  have hprod : ssRr H.x / √3 * (ssTs H.al H.be / √3) = ssRr H.x * ssTs H.al H.be / 3 := by
    rw [div_mul_div_comm, hs3]
  have hψ : costpsi H.x H.be H.al = arctan (√3 * μ / n) := by
    rw [costpsi, arctan_add (by rw [hprod]; linarith)]
    congr 1
    have e1 : (ssRr H.x + ssTs H.al H.be) / (3 - ssRr H.x * ssTs H.al H.be) = μ / n := by
      unfold ssRr ssTs
      rw [hμ, hn]
      have h1 : 0 < H.x + 1 := by linarith
      have h2 : 0 < H.be + H.al := by linarith
      rw [div_eq_div_iff (by unfold ssRr ssTs at hRT; linarith) hn0.ne']
      field_simp
      ring
    have hsum : ssRr H.x / √3 + ssTs H.al H.be / √3 = √3 * (ssRr H.x + ssTs H.al H.be) / 3 := by
      rw [← add_div, div_eq_div_iff hs0.ne' (by norm_num)]
      linear_combination (-(ssRr H.x + ssTs H.al H.be)) * hs3
    rw [hprod, hsum]
    have h3 : (0 : ℝ) < 3 - ssRr H.x * ssTs H.al H.be := by linarith
    calc √3 * (ssRr H.x + ssTs H.al H.be) / 3 / (1 - ssRr H.x * ssTs H.al H.be / 3) =
        √3 * ((ssRr H.x + ssTs H.al H.be) / (3 - ssRr H.x * ssTs H.al H.be)) := by
          field_simp
      _ = √3 * μ / n := by rw [e1]; ring
  -- `0 < ψ`, `0 < δ < π/2`
  have hy0 : 0 < √3 * μ / n := by positivity
  have hψ0 : 0 < costpsi H.x H.be H.al := by rw [hψ]; exact arctan_pos.2 hy0
  have hδπ : δ < π := by linarith [Real.pi_pos]
  have hsδ : 0 < sin δ := sin_pos_of_pos_of_lt_pi hδ hδπ
  -- raise `κ₀` to `κ` in the supporting line
  have hU0 : 0 < m2U (1 / (1 + H.x)) := by
    unfold m2U; have : 0 < 1 / (1 + H.x) := by positivity
    nlinarith [sq_nonneg (1 / (1 + H.x) - 1 / 2)]
  have hJ0 : 0 < 3 * H.u / (2 * m2U (1 / (1 + H.x))) := by positivity
  have hsup' : √(ssAn H.x H.be H.al ^ 2 + ssShear H.x H.be H.al H.rho ^ 2) ≤
      (ssAn H.x H.be H.al + 2 + 2 * H.pt.kap / (3 * H.u / (2 * m2U (1 / (1 + H.x))))) * sin δ +
        ssShear H.x H.be H.al H.rho * cos δ := by
    have h1 : 2 * (40 / 27) / (3 * H.u / (2 * m2U (1 / (1 + H.x)))) ≤
        2 * H.pt.kap / (3 * H.u / (2 * m2U (1 / (1 + H.x)))) :=
      div_le_div_of_nonneg_right (by linarith) hJ0.le
    have h2 := mul_le_mul_of_nonneg_right h1 hsδ.le
    have e : costK H.x H.be H.al H.u = ssAn H.x H.be H.al + 2 +
        2 * (40 / 27) / (3 * H.u / (2 * m2U (1 / (1 + H.x)))) := rfl
    rw [e] at hsup
    linarith
  have core : √3 * cos δ * (n * H.pt.BB - μ * H.pt.AA) - sin δ * (n * H.pt.AA + 3 * μ * H.pt.BB) ≤ 0 :=
    cost_angle_core hx1 hal0 hbe0 hρ0 hρ1 hu0 H.pt_u hk0 hsδ hsup'
  -- the defect data
  obtain ⟨-, hB0, hBA, -, -⟩ : 2 * H.pt.Tk ≤ H.pt.AA ∧ 0 < H.pt.BB ∧ H.pt.BB < H.pt.AA ∧
      4 * H.pt.Tk ≤ H.pt.AA + H.pt.BB ∧
      H.pt.cost + (H.pt.kap + 3 / 2) * (π / 3 - arctan (√3 * H.pt.BB / H.pt.AA)) ≤ octagonCost :=
    H.defect
  have hA0 : 0 < H.pt.AA := hB0.trans hBA
  -- `√3ℬ cos(ψ + δ) ≤ 𝒜 sin(ψ + δ)`
  have hq : 0 < √(1 + (√3 * μ / n) ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hcos : 0 < cos (costpsi H.x H.be H.al + δ) :=
    cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hkey : √3 * H.pt.BB * cos (costpsi H.x H.be H.al + δ) ≤
      H.pt.AA * sin (costpsi H.x H.be H.al + δ) := by
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
  have htan : √3 * H.pt.BB / H.pt.AA ≤ tan (costpsi H.x H.be H.al + δ) := by
    rw [tan_eq_sin_div_cos, div_le_div_iff₀ hA0 hcos]
    linarith
  calc arctan (√3 * H.pt.BB / H.pt.AA) ≤ arctan (tan (costpsi H.x H.be H.al + δ)) :=
        arctan_le_arctan_iff.2 htan
    _ = costpsi H.x H.be H.al + δ := arctan_tan (by linarith) (by linarith)

/-- The original window score dominates the central-scale score under `-hR > 2ν`.
The exact tangent curve and the three explicit losses give pointwise strict decrease;
the natural central-shear bound controls the angle throughout the continuation. -/
theorem cost_continuation (hS : H.SmallShape) (hΓ : 1829 / 10000 < H.Γ)
    (hh : ssShear H.x H.be H.al H.rho < 0)
    (hhR : 2 * ssAn H.x H.be H.al < -ssShear H.x H.be H.al H.rho * ssRr H.x) :
    costFc H.x H.be H.al H.u ≤
      H.pt.cost + (H.pt.kap + 3 / 2) * (π / 3 - arctan (√3 * H.pt.BB / H.pt.AA)) := by
  have hx1 := H.one_lt_x
  have hal1 := H.one_le_al
  have halx := H.al_lt_x
  have hxbe := H.x_le_be
  have hρ0 := H.rho_pos
  have hρ320 := H.rho_le
  have hal0 : 0 < H.al := by linarith only [hal1]
  have hbe0 : 0 < H.be := by linarith only [hx1, hxbe]
  have hbe : H.x * (1 + H.δ) = H.be := by unfold SmallerShortData.δ; field_simp; ring
  obtain ⟨hx2, hx13, hδ0, hδ19, hal1', hal2'⟩ := hS
  have hal : 13 / 5 * H.δ ≤ H.al - 1 := by linarith only [hal1']
  have hal' : H.al - 1 ≤ 3 * H.δ := by linarith only [hal2']
  obtain ⟨hR1, hR2, hT1, hT2, hA0, hAd, hZnat⟩ :=
    cost_continuation_shape hx2 hx13 hδ0 hδ19 hal hal'
  have hu2 : H.u ≤ 3/4+(ssRr H.x)^2/12 := by
    have hu := H.u_le_V.trans (ss_V_le_U0 hx1)
    have heq : ssU0 H.x = 3/4+(ssRr H.x)^2/12 := by
      unfold ssU0 ssRr
      field_simp
    rwa [heq] at hu
  rw [hbe] at hT1 hT2 hA0 hAd hZnat
  have hP : (H.be*H.x-H.al)*((H.x+2)*H.al+(2*H.x+1)*H.be) /
      ((1+H.x)^2*(H.al^2+H.al*H.be+H.be^2)) =
      ssRr H.x+(1+ssAn H.x H.be H.al)*ssTs H.al H.be := by
    unfold ssRr ssTs ssAn
    have hKA : 0 < H.al^2+H.al*H.be+H.be^2 := by positivity
    field_simp
    ring
  have hu34 := H.u_ge_34
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3g : (17 / 10 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  -- the incident ceilings `u ≤ U₁`, `u(1 + A) ≤ U₁`
  have hU1 : m2U (1 / (1 + H.x)) = (3 + ssRr H.x ^ 2) / 4 := by
    unfold m2U ssRr; field_simp; ring
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
  have hZ : costZ H.x H.be H.al = 2 * m2U (1 / (1 + H.x)) * (2 * H.be * H.x - H.x - H.al * H.be) *
      (1 / (H.x * (H.x + 2))) - (H.be * H.x - H.al) * ((H.x + 2) * H.al + (2 * H.x + 1) * H.be) /
        ((1 + H.x) ^ 2 * (H.al ^ 2 + H.al * H.be + H.be ^ 2)) := by
    rw [costZ, hP]; ring
  have hsh : ssShear H.x H.be H.al H.rho = √3 / 3 * ((H.be * H.x - H.al) *
      ((H.x + 2) * H.al + (2 * H.x + 1) * H.be) / ((1 + H.x) ^ 2 * (H.al ^ 2 + H.al * H.be + H.be ^ 2)) -
      2 * m2U (1 / (1 + H.x)) * (2 * H.be * H.x - H.x - H.al * H.be) * (H.rho / (1 - H.rho))) := by
    rw [ssShear, hU1']
  have hERT : (H.be * H.x - H.al) / ((1 + H.x) * (H.al + H.be)) =
      (ssRr H.x + ssTs H.al H.be) / 2 := by
    unfold ssRr ssTs
    have : 0 < H.be + H.al := by linarith only [hal0, hbe0]
    have : 0 < H.al + H.be := by linarith only [hal0, hbe0]
    field_simp; ring
  -- the cost identity `C_br = C_c + J₀h_c - J₀h_a`
  have hcost : H.pt.cost = costCc H.x H.be H.al H.u + costJ0 H.x H.u * -(costZ H.x H.be H.al / √3) -
      costJ0 H.x H.u * ssShear H.x H.be H.al H.rho := by
    rw [H.cost_pt_cost, costCc, hsh, hERT]
    have := cost_cost_id (u := H.u) (Q := 2 * H.be * H.x - H.x - H.al * H.be)
      (w := H.rho / (1 - H.rho)) (E := (ssRr H.x + ssTs H.al H.be) / 2) (J := costJ0 H.x H.u)
      hU0.ne' rfl hZ
    linear_combination this
  -- the shear at the central scale `h_c = -Z/√3`, below the actual shear
  have hcs : -(costZ H.x H.be H.al / √3) < ssShear H.x H.be H.al H.rho := by
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
    rw [Point.kap, H.cost_pt_gam]; exact (cost_kappa hΓ).le
  -- the angle constants
  set A := ssAn H.x H.be H.al with hAdef
  set R := ssRr H.x with hRdef
  set J₀ := costJ0 H.x H.u with hJdef
  set K := costK H.x H.be H.al H.u with hKdef
  set ha := ssShear H.x H.be H.al H.rho with hadef
  set hc := -(costZ H.x H.be H.al / √3) with hcdef
  have hu0 : 0 < H.u := by linarith only [hu34]
  have hJ0 : 0 < J₀ := by rw [hJdef, costJ0]; positivity
  have hK2 : A + 2 ≤ K := by
    rw [hKdef, costK]; have : 0 < 2 * (40 / 27) / J₀ := by positivity
    linarith only [this]
  have hKA : A < K := by linarith only [hK2]
  -- the pointwise barrier on `[h_c, h_a]`
  have hKJ : K = A + 2 + 2 * (40 / 27) / J₀ := rfl
  have hω : costomega H.x H.be H.al H.u =
      2 * arctan ((√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2))) := by
    rw [hcdef, neg_sq, sub_neg_eq_add]; rfl
  have hFc : costFc H.x H.be H.al H.u = costCc H.x H.be H.al H.u +
      161 / 54 * (π / 3 - costpsi H.x H.be H.al - costomega H.x H.be H.al H.u) := rfl
  clear_value A R J₀ K ha hc
  have hR2sq : R^2 < 1/7 := by nlinarith only [hR1,hR2]
  have hhc : -hc < R^2 := by
    rw [hcdef,neg_neg,div_lt_iff₀ (by positivity)]
    simpa only [mul_comm] using hZnat
  have hJbound : J₀ ≤ (9+R^2)/(2*(3+R^2)) := by
    rw [hJdef,costJ0,hU1]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [hu2]
  have hJ41 : J₀ ≤ 41/28 := by
    have hb : (9+R^2)/(2*(3+R^2)) ≤ 41/28 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hR1]
    exact hJbound.trans hb
  have hK4A : 4+A < K := by
    rw [hKJ]
    have ht : 2 < 2*(40/27)/J₀ := by
      rw [lt_div_iff₀ hJ0]
      linarith only [hJ41]
    linarith only [ht]
  have hD4 : 4 < √(K^2-A^2) := by
    rw [Real.lt_sqrt (by norm_num)]
    have hp := pow_lt_pow_left₀ (show A+4 < K by linarith only [hK4A])
      (show 0 ≤ A+4 by linarith only [hA0]) (by norm_num : (2:ℕ) ≠ 0)
    nlinarith only [hp,hA0]
  have hbar : ∀ h, hc ≤ h → h ≤ ha → J₀*√(h^2+A^2) <
      (161/54)*sin (2*arctan ((√(h^2+A^2)-h)/(K+√(K^2-A^2)))) := by
    intro h h1 h2
    have hH0 : 0 < -h := by linarith only [h2,hh]
    have hH1 : -h < R^2 := by linarith only [h1,hhc]
    have hHR : 2*A ≤ (-h)*R := by
      have hm := mul_le_mul_of_nonneg_right (neg_le_neg h2)
        (show 0 ≤ R by linarith only [hR1])
      linarith only [hm,hhR]
    have hb := cost_continuation_loss hR1 hR2 hδ19 hA0 hAd hH0 hH1 hHR hJ0 hJbound hKJ
    simpa only [neg_sq,sub_eq_add_neg] using hb
  -- the continuation from `δ_a` to `δ_c`
  obtain ⟨ha0', hac, hF⟩ := cost_cont_core (J₀ := J₀) (c := 161 / 54) hA0 hKA hcs hh hbar
  -- the supporting-line hypothesis of the angle bound holds with equality at `δ_a`
  obtain ⟨-, haπ, aeq⟩ := cost_tangent_inv hA0 hKA hh
  obtain ⟨e1, e2⟩ := cost_tangent_sqrt hA0 hKA ha0' haπ
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
  have hHRc : 2*A ≤ (-hc)*R := by
    have hm := mul_le_mul_of_nonneg_right (neg_le_neg hcs.le)
      (show 0 ≤ R by linarith only [hR1])
    linarith only [hm,hhR]
  have hnumR : √(hc^2+A^2)-hc ≤ (2+R/2)*(-hc) := by
    nlinarith only [hnum,hHRc]
  have hm1 := mul_le_mul_of_nonneg_left hhc.le
    (show 0 ≤ 2+R/2 by linarith only [hR1])
  have hm2 := mul_lt_mul_of_pos_left hR2sq
    (show 0 < 2+R/2 by linarith only [hR1])
  have hnum1 : √(hc^2+A^2)-hc < 1 := by
    nlinarith only [hnumR,hm1,hm2,hR2]
  have hy : (√(hc^2+A^2)-hc)/(K+√(K^2-A^2)) < 1/8 := by
    rw [div_lt_iff₀ (by linarith only [hD4,hK4A,hA0])]
    linarith only [hnum1,hD4,hK4A,hA0]
  have hatc : 2 * arctan ((√(hc ^ 2 + A ^ 2) - hc) / (K + √(K ^ 2 - A ^ 2))) < 1 / 4 := by
    linarith only [arctan_le_self hy0, hy]
  rw [← hω] at hac hF hatc
  generalize 2 * arctan ((√(ha ^ 2 + A ^ 2) - ha) / (K + √(K ^ 2 - A ^ 2))) = δa
    at ha0' hac hF haπ aeq e1 e2
  generalize costomega H.x H.be H.al H.u = δc at hac hF hatc hFc
  have hsup : √(A ^ 2 + ha ^ 2) ≤ K * sin δa + ha * cos δa := by rw [e1, e2, add_comm]
  -- `ψ + δ_a < π/2`
  have hψ : costpsi H.x H.be H.al < 11 / 25 := by
    have hs0 : 0 < √3 := by positivity
    have hT0 : 0 ≤ ssTs H.al H.be := by linarith only [hT1]
    have h1 := arctan_le_self (div_nonneg (by linarith only [hR1] : (0 : ℝ) ≤ R) hs0.le)
    have h2 := arctan_le_self (div_nonneg hT0 hs0.le)
    have h3 : ssTs H.al H.be / √3 ≤ R / √3 := div_le_div_of_nonneg_right hT2 hs0.le
    have h4 : R / √3 < 11 / 50 := by rw [div_lt_iff₀ hs0]; linarith only [hR2, hs3g]
    rw [costpsi, ← hRdef]
    linarith only [h1, h2, h3, h4]
  have hpi := Real.pi_gt_three
  have hδψ : δa < π / 2 - costpsi H.x H.be H.al := by linarith only [hψ, hpi, hac, hatc]
  rw [hAdef, hKdef, hadef] at hsup
  have hθ := H.cost_angle hκ ha0' hδψ hsup
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


/-- The physical completion theorem uses the unconditional exact-score
  comparison and the direct octagon-cost gap. -/
theorem octagonCost_lt_completion (hS : H.SmallShape) (hΓ : 1829 / 10000 < H.Γ) (hh : ssShear H.x H.be H.al H.rho < 0)
    (hhR : 2 * ssAn H.x H.be H.al < -ssShear H.x H.be H.al H.rho * ssRr H.x) :
    octagonCost < H.pt.cost + (H.pt.kap + 3 / 2) * (π / 3 - arctan (√3 * H.pt.BB / H.pt.AA)) := by
  have hx1 := H.one_lt_x
  have hbe : H.x * (1 + H.δ) = H.be := by
    unfold SmallerShortData.δ; field_simp; ring
  have hcont := H.cost_continuation hS hΓ hh hhR
  obtain ⟨hx2, hx13, hδ0, hδ19, hal1, hal2⟩ := hS
  have hal : 13 / 5 * H.δ ≤ H.al - 1 := by linarith
  have hal' : H.al - 1 ≤ 3 * H.δ := by linarith
  obtain ⟨hu1, hu2⟩ := cost_u_bounds hx2 hx13 hδ0 hδ19 hal hal'
  rw [hbe, ← H.u_eq] at hu1 hu2
  have hu3 : H.u ≤ (3 + ssTs H.al H.be ^ 2) / 4 := by
    have h := H.u_le_rA
    have := H.one_le_al
    have := H.x_le_be
    have hpos : 0 < H.al + H.be := by linarith
    have hpos' : 0 < H.be + H.al := by linarith
    have : m2U (ssRA H.al H.be) = (3 + ssTs H.al H.be ^ 2) / 4 := by
      unfold m2U ssRA ssTs
      field_simp
      ring
    rwa [this] at h
  have hF := cost_Fc_gt hx2 hx13 hδ0 hδ19 hal hal' (u := H.u)
    hu1.le hu2 (by rw [hbe]; exact hu3)
  rw [hbe] at hF
  have hB : 9/4000 < costBExact (ssRr H.x) (ssTs H.al H.be) (s6VarianceFloor (ssRr H.x) H.δ) (costZU (ssRr H.x) H.δ) (costZL (ssRr H.x) H.δ) := by
    obtain ⟨hR1, hR2, -⟩ := cost_shape hx2 hx13 hδ0 hδ19 hal hal'
    obtain ⟨η, hη1, hη2, hη⟩ : ∃ η : ℝ, 13 / 5 ≤ η ∧ η ≤ 3 ∧ H.al = 1 + η * H.δ := by
      rcases hδ0.lt_or_eq with hpos | hzero
      · refine ⟨(H.al - 1) / H.δ, ?_, ?_, ?_⟩
        · rw [le_div_iff₀ hpos]; linarith
        · rw [div_le_iff₀ hpos]; linarith
        · field_simp; ring
      · refine ⟨13 / 5, le_rfl, by norm_num, ?_⟩
        rw [← hzero] at hal1 hal2 ⊢
        linarith
    rw [← hbe, hη, cost_T_eq hx1 hδ0 (by linarith)]
    exact s6_final_score_gt hR1 hR2 hδ0 hδ19 hη1 hη2
  have ho := cost_octagon_lt_exact_score hB
  linarith only [ho,hF,hcont]


end SmallerShortData

/-- **The cost bound for the actual window**: on the small-shape
domain, with `Γ > 1829/10000`, `h < 0`, `-hR > 2A`, the window cost and completion exceed
`A_oct`. -/
theorem M2Short.octagonCost_lt_completion (D : M2Short) (h1 : 2 ≤ D.C / D.a) (h2 : D.C / D.a ≤ 13 / 6)
    (h3 : 0 ≤ D.B / D.C - 1) (h4 : D.B / D.C - 1 ≤ 1 / 19)
    (h5 : 1 + 13 / 5 * (D.B / D.C - 1) ≤ D.A / D.a) (h6 : D.A / D.a ≤ 1 + 3 * (D.B / D.C - 1))
    (hΓ : 1829 / 10000 < D.Γ)
    (hh : ssShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) < 0)
    (hhR : 2 * ssAn (D.C / D.a) (D.B / D.a) (D.A / D.a) <
      -ssShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) *
        ssRr (D.C / D.a)) :
    octagonCost <
      D.ss_pt.cost + (D.ss_pt.kap + 3 / 2) * (π / 3 - arctan (√3 * D.ss_pt.BB / D.ss_pt.AA)) := by
  rw [← D.toData_x, ← D.toData_be, ← D.toData_al, ← D.toData_rho] at hh hhR
  have h := D.toData.octagonCost_lt_completion (D.ss_smallShape h1 h2 h3 h4 h5 h6) (by rwa [D.toData_Γ]) hh hhR
  rwa [D.toData_pt] at h

end SmoothedOctagon
