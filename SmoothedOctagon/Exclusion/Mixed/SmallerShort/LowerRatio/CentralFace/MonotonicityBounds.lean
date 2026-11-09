module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.PathDerivative

/-!
# Smaller-short window, lower ratio, central face: auxiliary bounds for the monotonicity steps

* `lr_eps_le`: `ε(y) ≤ 1/625` for `2/3 ≤ y ≤ 3/2`;
* `lrc_y_bounds`: `2/3 ≤ y ≤ 3/2` on the box `8/5 ≤ x ≤ 2`, `1 ≤ α ≤ 7/6`,
  `x + (α - 1)/2 ≤ β ≤ x + 4(α - 1)/5` (`T = 2/y ∈ [4/3, 3]`);
* `lr_Ul_hasDerivAt`, `lr_Ul_bounds`: the β-dependent ceiling `u_ℓ(x, β)` decreases in `β` with
  slope at least `-15/1992`, and `3/4 ≤ u_ℓ ≤ 3/4 + 2/249` for `1 < x ≤ 2 ≤ ...`, `β ≥ x`;
* `lr_Vbar_hasDerivAt`, `lr_Vbar_bounds`: `u_v = V̄(x)` increases, `3/4 ≤ V̄ ≤ 3/4 + 2/249`.
-/

@[expose] public section

namespace SmoothedOctagon

theorem lr_eps_le {y : ℝ} (h0 : 2 / 3 ≤ y) (h1 : y ≤ 3 / 2) : lreps y ≤ 1 / 625 := by
  unfold lreps
  have hy : 0 < y + 1 := by linarith
  have hz : |(y - 1) / (y + 1)| ≤ 1 / 5 := by
    rw [abs_div, abs_of_pos hy, div_le_iff₀ hy]
    rw [abs_le]; constructor <;> linarith
  have h4 : ((y - 1) / (y + 1)) ^ 4 = |(y - 1) / (y + 1)| ^ 4 := by
    rw [← abs_pow]; exact (abs_of_nonneg (by positivity)).symm
  rw [h4]
  calc |(y - 1) / (y + 1)| ^ 4 ≤ (1 / 5) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hz 4
    _ = 1 / 625 := by norm_num

theorem lr_eps_nonneg (y : ℝ) : 0 ≤ lreps y := by unfold lreps; positivity

theorem lrc_y_bounds {x a b : ℝ} (hx0 : 8 / 5 ≤ x) (hx1 : x ≤ 2) (ha0 : 1 ≤ a) (ha1 : a ≤ 7 / 6)
    (hb0 : x + 1 / 2 * (a - 1) ≤ b) (hb1 : b ≤ x + 4 / 5 * (a - 1)) :
    2 / 3 ≤ lrcy x a b ∧ lrcy x a b ≤ 3 / 2 := by
  have hK : 0 < lrcK x a := by unfold lrcK; nlinarith
  unfold lrcy
  constructor
  · rw [le_div_iff₀ hK]; unfold lrcK; nlinarith
  · rw [div_le_iff₀ hK]; unfold lrcK; nlinarith

/-- The derivative of `β ↦ u_ℓ(x, β)`. -/
theorem lr_Ul_hasDerivAt {x b : ℝ} (hx : 1 < x) (hb : 1 < b) :
    HasDerivAt (fun s => ssUl x s)
      (-(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (b - 1) ^ 2))) b := by
  have h0 : 8 * (1 + x) * (35 * x + 13) * (b - 1) ≠ 0 := by
    have : 0 < b - 1 := by linarith
    exact (mul_pos (by positivity) this).ne'
  have := ((hasDerivAt_id' b).add_const (15 * x - 16)).const_mul ((x - 1) ^ 2) |>.fun_div
    (((hasDerivAt_id' b).sub_const 1).const_mul (8 * (1 + x) * (35 * x + 13))) h0
  unfold ssUl
  convert (this.const_add (3 / 4)) using 1
  · funext s; ring
  · have : b - 1 ≠ 0 := by linarith
    field_simp
    ring

theorem lr_Ul_deriv_bounds {x b : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hb : x ≤ b) :
    -(15 / 1992) ≤ -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (b - 1) ^ 2)) ∧
      -(15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (b - 1) ^ 2)) ≤ 0 := by
  have hx1 : 0 < x - 1 := by linarith
  have hb1 : x - 1 ≤ b - 1 := by linarith
  have hb0 : 0 < b - 1 := by linarith
  constructor
  · rw [neg_le_neg_iff, div_le_iff₀ (mul_pos (by positivity) (pow_pos hb0 2))]
    have h1 : (x - 1) ^ 3 ≤ (x - 1) * (b - 1) ^ 2 := by
      have := pow_le_pow_left₀ hx1.le hb1 2
      nlinarith
    have h2 : 1992 * (x - 1) ≤ 8 * (1 + x) * (35 * x + 13) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg (b - 1))]
  · have : 0 ≤ 15 * (x - 1) ^ 3 / (8 * (1 + x) * (35 * x + 13) * (b - 1) ^ 2) := by positivity
    linarith

theorem lr_Ul_bounds {x b : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hb : x ≤ b) :
    3 / 4 ≤ ssUl x b ∧ ssUl x b ≤ 3 / 4 + 2 / 249 := by
  unfold ssUl
  have hb1 : 0 < b - 1 := by linarith
  have hD : 0 < 8 * (1 + x) * (35 * x + 13) * (b - 1) := by positivity
  constructor
  · have : 0 ≤ (x - 1) ^ 2 * (b + 15 * x - 16) / (8 * (1 + x) * (35 * x + 13) * (b - 1)) := by
      apply div_nonneg _ hD.le
      apply mul_nonneg (sq_nonneg _); linarith
    linarith
  · have : (x - 1) ^ 2 * (b + 15 * x - 16) / (8 * (1 + x) * (35 * x + 13) * (b - 1)) ≤ 2 / 249 := by
      rw [div_le_iff₀ hD]
      have h1 : (x - 1) ^ 2 * (b + 15 * x - 16) ≤ 16 * (x - 1) ^ 2 * (b - 1) := by
        have : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
        nlinarith
      have h2 : 16 * (x - 1) ^ 2 * 249 ≤ 2 * (8 * (1 + x) * (35 * x + 13)) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right h2 hb1.le]
    linarith

/-- `u_ℓ(x, β) ≤ V̄(x)` for `β ≥ x > 1`. -/
theorem lr_Ul_le_Vbar {x b : ℝ} (hx : 1 < x) (hb : x ≤ b) : ssUl x b ≤ ssVbar x := by
  unfold ssUl ssVbar
  have hb1 : 0 < b - 1 := by linarith
  have hD : 0 < 8 * (1 + x) * (35 * x + 13) * (b - 1) := by positivity
  have hE : 0 < (x + 1) * (35 * x + 13) := by positivity
  rw [add_le_add_iff_left, div_le_div_iff₀ hD hE]
  have : 0 ≤ (x - 1) ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg this (sub_nonneg.2 hb), mul_nonneg (mul_nonneg this (sub_nonneg.2 hb)) hE.le]

theorem lr_Vbar_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt ssVbar (2 * (2 * (x - 1) * ((x + 1) * (35 * x + 13)) -
      (x - 1) ^ 2 * (70 * x + 48)) / ((x + 1) * (35 * x + 13)) ^ 2) x := by
  have h0 : (x + 1) * (35 * x + 13) ≠ 0 := by positivity
  have := ((((hasDerivAt_id' x).sub_const 1).fun_pow 2).const_mul 2).fun_div
    (((hasDerivAt_id' x).add_const 1).fun_mul (((hasDerivAt_id' x).const_mul 35).add_const 13)) h0
  have h := this.const_add (3 / 4)
  have he : ssVbar = fun s => 3 / 4 + 2 * (s - 1) ^ 2 / ((s + 1) * (35 * s + 13)) := by
    funext s; unfold ssVbar; ring
  rw [he]
  convert h using 1
  push_cast
  ring

theorem lr_Vbar_deriv_nonneg {x : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) :
    0 ≤ 2 * (2 * (x - 1) * ((x + 1) * (35 * x + 13)) -
      (x - 1) ^ 2 * (70 * x + 48)) / ((x + 1) * (35 * x + 13)) ^ 2 := by
  apply div_nonneg _ (sq_nonneg _)
  have : 0 < x - 1 := by linarith
  nlinarith [mul_pos this this]

theorem lr_Vbar_bounds {x : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) :
    3 / 4 ≤ ssVbar x ∧ ssVbar x ≤ 3 / 4 + 2 / 249 := by
  unfold ssVbar
  have hE : 0 < (x + 1) * (35 * x + 13) := by positivity
  constructor
  · have : 0 ≤ 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) := by positivity
    linarith
  · have : 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) ≤ 2 / 249 := by
      rw [div_le_iff₀ hE]
      nlinarith
    linarith

end SmoothedOctagon
