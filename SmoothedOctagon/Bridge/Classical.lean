module

public import SmoothedOctagon.Bridge.Octagon
public import SmoothedOctagon.Defs

/-!
# Reinhardt's smoothed octagon

Reinhardt described the smoothed octagon as a regular octagon whose corners are cut off by arcs of
hyperbolas. The library defines it instead as the region swept by the curve `σ₀(t) = g(t) s₀` of
the octagon's trajectory (`octagon`). This module proves that the two agree up to a linear map.

Write `d_k(x) = 1 - (x₀ cos(kπ/4) + x₁ sin(kπ/4))` for the distance from `x` to the `k`-th side
line of the regular octagon of inradius `1` (positive inside), `k : Fin 8`. Reinhardt's octagon
`smoothedOctagon` is the regular octagon `d_k(x) ≥ 0` with each corner `k` (between sides `k` and
`k + 1`) cut along the hyperbola `d_{k-1} d_{k+2} = √2/4`, whose asymptotes are the next two side
lines: beyond the chord `d_k + d_{k+1} = 3/2 - √2` through its two points of tangency with the
sides, only the points with `d_{k-1} d_{k+2} ≥ √2/4` are kept.

## The proof

Let `A = diag(1, b/√3)`, `b = 2√2 - 1 = 3y₀²`. In the frame of `A`:

* `A g₀(s) A⁻¹` has entries in `ℚ(√2)(W)`, `W = exp(√3 y₀ s) ∈ [1, √2]` on `[0, t_sw]`
  (`cls_frame_segG`), and `A h A⁻¹` is the rotation by `-π/4`, `h = g_sw R⁻¹`
  (`cls_frame_h`). Since `σ₀(t + 3 t_sw) = -h³ σ₀(t)`, the curve `A σ₀` is invariant under the
  rotation by `π/4` (`cls_frame_shift`).
* On `[0, 3 t_sw]`, `A σ₀` runs along side `0` (`(1, 1 - 1/W)`), around corner `0` on the
  hyperbola `d₇ d₂ = √2/4` (`(√2 + 1 - (√2/2)(W + 1/W), 1 - √2/(2W))`), and along side `1`
  (`(√2 - W/2, W/2)`) (`cls_piece₀`, `cls_piece₁`, `cls_piece₂`).
* Each point `q` of these pieces lies in `smoothedOctagon`, and `μ q` does not for `μ > 1`
  (`cls_good_piece₀`, …). Reinhardt's octagon is invariant under the rotation by `π/4`, so the
  same holds for every point `A σ₀(t)` (`cls_good`).
* Reinhardt's octagon is star-shaped about `0`, so `A` maps the radial hull of `σ₀` into it. For
  the converse, a point `p ≠ 0` of Reinhardt's octagon is a positive multiple `λ q` of a point
  `q = A σ₀(t)` (intermediate value theorem, `σ₀(t + 3 t_f) = -σ₀(t)`), and `λ ≤ 1` because
  `μ q` lies outside for `μ > 1`.

## Main API

* `smoothedOctagon`: Reinhardt's smoothed octagon.
* `clsEquiv`: the linear map `A`.
* `cls_image_octagon`: `A '' octagon = smoothedOctagon`.
* `octagon_classical`: the convex hull of the arcs of the octagon trajectory is a linear image of
  `smoothedOctagon`.
* `cls_exists_affine_iff`: affine images of `octagon` are the affine images of `smoothedOctagon`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set Matrix

/-! ### Constants -/

lemma cls_sqrt2_sq : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma cls_sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma cls_one_lt_sqrt2 : 1 < √2 := by
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma cls_sqrt2_lt : √2 < 3 / 2 := by
  nlinarith [cls_sqrt2_sq, Real.sqrt_nonneg 2]

lemma cls_sqrt3_pos : 0 < √3 := by positivity

lemma cls_sqrt2_pow3 : √2 ^ 3 = 2 * √2 := by rw [pow_succ, cls_sqrt2_sq]
lemma cls_sqrt2_pow4 : √2 ^ 4 = 4 := by
  rw [show √2 ^ 4 = (√2 ^ 2) ^ 2 by ring, cls_sqrt2_sq]; norm_num
lemma cls_sqrt2_pow5 : √2 ^ 5 = 4 * √2 := by rw [pow_succ, cls_sqrt2_pow4]
lemma cls_sqrt2_pow6 : √2 ^ 6 = 8 := by
  rw [show √2 ^ 6 = (√2 ^ 2) ^ 3 by ring, cls_sqrt2_sq]; norm_num
lemma cls_sqrt3_pow3 : √3 ^ 3 = 3 * √3 := by rw [pow_succ, cls_sqrt3_sq]
lemma cls_sqrt3_pow4 : √3 ^ 4 = 9 := by
  rw [show √3 ^ 4 = (√3 ^ 2) ^ 2 by ring, cls_sqrt3_sq]; norm_num

/-- `b = 2√2 - 1 = 3 y₀²`. -/
noncomputable def clsB : ℝ := 2 * √2 - 1

lemma cls_b_pos : 0 < clsB := by
  unfold clsB; linarith [cls_one_lt_sqrt2]

/-- `θ₁ = π/4`. -/
lemma cls_θ_one : θ 1 = Real.pi / 4 := by
  simp [θ]; ring

/-- `y₀² = (2√2 - 1)/3`. -/
lemma cls_y0_sq : y₀ 1 ^ 2 = clsB / 3 := by
  rw [poly_y₀_sq le_rfl, cls_θ_one, Real.cos_pi_div_four, clsB]
  have h2 : (0 : ℝ) < √2 := by positivity
  field_simp
  nlinarith [cls_sqrt2_sq]

lemma cls_y0_pos : 0 < y₀ 1 := poly_y0_pos (poly_y₀_mem le_rfl).1

/-- `W(t_sw) = exp(√3 y₀ t_sw) = √2`. -/
lemma cls_W_tsw : Real.exp (√3 * y₀ 1 * tsw 1) = √2 := by
  rw [tsw_eq_switchTime, str_exp_switchTime cls_y0_pos, cls_y0_sq, clsB]
  have h2 : (0 : ℝ) < √2 := by positivity
  field_simp
  nlinarith [cls_sqrt2_sq]

/-- On `[0, t_sw]`, `1 ≤ W ≤ √2`. -/
lemma cls_W_mem {s : ℝ} (hs : s ∈ Icc 0 (tsw 1)) :
    1 ≤ Real.exp (√3 * y₀ 1 * s) ∧ Real.exp (√3 * y₀ 1 * s) ≤ √2 := by
  have h := str_W_mem cls_y0_pos (t := s) (by rwa [← tsw_eq_switchTime])
  have e : 4 / (3 * y₀ 1 ^ 2 + 1) = √2 := by
    rw [← cls_W_tsw, tsw_eq_switchTime, str_exp_switchTime cls_y0_pos]
  rwa [e] at h

/-! ### The linear map `A = diag(1, b/√3)` -/

/-- The vertical scale `b/√3` of `A`. -/
noncomputable def clsβ : ℝ := clsB / √3

lemma cls_β_pos : 0 < clsβ := div_pos cls_b_pos cls_sqrt3_pos

/-- `A = diag(1, b/√3)`, the linear map from the library's octagon to Reinhardt's. -/
noncomputable def clsEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 0, clsβ * v 1]
  invFun v := ![v 0, v 1 / clsβ]
  map_add' v w := by ext i; fin_cases i <;> simp; ring
  map_smul' c v := by ext i; fin_cases i <;> simp; ring
  left_inv v := by
    ext i; fin_cases i <;> simp; field_simp [cls_β_pos.ne']
  right_inv v := by
    ext i; fin_cases i <;> simp; field_simp [cls_β_pos.ne']

lemma cls_apply (v : Fin 2 → ℝ) : clsEquiv v = ![v 0, clsβ * v 1] := rfl

/-- The rotation by `π/4`. -/
noncomputable def clsRot (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![√2 / 2 * (v 0 - v 1), √2 / 2 * (v 0 + v 1)]

/-- The rotation by `-π/4`. -/
noncomputable def clsRotInv (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![√2 / 2 * (v 0 + v 1), √2 / 2 * (v 1 - v 0)]

/-- `A g₀(s) A⁻¹` in the frame of `A`, `W = exp(√3 y₀ s)`. -/
noncomputable def clsG (W : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![v 0 - (W - 1) / clsB * v 1, (1 - 1 / W) * v 0 + (1 - (W - 2 + 1 / W) / clsB) * v 1]

/-- `A g₀(s) = (A g₀(s) A⁻¹) A`. -/
lemma cls_frame_segG (s : ℝ) (v : Fin 2 → ℝ) :
    clsEquiv (segG (y₀ 1) s *ᵥ v) = clsG (Real.exp (√3 * y₀ 1 * s)) (clsEquiv v) := by
  have hW := Real.exp_pos (√3 * y₀ 1 * s)
  have hb := cls_b_pos
  have h3 := cls_sqrt3_pos
  have hy := cls_y0_sq
  rw [segG_eq _ _ cls_y0_pos]
  generalize Real.exp (√3 * y₀ 1 * s) = W at hW ⊢
  ext i
  fin_cases i <;>
    simp [cls_apply, clsG, clsβ, dotProduct, Fin.sum_univ_two, hy]
  · field_simp
    ring
  · field_simp
    linear_combination (-(W - 1) * v 0) * cls_sqrt3_sq

/-- `A h A⁻¹` is the rotation by `-π/4`, `h = g_sw R⁻¹`. -/
lemma cls_frame_h (v : Fin 2 → ℝ) :
    clsEquiv ((segG (y₀ 1) (tsw 1) * R⁻¹) *ᵥ v) = clsRotInv (clsEquiv v) := by
  rw [← Matrix.mulVec_mulVec, cls_frame_segG, cls_W_tsw, str_R_inv]
  have hb := cls_b_pos
  have h3 := cls_sqrt3_pos
  have h2 : (0 : ℝ) < √2 := by positivity
  ext i
  fin_cases i <;>
    simp [cls_apply, clsG, clsβ, clsRotInv, dotProduct, Fin.sum_univ_two] <;>
    field_simp [hb.ne'] <;>
    simp only [clsB] <;>
    ring_nf <;>
    simp only [cls_sqrt3_sq, cls_sqrt2_sq, cls_sqrt2_pow3] <;>
    ring_nf

lemma cls_frame_h' (v : Fin 2 → ℝ) :
    clsEquiv (segG (y₀ 1) (tsw 1) *ᵥ (R⁻¹ *ᵥ v)) = clsRotInv (clsEquiv v) := by
  rw [Matrix.mulVec_mulVec, cls_frame_h]

/-! ### The curve `A σ₀` on one eighth of a period -/

lemma cls_tsw_pos : 0 < tsw 1 := oct_tsw_pos le_rfl

/-- On `[0, t_sw]` the trajectory is the `e₃`-trajectory `g₀`. -/
lemma cls_G_base {s : ℝ} (hs : s ∈ Icc 0 (tsw 1)) : smoothedPolygonG 1 s = segG (y₀ 1) s := by
  rcases hs.2.lt_or_eq with hlt | heq
  · rw [oct_G_of_nonneg le_rfl hs.1, polygonG]
    have h0 : ⌊s / tsw 1⌋₊ = 0 :=
      Nat.floor_eq_zero.2 ((div_lt_one cls_tsw_pos).2 hlt)
    simp [h0]
  · subst heq
    have h := oct_G_add_tsw (k := 1) le_rfl 0
    rw [zero_add, oct_G_zero le_rfl, Matrix.mul_one, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (by rw [str_det_R]; exact isUnit_one), Matrix.mul_one] at h
    exact h

lemma cls_sixthRoot_zero : sixthRoot 0 = ![1, 0] := by
  ext i; fin_cases i <;> simp [sixthRoot]

lemma cls_R_s0 : R *ᵥ ![1, 0] = ![1 / 2, √3 / 2] := by
  ext i; fin_cases i <;> simp [R]

lemma cls_R_s1 : R *ᵥ ![1 / 2, √3 / 2] = ![-1 / 2, √3 / 2] := by
  ext i; fin_cases i
  · simp [R]; ring_nf; simp only [cls_sqrt3_sq]; ring
  · simp [R]; ring

/-- `W = exp(√3 y₀ s)`. -/
noncomputable abbrev clsW (s : ℝ) : ℝ := Real.exp (√3 * y₀ 1 * s)

/-- The first piece, along side `0`: `A σ₀(s) = (1, 1 - 1/W)`. -/
lemma cls_piece₀ {s : ℝ} (hs : s ∈ Icc 0 (tsw 1)) :
    clsEquiv (smoothedPolygonCurve 1 0 s) = ![1, 1 - 1 / clsW s] := by
  rw [smoothedPolygonCurve, cls_G_base hs, cls_sixthRoot_zero, cls_frame_segG]
  have hW := Real.exp_pos (√3 * y₀ 1 * s)
  ext i; fin_cases i <;> simp [cls_apply, clsG]

/-- The second piece, around corner `0`:
`A σ₀(s + t_sw) = (√2 + 1 - (√2/2)(W + 1/W), 1 - √2/(2W))`. -/
lemma cls_piece₁ {s : ℝ} (hs : s ∈ Icc 0 (tsw 1)) :
    clsEquiv (smoothedPolygonCurve 1 0 (s + tsw 1)) =
      ![√2 + 1 - √2 / 2 * (clsW s + 1 / clsW s), 1 - √2 / (2 * clsW s)] := by
  rw [smoothedPolygonCurve, oct_G_add_tsw le_rfl, cls_G_base hs, cls_sixthRoot_zero,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cls_R_s0, cls_frame_h, cls_frame_segG]
  have hW := Real.exp_pos (√3 * y₀ 1 * s)
  have hb := cls_b_pos
  ext i; fin_cases i <;> simp [cls_apply, clsG, clsRotInv, clsβ] <;> field_simp <;>
    simp only [clsB] <;> ring_nf <;> simp only [cls_sqrt2_sq] <;> ring_nf

/-- The third piece, along side `1`: `A σ₀(s + 2 t_sw) = (√2 - W/2, W/2)`. -/
lemma cls_piece₂ {s : ℝ} (hs : s ∈ Icc 0 (tsw 1)) :
    clsEquiv (smoothedPolygonCurve 1 0 (s + 2 * tsw 1)) = ![√2 - clsW s / 2, clsW s / 2] := by
  rw [smoothedPolygonCurve, show s + 2 * tsw 1 = (s + tsw 1) + tsw 1 by ring,
    oct_G_add_tsw le_rfl, oct_G_add_tsw le_rfl, cls_G_base hs, cls_sixthRoot_zero]
  simp only [← Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [cls_R_s0, cls_R_s1, cls_frame_h', cls_frame_h', cls_frame_segG]
  have hW := Real.exp_pos (√3 * y₀ 1 * s)
  have hb := cls_b_pos
  ext i; fin_cases i <;> simp [cls_apply, clsG, clsRotInv, clsβ] <;> field_simp <;>
    simp only [clsB] <;> ring_nf <;> simp only [cls_sqrt2_sq, cls_sqrt2_pow3] <;> ring_nf

/-- `A σ₀(t + 3 t_sw)` is `A σ₀(t)` turned by `π/4`. -/
lemma cls_frame_shift (t : ℝ) :
    clsEquiv (smoothedPolygonCurve 1 0 (t + 3 * tsw 1)) =
      clsRot (clsEquiv (smoothedPolygonCurve 1 0 t)) := by
  rw [smoothedPolygonCurve, smoothedPolygonCurve, oct_G_add_three_tsw le_rfl,
    Matrix.neg_mul, Matrix.neg_mulVec, map_neg, pow_succ, pow_succ, pow_one]
  simp only [← Matrix.mulVec_mulVec]
  rw [cls_frame_h', cls_frame_h', cls_frame_h']
  generalize clsEquiv (smoothedPolygonG 1 t *ᵥ sixthRoot 0) = v
  ext i; fin_cases i <;> simp [clsRot, clsRotInv] <;> ring_nf <;>
    simp only [cls_sqrt2_pow3] <;> ring_nf

/-- `σ₀(t + 3 t_f) = -σ₀(t)`. -/
lemma cls_curve_add_three_tf (t : ℝ) :
    smoothedPolygonCurve 1 0 (t + 3 * tf 1) = -smoothedPolygonCurve 1 0 t := by
  rw [smoothedPolygonCurve, smoothedPolygonCurve,
    show t + 3 * tf 1 = ((t + tf 1) + tf 1) + tf 1 by ring, oct_G_add_tf le_rfl,
    oct_G_add_tf le_rfl, oct_G_add_tf le_rfl]
  have hR3 := poly_R_pow_three
  rw [pow_succ, pow_succ, pow_one] at hR3
  simp only [Matrix.mul_assoc, hR3, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mulVec]

lemma cls_curve_continuous : Continuous (smoothedPolygonCurve 1 0) :=
  (oct_G_continuous le_rfl).matrix_mulVec continuous_const

/-! ### Reinhardt's octagon -/

/-- The eight distances, explicitly. -/
noncomputable def clsD (x : Fin 2 → ℝ) : Fin 8 → ℝ :=
  ![1 - x 0, 1 - √2 / 2 * (x 0 + x 1), 1 - x 1, 1 - √2 / 2 * (x 1 - x 0), 1 + x 0,
    1 + √2 / 2 * (x 0 + x 1), 1 + x 1, 1 - √2 / 2 * (x 0 - x 1)]

lemma cls_dist_eq (k : Fin 8) (x : Fin 2 → ℝ) : octagonSideDist k x = clsD x k := by
  fin_cases k
  · simp [octagonSideDist, clsD]
  · simp [octagonSideDist, clsD, Real.cos_pi_div_four, Real.sin_pi_div_four]; ring
  · have e : (2 : ℝ) * Real.pi / 4 = Real.pi / 2 := by ring
    simp [octagonSideDist, clsD, e]
  · have e : (3 : ℝ) * Real.pi / 4 = Real.pi - Real.pi / 4 := by ring
    simp [octagonSideDist, clsD, e, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_four,
      Real.sin_pi_div_four]; ring
  · have e : (4 : ℝ) * Real.pi / 4 = Real.pi := by ring
    simp [octagonSideDist, clsD, e]
  · have e : (5 : ℝ) * Real.pi / 4 = Real.pi / 4 + Real.pi := by ring
    simp [octagonSideDist, clsD, e, Real.cos_add_pi, Real.sin_add_pi, Real.cos_pi_div_four,
      Real.sin_pi_div_four]; ring
  · have e : (6 : ℝ) * Real.pi / 4 = Real.pi / 2 + Real.pi := by ring
    simp [octagonSideDist, clsD, e, Real.cos_add_pi, Real.sin_add_pi]
  · have e : (7 : ℝ) * Real.pi / 4 = -(Real.pi / 4) + 2 * Real.pi := by ring
    simp [octagonSideDist, clsD, e, Real.cos_add_two_pi, Real.sin_add_two_pi, Real.cos_neg,
      Real.sin_neg, Real.cos_pi_div_four, Real.sin_pi_div_four]; ring

/-- The condition of Reinhardt's octagon at the side `k` and the corner `k`. -/
def ClsCond (d : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  0 ≤ d k ∧ (d k + d (k + 1) ≤ 3 / 2 - √2 → √2 / 4 ≤ d (k - 1) * d (k + 2))

lemma cls_mem_iff (x : Fin 2 → ℝ) :
    x ∈ smoothedOctagon ↔ ∀ k, ClsCond (clsD x) k := by
  simp [smoothedOctagon, ClsCond, cls_dist_eq]

/-- `d_k(μx) = 1 - μ(1 - d_k(x))`. -/
lemma cls_D_smul (μ : ℝ) (x : Fin 2 → ℝ) (k : Fin 8) :
    clsD (μ • x) k = 1 - μ * (1 - clsD x k) := by
  fin_cases k <;> simp [clsD] <;> ring

/-- `d_k(Tx) = d_{k-1}(x)` for the rotation `T` by `π/4`. -/
lemma cls_D_rot (x : Fin 2 → ℝ) (k : Fin 8) : clsD (clsRot x) k = clsD x (k - 1) := by
  fin_cases k <;> simp [clsD, clsRot] <;> ring_nf <;> simp only [cls_sqrt2_sq] <;> ring

lemma cls_mem_rot_iff (x : Fin 2 → ℝ) :
    clsRot x ∈ smoothedOctagon ↔ x ∈ smoothedOctagon := by
  rw [cls_mem_iff, cls_mem_iff]
  have e : ∀ k, ClsCond (clsD (clsRot x)) k ↔ ClsCond (clsD x) (k - 1) := by
    intro k
    simp only [ClsCond, cls_D_rot]
    rw [show k + 1 - 1 = k - 1 + 1 by revert k; decide,
      show k + 2 - 1 = k - 1 + 2 by revert k; decide]
  simp only [e]
  refine ⟨fun h k ↦ ?_, fun h k ↦ h (k - 1)⟩
  have hsub : ∀ j : Fin 8, j + 1 - 1 = j := by decide
  have := h (k + 1)
  rwa [hsub] at this

lemma cls_rot_smul (μ : ℝ) (x : Fin 2 → ℝ) : clsRot (μ • x) = μ • clsRot x := by
  ext i; fin_cases i <;> simp [clsRot] <;> ring

/-- Reinhardt's octagon is star-shaped about the origin. -/
lemma cls_smul_mem {x : Fin 2 → ℝ} (hx : x ∈ smoothedOctagon) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) : r • x ∈ smoothedOctagon := by
  rw [cls_mem_iff] at hx ⊢
  intro k
  have hk := hx k
  have hu := (hx (k - 1)).1
  have hv := (hx (k + 2)).1
  simp only [ClsCond, cls_D_smul] at hk ⊢
  set a := clsD x k
  set b := clsD x (k + 1)
  set u := clsD x (k - 1)
  set v := clsD x (k + 2)
  have h2 := cls_sqrt2_sq
  have h2a : 1 < √2 := cls_one_lt_sqrt2
  have h2b : √2 < 3 / 2 := cls_sqrt2_lt
  refine ⟨by nlinarith [mul_nonneg hr0 hk.1], fun hsum ↦ ?_⟩
  have hab : a + b ≤ 3 / 2 - √2 := by
    by_contra hab
    push Not at hab
    nlinarith [mul_le_mul_of_nonneg_left hab.le hr0]
  have huv := hk.2 hab
  have hpos : 0 ≤ √2 / 4 := by positivity
  have hsum2 : 2 * (√2 / 4) ≤ u + v := by
    nlinarith [sq_nonneg (u - v), mul_nonneg hu hv]
  have h1r : 0 ≤ 1 - r := by linarith
  nlinarith [mul_nonneg h1r hr0, mul_nonneg (mul_nonneg h1r hr0) (by linarith : 0 ≤ u + v - 2 * (√2 / 4)),
    mul_nonneg (mul_nonneg hr0 hr0) (by linarith : 0 ≤ u * v - √2 / 4), mul_nonneg h1r h1r]

/-- A point `q` of the boundary of Reinhardt's octagon: `q` lies in it, and `μ q` does not for
`μ > 1`. -/
def ClsGood (q : Fin 2 → ℝ) : Prop :=
  q ∈ smoothedOctagon ∧ ∀ μ : ℝ, 1 < μ → μ • q ∉ smoothedOctagon

lemma cls_good_rot_iff (q : Fin 2 → ℝ) : ClsGood (clsRot q) ↔ ClsGood q := by
  simp only [ClsGood, cls_mem_rot_iff, ← cls_rot_smul]

/-! ### The three pieces are on the boundary of Reinhardt's octagon -/

lemma cls_sqrt2_gt : 1.41 < √2 := by nlinarith [cls_sqrt2_sq, Real.sqrt_nonneg 2]

lemma cls_sqrt2_lt' : √2 < 1.42 := by nlinarith [cls_sqrt2_sq, Real.sqrt_nonneg 2]

/-- Past a point `(u, v)` of the hyperbola, moving away from `(1, 1)`, the product drops:
`(1 - μ(1 - v))(1 - μ(1 - u)) < uv` for `μ > 1` while both factors stay nonnegative. -/
lemma cls_beyond {u v μ : ℝ} (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1)
    (hμ : 1 < μ) (hU : 0 ≤ 1 - μ * (1 - u)) :
    (1 - μ * (1 - v)) * (1 - μ * (1 - u)) < u * v := by
  have he : 0 < μ - 1 := by linarith
  have h1 : (μ - 1) * (1 - u) ≤ u := by linarith
  have h2 : (μ - 1) * (1 - u) * (1 - v) ≤ u * (1 - v) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : 0 < v * (1 - u) := mul_pos hv0 (by linarith)
  have e : (1 - μ * (1 - v)) * (1 - μ * (1 - u)) =
      u * v - (μ - 1) * (u * (1 - v) + v * (1 - u) - (μ - 1) * (1 - u) * (1 - v)) := by ring
  rw [e]
  have : 0 < u * (1 - v) + v * (1 - u) - (μ - 1) * (1 - u) * (1 - v) := by linarith
  nlinarith [mul_pos he this]

/-- Side `0`, from `(1, 0)` to the point of tangency `(1, 1 - √2/2)`. -/
lemma cls_good_piece₀ {V : ℝ} (hV1 : √2 / 2 ≤ V) (hV2 : V ≤ 1) : ClsGood ![1, 1 - V] := by
  have h2 := cls_sqrt2_sq
  have ha := cls_sqrt2_gt
  have hb := cls_sqrt2_lt'
  have hsV : 1 ≤ √2 * V := by nlinarith
  have hsV2 : √2 * V ≤ √2 := by nlinarith
  have hV0 : 0 < V := by linarith
  refine ⟨?_, fun μ hμ hmem ↦ ?_⟩
  · rw [cls_mem_iff]
    intro k
    fin_cases k <;> simp [ClsCond, clsD] <;>
      first
      | exact ⟨by nlinarith, fun h ↦ by nlinarith⟩
      | exact fun h ↦ by nlinarith
  · rw [cls_mem_iff] at hmem
    have := (hmem 0).1
    rw [cls_D_smul] at this
    simp [clsD] at this
    linarith

/-- The arc of corner `0`, on the hyperbola `d₇ d₂ = √2/4`. -/
lemma cls_good_piece₁ {W V : ℝ} (hW1 : 1 ≤ W) (hW2 : W ≤ √2) (hWV : W * V = 1) :
    ClsGood ![√2 + 1 - √2 / 2 * (W + V), 1 - √2 / 2 * V] := by
  have h2 := cls_sqrt2_sq
  have ha := cls_sqrt2_gt
  have hb := cls_sqrt2_lt'
  have hV0 : 0 < V := by nlinarith
  have hV1 : √2 / 2 ≤ V := by nlinarith
  have hV2 : V ≤ 1 := by nlinarith
  have hWV2 : 2 ≤ W + V := by nlinarith [sq_nonneg (W - V)]
  have hsWV : √2 * (W * V) = √2 := by rw [hWV, mul_one]
  have hs1 : 2 * √2 ≤ √2 * (W + V) := by nlinarith
  have hd1 : √2 ≤ W / 2 + V := by nlinarith [sq_nonneg (W - √2)]
  have hsW2 : √2 * W ≤ 2 := by nlinarith
  have hsV1 : 1 ≤ √2 * V := by nlinarith
  have hsV2 : √2 * V ≤ √2 := by nlinarith
  -- the arc lies beyond the chord: `d₀ + d₁ ≤ 3/2 - √2`, i.e. `(√2 + 1)(W - 1)(√2 - W) ≥ 0`
  have hchord : √2 / 2 * (W + V) - √2 + (W / 2 + V - √2) ≤ 3 / 2 - √2 := by
    have hW0 : 0 < W := by linarith
    have hfac : 0 ≤ (√2 + 1) * ((W - 1) * (√2 - W)) :=
      mul_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))
    nlinarith
  have hD : clsD ![√2 + 1 - √2 / 2 * (W + V), 1 - √2 / 2 * V] =
      ![√2 / 2 * (W + V) - √2, W / 2 + V - √2, √2 / 2 * V, 2 - W / 2,
        2 + √2 - √2 / 2 * (W + V), 2 + √2 - W / 2 - V, 2 - √2 / 2 * V, W / 2] := by
    ext k
    fin_cases k <;> simp [clsD] <;> ring_nf <;> simp only [h2] <;> ring_nf
  refine ⟨?_, fun μ hμ hmem ↦ ?_⟩
  · rw [cls_mem_iff, hD]
    intro k
    fin_cases k <;> simp [ClsCond] <;>
      exact ⟨by nlinarith, fun h ↦ by nlinarith⟩
  · rw [cls_mem_iff] at hmem
    have h0 := (hmem 0).2
    have hu := (hmem 2).1
    simp only [cls_D_smul, hD] at h0 hu
    change 1 - μ * (1 - (√2 / 2 * (W + V) - √2)) + (1 - μ * (1 - (W / 2 + V - √2))) ≤
        3 / 2 - √2 → √2 / 4 ≤ (1 - μ * (1 - W / 2)) * (1 - μ * (1 - √2 / 2 * V)) at h0
    change 0 ≤ 1 - μ * (1 - √2 / 2 * V) at hu
    have hlt := cls_beyond (u := √2 / 2 * V) (v := W / 2) (μ := μ) (by nlinarith) (by linarith) (by nlinarith) hμ hu
    have hprod : √2 / 2 * V * (W / 2) = √2 / 4 := by
      rw [show √2 / 2 * V * (W / 2) = √2 / 4 * (W * V) by ring, hWV, mul_one]
    have hs : 1 - μ * (1 - (√2 / 2 * (W + V) - √2)) + (1 - μ * (1 - (W / 2 + V - √2))) ≤
        3 / 2 - √2 := by
      set d := √2 / 2 * (W + V) - √2 + (W / 2 + V - √2)
      have hd2 : 0 ≤ (μ - 1) * (2 - d) := mul_nonneg (by linarith) (by linarith)
      have e : 1 - μ * (1 - (√2 / 2 * (W + V) - √2)) + (1 - μ * (1 - (W / 2 + V - √2))) =
          d - (μ - 1) * (2 - d) := by simp only [d]; ring
      rw [e]
      linarith
    linarith [h0 hs]

/-- Side `1`, from the point of tangency `(√2 - 1/2, 1/2)` to the midpoint `(√2/2, √2/2)`. -/
lemma cls_good_piece₂ {W : ℝ} (hW1 : 1 ≤ W) (hW2 : W ≤ √2) : ClsGood ![√2 - W / 2, W / 2] := by
  have h2 := cls_sqrt2_sq
  have ha := cls_sqrt2_gt
  have hb := cls_sqrt2_lt'
  have hsW : √2 ≤ √2 * W := by nlinarith
  have hsW2 : √2 * W ≤ 2 := by nlinarith
  refine ⟨?_, fun μ hμ hmem ↦ ?_⟩
  · rw [cls_mem_iff]
    intro k
    fin_cases k <;> simp [ClsCond, clsD] <;>
      exact ⟨by nlinarith, fun h ↦ by nlinarith⟩
  · rw [cls_mem_iff] at hmem
    have := (hmem 1).1
    rw [cls_D_smul] at this
    simp [clsD] at this
    nlinarith

/-! ### Every point `A σ₀(t)` is on the boundary of Reinhardt's octagon -/

lemma cls_inv_W_mem {W : ℝ} (hW1 : 1 ≤ W) (hW2 : W ≤ √2) : √2 / 2 ≤ 1 / W ∧ 1 / W ≤ 1 := by
  have h2 := cls_sqrt2_sq
  have hW0 : 0 < W := by linarith
  constructor
  · rw [le_div_iff₀ hW0]; nlinarith
  · rw [div_le_one hW0]; exact hW1

/-- On `[0, 3 t_sw]`. -/
lemma cls_good_unit {t : ℝ} (ht : t ∈ Icc 0 (3 * tsw 1)) :
    ClsGood (clsEquiv (smoothedPolygonCurve 1 0 t)) := by
  have hτ := cls_tsw_pos
  rcases le_or_gt t (tsw 1) with h1 | h1
  · have hs : t ∈ Icc 0 (tsw 1) := ⟨ht.1, h1⟩
    obtain ⟨hW1, hW2⟩ := cls_W_mem hs
    rw [cls_piece₀ hs]
    exact cls_good_piece₀ (cls_inv_W_mem hW1 hW2).1 (cls_inv_W_mem hW1 hW2).2
  rcases le_or_gt t (2 * tsw 1) with h2 | h2
  · have hs : t - tsw 1 ∈ Icc 0 (tsw 1) := ⟨by linarith, by linarith⟩
    obtain ⟨hW1, hW2⟩ := cls_W_mem hs
    have hW0 : 0 < clsW (t - tsw 1) := Real.exp_pos _
    have e := cls_piece₁ hs
    rw [sub_add_cancel] at e
    rw [e, show √2 / (2 * clsW (t - tsw 1)) = √2 / 2 * (1 / clsW (t - tsw 1)) by
      field_simp]
    exact cls_good_piece₁ hW1 hW2 (by field_simp)
  · have hs : t - 2 * tsw 1 ∈ Icc 0 (tsw 1) := ⟨by linarith, by linarith [ht.2]⟩
    obtain ⟨hW1, hW2⟩ := cls_W_mem hs
    have e := cls_piece₂ hs
    rw [sub_add_cancel] at e
    rw [e]
    exact cls_good_piece₂ hW1 hW2

lemma cls_good_add_int (n : ℤ) (x : ℝ) :
    ClsGood (clsEquiv (smoothedPolygonCurve 1 0 (x + n * (3 * tsw 1)))) ↔
      ClsGood (clsEquiv (smoothedPolygonCurve 1 0 x)) := by
  have key : ∀ y, ClsGood (clsEquiv (smoothedPolygonCurve 1 0 (y + 3 * tsw 1))) ↔
      ClsGood (clsEquiv (smoothedPolygonCurve 1 0 y)) := fun y ↦ by
    rw [cls_frame_shift, cls_good_rot_iff]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    have e : x + (((n : ℤ) + 1 : ℤ) : ℝ) * (3 * tsw 1) =
        (x + ((n : ℤ) : ℝ) * (3 * tsw 1)) + 3 * tsw 1 := by push_cast; ring
    rw [e]
    exact (key _).trans ih
  | pred n ih =>
    have e : x + ((-(n : ℤ) - 1 : ℤ) : ℝ) * (3 * tsw 1) + 3 * tsw 1 =
        x + ((-(n : ℤ) : ℤ) : ℝ) * (3 * tsw 1) := by push_cast; ring
    have := key (x + ((-(n : ℤ) - 1 : ℤ) : ℝ) * (3 * tsw 1))
    rw [e] at this
    exact this.symm.trans ih

/-- Every point `A σ₀(t)` lies in Reinhardt's octagon, and `μ A σ₀(t)` does not for `μ > 1`. -/
lemma cls_good (t : ℝ) : ClsGood (clsEquiv (smoothedPolygonCurve 1 0 t)) := by
  have hP : 0 < 3 * tsw 1 := by linarith [cls_tsw_pos]
  set n := ⌊t / (3 * tsw 1)⌋
  have h1 := Int.floor_le (t / (3 * tsw 1))
  have h2 := Int.lt_floor_add_one (t / (3 * tsw 1))
  rw [le_div_iff₀ hP] at h1
  rw [div_lt_iff₀ hP] at h2
  have e : t = (t - n * (3 * tsw 1)) + n * (3 * tsw 1) := by ring
  rw [e, cls_good_add_int]
  exact cls_good_unit ⟨by linarith, by linarith⟩

/-! ### `A` maps the octagon onto Reinhardt's octagon -/

lemma cls_zero_mem : (0 : Fin 2 → ℝ) ∈ smoothedOctagon := by
  rw [cls_mem_iff]
  have hb := cls_sqrt2_gt
  intro k
  fin_cases k <;> simp [ClsCond, clsD] <;> intro h <;> linarith

lemma cls_parallel {q p : Fin 2 → ℝ} (hq : q ≠ 0) (h : q 0 * p 1 - q 1 * p 0 = 0) :
    p = ((q 0 * p 0 + q 1 * p 1) / (q 0 ^ 2 + q 1 ^ 2)) • q := by
  have hq' : q 0 ^ 2 + q 1 ^ 2 ≠ 0 := by
    intro h0
    apply hq
    have a : q 0 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    have b : q 1 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
    ext i; fin_cases i <;> simp [a, b]
  ext i
  fin_cases i <;> simp <;> field_simp
  · linear_combination (-q 1) * h
  · linear_combination (q 0) * h

lemma cls_ne_zero {q : Fin 2 → ℝ} (hq : ClsGood q) : q ≠ 0 := by
  rintro rfl
  exact hq.2 2 (by norm_num) (by simpa using cls_zero_mem)

/-- **`A` maps the library's octagon onto Reinhardt's.** -/
theorem cls_image_octagon : clsEquiv '' octagon = smoothedOctagon := by
  have htf : 0 < tf 1 := oct_tf_pos le_rfl
  refine Subset.antisymm ?_ fun p hp ↦ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, -, r, ⟨hr0, hr1⟩, rfl⟩ := hx
    rw [map_smul]
    exact cls_smul_mem (cls_good t).1 hr0 hr1
  by_cases hp0 : p = 0
  · refine ⟨0, ⟨0, ⟨le_rfl, by linarith⟩, 0, ⟨le_rfl, zero_le_one⟩, by simp⟩, by simp [hp0]⟩
  -- a curve point on the ray through `p`
  set f : ℝ → ℝ := fun t ↦
    clsEquiv (smoothedPolygonCurve 1 0 t) 0 * p 1 - clsEquiv (smoothedPolygonCurve 1 0 t) 1 * p 0
  have hfc : Continuous f := by
    have hc : Continuous fun t ↦ clsEquiv (smoothedPolygonCurve 1 0 t) :=
      clsEquiv.toLinearMap.continuous_of_finiteDimensional.comp cls_curve_continuous
    exact ((continuous_apply 0).comp hc).mul continuous_const |>.sub
      (((continuous_apply 1).comp hc).mul continuous_const)
  have hneg : ∀ t, clsEquiv (smoothedPolygonCurve 1 0 (t + 3 * tf 1)) =
      -clsEquiv (smoothedPolygonCurve 1 0 t) := fun t ↦ by
    rw [cls_curve_add_three_tf, map_neg]
  have hf3 : f (0 + 3 * tf 1) = -f 0 := by
    simp only [f, hneg, Pi.neg_apply]; ring
  have h3 : (0 : ℝ) ≤ 3 * tf 1 := by linarith
  obtain ⟨t, ht, hft⟩ : ∃ t ∈ Icc 0 (3 * tf 1), f t = 0 := by
    rw [zero_add] at hf3
    rcases le_total (f 0) 0 with h | h
    · exact intermediate_value_Icc h3 hfc.continuousOn ⟨h, by rw [hf3]; linarith⟩
    · exact intermediate_value_Icc' h3 hfc.continuousOn ⟨by rw [hf3]; linarith, h⟩
  set q := clsEquiv (smoothedPolygonCurve 1 0 t)
  have hpar := cls_parallel (cls_ne_zero (cls_good t)) hft
  set l := (q 0 * p 0 + q 1 * p 1) / (q 0 ^ 2 + q 1 ^ 2)
  -- choose the sign: `p = λ' • A σ₀(t')` with `λ' > 0`
  obtain ⟨t', ht', l', hl', hp'⟩ : ∃ t' ∈ Icc 0 (6 * tf 1), ∃ l' : ℝ, 0 < l' ∧
      p = l' • clsEquiv (smoothedPolygonCurve 1 0 t') := by
    have hl0 : l ≠ 0 := by
      rintro hl
      rw [hl, zero_smul] at hpar
      exact hp0 hpar
    rcases hl0.lt_or_gt with hl | hl
    · refine ⟨t + 3 * tf 1, ⟨by linarith [ht.1], by linarith [ht.2]⟩, -l, by linarith, ?_⟩
      rw [hneg, smul_neg, neg_smul, neg_neg]
      exact hpar
    · exact ⟨t, ⟨ht.1, by linarith [ht.2]⟩, l, hl, hpar⟩
  rcases le_or_gt l' 1 with hl1 | hl1
  · exact ⟨l' • smoothedPolygonCurve 1 0 t', ⟨t', ht', l', ⟨hl'.le, hl1⟩, rfl⟩,
      by rw [map_smul, hp']⟩
  · exact absurd (hp' ▸ hp) ((cls_good t').2 l' hl1)

/-- **The smoothed octagon is Reinhardt's.** The convex hull of the six arcs of the octagon
trajectory is a linear image of Reinhardt's smoothed octagon. -/
theorem octagon_classical (g X : ℝ → Mat2)
    (h : IsStateTrajectory (tf 1) (polygonControl 1) g X) (hg0 : g 0 = 1)
    (hX0 : X 0 = Φ 0 (y₀ 1)) :
    ∃ A : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ),
      A '' convexHull ℝ
          (⋃ j : ZMod 6, (fun t ↦ Matrix.mulVec (g t) (sixthRoot j)) '' Set.Icc 0 (tf 1)) =
        smoothedOctagon :=
  ⟨clsEquiv, by rw [bridge_convexHull_arcs g X h hg0 hX0, cls_image_octagon]⟩

/-- An affine image of the library's octagon is an affine image of Reinhardt's, and conversely. -/
theorem cls_exists_affine_iff (K : Set (Fin 2 → ℝ)) :
    (∃ A : (Fin 2 → ℝ) ≃ᵃ[ℝ] (Fin 2 → ℝ), K = A '' octagon) ↔
      ∃ B : (Fin 2 → ℝ) ≃ᵃ[ℝ] (Fin 2 → ℝ), K = B '' smoothedOctagon := by
  rw [← cls_image_octagon]
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨clsEquiv.symm.toAffineEquiv.trans A, ?_⟩
    rw [AffineEquiv.coe_trans, image_image]
    simp
  · rintro ⟨B, rfl⟩
    refine ⟨clsEquiv.toAffineEquiv.trans B, ?_⟩
    rw [AffineEquiv.coe_trans, image_comp]
    rfl

end SmoothedOctagon
