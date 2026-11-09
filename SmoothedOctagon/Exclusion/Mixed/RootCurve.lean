module

public import SmoothedOctagon.Exclusion.Mixed.Scalar
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Case M2: the root function along the central margin

Hold `a, c, d, r, v` fixed and move the central margin `b`.
With `K = a² + 4`, `T = a + c`, `Q = d² + 4`, `Z = d + r`, `Y = m2Y a c d`, the root function
with central stationarity imposed is affine in `u` and in `C_a = m2Stat b a c`:
`R_d(u; b) = α + β u + γ ((a + b) u + T v - C_a)` (`rc_root_lin`), with slope
`R_u(b) = β + γ (a + b)` (`rcRu`).

## Main API

* `rc_strictAntiOn`: a function with negative derivative on `(x₀, x₁)` and a derivative on
  `[x₀, x₁]` is strictly decreasing there.
* `rc_hasDerivAt_stat`: `∂_b m2Stat b a c = U(a/(a + b))`.
* `rcα`, `rcβ`, `rcγ`, `rcRu`; `rc_root_lin`; `rc_Ru_neg`: `R_u < 0`.
* `rcG b = R_d(U(a/(a + b)); b)` with `rc_hasDerivAt_G`: `G' = R_u a (b - a)/(a + b)³`.
* `rcH b`, the central diagonal on the root curve, with `rc_hasDerivAt_H`:
  `H' = -(K/(16a)) β G/R_u²`; `rc_h_of_root`: at a root, `m2h = rcH`.
* `rc_w_of_root`: at a root, `w = (C_d - W v + 16 d h_d/Q)/Z`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- A function with a derivative at every point of `[x₀, x₁]`, negative on `(x₀, x₁)`, is strictly
decreasing on `[x₀, x₁]`. -/
theorem rc_strictAntiOn {f f' : ℝ → ℝ} {x₀ x₁ : ℝ}
    (hd : ∀ x ∈ Set.Icc x₀ x₁, HasDerivAt f (f' x) x) (hneg : ∀ x ∈ Set.Ioo x₀ x₁, f' x < 0) :
    StrictAntiOn f (Set.Icc x₀ x₁) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc x₀ x₁)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x (Set.Ioo_subset_Icc_self hx)).deriv]
  exact hneg x hx

/-- A function with a derivative at every point of `[x₀, x₁]`, positive on `(x₀, x₁)`, is strictly
increasing on `[x₀, x₁]`. -/
theorem rc_strictMonoOn {f f' : ℝ → ℝ} {x₀ x₁ : ℝ}
    (hd : ∀ x ∈ Set.Icc x₀ x₁, HasDerivAt f (f' x) x) (hpos : ∀ x ∈ Set.Ioo x₀ x₁, 0 < f' x) :
    StrictMonoOn f (Set.Icc x₀ x₁) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc x₀ x₁)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x (Set.Ioo_subset_Icc_self hx)).deriv]
  exact hpos x hx

/-- `∂_b m2Stat b a c = U(a/(a + b))`, i.e. `dC_a/db = U(a/S)`. -/
theorem rc_hasDerivAt_stat {a c b : ℝ} (hab : 0 < a + b) (hac : 0 < a + c) :
    HasDerivAt (fun x => m2Stat x a c) (m2U (a / (a + b))) b := by
  have hK : 0 < a ^ 2 + 4 := by positivity
  have hba : b + a ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => x + a) 1 b := (hasDerivAt_id' b).add_const a
  have h2 : HasDerivAt (fun x : ℝ => 1 / (x + a)) ((0 * (b + a) - 1 * 1) / (b + a) ^ 2) b :=
    (hasDerivAt_const b (1 : ℝ)).div h1 hba
  have h3 : HasDerivAt (fun x : ℝ => (x + a) * (a + c) / (a ^ 2 + 4))
      (1 * (a + c) / (a ^ 2 + 4)) b := (h1.mul_const (a + c)).div_const (a ^ 2 + 4)
  have h4 := h3.log (by positivity)
  have h5 := ((((h1.add_const c).sub ((h2.add_const (1 / (a + c))).const_mul (a ^ 2))).add_const
    (a ^ 3 / (a ^ 2 + 4))).sub (h4.const_mul a))
  unfold m2Stat
  convert h5 using 1
  unfold m2U
  have : a + b ≠ 0 := by linarith
  field_simp
  ring

/-- `∂_b U(a/(a + b)) = a (b - a)/(a + b)³`. -/
theorem rc_hasDerivAt_U {a b : ℝ} (hab : 0 < a + b) :
    HasDerivAt (fun x => m2U (a / (a + x))) (a * (b - a) / (a + b) ^ 3) b := by
  have hne : a + b ≠ 0 := hab.ne'
  have h1 : HasDerivAt (fun x : ℝ => a + x) 1 b := (hasDerivAt_id' b).const_add a
  have h2 : HasDerivAt (fun x : ℝ => a / (a + x)) ((0 * (a + b) - a * 1) / (a + b) ^ 2) b :=
    (hasDerivAt_const b a).div h1 hne
  have h3 := (h2.const_sub 1).add (h2.pow 2)
  unfold m2U
  convert h3 using 1
  norm_num
  field_simp
  ring

/-- `β = -Z K²/Q²`, the direct `u`-coefficient of `R_d`. -/
noncomputable def rcβ (a d r : ℝ) : ℝ := -(d + r) * (a ^ 2 + 4) ^ 2 / (d ^ 2 + 4) ^ 2

/-- `γ = K (dQ - ZY)/(a Q²)`, the coefficient of `(a + b) u + T v - C_a` in `R_d`. -/
noncomputable def rcγ (a c d r : ℝ) : ℝ :=
  (a ^ 2 + 4) * (d * (d ^ 2 + 4) - (d + r) * m2Y a c d) / (a * (d ^ 2 + 4) ^ 2)

/-- `α = C_d - W v - Z v Y²/Q² + 2 d v Y/Q`, the part of `R_d` free of `u` and `h`. -/
noncomputable def rcα (a c d r v : ℝ) : ℝ :=
  m2Stat c d r - (c + d) * v - (d + r) * v * m2Y a c d ^ 2 / (d ^ 2 + 4) ^ 2
    + 2 * d * v * m2Y a c d / (d ^ 2 + 4)

/-- The slope `R_u(b) = β + γ (a + b)`. -/
noncomputable def rcRu (a b c d r : ℝ) : ℝ := rcβ a d r + rcγ a c d r * (a + b)

/-- The root function with central stationarity imposed, in affine form. -/
theorem rc_root_lin {a b c d r u v : ℝ} (ha : a ≠ 0) :
    m2Root a c d r u v (m2h a b c u v) =
      rcα a c d r v + rcβ a d r * u + rcγ a c d r * ((a + b) * u + (a + c) * v - m2Stat b a c) := by
  have hQ : d ^ 2 + 4 ≠ 0 := by positivity
  unfold m2Root m2h m2hd m2wOf rcα rcβ rcγ
  field_simp
  ring

/-- The root function is affine in `u` with slope `R_u(b)`. -/
theorem rc_root_affine {a b c d r u v : ℝ} (ha : a ≠ 0) :
    m2Root a c d r u v (m2h a b c u v) =
      m2Root a c d r 0 v (m2h a b c 0 v) + u * rcRu a b c d r := by
  rw [rc_root_lin ha, rc_root_lin ha]
  unfold rcRu
  ring

/-- `R_u = (K/(a Q²)) (d S Q - Z (a K + S Y))`. -/
theorem rc_Ru_eq {a b c d r : ℝ} (ha : a ≠ 0) :
    rcRu a b c d r = (a ^ 2 + 4) / (a * (d ^ 2 + 4) ^ 2) *
      (d * (a + b) * (d ^ 2 + 4) - (d + r) * (a * (a ^ 2 + 4) + (a + b) * m2Y a c d)) := by
  have hQ : d ^ 2 + 4 ≠ 0 := by positivity
  unfold rcRu rcβ rcγ
  field_simp
  ring

/-- **The sign of the root coefficient**: for `0 < a < d`,
`c > 0`, `q > 1` and `0 < S T ≤ K`, `R_u < 0`. -/
theorem rc_Ru_neg {a b c d r : ℝ} (ha : 0 < a) (hc : 0 < c) (had : a < d)
    (hq : d ^ 2 + 4 < (c + d) * (d + r)) (hS : 0 < a + b) (hST : (a + b) * (a + c) ≤ a ^ 2 + 4) :
    rcRu a b c d r < 0 := by
  rw [rc_Ru_eq ha.ne']
  have hK : 0 < a ^ 2 + 4 := by positivity
  have hQ : 0 < d ^ 2 + 4 := by positivity
  have hW : 0 < c + d := by linarith
  have hY : 0 < m2Y a c d := by
    unfold m2Y; nlinarith
  refine mul_neg_of_pos_of_neg (by positivity) ?_
  -- `W X = Q [a (ST - K) + S c (a - d)] - (Z W - Q)(a K + S Y)`
  have key : (c + d) * (d * (a + b) * (d ^ 2 + 4) - (d + r) * (a * (a ^ 2 + 4) + (a + b) * m2Y a c d))
      = (d ^ 2 + 4) * (a * ((a + b) * (a + c) - (a ^ 2 + 4)) + (a + b) * c * (a - d))
        - ((c + d) * (d + r) - (d ^ 2 + 4)) * (a * (a ^ 2 + 4) + (a + b) * m2Y a c d) := by
    unfold m2Y; ring
  have h1 : (d ^ 2 + 4) * (a * ((a + b) * (a + c) - (a ^ 2 + 4)) + (a + b) * c * (a - d)) < 0 := by
    have : a * ((a + b) * (a + c) - (a ^ 2 + 4)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le (by linarith)
    have : (a + b) * c * (a - d) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
    exact mul_neg_of_pos_of_neg hQ (by linarith)
  have h2 : 0 < ((c + d) * (d + r) - (d ^ 2 + 4)) * (a * (a ^ 2 + 4) + (a + b) * m2Y a c d) :=
    mul_pos (by linarith) (by positivity)
  have : (c + d) * (d * (a + b) * (d ^ 2 + 4) - (d + r) * (a * (a ^ 2 + 4) + (a + b) * m2Y a c d))
      < 0 := by rw [key]; linarith
  exact neg_of_mul_neg_right this hW.le

/-- `G(b) = R_d(U(a/(a + b)); b)`, the root function along the incident ceiling. -/
noncomputable def rcG (a c d r v b : ℝ) : ℝ :=
  m2Root a c d r (m2U (a / (a + b))) v (m2h a b c (m2U (a / (a + b))) v)

/-- **`G' = R_u a (b - a)/(a + b)³`**. -/
theorem rc_hasDerivAt_G {a c d r v b : ℝ} (ha : 0 < a) (hab : 0 < a + b) (hac : 0 < a + c) :
    HasDerivAt (rcG a c d r v) (rcRu a b c d r * (a * (b - a) / (a + b) ^ 3)) b := by
  have hfun : rcG a c d r v = fun x => rcα a c d r v + rcβ a d r * m2U (a / (a + x)) +
      rcγ a c d r * ((a + x) * m2U (a / (a + x)) + (a + c) * v - m2Stat x a c) := by
    funext x; exact rc_root_lin ha.ne'
  rw [hfun]
  have hU := rc_hasDerivAt_U (a := a) hab
  have hC := rc_hasDerivAt_stat (c := c) hab hac
  have hS : HasDerivAt (fun x : ℝ => a + x) 1 b := (hasDerivAt_id' b).const_add a
  have h := ((hU.const_mul (rcβ a d r)).const_add (rcα a c d r v)).add
    ((((hS.mul hU).add_const ((a + c) * v)).sub hC).const_mul (rcγ a c d r))
  convert h using 1
  unfold rcRu m2U
  have : a + b ≠ 0 := hab.ne'
  field_simp
  ring

/-- The central diagonal on the root curve, `H(b) = (K/(16a)) (β T v - S α - β C_a)/R_u`. -/
noncomputable def rcH (a c d r v b : ℝ) : ℝ :=
  (a ^ 2 + 4) / (16 * a) *
    ((rcβ a d r * ((a + c) * v) - (a + b) * rcα a c d r v - rcβ a d r * m2Stat b a c) /
      rcRu a b c d r)

/-- **`H' = -(K/(16a)) β G/R_u²`**, the derivative `dh/db` of the central diagonal on the root
curve. -/
theorem rc_hasDerivAt_H {a c d r v b : ℝ} (ha : 0 < a) (hab : 0 < a + b) (hac : 0 < a + c)
    (hR : rcRu a b c d r ≠ 0) :
    HasDerivAt (rcH a c d r v)
      (-((a ^ 2 + 4) / (16 * a)) * rcβ a d r * rcG a c d r v b / rcRu a b c d r ^ 2) b := by
  have hC := rc_hasDerivAt_stat (c := c) hab hac
  have hS : HasDerivAt (fun x : ℝ => a + x) 1 b := (hasDerivAt_id' b).const_add a
  have hN : HasDerivAt (fun x => rcβ a d r * ((a + c) * v) - (a + x) * rcα a c d r v -
      rcβ a d r * m2Stat x a c) (-(1 * rcα a c d r v) - rcβ a d r * m2U (a / (a + b))) b :=
    ((hS.mul_const (rcα a c d r v)).const_sub (rcβ a d r * ((a + c) * v))).sub
      (hC.const_mul (rcβ a d r))
  have hD : HasDerivAt (fun x => rcRu a x c d r) (rcγ a c d r * 1) b := by
    unfold rcRu; exact (hS.const_mul (rcγ a c d r)).const_add (rcβ a d r)
  have h := (hN.div hD hR).const_mul ((a ^ 2 + 4) / (16 * a))
  unfold rcH
  convert h using 1
  rw [rcG, rc_root_lin ha.ne']
  unfold rcRu
  have hR' : rcβ a d r + rcγ a c d r * (a + b) ≠ 0 := hR
  field_simp
  ring

/-- At a root, the central diagonal is `rcH`. -/
theorem rc_h_of_root {a b c d r u v : ℝ} (ha : 0 < a) (hR : rcRu a b c d r ≠ 0)
    (hroot : m2Root a c d r u v (m2h a b c u v) = 0) : m2h a b c u v = rcH a c d r v b := by
  rw [rc_root_lin ha.ne'] at hroot
  have key : ((a + b) * u + (a + c) * v - m2Stat b a c) * rcRu a b c d r =
      rcβ a d r * ((a + c) * v) - (a + b) * rcα a c d r v - rcβ a d r * m2Stat b a c := by
    unfold rcRu; linear_combination (a + b) * hroot
  unfold rcH m2h
  rw [← key, mul_div_cancel_right₀ _ hR]

/-- At a root, `w = (C_d - W v + 16 d h_d/Q)/Z`. -/
theorem rc_w_of_root {a c d r u v h : ℝ} (hZ : 0 < d + r) (hroot : m2Root a c d r u v h = 0) :
    m2wOf a c d u v h = (m2Stat c d r - (c + d) * v + 16 * d * m2hd a c d v h / (d ^ 2 + 4)) /
      (d + r) := by
  unfold m2Root at hroot
  rw [eq_div_iff hZ.ne']
  linarith

end SmoothedOctagon
