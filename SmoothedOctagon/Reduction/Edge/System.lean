module

public import SmoothedOctagon.Reduction.Edge.Calculus
public import External.Pontryagin

/-!
# The edge control system in physical time

On an edge of the control simplex (`u₀ = 0`, rotated there by relabeling), a star state
`X = [[a, b], [c, -a]]` (`det X = 1`, so `b = -(1 + a²)/c`) is determined by `(a, c)`, and the
frame, up to a constant left factor, by `x = a/c` and `s = ∫ c` (the frame `h(x, s)` below). With
`u = (0, v, 1 - v)`, `v ∈ [0, 1]`, `α = (2v - 1)/√3`, the state equation `X' = [P_u, X]` reads

  `a' = c/(c - 3αa)`, `c' = 3αc/(c - 3αa)`, `s' = c`,

with cost density `-(3/2) tr(JX) = (3/2)(c + (1 + a²)/c)`. This is a control system on the open
set `edge_edgeDomain = {c > 0, 3a² < c² < 3(1 + a²)}` of `ℝ³` (the strict star conditions), to which
the free-time maximum principle applies.

Main API:

* `edge_edgeAlpha`, `edge_edgeField`, `edge_edgeCost`, `edge_edgeDomain`, `edge_edgeX`, `edge_edgeFrame`,
  `edge_edgeControl`;
* `edge_isOpen_edgeDomain`, `edge_edgeDenom_pos`, `edge_isC1On_edgeField`, `edge_isC1On_edgeCost`;
* `edge_isStarState_edgeX`, `edge_edgeX_of_isStarState`, `edge_mem_edgeDomain_of_isStarState`,
  `edge_edgeControl_mem`, `edge_det_edgeFrame`, `edge_edgeCost_eq_traceForm`;
* `edge_fderiv_edgeField_scale`, `edge_fderiv_edgeField_s`, `edge_fderiv_edgeCost_scale`,
  `edge_fderiv_edgeCost_s`: the derivatives of the field and the cost along the scaling direction
  `(a, c, 0)` and along the `s` direction.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction.Edge

open SmoothedPolygons MeasureTheory Set Filter ControlSystem
open scoped Topology

/-- `α(v) = (2v - 1)/√3 = (u₁ - u₂)/√3` for `u = (0, v, 1 - v)`. -/
noncomputable def edge_edgeAlpha (v : ℝ) : ℝ := (2 * v - 1) / √3

/-- The edge dynamics `(a, c, s)' = (c/(c - 3αa), 3αc/(c - 3αa), c)`. -/
noncomputable def edge_edgeField (z : ℝ × ℝ × ℝ) (v : ℝ) : ℝ × ℝ × ℝ :=
  (z.2.1 / (z.2.1 - 3 * edge_edgeAlpha v * z.1),
    3 * edge_edgeAlpha v * z.2.1 / (z.2.1 - 3 * edge_edgeAlpha v * z.1), z.2.1)

/-- The cost density `(3/2)(c + (1 + a²)/c) = -(3/2) tr(J X)`. -/
noncomputable def edge_edgeCost (z : ℝ × ℝ × ℝ) (_v : ℝ) : ℝ :=
  3 / 2 * (z.2.1 + (1 + z.1 ^ 2) / z.2.1)

/-- The strict star conditions in the coordinates `(a, c, s)`. -/
def edge_edgeDomain : Set (ℝ × ℝ × ℝ) :=
  {z | 0 < z.2.1 ∧ 3 * z.1 ^ 2 < z.2.1 ^ 2 ∧ z.2.1 ^ 2 < 3 * (1 + z.1 ^ 2)}

/-- The star state `[[a, -(1 + a²)/c], [c, -a]]` of `(a, c, s)`. -/
noncomputable def edge_edgeX (z : ℝ × ℝ × ℝ) : Mat2 :=
  !![z.1, -(1 + z.1 ^ 2) / z.2.1; z.2.1, -z.1]

/-- The frame `h(x, s) = [[1, -x], [s, 1 - s x]]`, `x = a/c`. -/
noncomputable def edge_edgeFrame (z : ℝ × ℝ × ℝ) : Mat2 :=
  !![1, -(z.1 / z.2.1); z.2.2, 1 - z.2.2 * (z.1 / z.2.1)]

/-- The control `(0, v, 1 - v)` on the edge `u₀ = 0`. -/
def edge_edgeControl (v : ℝ) : Fin 3 → ℝ := ![0, v, 1 - v]

private lemma edge_sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private lemma edge_sqrt3_pos : (0 : ℝ) < √3 := by positivity

theorem edge_isOpen_edgeDomain : IsOpen edge_edgeDomain := by
  have h1 : IsOpen {z : ℝ × ℝ × ℝ | 0 < z.2.1} := isOpen_lt continuous_const (by fun_prop)
  have h2 : IsOpen {z : ℝ × ℝ × ℝ | 3 * z.1 ^ 2 < z.2.1 ^ 2} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  have h3 : IsOpen {z : ℝ × ℝ × ℝ | z.2.1 ^ 2 < 3 * (1 + z.1 ^ 2)} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  exact h1.inter (h2.inter h3)

/-- `(3α)² = 3 (2v - 1)² ≤ 3` on `[0, 1]`. -/
theorem edge_edgeAlpha_sq (v : ℝ) : (3 * edge_edgeAlpha v) ^ 2 = 3 * (2 * v - 1) ^ 2 := by
  rw [edge_edgeAlpha, mul_pow, div_pow, edge_sqrt3_sq]
  ring

/-- The denominator `c - 3αa` is positive on the domain. -/
theorem edge_edgeDenom_pos {z : ℝ × ℝ × ℝ} (hz : z ∈ edge_edgeDomain) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < z.2.1 - 3 * edge_edgeAlpha v * z.1 := by
  obtain ⟨hc, h1, -⟩ := hz
  have hα := edge_edgeAlpha_sq v
  have hb : (2 * v - 1) ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
  have hsq : (3 * edge_edgeAlpha v * z.1) ^ 2 < z.2.1 ^ 2 := by
    rw [mul_pow, hα]
    nlinarith [sq_nonneg z.1]
  nlinarith [abs_lt_of_sq_lt_sq' hsq hc.le, abs_lt.1 (abs_lt_of_sq_lt_sq hsq hc.le)]

/-- A joint `C¹` function on an open set containing `Ω × U` satisfies `IsC1On`. -/
private lemma edge_isC1On_of_contDiffOn {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E → V → F} {Ω : Set E} {U : Set V} {O : Set (E × V)} (hO : IsOpen O)
    (hΩU : Ω ×ˢ U ⊆ O) (hf : ContDiffOn ℝ 1 (fun q : E × V ↦ f q.1 q.2) O) : IsC1On f Ω U where
  continuousOn := hf.continuousOn.mono hΩU
  differentiableAt x hx u hu := by
    have hd : DifferentiableAt ℝ (fun q : E × V ↦ f q.1 q.2) (x, u) :=
      (hf.contDiffAt (hO.mem_nhds (hΩU ⟨hx, hu⟩))).differentiableAt one_ne_zero
    exact DifferentiableAt.comp (𝕜 := ℝ) x hd
      (by fun_prop : DifferentiableAt ℝ (fun x : E ↦ (x, u)) x)
  continuousOn_fderiv := by
    have key : ∀ q ∈ O, fderiv ℝ (f · q.2) q.1 =
        (fderiv ℝ (fun q : E × V ↦ f q.1 q.2) q).comp (ContinuousLinearMap.inl ℝ E V) := by
      rintro ⟨x, u⟩ hq
      have hd := (hf.contDiffAt (hO.mem_nhds hq)).differentiableAt one_ne_zero
      exact (HasFDerivAt.comp (𝕜 := ℝ) x hd.hasFDerivAt (hasFDerivAt_prodMk_left x u)).fderiv
    refine ContinuousOn.congr ?_ (fun q hq ↦ key q (hΩU hq))
    exact ((hf.continuousOn_fderiv_of_isOpen hO le_rfl).clm_comp continuousOn_const).mono hΩU

/-- The open set where the field is smooth. -/
private def edge_O : Set ((ℝ × ℝ × ℝ) × ℝ) :=
  {q | q.1.2.1 ≠ 0 ∧ q.1.2.1 - 3 * edge_edgeAlpha q.2 * q.1.1 ≠ 0}

private lemma edge_isOpen_O : IsOpen edge_O := by
  refine (isOpen_ne_fun (by fun_prop) continuous_const).inter (isOpen_ne_fun ?_ continuous_const)
  simp only [edge_edgeAlpha]
  fun_prop

private lemma edge_subset_O : edge_edgeDomain ×ˢ Icc (0 : ℝ) 1 ⊆ edge_O := by
  rintro ⟨z, v⟩ ⟨hz, hv⟩
  exact ⟨hz.1.ne', (edge_edgeDenom_pos hz hv).ne'⟩

theorem edge_isC1On_edgeField : IsC1On edge_edgeField edge_edgeDomain (Icc (0 : ℝ) 1) := by
  refine edge_isC1On_of_contDiffOn edge_isOpen_O edge_subset_O fun q hq ↦ ?_
  obtain ⟨_, hD⟩ := hq
  simp only [edge_edgeAlpha] at hD
  simp only [edge_edgeField, edge_edgeAlpha]
  refine ContDiffAt.contDiffWithinAt ?_
  fun_prop (disch := assumption)

theorem edge_isC1On_edgeCost : IsC1On edge_edgeCost edge_edgeDomain (Icc (0 : ℝ) 1) := by
  refine edge_isC1On_of_contDiffOn edge_isOpen_O edge_subset_O fun q hq ↦ ?_
  obtain ⟨hc, _⟩ := hq
  simp only [edge_edgeCost]
  refine ContDiffAt.contDiffWithinAt ?_
  fun_prop (disch := assumption)

/-! ### Star states and frames -/

@[simp] theorem edge_edgeX_00 (z : ℝ × ℝ × ℝ) : edge_edgeX z 0 0 = z.1 := rfl
@[simp] theorem edge_edgeX_01 (z : ℝ × ℝ × ℝ) : edge_edgeX z 0 1 = -(1 + z.1 ^ 2) / z.2.1 := rfl
@[simp] theorem edge_edgeX_10 (z : ℝ × ℝ × ℝ) : edge_edgeX z 1 0 = z.2.1 := rfl
@[simp] theorem edge_edgeX_11 (z : ℝ × ℝ × ℝ) : edge_edgeX z 1 1 = -z.1 := rfl
@[simp] theorem edge_edgeFrame_00 (z : ℝ × ℝ × ℝ) : edge_edgeFrame z 0 0 = 1 := rfl
@[simp] theorem edge_edgeFrame_01 (z : ℝ × ℝ × ℝ) : edge_edgeFrame z 0 1 = -(z.1 / z.2.1) := rfl
@[simp] theorem edge_edgeFrame_10 (z : ℝ × ℝ × ℝ) : edge_edgeFrame z 1 0 = z.2.2 := rfl
@[simp] theorem edge_edgeFrame_11 (z : ℝ × ℝ × ℝ) :
    edge_edgeFrame z 1 1 = 1 - z.2.2 * (z.1 / z.2.1) := rfl
@[simp] theorem edge_edgeControl_0 (v : ℝ) : edge_edgeControl v 0 = 0 := rfl
@[simp] theorem edge_edgeControl_1 (v : ℝ) : edge_edgeControl v 1 = v := rfl
@[simp] theorem edge_edgeControl_2 (v : ℝ) : edge_edgeControl v 2 = 1 - v := rfl

theorem edge_isStarState_edgeX {z : ℝ × ℝ × ℝ} (hz : z ∈ edge_edgeDomain) :
    IsStarState (edge_edgeX z) := by
  obtain ⟨hc, h1, h2⟩ := hz
  have h3 := edge_sqrt3_sq
  have h3p := edge_sqrt3_pos
  have hprod : 0 < (z.2.1 + √3 * z.1) * (z.2.1 - √3 * z.1) := by nlinarith
  have hp : 0 < z.2.1 + √3 * z.1 ∧ 0 < z.2.1 - √3 * z.1 := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hprod with h | h
    · exact h
    · exact absurd (add_neg h.1 h.2) (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.trace_fin_two]
    simp
  · rw [Matrix.det_fin_two]
    simp only [edge_edgeX_00, edge_edgeX_01, edge_edgeX_10, edge_edgeX_11]
    field_simp
    ring
  · simp only [ρ₀, edge_edgeX_00, edge_edgeX_10]
    exact div_pos hp.1 h3p
  · simp only [ρ₁, edge_edgeX_00, edge_edgeX_10]
    exact div_pos hp.2 h3p
  · simp only [ρ₂, edge_edgeX_01, edge_edgeX_10]
    refine div_pos ?_ (by positivity)
    have : 3 * (-(1 + z.1 ^ 2) / z.2.1) + z.2.1 = (z.2.1 ^ 2 - 3 * (1 + z.1 ^ 2)) / z.2.1 := by
      field_simp
      ring
    rw [this, neg_pos]
    exact div_neg_of_neg_of_pos (by linarith) hc

/-- The coordinates `(X₀₀, X₁₀, s)` of a star state lie in the edge domain. -/
theorem edge_mem_edgeDomain_of_isStarState {X : Mat2} (hX : IsStarState X) (s : ℝ) :
    ((X 0 0, X 1 0, s) : ℝ × ℝ × ℝ) ∈ edge_edgeDomain := by
  obtain ⟨htr, hdet, h0, h1, h2⟩ := hX
  have h3 := edge_sqrt3_sq
  have h3p := edge_sqrt3_pos
  simp only [ρ₀, ρ₁, ρ₂] at h0 h1 h2
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  have a0 : 0 < X 1 0 + √3 * X 0 0 := (div_pos_iff_of_pos_right h3p).1 h0
  have a1 : 0 < X 1 0 - √3 * X 0 0 := (div_pos_iff_of_pos_right h3p).1 h1
  have a2 : 0 < -(3 * X 0 1 + X 1 0) := (div_pos_iff_of_pos_right (by positivity)).1 h2
  have hc : 0 < X 1 0 := by linarith
  refine ⟨hc, ?_, ?_⟩
  · show 3 * X 0 0 ^ 2 < X 1 0 ^ 2
    nlinarith [mul_pos a0 a1]
  · show X 1 0 ^ 2 < 3 * (1 + X 0 0 ^ 2)
    have hX11 : X 1 1 = -X 0 0 := by linarith
    rw [hX11] at hdet
    nlinarith [mul_pos a2 hc]

/-- A star state is the `edge_edgeX` of its coordinates. -/
theorem edge_edgeX_of_isStarState {X : Mat2} (hX : IsStarState X) (s : ℝ) :
    edge_edgeX (X 0 0, X 1 0, s) = X := by
  have hc := (edge_mem_edgeDomain_of_isStarState hX s).1
  obtain ⟨htr, hdet, -⟩ := hX
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · show -(1 + X 0 0 ^ 2) / X 1 0 = X 0 1
    have hX11 : X 1 1 = -X 0 0 := by linarith
    rw [hX11] at hdet
    rw [div_eq_iff hc.ne']
    linear_combination hdet
  · rfl
  · show -X 0 0 = X 1 1
    linarith

theorem edge_edgeControl_mem {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    edge_edgeControl v ∈ controlSimplex := by
  refine ⟨fun i ↦ ?_, by simp⟩
  fin_cases i <;> simp [hv.1, hv.2]

theorem edge_measurable_edgeControl : Measurable edge_edgeControl := by
  refine measurable_pi_iff.mpr fun i ↦ ?_
  fin_cases i
  · exact measurable_const
  · exact measurable_id
  · exact measurable_const.sub measurable_id

theorem edge_det_edgeFrame (z : ℝ × ℝ × ℝ) : (edge_edgeFrame z).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [edge_edgeFrame_00, edge_edgeFrame_01, edge_edgeFrame_10, edge_edgeFrame_11]
  ring

/-- The cost density is `-(3/2) tr(J X)`. -/
theorem edge_edgeCost_eq_traceForm (z : ℝ × ℝ × ℝ) (v : ℝ) :
    edge_edgeCost z v = -(3 / 2) * traceForm J (edge_edgeX z) := by
  simp only [edge_edgeCost, traceForm, J, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, edge_edgeX_00, edge_edgeX_01, edge_edgeX_10, edge_edgeX_11]
  ring

/-- On the edge `u₀ = 0`, `Z_u = [[α, -2/3], [0, -α]]` with `α = (u₁ - u₂)/√3`. -/
theorem edge_controlMatrix_edge {u : Fin 3 → ℝ} (hu0 : u 0 = 0) (hu2 : u 2 = 1 - u 1) :
    controlMatrix u = !![edge_edgeAlpha (u 1), -(2 / 3); 0, -edge_edgeAlpha (u 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [controlMatrix, edge_edgeAlpha, hu0, hu2] <;> ring

theorem edge_controlMatrix_edgeControl (v : ℝ) :
    controlMatrix (edge_edgeControl v) = !![edge_edgeAlpha v, -(2 / 3); 0, -edge_edgeAlpha v] :=
  edge_controlMatrix_edge (by simp) (by simp)

/-- The state field `[P_u, X]` at `X = edge_edgeX z` for `u = (0, v, 1 - v)`. -/
theorem edge_stateField_edgeX {z : ℝ × ℝ × ℝ} (hz : z ∈ edge_edgeDomain) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    controlP (edge_edgeControl v) (edge_edgeX z) * edge_edgeX z -
        edge_edgeX z * controlP (edge_edgeControl v) (edge_edgeX z) =
      !![(edge_edgeField z v).1, (3 * edge_edgeAlpha v * (1 + z.1 ^ 2) - 2 * z.1 * z.2.1) /
          (z.2.1 * (z.2.1 - 3 * edge_edgeAlpha v * z.1));
        (edge_edgeField z v).2.1, -(edge_edgeField z v).1] := by
  have hD := (edge_edgeDenom_pos hz hv).ne'
  have hc := hz.1.ne'
  have htr : traceForm (controlMatrix (edge_edgeControl v)) (edge_edgeX z) =
      -(2 / 3) * (z.2.1 - 3 * edge_edgeAlpha v * z.1) := by
    rw [edge_controlMatrix_edgeControl]
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, edge_edgeX_00, edge_edgeX_01, edge_edgeX_10,
      edge_edgeX_11]
    ring
  simp only [controlP, htr, edge_edgeField]
  rw [edge_controlMatrix_edgeControl]
  generalize edge_edgeAlpha v = α at hD ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, edge_edgeX_00, edge_edgeX_01,
      edge_edgeX_10, edge_edgeX_11, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    field_simp <;> ring

/-- On the edge `u₀ = 0`, the entries `(0, 0)` and `(1, 0)` of the state field `[P_u, X]` are the
first two components of `edge_edgeField`. -/
theorem edge_stateField_edge {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) (hu0 : u 0 = 0) {X : Mat2}
    (hX : IsStarState X) (s : ℝ) :
    (controlP u X * X - X * controlP u X) 0 0 = (edge_edgeField (X 0 0, X 1 0, s) (u 1)).1 ∧
    (controlP u X * X - X * controlP u X) 1 0 = (edge_edgeField (X 0 0, X 1 0, s) (u 1)).2.1 := by
  have hz := edge_mem_edgeDomain_of_isStarState hX s
  have hv : u 1 ∈ Icc (0 : ℝ) 1 := ⟨(hu.1 1).1, (hu.1 1).2⟩
  have hu2 : u 2 = 1 - u 1 := by linarith [hu.2]
  have hP : controlP u X = controlP (edge_edgeControl (u 1)) X := by
    simp only [controlP, edge_controlMatrix_edge hu0 hu2, edge_controlMatrix_edgeControl]
  have h := edge_stateField_edgeX hz hv
  rw [edge_edgeX_of_isStarState hX s] at h
  rw [hP, h]
  exact ⟨rfl, rfl⟩

/-! ### Derivatives along the scaling and `s` directions -/

private lemma edge_hasDerivAt_line (z w : ℝ × ℝ × ℝ) :
    HasDerivAt (fun l : ℝ ↦ z + l • w) w 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z

private lemma edge_fderiv_eq {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {F : ℝ × ℝ × ℝ → E'} {z w : ℝ × ℝ × ℝ} {d : E'} (hF : DifferentiableAt ℝ F z)
    (h : HasDerivAt (fun l : ℝ ↦ F (z + l • w)) d 0) : fderiv ℝ F z w = d := by
  have h1 : HasDerivAt (fun l : ℝ ↦ F (z + l • w)) (fderiv ℝ F z w) 0 :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (edge_hasDerivAt_line z w) (by simp)
  exact h1.unique h

/-- `∂f(z)(a, c, 0) = (0, 0, c)`: the field is homogeneous of degree `0` in `(a, c)`, except for
`s' = c`. -/
theorem edge_fderiv_edgeField_scale {z : ℝ × ℝ × ℝ} (hz : z ∈ edge_edgeDomain) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    fderiv ℝ (edge_edgeField · v) z (z.1, z.2.1, 0) = (0, 0, z.2.1) := by
  refine edge_fderiv_eq (edge_isC1On_edgeField.differentiableAt z hz v hv) ?_
  have hD := edge_edgeDenom_pos hz hv
  have hc := hz.1
  have e : (fun l : ℝ ↦ edge_edgeField (z + l • (z.1, z.2.1, 0)) v) =ᶠ[𝓝 0]
      fun l ↦ (z.2.1 / (z.2.1 - 3 * edge_edgeAlpha v * z.1),
        3 * edge_edgeAlpha v * z.2.1 / (z.2.1 - 3 * edge_edgeAlpha v * z.1), z.2.1 + l * z.2.1) := by
    have hl : ∀ᶠ l : ℝ in 𝓝 0, 0 < 1 + l := by
      have := (continuous_const.add continuous_id).continuousAt (x := (0 : ℝ))
        |>.eventually (lt_mem_nhds (show (0 : ℝ) < 1 + 0 by norm_num))
      simpa using this
    filter_upwards [hl] with l hl
    simp only [edge_edgeField, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_zero]
    have e1 : z.2.1 + l * z.2.1 - 3 * edge_edgeAlpha v * (z.1 + l * z.1) =
        (1 + l) * (z.2.1 - 3 * edge_edgeAlpha v * z.1) := by ring
    rw [e1]
    refine Prod.ext ?_ (Prod.ext ?_ rfl)
    · simp only
      field_simp
    · simp only
      field_simp
  refine HasDerivAt.congr_of_eventuallyEq ?_ e
  refine (hasDerivAt_const _ _).prodMk ((hasDerivAt_const _ _).prodMk ?_)
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const z.2.1).const_add z.2.1

/-- `∂f(z)(0, 0, 1) = 0`: the field does not depend on `s`. -/
theorem edge_fderiv_edgeField_s {z : ℝ × ℝ × ℝ} (hz : z ∈ edge_edgeDomain) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) : fderiv ℝ (edge_edgeField · v) z (0, 0, 1) = 0 := by
  refine edge_fderiv_eq (edge_isC1On_edgeField.differentiableAt z hz v hv) ?_
  have e : (fun l : ℝ ↦ edge_edgeField (z + l • ((0 : ℝ), (0 : ℝ), (1 : ℝ))) v) =
      fun _ ↦ edge_edgeField z v := by
    funext l
    simp [edge_edgeField]
  rw [e]
  exact hasDerivAt_const _ _

/-- `∂φ(z)(a, c, 0) = (3/2)(c + (a² - 1)/c)`. -/
theorem edge_fderiv_edgeCost_scale {z : ℝ × ℝ × ℝ} (hz : z ∈ edge_edgeDomain) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    fderiv ℝ (edge_edgeCost · v) z (z.1, z.2.1, 0) = 3 / 2 * (z.2.1 + (z.1 ^ 2 - 1) / z.2.1) := by
  refine edge_fderiv_eq (edge_isC1On_edgeCost.differentiableAt z hz v hv) ?_
  have hc := hz.1
  have e : (fun l : ℝ ↦ edge_edgeCost (z + l • (z.1, z.2.1, 0)) v) =
      fun l ↦ 3 / 2 * ((z.2.1 + l * z.2.1) + (1 + (z.1 + l * z.1) ^ 2) / (z.2.1 + l * z.2.1)) := by
    funext l
    simp [edge_edgeCost]
  rw [e]
  have h1 : HasDerivAt (fun l : ℝ ↦ z.2.1 + l * z.2.1) z.2.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const z.2.1).const_add z.2.1
  have h2 : HasDerivAt (fun l : ℝ ↦ z.1 + l * z.1) z.1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const z.1).const_add z.1
  have h3 := ((h2.pow 2).const_add 1).div h1 (by simpa using hc.ne')
  convert (h1.add h3).const_mul (3 / 2) using 1
  simp only [zero_mul, add_zero, Pi.pow_apply]
  field_simp
  ring

/-- `∂φ(z)(0, 0, 1) = 0`. -/
theorem edge_fderiv_edgeCost_s {z : ℝ × ℝ × ℝ} (hz : z ∈ edge_edgeDomain) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) : fderiv ℝ (edge_edgeCost · v) z (0, 0, 1) = 0 := by
  refine edge_fderiv_eq (edge_isC1On_edgeCost.differentiableAt z hz v hv) ?_
  have e : (fun l : ℝ ↦ edge_edgeCost (z + l • ((0 : ℝ), (0 : ℝ), (1 : ℝ))) v) =
      fun _ ↦ edge_edgeCost z v := by
    funext l
    simp [edge_edgeCost]
  rw [e]
  exact hasDerivAt_const _ _

end SmoothedOctagon.Reduction.Edge
