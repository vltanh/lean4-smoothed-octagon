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
set `e4_edgeDomain = {c > 0, 3a² < c² < 3(1 + a²)}` of `ℝ³` (the strict star conditions), to which
the free-time maximum principle applies.

Main API:

* `e4_edgeAlpha`, `e4_edgeField`, `e4_edgeCost`, `e4_edgeDomain`, `e4_edgeX`, `e4_edgeFrame`,
  `e4_edgeControl`;
* `e4_isOpen_edgeDomain`, `e4_edgeDenom_pos`, `e4_isC1On_edgeField`, `e4_isC1On_edgeCost`;
* `e4_isStarState_edgeX`, `e4_edgeX_of_isStarState`, `e4_mem_edgeDomain_of_isStarState`,
  `e4_edgeControl_mem`, `e4_det_edgeFrame`, `e4_edgeCost_eq_traceForm`;
* `e4_fderiv_edgeField_scale`, `e4_fderiv_edgeField_s`, `e4_fderiv_edgeCost_scale`,
  `e4_fderiv_edgeCost_s`: the derivatives of the field and the cost along the scaling direction
  `(a, c, 0)` and along the `s` direction.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction.Edge

open SmoothedPolygons MeasureTheory Set Filter ControlSystem
open scoped Topology

/-- `α(v) = (2v - 1)/√3 = (u₁ - u₂)/√3` for `u = (0, v, 1 - v)`. -/
noncomputable def e4_edgeAlpha (v : ℝ) : ℝ := (2 * v - 1) / √3

/-- The edge dynamics `(a, c, s)' = (c/(c - 3αa), 3αc/(c - 3αa), c)`. -/
noncomputable def e4_edgeField (z : ℝ × ℝ × ℝ) (v : ℝ) : ℝ × ℝ × ℝ :=
  (z.2.1 / (z.2.1 - 3 * e4_edgeAlpha v * z.1),
    3 * e4_edgeAlpha v * z.2.1 / (z.2.1 - 3 * e4_edgeAlpha v * z.1), z.2.1)

/-- The cost density `(3/2)(c + (1 + a²)/c) = -(3/2) tr(J X)`. -/
noncomputable def e4_edgeCost (z : ℝ × ℝ × ℝ) (_v : ℝ) : ℝ :=
  3 / 2 * (z.2.1 + (1 + z.1 ^ 2) / z.2.1)

/-- The strict star conditions in the coordinates `(a, c, s)`. -/
def e4_edgeDomain : Set (ℝ × ℝ × ℝ) :=
  {z | 0 < z.2.1 ∧ 3 * z.1 ^ 2 < z.2.1 ^ 2 ∧ z.2.1 ^ 2 < 3 * (1 + z.1 ^ 2)}

/-- The star state `[[a, -(1 + a²)/c], [c, -a]]` of `(a, c, s)`. -/
noncomputable def e4_edgeX (z : ℝ × ℝ × ℝ) : Mat2 :=
  !![z.1, -(1 + z.1 ^ 2) / z.2.1; z.2.1, -z.1]

/-- The frame `h(x, s) = [[1, -x], [s, 1 - s x]]`, `x = a/c`. -/
noncomputable def e4_edgeFrame (z : ℝ × ℝ × ℝ) : Mat2 :=
  !![1, -(z.1 / z.2.1); z.2.2, 1 - z.2.2 * (z.1 / z.2.1)]

/-- The control `(0, v, 1 - v)` on the edge `u₀ = 0`. -/
def e4_edgeControl (v : ℝ) : Fin 3 → ℝ := ![0, v, 1 - v]

private lemma e4_sqrt3_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private lemma e4_sqrt3_pos : (0 : ℝ) < √3 := by positivity

theorem e4_isOpen_edgeDomain : IsOpen e4_edgeDomain := by
  have h1 : IsOpen {z : ℝ × ℝ × ℝ | 0 < z.2.1} := isOpen_lt continuous_const (by fun_prop)
  have h2 : IsOpen {z : ℝ × ℝ × ℝ | 3 * z.1 ^ 2 < z.2.1 ^ 2} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  have h3 : IsOpen {z : ℝ × ℝ × ℝ | z.2.1 ^ 2 < 3 * (1 + z.1 ^ 2)} :=
    isOpen_lt (by fun_prop) (by fun_prop)
  exact h1.inter (h2.inter h3)

/-- `(3α)² = 3 (2v - 1)² ≤ 3` on `[0, 1]`. -/
theorem e4_edgeAlpha_sq (v : ℝ) : (3 * e4_edgeAlpha v) ^ 2 = 3 * (2 * v - 1) ^ 2 := by
  rw [e4_edgeAlpha, mul_pow, div_pow, e4_sqrt3_sq]
  ring

/-- The denominator `c - 3αa` is positive on the domain. -/
theorem e4_edgeDenom_pos {z : ℝ × ℝ × ℝ} (hz : z ∈ e4_edgeDomain) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    0 < z.2.1 - 3 * e4_edgeAlpha v * z.1 := by
  obtain ⟨hc, h1, -⟩ := hz
  have hα := e4_edgeAlpha_sq v
  have hb : (2 * v - 1) ^ 2 ≤ 1 := by nlinarith [hv.1, hv.2]
  have hsq : (3 * e4_edgeAlpha v * z.1) ^ 2 < z.2.1 ^ 2 := by
    rw [mul_pow, hα]
    nlinarith [sq_nonneg z.1]
  nlinarith [abs_lt_of_sq_lt_sq' hsq hc.le, abs_lt.1 (abs_lt_of_sq_lt_sq hsq hc.le)]

/-- A joint `C¹` function on an open set containing `Ω × U` satisfies `IsC1On`. -/
private lemma e4_isC1On_of_contDiffOn {E V F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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
private def e4_O : Set ((ℝ × ℝ × ℝ) × ℝ) :=
  {q | q.1.2.1 ≠ 0 ∧ q.1.2.1 - 3 * e4_edgeAlpha q.2 * q.1.1 ≠ 0}

private lemma e4_isOpen_O : IsOpen e4_O := by
  refine (isOpen_ne_fun (by fun_prop) continuous_const).inter (isOpen_ne_fun ?_ continuous_const)
  simp only [e4_edgeAlpha]
  fun_prop

private lemma e4_subset_O : e4_edgeDomain ×ˢ Icc (0 : ℝ) 1 ⊆ e4_O := by
  rintro ⟨z, v⟩ ⟨hz, hv⟩
  exact ⟨hz.1.ne', (e4_edgeDenom_pos hz hv).ne'⟩

theorem e4_isC1On_edgeField : IsC1On e4_edgeField e4_edgeDomain (Icc (0 : ℝ) 1) := by
  refine e4_isC1On_of_contDiffOn e4_isOpen_O e4_subset_O fun q hq ↦ ?_
  obtain ⟨_, hD⟩ := hq
  simp only [e4_edgeAlpha] at hD
  simp only [e4_edgeField, e4_edgeAlpha]
  refine ContDiffAt.contDiffWithinAt ?_
  fun_prop (disch := assumption)

theorem e4_isC1On_edgeCost : IsC1On e4_edgeCost e4_edgeDomain (Icc (0 : ℝ) 1) := by
  refine e4_isC1On_of_contDiffOn e4_isOpen_O e4_subset_O fun q hq ↦ ?_
  obtain ⟨hc, _⟩ := hq
  simp only [e4_edgeCost]
  refine ContDiffAt.contDiffWithinAt ?_
  fun_prop (disch := assumption)

/-! ### Star states and frames -/

@[simp] theorem e4_edgeX_00 (z : ℝ × ℝ × ℝ) : e4_edgeX z 0 0 = z.1 := rfl
@[simp] theorem e4_edgeX_01 (z : ℝ × ℝ × ℝ) : e4_edgeX z 0 1 = -(1 + z.1 ^ 2) / z.2.1 := rfl
@[simp] theorem e4_edgeX_10 (z : ℝ × ℝ × ℝ) : e4_edgeX z 1 0 = z.2.1 := rfl
@[simp] theorem e4_edgeX_11 (z : ℝ × ℝ × ℝ) : e4_edgeX z 1 1 = -z.1 := rfl
@[simp] theorem e4_edgeFrame_00 (z : ℝ × ℝ × ℝ) : e4_edgeFrame z 0 0 = 1 := rfl
@[simp] theorem e4_edgeFrame_01 (z : ℝ × ℝ × ℝ) : e4_edgeFrame z 0 1 = -(z.1 / z.2.1) := rfl
@[simp] theorem e4_edgeFrame_10 (z : ℝ × ℝ × ℝ) : e4_edgeFrame z 1 0 = z.2.2 := rfl
@[simp] theorem e4_edgeFrame_11 (z : ℝ × ℝ × ℝ) :
    e4_edgeFrame z 1 1 = 1 - z.2.2 * (z.1 / z.2.1) := rfl
@[simp] theorem e4_edgeControl_0 (v : ℝ) : e4_edgeControl v 0 = 0 := rfl
@[simp] theorem e4_edgeControl_1 (v : ℝ) : e4_edgeControl v 1 = v := rfl
@[simp] theorem e4_edgeControl_2 (v : ℝ) : e4_edgeControl v 2 = 1 - v := rfl

theorem e4_isStarState_edgeX {z : ℝ × ℝ × ℝ} (hz : z ∈ e4_edgeDomain) :
    IsStarState (e4_edgeX z) := by
  obtain ⟨hc, h1, h2⟩ := hz
  have h3 := e4_sqrt3_sq
  have h3p := e4_sqrt3_pos
  have hprod : 0 < (z.2.1 + √3 * z.1) * (z.2.1 - √3 * z.1) := by nlinarith
  have hp : 0 < z.2.1 + √3 * z.1 ∧ 0 < z.2.1 - √3 * z.1 := by
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hprod with h | h
    · exact h
    · exact absurd (add_neg h.1 h.2) (by linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.trace_fin_two]
    simp
  · rw [Matrix.det_fin_two]
    simp only [e4_edgeX_00, e4_edgeX_01, e4_edgeX_10, e4_edgeX_11]
    field_simp
    ring
  · simp only [ρ₀, e4_edgeX_00, e4_edgeX_10]
    exact div_pos hp.1 h3p
  · simp only [ρ₁, e4_edgeX_00, e4_edgeX_10]
    exact div_pos hp.2 h3p
  · simp only [ρ₂, e4_edgeX_01, e4_edgeX_10]
    refine div_pos ?_ (by positivity)
    have : 3 * (-(1 + z.1 ^ 2) / z.2.1) + z.2.1 = (z.2.1 ^ 2 - 3 * (1 + z.1 ^ 2)) / z.2.1 := by
      field_simp
      ring
    rw [this, neg_pos]
    exact div_neg_of_neg_of_pos (by linarith) hc

/-- The coordinates `(X₀₀, X₁₀, s)` of a star state lie in the edge domain. -/
theorem e4_mem_edgeDomain_of_isStarState {X : Mat2} (hX : IsStarState X) (s : ℝ) :
    ((X 0 0, X 1 0, s) : ℝ × ℝ × ℝ) ∈ e4_edgeDomain := by
  obtain ⟨htr, hdet, h0, h1, h2⟩ := hX
  have h3 := e4_sqrt3_sq
  have h3p := e4_sqrt3_pos
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

/-- A star state is the `e4_edgeX` of its coordinates. -/
theorem e4_edgeX_of_isStarState {X : Mat2} (hX : IsStarState X) (s : ℝ) :
    e4_edgeX (X 0 0, X 1 0, s) = X := by
  have hc := (e4_mem_edgeDomain_of_isStarState hX s).1
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

theorem e4_edgeControl_mem {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    e4_edgeControl v ∈ controlSimplex := by
  refine ⟨fun i ↦ ?_, by simp⟩
  fin_cases i <;> simp [hv.1, hv.2]

theorem e4_measurable_edgeControl : Measurable e4_edgeControl := by
  refine measurable_pi_iff.mpr fun i ↦ ?_
  fin_cases i
  · exact measurable_const
  · exact measurable_id
  · exact measurable_const.sub measurable_id

theorem e4_det_edgeFrame (z : ℝ × ℝ × ℝ) : (e4_edgeFrame z).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [e4_edgeFrame_00, e4_edgeFrame_01, e4_edgeFrame_10, e4_edgeFrame_11]
  ring

/-- The cost density is `-(3/2) tr(J X)`. -/
theorem e4_edgeCost_eq_traceForm (z : ℝ × ℝ × ℝ) (v : ℝ) :
    e4_edgeCost z v = -(3 / 2) * traceForm J (e4_edgeX z) := by
  simp only [e4_edgeCost, traceForm, J, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, e4_edgeX_00, e4_edgeX_01, e4_edgeX_10, e4_edgeX_11]
  ring

/-- On the edge `u₀ = 0`, `Z_u = [[α, -2/3], [0, -α]]` with `α = (u₁ - u₂)/√3`. -/
theorem e4_controlMatrix_edge {u : Fin 3 → ℝ} (hu0 : u 0 = 0) (hu2 : u 2 = 1 - u 1) :
    controlMatrix u = !![e4_edgeAlpha (u 1), -(2 / 3); 0, -e4_edgeAlpha (u 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [controlMatrix, e4_edgeAlpha, hu0, hu2] <;> ring

theorem e4_controlMatrix_edgeControl (v : ℝ) :
    controlMatrix (e4_edgeControl v) = !![e4_edgeAlpha v, -(2 / 3); 0, -e4_edgeAlpha v] :=
  e4_controlMatrix_edge (by simp) (by simp)

/-- The state field `[P_u, X]` at `X = e4_edgeX z` for `u = (0, v, 1 - v)`. -/
theorem e4_stateField_edgeX {z : ℝ × ℝ × ℝ} (hz : z ∈ e4_edgeDomain) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    controlP (e4_edgeControl v) (e4_edgeX z) * e4_edgeX z -
        e4_edgeX z * controlP (e4_edgeControl v) (e4_edgeX z) =
      !![(e4_edgeField z v).1, (3 * e4_edgeAlpha v * (1 + z.1 ^ 2) - 2 * z.1 * z.2.1) /
          (z.2.1 * (z.2.1 - 3 * e4_edgeAlpha v * z.1));
        (e4_edgeField z v).2.1, -(e4_edgeField z v).1] := by
  have hD := (e4_edgeDenom_pos hz hv).ne'
  have hc := hz.1.ne'
  have htr : traceForm (controlMatrix (e4_edgeControl v)) (e4_edgeX z) =
      -(2 / 3) * (z.2.1 - 3 * e4_edgeAlpha v * z.1) := by
    rw [e4_controlMatrix_edgeControl]
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, e4_edgeX_00, e4_edgeX_01, e4_edgeX_10,
      e4_edgeX_11]
    ring
  simp only [controlP, htr, e4_edgeField]
  rw [e4_controlMatrix_edgeControl]
  generalize e4_edgeAlpha v = α at hD ⊢
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, e4_edgeX_00, e4_edgeX_01,
      e4_edgeX_10, e4_edgeX_11, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    field_simp <;> ring

/-- On the edge `u₀ = 0`, the entries `(0, 0)` and `(1, 0)` of the state field `[P_u, X]` are the
first two components of `e4_edgeField`. -/
theorem e4_stateField_edge {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) (hu0 : u 0 = 0) {X : Mat2}
    (hX : IsStarState X) (s : ℝ) :
    (controlP u X * X - X * controlP u X) 0 0 = (e4_edgeField (X 0 0, X 1 0, s) (u 1)).1 ∧
    (controlP u X * X - X * controlP u X) 1 0 = (e4_edgeField (X 0 0, X 1 0, s) (u 1)).2.1 := by
  have hz := e4_mem_edgeDomain_of_isStarState hX s
  have hv : u 1 ∈ Icc (0 : ℝ) 1 := ⟨(hu.1 1).1, (hu.1 1).2⟩
  have hu2 : u 2 = 1 - u 1 := by linarith [hu.2]
  have hP : controlP u X = controlP (e4_edgeControl (u 1)) X := by
    simp only [controlP, e4_controlMatrix_edge hu0 hu2, e4_controlMatrix_edgeControl]
  have h := e4_stateField_edgeX hz hv
  rw [e4_edgeX_of_isStarState hX s] at h
  rw [hP, h]
  exact ⟨rfl, rfl⟩

/-! ### Derivatives along the scaling and `s` directions -/

private lemma e4_hasDerivAt_line (z w : ℝ × ℝ × ℝ) :
    HasDerivAt (fun l : ℝ ↦ z + l • w) w 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z

private lemma e4_fderiv_eq {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {F : ℝ × ℝ × ℝ → E'} {z w : ℝ × ℝ × ℝ} {d : E'} (hF : DifferentiableAt ℝ F z)
    (h : HasDerivAt (fun l : ℝ ↦ F (z + l • w)) d 0) : fderiv ℝ F z w = d := by
  have h1 : HasDerivAt (fun l : ℝ ↦ F (z + l • w)) (fderiv ℝ F z w) 0 :=
    hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) (e4_hasDerivAt_line z w) (by simp)
  exact h1.unique h

/-- `∂f(z)(a, c, 0) = (0, 0, c)`: the field is homogeneous of degree `0` in `(a, c)`, except for
`s' = c`. -/
theorem e4_fderiv_edgeField_scale {z : ℝ × ℝ × ℝ} (hz : z ∈ e4_edgeDomain) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    fderiv ℝ (e4_edgeField · v) z (z.1, z.2.1, 0) = (0, 0, z.2.1) := by
  refine e4_fderiv_eq (e4_isC1On_edgeField.differentiableAt z hz v hv) ?_
  have hD := e4_edgeDenom_pos hz hv
  have hc := hz.1
  have e : (fun l : ℝ ↦ e4_edgeField (z + l • (z.1, z.2.1, 0)) v) =ᶠ[𝓝 0]
      fun l ↦ (z.2.1 / (z.2.1 - 3 * e4_edgeAlpha v * z.1),
        3 * e4_edgeAlpha v * z.2.1 / (z.2.1 - 3 * e4_edgeAlpha v * z.1), z.2.1 + l * z.2.1) := by
    have hl : ∀ᶠ l : ℝ in 𝓝 0, 0 < 1 + l := by
      have := (continuous_const.add continuous_id).continuousAt (x := (0 : ℝ))
        |>.eventually (lt_mem_nhds (show (0 : ℝ) < 1 + 0 by norm_num))
      simpa using this
    filter_upwards [hl] with l hl
    simp only [e4_edgeField, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, mul_zero]
    have e1 : z.2.1 + l * z.2.1 - 3 * e4_edgeAlpha v * (z.1 + l * z.1) =
        (1 + l) * (z.2.1 - 3 * e4_edgeAlpha v * z.1) := by ring
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
theorem e4_fderiv_edgeField_s {z : ℝ × ℝ × ℝ} (hz : z ∈ e4_edgeDomain) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) : fderiv ℝ (e4_edgeField · v) z (0, 0, 1) = 0 := by
  refine e4_fderiv_eq (e4_isC1On_edgeField.differentiableAt z hz v hv) ?_
  have e : (fun l : ℝ ↦ e4_edgeField (z + l • ((0 : ℝ), (0 : ℝ), (1 : ℝ))) v) =
      fun _ ↦ e4_edgeField z v := by
    funext l
    simp [e4_edgeField]
  rw [e]
  exact hasDerivAt_const _ _

/-- `∂φ(z)(a, c, 0) = (3/2)(c + (a² - 1)/c)`. -/
theorem e4_fderiv_edgeCost_scale {z : ℝ × ℝ × ℝ} (hz : z ∈ e4_edgeDomain) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    fderiv ℝ (e4_edgeCost · v) z (z.1, z.2.1, 0) = 3 / 2 * (z.2.1 + (z.1 ^ 2 - 1) / z.2.1) := by
  refine e4_fderiv_eq (e4_isC1On_edgeCost.differentiableAt z hz v hv) ?_
  have hc := hz.1
  have e : (fun l : ℝ ↦ e4_edgeCost (z + l • (z.1, z.2.1, 0)) v) =
      fun l ↦ 3 / 2 * ((z.2.1 + l * z.2.1) + (1 + (z.1 + l * z.1) ^ 2) / (z.2.1 + l * z.2.1)) := by
    funext l
    simp [e4_edgeCost]
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
theorem e4_fderiv_edgeCost_s {z : ℝ × ℝ × ℝ} (hz : z ∈ e4_edgeDomain) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) : fderiv ℝ (e4_edgeCost · v) z (0, 0, 1) = 0 := by
  refine e4_fderiv_eq (e4_isC1On_edgeCost.differentiableAt z hz v hv) ?_
  have e : (fun l : ℝ ↦ e4_edgeCost (z + l • ((0 : ℝ), (0 : ℝ), (1 : ℝ))) v) =
      fun _ ↦ e4_edgeCost z v := by
    funext l
    simp [e4_edgeCost]
  rw [e]
  exact hasDerivAt_const _ _

end SmoothedOctagon.Reduction.Edge
