module

public import SmoothedOctagon.Period.Defs
public import SmoothedPolygons.Ch7.DiscreteK

/-!
# Vertex flows: the explicit trajectory on a vertex piece

On a piece where the control is almost everywhere a vertex `e_i` of the control simplex, the state
and the frame of a (Carathéodory) state trajectory are the explicit constant-control flows. This
module proves this and the one-arc formulas used throughout the whole-period arguments, stated with
the margins `p_j = margin j` of `Period.Defs`.

## Margins

* `margin_zero_apply`, `margin_one_apply`, `margin_two_apply`: the margins in matrix entries.
* `margin_eq_two_mul_rho`: `p_i = 2 ρ_{2-i}` on traceless matrices.
* `margin_mul_add_eq_four`: `p₀p₁ + p₁p₂ + p₂p₀ = 4` on states (`margin_mul_add_eq`: `= 4 det X`).
* `isStarState_iff_margin`, `margin_pos_of_isStarState`: strict star states are the states with
  positive margins.
* `margin_Rinv_conj`: the twist relabels margins, `p_i(R⁻¹ X R) = p_{i-1}(X)`.
* `sum_margin`, `neg_three_halves_traceForm_J`: the cost density is `(√3/2)(p₀ + p₁ + p₂)`.

## Tangent factors and the one-arc margin map (pure algebra)

* `tangentFactor i w = ((w + w⁻¹)/2) I + (√3 (w - w⁻¹)/2) Z_{e_i}`; explicit forms
  `tangentFactor_zero_eq`, `tangentFactor_one_eq`, `tangentFactor_two_eq`; `tangentFactor_mul`
  (`T_i(w) T_i(v) = T_i(wv)`), `tangentFactor_one`, `tangentFactor_inv_mul`,
  `tangentFactor_mul_inv`, `det_tangentFactor`, `tangentFactor_Rinv_conj`
  (`R⁻¹ T_i(w) R = T_{i+1}(w)`).
* `margin_halfFlow`: for traceless `X`, `Y = T_i(w)⁻¹ X T_i(w)` has margins
  `p_i(Y) = a`, `p_{i+1}(Y) = (a + p_{i+1}(X)) w² - a`, `p_{i-1}(Y) = (a + p_{i-1}(X))/w² - a`,
  `a = p_i(X)`.

## Constant vertex control

* `controlP_vertex`: `P = Z_i/tr(Z_i X) = -(√3/a) Z_i`.
* `exp_smul_controlP_vertex`, `constControlX_vertex`: `X(t) = T_i(w)⁻¹ X₀ T_i(w)`,
  `w = exp(t/a)`.
* `vertexFrame i X q = I + (a/4)((q - q⁻¹) X + √3 (q + q⁻¹ - 2) X Z_i)` and
  `constControlG_vertex`: `g(t) = F_i(X₀, exp(2t/a))`.
* `constControl_tangent`: the tangent frame `V = g X` is `X₀ T_i(exp(2t/a))`.
* `mul_self_eq_neg_one`: `X² = -I` for states.

## Vertex pieces of a state trajectory

For `h : IsStateTrajectory T u g X`, `0 ≤ s₀ ≤ s₁ ≤ T` and `u = e_i` a.e. on `(s₀, s₁)`, with
`a = p_i(X(s₀))`:
* `vertexPiece_flow`: `X` and `g` are the constant-control flows from `(g(s₀), X(s₀))`
  (uniqueness of Carathéodory solutions; the control may differ from `e_i` on a null set);
* `vertexPiece_eq`: `X(t) = T_i(w)⁻¹ X(s₀) T_i(w)`, `g(t) = g(s₀) F_i(X(s₀), w²)`,
  `V(t) = V(s₀) T_i(w²)`, `w = exp((t - s₀)/a)`;
* `vertexPiece_margin`: the active margin stays `a`, and with `q = exp(2(t - s₀)/a)` the other
  margins are `(a + b) q - a` and `(a + c)/q - a`;
* `vertexPiece_cost`: `-(3/2) ∫_{s₀}^{s₁} tr(J X) = (√3/4) a ((a+b)(q-1) + (a+c)(1-q⁻¹) - a log q)`.

## Normal periods

For `P : NormalPeriod` and pieces `0 ≤ k < N` (times `τ_k`, labels `i_k`):
* `VertexRepresentation.τ_N` (`τ_N = T`), `τ_lt_succ`, `T_pos`, `τ_nonneg`, `τ_le_T`,
  `duration_add_period`, `piece_subset`;
* `NormalPeriod.isStateTrajectory`, `g_zero`, `g_T`, `X_T`, `isStarState`, `isStarState_τ`,
  `ae_eq_vertex`;
* `activeMargin_eq` (`a_k = p_{i_k}(X(τ_k))`), `activeMargin_add_N`, `activeMargin_pos`;
* `factor k = exp(2 (τ_{k+1} - τ_k)/a_k)`, `one_lt_factor`, `factor_pos`, `factor_add_N`,
  `log_factor`;
* `piece_margin` (the one-arc margin map at `τ_{k+1}`), `piece_state`, `piece_frame`,
  `piece_tangent`;
* `arcCost a b c q = (√3/4) a ((a + b)(q - 1) + (a + c)(1 - q⁻¹) - a log q)`, `piece_cost`,
  `cost_eq_sum` (the cost is the sum of the piece costs);
* `tangentProduct n = T_{i_0}(q_0) ⋯ T_{i_{n-1}}(q_{n-1})`, `tangent_τ`
  (`V(τ_n) = X(0) · tangentProduct n`) and the **tangent closure** `tangentProduct_N`
  (`tangentProduct N = R`);
* `margin_τ_N`: `p_j(X(τ_N)) = p_{j-1}(X(0))`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set

private lemma vf_s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma vf_s3pos : (0 : ℝ) < √3 := by positivity
private lemma vf_s3c : √3 ^ 3 = 3 * √3 := by rw [pow_succ, vf_s3]
private lemma vf_s3q : √3 ^ 4 = 9 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, vf_s3]; norm_num

/-- Normalize a polynomial identity in `√3`, using `√3² = 3`. -/
local macro "vf_ring" : tactic =>
  `(tactic| ((try ring_nf); (try simp only [vf_s3, vf_s3c, vf_s3q]); (try ring_nf)))

theorem controlMatrix_vertex_zero : controlMatrix (vertex 0) = !![0, 1 / 3; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [controlMatrix, vertex]

theorem controlMatrix_vertex_one :
    controlMatrix (vertex 1) = !![1 / √3, -(2 / 3); 0, -(1 / √3)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [controlMatrix, vertex] <;> ring

theorem controlMatrix_vertex_two :
    controlMatrix (vertex 2) = !![-(1 / √3), -(2 / 3); 0, 1 / √3] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [controlMatrix, vertex] <;> ring

theorem margin_zero_apply (X : Mat2) : margin 0 X = -(√3 * X 0 1) - X 1 0 / √3 := by
  have h := vf_s3pos
  rw [margin, traceForm, controlMatrix_vertex_zero, Matrix.eta_fin_two X]
  simp [Matrix.trace_fin_two]
  field_simp
  ring_nf
  simp only [vf_s3]
  ring

theorem margin_one_apply (X : Mat2) : margin 1 X = -X 0 0 + X 1 1 + 2 * X 1 0 / √3 := by
  have h := vf_s3pos
  rw [margin, traceForm, controlMatrix_vertex_one, Matrix.eta_fin_two X]
  simp [Matrix.trace_fin_two]
  field_simp
  ring_nf
  simp only [vf_s3]
  ring

theorem margin_two_apply (X : Mat2) : margin 2 X = X 0 0 - X 1 1 + 2 * X 1 0 / √3 := by
  have h := vf_s3pos
  rw [margin, traceForm, controlMatrix_vertex_two, Matrix.eta_fin_two X]
  simp [Matrix.trace_fin_two]
  field_simp
  ring_nf
  simp only [vf_s3]
  ring


/-- `p_i = 2 ρ_{2-i}` on traceless matrices: `p₀ = 2ρ₂`, `p₁ = 2ρ₁`, `p₂ = 2ρ₀`. -/
theorem margin_eq_two_mul_rho (X : Mat2) (hX : X.trace = 0) :
    margin 0 X = 2 * ρ₂ X ∧ margin 1 X = 2 * ρ₁ X ∧ margin 2 X = 2 * ρ₀ X := by
  have h := vf_s3pos
  have h11 : X 1 1 = -X 0 0 := by rw [Matrix.trace_fin_two] at hX; linarith
  rw [margin_zero_apply, margin_one_apply, margin_two_apply, h11]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ρ₀, ρ₁, ρ₂] <;> field_simp <;> ring_nf
  simp only [vf_s3]
  ring

/-- On traceless matrices, `p₀p₁ + p₁p₂ + p₂p₀ = 4 det X`. -/
theorem margin_mul_add_eq (X : Mat2) (hX : X.trace = 0) :
    margin 0 X * margin 1 X + margin 1 X * margin 2 X + margin 2 X * margin 0 X =
      4 * X.det := by
  have h := vf_s3pos
  have h11 : X 1 1 = -X 0 0 := by rw [Matrix.trace_fin_two] at hX; linarith
  rw [margin_zero_apply, margin_one_apply, margin_two_apply, Matrix.det_fin_two, h11]
  field_simp
  ring_nf

/-- On states (`tr X = 0`, `det X = 1`), `p₀p₁ + p₁p₂ + p₂p₀ = 4`. -/
theorem margin_mul_add_eq_four (X : Mat2) (hX : X.trace = 0) (hdet : X.det = 1) :
    margin 0 X * margin 1 X + margin 1 X * margin 2 X + margin 2 X * margin 0 X = 4 := by
  rw [margin_mul_add_eq X hX, hdet]; ring

/-- Strict star states are the traceless determinant-one matrices with positive margins. -/
theorem isStarState_iff_margin (X : Mat2) :
    IsStarState X ↔ X.trace = 0 ∧ X.det = 1 ∧ ∀ i, 0 < margin i X := by
  constructor
  · rintro ⟨htr, hdet, h0, h1, h2⟩
    obtain ⟨e0, e1, e2⟩ := margin_eq_two_mul_rho X htr
    refine ⟨htr, hdet, fun i ↦ ?_⟩
    fin_cases i
    · simp only [Fin.zero_eta, e0]; linarith
    · simp only [Fin.mk_one, e1]; linarith
    · simp only [Fin.reduceFinMk, e2]; linarith
  · rintro ⟨htr, hdet, hm⟩
    obtain ⟨e0, e1, e2⟩ := margin_eq_two_mul_rho X htr
    have h0 := hm 0; have h1 := hm 1; have h2 := hm 2
    refine ⟨htr, hdet, ?_, ?_, ?_⟩ <;> linarith

/-- The margins of a star state are positive. -/
theorem margin_pos_of_isStarState {X : Mat2} (hX : IsStarState X) (i : Fin 3) : 0 < margin i X :=
  ((isStarState_iff_margin X).1 hX).2.2 i

/-- The twist relabels margins: `p_i(R⁻¹ X R) = p_{i-1}(X)`. -/
theorem margin_Rinv_conj (X : Mat2) (i : Fin 3) : margin i (R⁻¹ * X * R) = margin (i - 1) X := by
  have h := poly_Rinv_conj_vertex (i - 1)
  rw [sub_add_cancel] at h
  rw [margin, margin, ← h, traceForm, traceForm]
  congr 1
  set Z := controlMatrix (vertex (i - 1))
  rw [show R⁻¹ * Z * R * (R⁻¹ * X * R) = R⁻¹ * (Z * X * R) by
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (R⁻¹ * Z) R R⁻¹, poly_R_mul_inv, Matrix.mul_one],
    Matrix.trace_mul_comm, Matrix.mul_assoc, poly_R_mul_inv, Matrix.mul_one]

/-- The sum of the margins is `-√3 tr(J X)`, because `Z₀ + Z₁ + Z₂ = J`. -/
theorem sum_margin (X : Mat2) :
    margin 0 X + margin 1 X + margin 2 X = -√3 * traceForm J X := by
  have h := vf_s3pos
  rw [margin_zero_apply, margin_one_apply, margin_two_apply, traceForm, J, Matrix.eta_fin_two X]
  simp [Matrix.trace_fin_two]
  field_simp
  ring_nf
  simp only [vf_s3]
  ring

/-- The cost density in margins: `-(3/2) tr(J X) = (√3/2)(p₀ + p₁ + p₂)`. -/
theorem neg_three_halves_traceForm_J (X : Mat2) :
    -(3 / 2) * traceForm J X = √3 / 2 * (margin 0 X + margin 1 X + margin 2 X) := by
  rw [sum_margin]
  have : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  linear_combination (traceForm J X / 2) * this


/-! ### Tangent factors -/

/-- The tangent factor `T_i(w) = ((w + w⁻¹)/2) I + (√3 (w - w⁻¹)/2) Z_{e_i}` of the vertex `e_i`.
On a piece of constant control `e_i` with active margin `a` and duration `t`, the tangent frame
`V = g X` is multiplied on the right by `T_i(q)`, `q = exp(2t/a)`, and the state is conjugated:
`X(t) = T_i(√q)⁻¹ X(0) T_i(√q)`, with `T_i(w)⁻¹ = T_i(w⁻¹)`. -/
noncomputable def tangentFactor (i : Fin 3) (w : ℝ) : Mat2 :=
  ((w + w⁻¹) / 2) • (1 : Mat2) + (√3 * (w - w⁻¹) / 2) • controlMatrix (vertex i)

theorem tangentFactor_zero_eq {w : ℝ} (hw : w ≠ 0) :
    tangentFactor 0 w =
      !![(w + w⁻¹) / 2, (w - w⁻¹) / (2 * √3); √3 * (w - w⁻¹) / 2, (w + w⁻¹) / 2] := by
  have h := vf_s3pos
  rw [tangentFactor, controlMatrix_vertex_zero]
  ext i j; fin_cases i <;> fin_cases j <;> simp
  field_simp
  vf_ring

theorem tangentFactor_one_eq {w : ℝ} (hw : w ≠ 0) :
    tangentFactor 1 w = !![w, -((w - w⁻¹) / √3); 0, w⁻¹] := by
  have h := vf_s3pos
  rw [tangentFactor, controlMatrix_vertex_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> vf_ring

theorem tangentFactor_two_eq {w : ℝ} (hw : w ≠ 0) :
    tangentFactor 2 w = !![w⁻¹, -((w - w⁻¹) / √3); 0, w] := by
  have h := vf_s3pos
  rw [tangentFactor, controlMatrix_vertex_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> vf_ring

/-- `Z_{e_i}² = I/3`. -/
theorem controlMatrix_vertex_mul_self (i : Fin 3) :
    controlMatrix (vertex i) * controlMatrix (vertex i) = (1 / 3 : ℝ) • (1 : Mat2) := by
  have h := vf_s3pos
  fin_cases i
  · rw [Fin.zero_eta, controlMatrix_vertex_zero]
    ext a b; fin_cases a <;> fin_cases b <;> simp
  · rw [Fin.mk_one, controlMatrix_vertex_one]
    ext a b; fin_cases a <;> fin_cases b <;> simp <;> field_simp <;> vf_ring
  · rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, controlMatrix_vertex_two]
    ext a b; fin_cases a <;> fin_cases b <;> simp <;> field_simp <;> vf_ring

private lemma vf_smul_pair_mul {Z : Mat2} (hZ : Z * Z = (1 / 3 : ℝ) • (1 : Mat2))
    (a b c d : ℝ) :
    (a • (1 : Mat2) + b • Z) * (c • (1 : Mat2) + d • Z) =
      (a * c + b * d / 3) • (1 : Mat2) + (a * d + b * c) • Z := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hZ, smul_smul]
  module

/-- `T_i(w) T_i(v) = T_i(wv)`. -/
theorem tangentFactor_mul (i : Fin 3) {w v : ℝ} (hw : w ≠ 0) (hv : v ≠ 0) :
    tangentFactor i w * tangentFactor i v = tangentFactor i (w * v) := by
  rw [tangentFactor, tangentFactor, tangentFactor,
    vf_smul_pair_mul (controlMatrix_vertex_mul_self i)]
  have h := vf_s3pos
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  congr 2
  · field_simp; vf_ring
  · field_simp; vf_ring

theorem tangentFactor_one (i : Fin 3) : tangentFactor i 1 = 1 := by
  norm_num [tangentFactor]

/-- `T_i(w⁻¹) T_i(w) = I`. -/
theorem tangentFactor_inv_mul (i : Fin 3) {w : ℝ} (hw : w ≠ 0) :
    tangentFactor i w⁻¹ * tangentFactor i w = 1 := by
  rw [tangentFactor_mul i (inv_ne_zero hw) hw, inv_mul_cancel₀ hw, tangentFactor_one]

/-- `T_i(w) T_i(w⁻¹) = I`. -/
theorem tangentFactor_mul_inv (i : Fin 3) {w : ℝ} (hw : w ≠ 0) :
    tangentFactor i w * tangentFactor i w⁻¹ = 1 := by
  rw [tangentFactor_mul i hw (inv_ne_zero hw), mul_inv_cancel₀ hw, tangentFactor_one]

theorem det_tangentFactor (i : Fin 3) {w : ℝ} (hw : w ≠ 0) : (tangentFactor i w).det = 1 := by
  have h := vf_s3pos
  fin_cases i
  · rw [Fin.zero_eta, tangentFactor_zero_eq hw, Matrix.det_fin_two_of]
    field_simp; vf_ring
  · rw [Fin.mk_one, tangentFactor_one_eq hw, Matrix.det_fin_two_of]
    field_simp; vf_ring
  · rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, tangentFactor_two_eq hw,
      Matrix.det_fin_two_of]
    field_simp; vf_ring

/-- Conjugation by `R` relabels the tangent factors: `R⁻¹ T_i(w) R = T_{i+1}(w)`. -/
theorem tangentFactor_Rinv_conj (i : Fin 3) (w : ℝ) :
    R⁻¹ * tangentFactor i w * R = tangentFactor (i + 1) w := by
  rw [tangentFactor, tangentFactor, ← poly_Rinv_conj_vertex i]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    poly_inv_mul_R, Matrix.mul_assoc]


/-! ### The state transport along a vertex piece (pure algebra) -/

/-- **One-arc margin map.** Conjugating a traceless `X` by the half factor of the vertex `e_i`,
`Y = T_i(w)⁻¹ X T_i(w)`, keeps the active margin `a = p_i` and moves the other two margins as
`p_{i+1} ↦ (a + p_{i+1}) w² - a`, `p_{i-1} ↦ (a + p_{i-1}) / w² - a`. On a vertex piece of
duration `t` and active margin `a`, `w² = q = exp(2t/a)` is the factor of the piece. -/
theorem margin_halfFlow (X : Mat2) (hX : X.trace = 0) (i : Fin 3) {w : ℝ} (hw : w ≠ 0) :
    margin i (tangentFactor i w⁻¹ * X * tangentFactor i w) = margin i X ∧
      margin (i + 1) (tangentFactor i w⁻¹ * X * tangentFactor i w) =
        (margin i X + margin (i + 1) X) * w ^ 2 - margin i X ∧
      margin (i - 1) (tangentFactor i w⁻¹ * X * tangentFactor i w) =
        (margin i X + margin (i - 1) X) / w ^ 2 - margin i X := by
  have h := vf_s3pos
  have hw' : w⁻¹ ≠ 0 := inv_ne_zero hw
  have h11 : X 1 1 = -X 0 0 := by rw [Matrix.trace_fin_two] at hX; linarith
  rw [Matrix.eta_fin_two X]
  fin_cases i
  · simp only [Fin.zero_eta, show (0 : Fin 3) + 1 = 1 from rfl,
      show (0 : Fin 3) - 1 = 2 from rfl]
    rw [tangentFactor_zero_eq hw', tangentFactor_zero_eq hw]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [margin_zero_apply, margin_one_apply, margin_two_apply] <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h11] <;> field_simp <;> vf_ring
  · simp only [Fin.mk_one, show (1 : Fin 3) + 1 = 2 from rfl,
      show (1 : Fin 3) - 1 = 0 from rfl]
    rw [tangentFactor_one_eq hw', tangentFactor_one_eq hw]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [margin_zero_apply, margin_one_apply, margin_two_apply] <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h11] <;> field_simp <;> vf_ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      show (2 : Fin 3) - 1 = 1 from rfl]
    rw [tangentFactor_two_eq hw', tangentFactor_two_eq hw]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [margin_zero_apply, margin_one_apply, margin_two_apply] <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h11] <;> field_simp <;> vf_ring


/-! ### Constant vertex control: the explicit flow -/

theorem trace_controlMatrix_vertex (i : Fin 3) : (controlMatrix (vertex i)).trace = 0 := by
  fin_cases i <;> simp [controlMatrix, vertex, Matrix.trace_fin_two] <;> ring

theorem det_controlMatrix_vertex (i : Fin 3) : (controlMatrix (vertex i)).det = -(1 / 3) := by
  have h := vf_s3pos
  fin_cases i
  · rw [Fin.zero_eta, controlMatrix_vertex_zero, Matrix.det_fin_two_of]; norm_num
  · rw [Fin.mk_one, controlMatrix_vertex_one, Matrix.det_fin_two_of]
    field_simp; vf_ring
  · rw [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, controlMatrix_vertex_two,
      Matrix.det_fin_two_of]
    field_simp; vf_ring

/-- `tr(Z_i X) = -p_i(X)/√3`. -/
theorem traceForm_controlMatrix_vertex (i : Fin 3) (X : Mat2) :
    traceForm (controlMatrix (vertex i)) X = -(margin i X / √3) := by
  have h := vf_s3pos
  rw [margin]; field_simp

/-- `P = Z_i / tr(Z_i X) = -(√3/a) Z_i`, `a = p_i(X)`. -/
theorem controlP_vertex (i : Fin 3) (X : Mat2) :
    controlP (vertex i) X = (-(√3 / margin i X)) • controlMatrix (vertex i) := by
  rw [controlP, traceForm_controlMatrix_vertex]
  congr 1
  rw [inv_neg, inv_div]

private lemma vf_det_add (A B : Mat2) (hA : A.trace = 0) (hB : B.trace = 0) :
    (A + B).det = A.det + B.det - (A * B).trace := by
  rw [Matrix.trace_fin_two] at hA hB
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.mul_apply,
    Fin.sum_univ_two]
  have hA' : A 1 1 = -A 0 0 := by linarith
  have hB' : B 1 1 = -B 0 0 := by linarith
  rw [hA', hB']
  ring

private lemma vf_trace_controlP (i : Fin 3) (X : Mat2) : (controlP (vertex i) X).trace = 0 := by
  rw [controlP_vertex, Matrix.trace_smul, trace_controlMatrix_vertex, smul_zero]

private lemma vf_det_controlP (i : Fin 3) (X : Mat2) (ha : 0 < margin i X) :
    (controlP (vertex i) X).det = -(1 / margin i X ^ 2) := by
  have h3 := vf_s3pos
  rw [controlP_vertex, Matrix.det_smul, det_controlMatrix_vertex]
  simp only [Fintype.card_fin]
  field_simp; vf_ring

private lemma vf_sqrt_inv_sq {a : ℝ} (ha : 0 < a) : √(-(-(1 / a ^ 2))) = 1 / a := by
  rw [neg_neg, one_div, Real.sqrt_inv, Real.sqrt_sq ha.le, one_div]

private lemma vf_neg_inv_sq {a : ℝ} (ha : 0 < a) : -(1 / a ^ 2) < 0 := by
  have := pow_pos ha 2
  rw [neg_lt_zero]; positivity

/-- `exp(t P) = T_i(exp(-t/a))` for `P = Z_i/tr(Z_i X)`, `a = p_i(X) > 0`. -/
theorem exp_smul_controlP_vertex (i : Fin 3) (X : Mat2) (ha : 0 < margin i X) (t : ℝ) :
    NormedSpace.exp (t • controlP (vertex i) X) =
      tangentFactor i (Real.exp (-(t / margin i X))) := by
  have h3 := vf_s3pos
  have hdet := vf_det_controlP i X ha
  rw [((lemmaA_6_4 _ (vf_trace_controlP i X)).2 t).1 (hdet ▸ vf_neg_inv_sq ha), hdet,
    vf_sqrt_inv_sq ha, controlP_vertex, tangentFactor, smul_smul,
    Real.cosh_eq, Real.sinh_eq, Real.exp_neg, Real.exp_neg, inv_inv]
  congr 2
  · rw [mul_one_div]; ring
  · rw [mul_one_div]
    field_simp
    ring

/-- The state with constant control `e_i` from `X₀`, after time `t`:
`X(t) = T_i(w)⁻¹ X₀ T_i(w)` with `w = exp(t/a)`, `a = p_i(X₀) > 0`. -/
theorem constControlX_vertex (i : Fin 3) (X : Mat2) (ha : 0 < margin i X) (t : ℝ) :
    constControlX X (controlP (vertex i) X) t =
      tangentFactor i (Real.exp (t / margin i X))⁻¹ * X *
        tangentFactor i (Real.exp (t / margin i X)) := by
  rw [constControlX, exp_smul_controlP_vertex i X ha, exp_smul_controlP_vertex i X ha,
    Real.exp_neg, neg_div, neg_neg]

/-- The frame increment of a vertex piece with factor `q`:
`F_i(X, q) = I + (a/4)((q - q⁻¹) X + √3 (q + q⁻¹ - 2) X Z_i)`, `a = p_i(X)`. -/
noncomputable def vertexFrame (i : Fin 3) (X : Mat2) (q : ℝ) : Mat2 :=
  1 + (margin i X / 4) •
    ((q - q⁻¹) • X + (√3 * (q + q⁻¹ - 2)) • (X * controlMatrix (vertex i)))

private lemma vf_trace_mul_controlP (i : Fin 3) (X : Mat2) (ha : 0 < margin i X) :
    (X * controlP (vertex i) X).trace = 1 := by
  have h3 := vf_s3pos
  rw [controlP_vertex, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_comm, ← traceForm,
    traceForm_controlMatrix_vertex, smul_eq_mul]
  field_simp

private lemma vf_det_add_controlP (i : Fin 3) (X : Mat2) (hX : X.trace = 0) (hdetX : X.det = 1)
    (ha : 0 < margin i X) : (X + controlP (vertex i) X).det = -(1 / margin i X ^ 2) := by
  rw [vf_det_add X _ hX (vf_trace_controlP i X), hdetX, vf_det_controlP i X ha,
    vf_trace_mul_controlP i X ha]
  ring

/-- `exp(t(X + P)) = cosh(t/a) I + a sinh(t/a) (X + P)`. -/
private lemma vf_exp_add (i : Fin 3) (X : Mat2) (hX : X.trace = 0) (hdetX : X.det = 1)
    (ha : 0 < margin i X) (t : ℝ) :
    NormedSpace.exp (t • (X + controlP (vertex i) X)) =
      Real.cosh (t * (1 / margin i X)) • (1 : Mat2) +
        (Real.sinh (t * (1 / margin i X)) / (1 / margin i X)) • (X + controlP (vertex i) X) := by
  have htr : (X + controlP (vertex i) X).trace = 0 := by
    rw [Matrix.trace_add, hX, vf_trace_controlP, add_zero]
  have hdet := vf_det_add_controlP i X hX hdetX ha
  rw [((lemmaA_6_4 _ htr).2 t).1 (hdet ▸ vf_neg_inv_sq ha), hdet, vf_sqrt_inv_sq ha]

/-- The frame with constant control `e_i` from `g(0) = I`, `X(0) = X₀`, after time `t`:
`g(t) = F_i(X₀, exp(2t/a))`. -/
theorem constControlG_vertex (i : Fin 3) (X : Mat2) (hX : X.trace = 0) (hdetX : X.det = 1)
    (ha : 0 < margin i X) (t : ℝ) :
    constControlG X (controlP (vertex i) X) t =
      vertexFrame i X (Real.exp (2 * t / margin i X)) := by
  have h3 := vf_s3pos
  have hZZ := controlMatrix_vertex_mul_self i
  have ha0 := ha.ne'
  rw [constControlG, vf_exp_add i X hX hdetX ha, exp_smul_controlP_vertex i X ha, neg_div,
    neg_neg, controlP_vertex, tangentFactor, vertexFrame, Real.cosh_eq, Real.sinh_eq]
  have hw0 : 0 < Real.exp (t / margin i X) := Real.exp_pos _
  have hq : Real.exp (2 * t / margin i X) = Real.exp (t / margin i X) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hneg' : Real.exp (-(t * (1 / margin i X))) = (Real.exp (t / margin i X))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  have hpos' : Real.exp (t * (1 / margin i X)) = Real.exp (t / margin i X) := by
    congr 1; ring
  rw [hq, hneg', hpos']
  generalize Real.exp (t / margin i X) = w at hw0 ⊢
  generalize margin i X = a at ha0 ⊢
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hZZ, smul_smul, smul_add]
  match_scalars <;> field_simp <;> vf_ring


/-- `X² = -I` for a traceless determinant-one `X`. -/
theorem mul_self_eq_neg_one (X : Mat2) (hX : X.trace = 0) (hdetX : X.det = 1) : X * X = -1 := by
  have h := (lemma3_4_1).2.2.1 X X hX hX
  rw [(lemma3_4_1).1 X hX, hdetX] at h
  have h2 : (2 : ℝ) • (X * X) = (2 : ℝ) • (-1 : Mat2) := by
    rw [two_smul, h]; module
  exact smul_right_injective _ two_ne_zero h2

/-- The tangent frame `V = g X` with constant control `e_i` from `g(0) = I`, `X(0) = X₀`:
`V(t) = X₀ T_i(exp(2t/a))`. -/
theorem constControl_tangent (i : Fin 3) (X : Mat2) (hX : X.trace = 0) (hdetX : X.det = 1)
    (ha : 0 < margin i X) (t : ℝ) :
    constControlG X (controlP (vertex i) X) t * constControlX X (controlP (vertex i) X) t =
      X * tangentFactor i (Real.exp (2 * t / margin i X)) := by
  have hXX := mul_self_eq_neg_one X hX hdetX
  have hPX : controlP (vertex i) X * X + X * controlP (vertex i) X = 1 := by
    rw [(lemma3_4_1).2.2.1 _ X (vf_trace_controlP i X) hX, traceForm, Matrix.trace_mul_comm,
      vf_trace_mul_controlP i X ha, one_smul]
  have hw0 : Real.exp (t / margin i X) ≠ 0 := (Real.exp_pos _).ne'
  have hq : Real.exp (2 * t / margin i X) = Real.exp (t / margin i X) * Real.exp (t / margin i X) := by
    rw [← Real.exp_add]; congr 1; ring
  -- `exp(t(X + P)) X = X exp(-tP)`, because `X(X + P) + (X + P)X = 2X² + PX + XP = -I`
  have hcomm : NormedSpace.exp (t • (X + controlP (vertex i) X)) * X =
      X * NormedSpace.exp (-t • controlP (vertex i) X) := by
    have hdet := vf_det_controlP i X ha
    rw [vf_exp_add i X hX hdetX ha,
      ((lemmaA_6_4 _ (vf_trace_controlP i X)).2 (-t)).1 (hdet ▸ vf_neg_inv_sq ha), hdet,
      vf_sqrt_inv_sq ha, neg_mul, Real.cosh_neg, Real.sinh_neg]
    have hPX' : controlP (vertex i) X * X = 1 - X * controlP (vertex i) X := by
      rw [← hPX]; abel
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hXX, hPX', neg_div]
    module
  have hEF := Matrix.exp_neg_smul_mul_exp_smul (controlP (vertex i) X) t
  have hE : NormedSpace.exp (-t • controlP (vertex i) X) =
      tangentFactor i (Real.exp (t / margin i X)) := by
    rw [exp_smul_controlP_vertex i X ha, neg_div, neg_neg]
  rw [constControlG, constControlX, hq, ← tangentFactor_mul i hw0 hw0, ← hE,
    show NormedSpace.exp (t • (X + controlP (vertex i) X)) *
        NormedSpace.exp (-t • controlP (vertex i) X) *
        (NormedSpace.exp (t • controlP (vertex i) X) * X *
          NormedSpace.exp (-t • controlP (vertex i) X)) =
      NormedSpace.exp (t • (X + controlP (vertex i) X)) *
        (NormedSpace.exp (-t • controlP (vertex i) X) *
          NormedSpace.exp (t • controlP (vertex i) X)) * X *
          NormedSpace.exp (-t • controlP (vertex i) X) by simp only [Matrix.mul_assoc],
    hEF, Matrix.mul_one, hcomm, Matrix.mul_assoc]


/-! ### Vertex pieces of a state trajectory -/

/-- An integral curve on `[0, T]`, restricted to `[a, b] ⊆ [0, T]`, with the right-hand side
replaced by a continuous `w` agreeing with it almost everywhere on `(a, b)`. -/
private lemma vf_integral_form_restrict_ae {f v w : ℝ → Mat2} {T a b : ℝ}
    (hI : IsIntegralCurve f v T) (ha : 0 ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (hw : ContinuousOn w (Icc a b)) (hvw : ∀ᵐ t, t ∈ Ioo a b → v t = w t) :
    ∀ i j, IntervalIntegrable (fun s ↦ w s i j) volume a b ∧
      ∀ t ∈ Icc a b, f t i j = f a i j + ∫ s in a..t, w s i j := by
  intro i j
  obtain ⟨hint, heq⟩ := hI i j
  have hwij : ContinuousOn (fun s ↦ w s i j) (Icc a b) :=
    Matrix.continuousOn_iff_entrywise.1 hw i j
  refine ⟨hwij.intervalIntegrable_of_Icc hab, fun t ht ↦ ?_⟩
  have hT : 0 ≤ T := ha.trans (hab.trans hbT)
  have h0a : IntervalIntegrable (fun s ↦ v s i j) volume 0 a := hint.mono_set (by
    rw [uIcc_of_le ha, uIcc_of_le hT]; exact Icc_subset_Icc_right (hab.trans hbT))
  have hat : IntervalIntegrable (fun s ↦ v s i j) volume a t := hint.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc ha (ht.2.trans hbT))
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0a hat
  have hcongr : ∫ s in a..t, v s i j = ∫ s in a..t, w s i j := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [(countable_singleton b).ae_notMem volume, hvw] with s hs hsv hsI
    rw [uIoc_of_le ht.1] at hsI
    have : s ∈ Ioo a b := ⟨hsI.1, lt_of_le_of_ne (hsI.2.trans ht.2) hs⟩
    rw [hsv this]
  rw [heq t ⟨ha.trans ht.1, ht.2.trans hbT⟩, heq a ⟨ha, hab.trans hbT⟩, ← hcongr, ← hadd]
  ring

/-- **A vertex piece of a state trajectory.** If the control of a (Carathéodory) state trajectory
is almost everywhere the vertex `e_i` on `(s₀, s₁) ⊆ [0, T]`, then on `[s₀, s₁]` the state and
the frame are the constant-control flows from `(g(s₀), X(s₀))`. -/
theorem vertexPiece_flow {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀) (h01 : s₀ ≤ s₁) (h1 : s₁ ≤ T)
    {i : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo s₀ s₁ → u t = vertex i) :
    ∀ t ∈ Icc s₀ s₁, X t = constControlX (X s₀) (controlP (vertex i) (X s₀)) (t - s₀) ∧
      g t = g s₀ * constControlG (X s₀) (controlP (vertex i) (X s₀)) (t - s₀) := by
  obtain ⟨-, -, -, hst, hgI, hXI⟩ := h
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hgc : ContinuousOn g (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hgI
  have hsub : Icc s₀ s₁ ⊆ Icc 0 T := Icc_subset_Icc h0 h1
  have hu' : vertex i ∈ controlSimplex := poly_vertex_mem i
  set P₀ := controlP (vertex i) (X s₀) with hP₀
  have hPc : ContinuousOn (fun t ↦ controlP (vertex i) (X t)) (Icc s₀ s₁) :=
    poly_controlP_continuousOn (hXc.mono hsub) hu' fun t ht ↦ (hst t (hsub ht)).2
  have hwc : ContinuousOn (fun t ↦ controlP (vertex i) (X t) * X t -
      X t * controlP (vertex i) (X t)) (Icc s₀ s₁) :=
    (hPc.mul (hXc.mono hsub)).sub ((hXc.mono hsub).mul hPc)
  have hform := vf_integral_form_restrict_ae hXI h0 h01 h1 hwc (by
    filter_upwards [hu] with t ht htI
    simp only [ht htI])
  have hXd := fun t (ht : t ∈ Icc s₀ s₁) ↦
    Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hform ht (hwc t ht)
  -- Lemma 7.1.1: `⟨X, Z_u⟩` is constant on the piece
  have hconst := lemma7_1_1 _ X _ _ hXd
  have hP : ∀ t ∈ Icc s₀ s₁, controlP (vertex i) (X t) = P₀ := by
    intro t ht
    unfold controlP
    rw [poly_traceForm_comm _ (X t), hconst t ht, poly_traceForm_comm (X _)]
    rfl
  -- the explicit flow and its derivative
  set Y : ℝ → Mat2 := fun t ↦ constControlX (X s₀) P₀ (t - s₀) with hY
  set G : ℝ → Mat2 := fun t ↦ g s₀ * constControlG (X s₀) P₀ (t - s₀) with hG
  have hYd : ∀ t, Matrix.HasDerivAtEntrywise Y
      (controlP (vertex i) (Y t) * Y t - Y t * controlP (vertex i) (Y t)) t := by
    intro t
    have h1 := Matrix.HasDerivAtEntrywise.scomp (h := fun s ↦ s - s₀)
      (constControl_solution (vertex i) (X s₀) (t - s₀)).2.1 ((hasDerivAt_id' t).sub_const _)
    rwa [one_smul] at h1
  have hGd : ∀ t, Matrix.HasDerivAtEntrywise G (G t * Y t) t := by
    intro t
    have h1 := Matrix.HasDerivAtEntrywise.scomp (h := fun s ↦ s - s₀)
      (constControl_solution (vertex i) (X s₀) (t - s₀)).1 ((hasDerivAt_id' t).sub_const _)
    rw [one_smul] at h1
    have h2 := h1.const_mul (g s₀)
    rwa [← Matrix.mul_assoc] at h2
  have hY0 : Y s₀ = X s₀ := by
    simp only [hY, sub_self]; exact (constControl_solution (vertex i) (X s₀) 0).2.2.2
  have hG0 : G s₀ = g s₀ := by
    simp only [hG, sub_self]
    rw [show constControlG (X s₀) P₀ 0 = 1 from (constControl_solution (vertex i) (X s₀) 0).2.2.1,
      Matrix.mul_one]
  have hYc : Continuous Y := continuous_iff_continuousAt.2 fun t ↦ (hYd t).continuousAt
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun t ↦ (hGd t).continuousAt
  have hconstY := lemma7_1_1 _ Y s₀ s₁ fun t _ ↦ (hYd t).hasDerivWithinAtEntrywise
  have hPY : ∀ t ∈ Icc s₀ s₁, controlP (vertex i) (Y t) = P₀ := by
    intro t ht
    unfold controlP
    rw [poly_traceForm_comm _ (Y t), hconstY t ht, hY0, poly_traceForm_comm (X _)]
    rfl
  -- uniqueness for the linear equation `X' = [P₀, X]`
  have hXY : EqOn X Y (Icc s₀ s₁) := by
    refine Matrix.ODE_solution_unique_of_bound_Icc
      (G := fun _ M ↦ P₀ * M - M * P₀) (K := 4 * ∑ k, ∑ l, |P₀ k l|)
      (fun _ _ P Q k l ↦ ?_) (hXc.mono hsub) (fun t ht ↦ ?_) hYc.continuousOn (fun t ht ↦ ?_)
      hY0.symm
    · rw [← Matrix.sub_apply, show ∀ P0 : Mat2, P0 * P - P * P0 - (P0 * Q - Q * P0) =
        P0 * (P - Q) - (P - Q) * P0 from fun P0 ↦ by noncomm_ring]
      simpa only [Matrix.sub_apply] using poly_abs_bracket_le _ (P - Q) k l
    · have := hXd t (Ico_subset_Icc_self ht)
      rwa [hP t (Ico_subset_Icc_self ht)] at this
    · have := (hYd t).hasDerivWithinAtEntrywise (s := Icc s₀ s₁)
      rwa [hPY t (Ico_subset_Icc_self ht)] at this
  -- then `g' = g X`
  have hgd : ∀ t ∈ Ico s₀ s₁, Matrix.HasDerivWithinAtEntrywise g (g t * Y t) (Icc s₀ s₁) t := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    rw [← hXY ht']
    exact (Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hgI (hsub ht')
      ((hgc.mul hXc) t (hsub ht'))).mono hsub
  have hgG : EqOn g G (Icc s₀ s₁) :=
    Matrix.ODE_solution_unique_mul_right hYc.continuousOn (hgc.mono hsub) hgd hGc.continuousOn
      (fun t _ ↦ (hGd t).hasDerivWithinAtEntrywise) hG0.symm
  exact fun t ht ↦ ⟨hXY ht, hgG ht⟩


/-- **A vertex piece, explicitly.** With `a = p_i(X(s₀)) > 0` and `w = exp((t - s₀)/a)`, on the
piece `[s₀, s₁]`: `X(t) = T_i(w)⁻¹ X(s₀) T_i(w)`, `g(t) = g(s₀) F_i(X(s₀), w²)`, and the tangent
frame `V = g X` satisfies `V(t) = V(s₀) T_i(w²)`. -/
theorem vertexPiece_eq {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀) (h01 : s₀ ≤ s₁) (h1 : s₁ ≤ T)
    {i : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo s₀ s₁ → u t = vertex i) :
    ∀ t ∈ Icc s₀ s₁,
      X t = tangentFactor i (Real.exp ((t - s₀) / margin i (X s₀)))⁻¹ * X s₀ *
          tangentFactor i (Real.exp ((t - s₀) / margin i (X s₀))) ∧
        g t = g s₀ * vertexFrame i (X s₀) (Real.exp (2 * (t - s₀) / margin i (X s₀))) ∧
        g t * X t = g s₀ * X s₀ * tangentFactor i (Real.exp (2 * (t - s₀) / margin i (X s₀))) := by
  have hst := (h.2.2.2.1 s₀ ⟨h0, h01.trans h1⟩).2
  have ha := margin_pos_of_isStarState hst i
  intro t ht
  obtain ⟨hX, hg⟩ := vertexPiece_flow h h0 h01 h1 hu t ht
  refine ⟨?_, ?_, ?_⟩
  · rw [hX, constControlX_vertex i _ ha]
  · rw [hg, constControlG_vertex i _ hst.1 hst.2.1 ha]
  · rw [hg, hX, Matrix.mul_assoc, constControl_tangent i _ hst.1 hst.2.1 ha, Matrix.mul_assoc]

/-- **One-arc margin formulas.** On a vertex piece `[s₀, s₁]` with active vertex `e_i` and
margins `(a, b, c) = (p_i, p_{i+1}, p_{i-1})` at `s₀`, at time `t` (with `q = exp(2(t - s₀)/a)`)
the active margin is still `a`, and the other two are `(a + b) q - a` and `(a + c)/q - a`. -/
theorem vertexPiece_margin {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀) (h01 : s₀ ≤ s₁) (h1 : s₁ ≤ T)
    {i : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo s₀ s₁ → u t = vertex i) :
    ∀ t ∈ Icc s₀ s₁,
      margin i (X t) = margin i (X s₀) ∧
        margin (i + 1) (X t) = (margin i (X s₀) + margin (i + 1) (X s₀)) *
            Real.exp (2 * (t - s₀) / margin i (X s₀)) - margin i (X s₀) ∧
        margin (i - 1) (X t) = (margin i (X s₀) + margin (i - 1) (X s₀)) /
            Real.exp (2 * (t - s₀) / margin i (X s₀)) - margin i (X s₀) := by
  have hst := (h.2.2.2.1 s₀ ⟨h0, h01.trans h1⟩).2
  intro t ht
  have hw : Real.exp ((t - s₀) / margin i (X s₀)) ≠ 0 := (Real.exp_pos _).ne'
  have hq : Real.exp (2 * (t - s₀) / margin i (X s₀)) =
      Real.exp ((t - s₀) / margin i (X s₀)) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [(vertexPiece_eq h h0 h01 h1 hu t ht).1, hq]
  exact margin_halfFlow _ hst.1 i hw

private lemma vf_sum_margin_perm (i : Fin 3) (X : Mat2) :
    margin 0 X + margin 1 X + margin 2 X = margin i X + margin (i + 1) X + margin (i - 1) X := by
  fin_cases i
  · simp only [Fin.zero_eta, show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) - 1 = 2 from rfl]
  · simp only [Fin.mk_one, show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) - 1 = 0 from rfl]
    ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      show (2 : Fin 3) - 1 = 1 from rfl]
    ring

/-- **The cost of a vertex piece.** With margins `(a, b, c) = (p_i, p_{i+1}, p_{i-1})` at `s₀`
and factor `q = exp(2(s₁ - s₀)/a)`,
`-(3/2) ∫_{s₀}^{s₁} tr(J X) = (√3/4) a ((a + b)(q - 1) + (a + c)(1 - q⁻¹) - a log q)`. -/
theorem vertexPiece_cost {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2}
    (h : IsStateTrajectory T u g X) {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀) (h01 : s₀ ≤ s₁) (h1 : s₁ ≤ T)
    {i : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo s₀ s₁ → u t = vertex i) :
    -(3 / 2) * ∫ t in s₀..s₁, traceForm J (X t) =
      √3 / 4 * margin i (X s₀) *
        ((margin i (X s₀) + margin (i + 1) (X s₀)) *
            (Real.exp (2 * (s₁ - s₀) / margin i (X s₀)) - 1) +
          (margin i (X s₀) + margin (i - 1) (X s₀)) *
            (1 - (Real.exp (2 * (s₁ - s₀) / margin i (X s₀)))⁻¹) -
          margin i (X s₀) * Real.log (Real.exp (2 * (s₁ - s₀) / margin i (X s₀)))) := by
  have hst := (h.2.2.2.1 s₀ ⟨h0, h01.trans h1⟩).2
  have ha := margin_pos_of_isStarState hst i
  set a := margin i (X s₀) with ha_def
  set b := margin (i + 1) (X s₀)
  set c := margin (i - 1) (X s₀)
  have key : ∀ t ∈ uIcc s₀ s₁, -(3 / 2) * traceForm J (X t) =
      √3 / 2 * (-a + (a + b) * Real.exp ((2 / a) * (t - s₀)) +
        (a + c) * Real.exp (-((2 / a) * (t - s₀)))) := by
    intro t ht
    rw [uIcc_of_le h01] at ht
    obtain ⟨m0, m1, m2⟩ := vertexPiece_margin h h0 h01 h1 hu t ht
    rw [neg_three_halves_traceForm_J, vf_sum_margin_perm i, m0, m1, m2, Real.exp_neg,
      show 2 / a * (t - s₀) = 2 * (t - s₀) / a by ring]
    ring
  have hFd : ∀ t, HasDerivAt (fun t ↦ √3 / 2 * (-a * t +
      (a + b) * (a / 2) * Real.exp ((2 / a) * (t - s₀)) -
      (a + c) * (a / 2) * Real.exp (-((2 / a) * (t - s₀)))))
      (√3 / 2 * (-a + (a + b) * Real.exp ((2 / a) * (t - s₀)) +
        (a + c) * Real.exp (-((2 / a) * (t - s₀))))) t := by
    intro t
    have hl : HasDerivAt (fun t ↦ (2 / a) * (t - s₀)) (2 / a) t := by
      simpa using ((hasDerivAt_id t).sub_const s₀).const_mul (2 / a)
    have e1 : HasDerivAt (fun t ↦ Real.exp ((2 / a) * (t - s₀)))
        (Real.exp ((2 / a) * (t - s₀)) * (2 / a)) t := (Real.hasDerivAt_exp _).comp t hl
    have e2 : HasDerivAt (fun t ↦ Real.exp (-((2 / a) * (t - s₀))))
        (Real.exp (-((2 / a) * (t - s₀))) * (-(2 / a))) t := (Real.hasDerivAt_exp _).comp t hl.neg
    have h := ((((hasDerivAt_id t).const_mul (-a)).add (e1.const_mul ((a + b) * (a / 2)))).sub
      (e2.const_mul ((a + c) * (a / 2)))).const_mul (√3 / 2)
    refine h.congr_deriv ?_
    field_simp
    ring
  have hcont : Continuous fun t ↦ √3 / 2 * (-a + (a + b) * Real.exp ((2 / a) * (t - s₀)) +
      (a + c) * Real.exp (-((2 / a) * (t - s₀)))) := by fun_prop
  rw [← intervalIntegral.integral_const_mul, intervalIntegral.integral_congr key,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hFd t)
      (hcont.intervalIntegrable _ _), Real.log_exp]
  simp only [sub_self, mul_zero, Real.exp_zero, Real.exp_neg]
  rw [show 2 / a * (s₁ - s₀) = 2 * (s₁ - s₀) / a by ring]
  field_simp
  ring


/-! ### Vertex representations: the switching times -/

namespace VertexRepresentation

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} (ρ : VertexRepresentation T u)

/-- `τ_N = T`. -/
theorem τ_N : ρ.τ ρ.N = T := by
  have h := ρ.τ_add_period 0
  rwa [zero_add, ρ.τ_zero, zero_add] at h

theorem τ_lt_succ (k : ℤ) : ρ.τ k < ρ.τ (k + 1) := ρ.τ_strictMono (lt_add_one k)

include ρ in
theorem T_pos : 0 < T := by
  have h := ρ.τ_strictMono (show (0 : ℤ) < ρ.N by exact_mod_cast ρ.N_pos)
  rwa [ρ.τ_zero, ρ.τ_N] at h

theorem τ_nonneg {k : ℤ} (hk : 0 ≤ k) : 0 ≤ ρ.τ k := by
  rw [← ρ.τ_zero]; exact ρ.τ_strictMono.monotone hk

theorem τ_le_T {k : ℤ} (hk : k ≤ ρ.N) : ρ.τ k ≤ T :=
  (ρ.τ_strictMono.monotone hk).trans_eq ρ.τ_N

/-- The duration `τ_{k+1} - τ_k` of piece `k` is `N`-periodic. -/
theorem duration_add_period (k : ℤ) :
    ρ.τ (k + ρ.N + 1) - ρ.τ (k + ρ.N) = ρ.τ (k + 1) - ρ.τ k := by
  rw [show k + ρ.N + 1 = k + 1 + ρ.N by ring, ρ.τ_add_period, ρ.τ_add_period]; ring

/-- Piece `k`, for `0 ≤ k < N`, is a subinterval of `[0, T]`. -/
theorem piece_subset {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < ρ.N) :
    0 ≤ ρ.τ k ∧ ρ.τ k ≤ ρ.τ (k + 1) ∧ ρ.τ (k + 1) ≤ T :=
  ⟨ρ.τ_nonneg hk0, (ρ.τ_lt_succ k).le, ρ.τ_le_T (by omega)⟩

end VertexRepresentation

/-! ### Normal periods: one-arc formulas, cost and tangent closure -/

namespace NormalPeriod

variable (P : NormalPeriod)

theorem isStateTrajectory : IsStateTrajectory P.T P.u P.g P.X := P.extremal.1

theorem g_zero : P.g 0 = 1 := P.extremal.2.1

theorem g_T : P.g P.T = R := P.extremal.2.2.1

theorem X_T : P.X P.T = R⁻¹ * P.X 0 * R := P.extremal.2.2.2.1

theorem isStarState {t : ℝ} (ht : t ∈ Icc 0 P.T) : IsStarState (P.X t) :=
  (P.isStateTrajectory.2.2.2.1 t ht).2

theorem T_pos : 0 < P.T := VertexRepresentation.T_pos P.rep

/-- The state at the switching time `τ_k`, `0 ≤ k ≤ N`, is a star state. -/
theorem isStarState_τ {k : ℤ} (hk0 : 0 ≤ k) (hkN : k ≤ P.N) : IsStarState (P.X (P.rep.τ k)) :=
  P.isStarState ⟨P.rep.τ_nonneg hk0, P.rep.τ_le_T hkN⟩

/-- On piece `k`, `0 ≤ k < N`, the control is a.e. the vertex `e_{i_k}`. -/
theorem ae_eq_vertex {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) :
    ∀ᵐ t, t ∈ Ioo (P.rep.τ k) (P.rep.τ (k + 1)) → P.u t = vertex (P.rep.label k) :=
  P.rep.ae_eq_vertex k hk0 hkN

theorem activeMargin_eq {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) :
    P.activeMargin k = margin (P.rep.label k) (P.X (P.rep.τ k)) := by
  rw [activeMargin, Int.emod_eq_of_lt hk0 hkN]

theorem activeMargin_add_N (k : ℤ) : P.activeMargin (k + P.N) = P.activeMargin k := by
  simp only [activeMargin, Int.add_emod_right]

/-- Every active margin is positive. -/
theorem activeMargin_pos (k : ℤ) : 0 < P.activeMargin k := by
  have hN : (0 : ℤ) < P.N := by exact_mod_cast P.rep.N_pos
  rw [activeMargin]
  exact margin_pos_of_isStarState
    (P.isStarState_τ (Int.emod_nonneg k hN.ne') (Int.emod_lt_of_pos k hN).le) _

/-- The factor `q_k = exp(2 (τ_{k+1} - τ_k)/a_k) > 1` of piece `k`; the duration of the piece is
`(a_k/2) log q_k`. Pieces are read modulo `N`. -/
noncomputable def factor (k : ℤ) : ℝ :=
  Real.exp (2 * (P.rep.τ (k + 1) - P.rep.τ k) / P.activeMargin k)

theorem one_lt_factor (k : ℤ) : 1 < P.factor k := by
  rw [factor, Real.one_lt_exp_iff]
  have := P.rep.τ_lt_succ k
  have := P.activeMargin_pos k
  apply div_pos <;> linarith

theorem factor_pos (k : ℤ) : 0 < P.factor k := Real.exp_pos _

theorem factor_add_N (k : ℤ) : P.factor (k + P.N) = P.factor k := by
  rw [factor, factor, P.activeMargin_add_N, P.rep.duration_add_period]

/-- `log q_k = 2 (τ_{k+1} - τ_k)/a_k`. -/
theorem log_factor (k : ℤ) :
    Real.log (P.factor k) = 2 * (P.rep.τ (k + 1) - P.rep.τ k) / P.activeMargin k := by
  rw [factor, Real.log_exp]

/-- **One-arc margin formulas** for piece `k`, `0 ≤ k < N`, with active vertex `i = i_k` and
margins `(a, b, c) = (p_i, p_{i+1}, p_{i-1})` at `τ_k`: at `τ_{k+1}` the margins are
`(a, (a + b) q_k - a, (a + c)/q_k - a)`. -/
theorem piece_margin {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) :
    margin (P.rep.label k) (P.X (P.rep.τ (k + 1))) = P.activeMargin k ∧
      margin (P.rep.label k + 1) (P.X (P.rep.τ (k + 1))) =
        (P.activeMargin k + margin (P.rep.label k + 1) (P.X (P.rep.τ k))) * P.factor k -
          P.activeMargin k ∧
      margin (P.rep.label k - 1) (P.X (P.rep.τ (k + 1))) =
        (P.activeMargin k + margin (P.rep.label k - 1) (P.X (P.rep.τ k))) / P.factor k -
          P.activeMargin k := by
  obtain ⟨h0, h01, h1⟩ := P.rep.piece_subset hk0 hkN
  have := vertexPiece_margin P.isStateTrajectory h0 h01 h1 (P.ae_eq_vertex hk0 hkN) _
    ⟨h01, le_rfl⟩
  rwa [factor, P.activeMargin_eq hk0 hkN]

/-- The state at the end of piece `k`: `X(τ_{k+1}) = T_i(√q_k)⁻¹ X(τ_k) T_i(√q_k)`,
`√q_k = exp((τ_{k+1} - τ_k)/a_k)`. -/
theorem piece_state {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) :
    P.X (P.rep.τ (k + 1)) =
      tangentFactor (P.rep.label k)
          (Real.exp ((P.rep.τ (k + 1) - P.rep.τ k) / P.activeMargin k))⁻¹ *
        P.X (P.rep.τ k) *
        tangentFactor (P.rep.label k) (Real.exp ((P.rep.τ (k + 1) - P.rep.τ k) / P.activeMargin k)) := by
  obtain ⟨h0, h01, h1⟩ := P.rep.piece_subset hk0 hkN
  rw [P.activeMargin_eq hk0 hkN]
  exact (vertexPiece_eq P.isStateTrajectory h0 h01 h1 (P.ae_eq_vertex hk0 hkN) _
    ⟨h01, le_rfl⟩).1

/-- **Frame increment** of piece `k`: `g(τ_{k+1}) = g(τ_k) F_{i_k}(X(τ_k), q_k)`. -/
theorem piece_frame {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) :
    P.g (P.rep.τ (k + 1)) =
      P.g (P.rep.τ k) * vertexFrame (P.rep.label k) (P.X (P.rep.τ k)) (P.factor k) := by
  obtain ⟨h0, h01, h1⟩ := P.rep.piece_subset hk0 hkN
  rw [factor, P.activeMargin_eq hk0 hkN]
  exact (vertexPiece_eq P.isStateTrajectory h0 h01 h1 (P.ae_eq_vertex hk0 hkN) _
    ⟨h01, le_rfl⟩).2.1

/-- **Tangent transition** of piece `k`: `V(τ_{k+1}) = V(τ_k) T_{i_k}(q_k)` for `V = g X`. -/
theorem piece_tangent {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) :
    P.g (P.rep.τ (k + 1)) * P.X (P.rep.τ (k + 1)) =
      P.g (P.rep.τ k) * P.X (P.rep.τ k) * tangentFactor (P.rep.label k) (P.factor k) := by
  obtain ⟨h0, h01, h1⟩ := P.rep.piece_subset hk0 hkN
  rw [factor, P.activeMargin_eq hk0 hkN]
  exact (vertexPiece_eq P.isStateTrajectory h0 h01 h1 (P.ae_eq_vertex hk0 hkN) _
    ⟨h01, le_rfl⟩).2.2

/-- The cost `(√3/4) a ((a + b)(q - 1) + (a + c)(1 - q⁻¹) - a log q)` of a vertex piece with
active margin `a`, growing margin `b`, decreasing margin `c` and factor `q`. -/
noncomputable def arcCost (a b c q : ℝ) : ℝ :=
  √3 / 4 * a * ((a + b) * (q - 1) + (a + c) * (1 - q⁻¹) - a * Real.log q)

/-- **Cost of piece `k`**, `0 ≤ k < N`. -/
theorem piece_cost {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) :
    -(3 / 2) * ∫ t in P.rep.τ k..P.rep.τ (k + 1), traceForm J (P.X t) =
      arcCost (P.activeMargin k) (margin (P.rep.label k + 1) (P.X (P.rep.τ k)))
        (margin (P.rep.label k - 1) (P.X (P.rep.τ k))) (P.factor k) := by
  obtain ⟨h0, h01, h1⟩ := P.rep.piece_subset hk0 hkN
  rw [arcCost, factor, P.activeMargin_eq hk0 hkN]
  exact vertexPiece_cost P.isStateTrajectory h0 h01 h1 (P.ae_eq_vertex hk0 hkN)

/-- **The cost is the sum of the piece costs.** -/
theorem cost_eq_sum :
    P.cost = ∑ k ∈ Finset.range P.N, arcCost (P.activeMargin k)
      (margin (P.rep.label k + 1) (P.X (P.rep.τ k)))
      (margin (P.rep.label k - 1) (P.X (P.rep.τ k))) (P.factor k) := by
  have hXc : ContinuousOn P.X (Icc 0 P.T) :=
    Matrix.continuousOn_of_eq_add_integral P.isStateTrajectory.2.2.2.2.2
  have hJc : ContinuousOn (fun t ↦ traceForm J (P.X t)) (Icc 0 P.T) :=
    ((continuous_const.matrix_mul continuous_id).matrix_trace).comp_continuousOn hXc
  have hint : ∀ k < P.N, IntervalIntegrable (fun t ↦ traceForm J (P.X t)) volume
      (P.rep.τ (k : ℤ)) (P.rep.τ ((k + 1 : ℕ) : ℤ)) := by
    intro k hk
    obtain ⟨h0, h01, h1⟩ := P.rep.piece_subset (k := k) (by positivity) (by exact_mod_cast hk)
    push_cast
    exact (hJc.mono (Icc_subset_Icc h0 h1)).intervalIntegrable_of_Icc h01
  rw [cost, reinhardtCost]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [show ((P.N : ℕ) : ℤ) = P.rep.N from rfl, P.rep.τ_N, show ((0 : ℕ) : ℤ) = 0 from rfl,
    P.rep.τ_zero] at hsum
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have := P.piece_cost (k := k) (by positivity) (by exact_mod_cast Finset.mem_range.1 hk)
  push_cast
  exact this

/-- The ordered product `T_{i_0}(q_0) ⋯ T_{i_{n-1}}(q_{n-1})` of the first `n` tangent factors. -/
noncomputable def tangentProduct (n : ℕ) : Mat2 :=
  ((List.range n).map fun k : ℕ ↦ tangentFactor (P.rep.label k) (P.factor k)).prod

theorem tangentProduct_succ (n : ℕ) :
    P.tangentProduct (n + 1) =
      P.tangentProduct n * tangentFactor (P.rep.label n) (P.factor n) := by
  simp [tangentProduct, List.range_succ]

/-- `V(τ_n) = X(0) T_{i_0}(q_0) ⋯ T_{i_{n-1}}(q_{n-1})` for `n ≤ N`. -/
theorem tangent_τ (n : ℕ) (hn : n ≤ P.N) :
    P.g (P.rep.τ n) * P.X (P.rep.τ n) = P.X 0 * P.tangentProduct n := by
  induction n with
  | zero => simp [tangentProduct, P.rep.τ_zero, P.g_zero]
  | succ n ih =>
    have h := P.piece_tangent (k := n) (by positivity) (by exact_mod_cast hn)
    push_cast at h ⊢
    rw [h, ih (by omega), P.tangentProduct_succ, Matrix.mul_assoc]

/-- **Tangent closure**: `T_{i_0}(q_0) ⋯ T_{i_{N-1}}(q_{N-1}) = R`. -/
theorem tangentProduct_N : P.tangentProduct P.N = R := by
  have h := P.tangent_τ P.N le_rfl
  rw [P.rep.τ_N, P.g_T, P.X_T] at h
  have hst := P.isStarState ⟨le_rfl, P.T_pos.le⟩
  have hXX := mul_self_eq_neg_one (P.X 0) hst.1 hst.2.1
  have h' : P.X 0 * R = P.X 0 * P.tangentProduct P.N := by
    rw [← h]; simp only [← Matrix.mul_assoc, poly_R_mul_inv, Matrix.one_mul]
  have h'' := congrArg (P.X 0 * ·) h'
  simp only [← Matrix.mul_assoc, hXX, Matrix.neg_mul, Matrix.one_mul, neg_inj] at h''
  exact h''.symm

/-- The twist relabels the margins at the seam: `p_j(X(τ_N)) = p_{j-1}(X(0))`. -/
theorem margin_τ_N (j : Fin 3) : margin j (P.X (P.rep.τ P.N)) = margin (j - 1) (P.X 0) := by
  rw [P.rep.τ_N, P.X_T, margin_Rinv_conj]

end NormalPeriod

end SmoothedOctagon
