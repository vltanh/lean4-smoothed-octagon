module

public import SmoothedOctagon.Period.VertexFlow
public import SmoothedOctagon.Period.Hamiltonian
public import SmoothedOctagon.Terminal.Cycle
public import SmoothedPolygons.Ch7.Isolated.VertexFlow

/-!
# The costate of a normal vertex period

The costate calculus of a Pontryagin extremal with cost multiplier `λ = -1` on vertex pieces,
written in the margin coordinates `p_j = margin j` of `Period/Defs.lean`, and its transport through
the twist. Cases R and M3 are derived from it (`Exclusion/Reverse`, `Exclusion/Minimum`); it is
meant for cases M1, F and M2 as well.

## Coordinates

With `L = Λ₁ - (3/2) λ J = Λ₁ + (3/2) J` (`costateL`), put `Â = X L X` (`costateA`) and
`B̂ = -(Λ_R + 2L + ⟨L, X⟩ X)` (`costateB`), and `α_j = p_j(Â)` (`costateAlpha`),
`β_j = p_j(B̂)` (`costateBeta`). Then (`margin_mul_hamiltonian`) the vertex Hamiltonians are
`p_j H_j = σ_j := 2 α_j + β_j`, so `H_j` has the sign of `σ_j`; and `⟨Λ_R, X⟩ = 0` reads
`∑_{j ≠ l} β_j p_l = 0` (`costateB_perp`). The costate is recovered from `(X, α, β)`:
`L = -X Â X`, `Λ_R = -B̂ - 2L - ⟨L, X⟩ X`.

* Margins as linear coordinates: `cst_margin_add/sub/neg/smul`, `cst_hasDerivAt_margin`,
  `cst_margin_bracket` (`p_j([Z_i, F])`), `cst_margin_bracket_P` (`P = -(√3/a) Z_i`),
  `cst_margin_J_bracket` (`p_j((3/2)[J, F]) = √3 (p_{j+1}(F) - p_{j-1}(F))`), `cst_margin_pair`
  (`∑_{j ≠ l} p_j(M) p_l(X) = -4 ⟨M, X⟩`).
* `cst_mul_mul_self` (`X Λ X = ⟨Λ, X⟩ X + Λ`), `trace_costateL`.
* Twist: `costateL_conj`, `costateA_conj`, `costateB_conj` (conjugation by `R` commutes with
  `Â, B̂`), so `α_j(T) = α_{j-1}(0)` like the margins (`margin_Rinv_conj`).

## The costate equations on a vertex piece

On a piece with control `e_i` (`P = -(√3/a) Z_i`, `a = p_i`), with `X' = [P, X]`, `Λ₁' = [Λ₁, X]`:
`Â' = 2 [P, Â] - (3/2)[J, X]` (`costateA_deriv_eq`) and
`B̂' = [P, B̂] + 3 [J, X] - H_i [P, X]` (`costateB_deriv_eq`), and `H_i = 0` on the piece
(`vertexPiece_hamiltonian_eq_zero`). In coordinates these are scalar linear equations with
explicit inhomogeneities (`vertexPiece_costate_deriv`, solved by `cst_ode`), giving
(`vertexPiece_costate`), with margins `(a, b, c) = (p_i, p_{i+1}, p_{i-1})` at the start and
running factor `q = exp(2 t/a)`:
* `α_i ↦ α_i + costateAct a b c q`, `β_i ↦ β_i - 2 costateAct a b c q` (so `σ_i` is constant);
* `α_i + α_{i+1} ↦ q² (α_i + α_{i+1}) + costateAGrow a b q`,
  `α_i + α_{i-1} ↦ q⁻² (α_i + α_{i-1}) + costateADecr a c q`;
* `β_i + β_{i+1} ↦ q (β_i + β_{i+1}) + costateBGrow a b q`,
  `β_i + β_{i-1} ↦ q⁻¹ (β_i + β_{i-1}) + costateBDecr a c q`.
These replace the first-variation identities of the notes: every needle identity
(GLOBAL_REVERSE_PERIOD_EXCLUSION (24)) is a linear identity between the `σ_j` at the switches.

## Normal periods

* `NormalPeriod.Λ₁_eq_conj`: `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` (Corollary 6.5.3).
* `NormalPeriod.cutShift`, `cutAlpha`, `cutBeta` (`k : ℤ`): the costate coordinates at the switch
  `τ_k` of the twisted extension, relabeled like `termMargin`; `cutAlpha_succ`, `cutBeta_succ`,
  `termMargin_succ` (the seam, through `costateAlpha_τ_N`, `costateBeta_τ_N`), `Λ₁_T`, `ΛR_T`.
* `sig_le_of_mem` (`σ_j ≤ 0` at every time), `sig_act_of_mem` (`σ_{i_r} = 0` on piece `r`),
  `cut_transport`, `cut_sig_grow_le`, `cut_sig_decr_le`.
* **`CostateCycle N`**: a `Term.Cycle N` with costate coordinates `α k j`, `β k j`, the one-arc
  transport, `σ_{i_k} = 0` (`sig_act`, `sig_act_succ`), `σ_j ≤ 0` at the switches (`sig_le`) and
  along the pieces for the two inactive labels (`sig_grow_le`, `sig_decr_le`), and `perp`.
  API: `sig`, `act` (`a_k = m_k(i_k)`), `act_add`, `act_pos`, `act_emod`, `exists_act_min`,
  `transport` (all transports for a given label), `perp_rot`.
* **`NormalPeriod.costateCycle : CostateCycle P.N`**, with `costateCycle_lab`, `costateCycle_m`,
  `costateCycle_q`, `costateCycle_m_lab` (`a_k` is `P.activeMargin k`).
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set

private lemma cst_s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma cst_s3pos : (0 : ℝ) < √3 := by positivity
private lemma cst_s3c : √3 ^ 3 = 3 * √3 := by rw [pow_succ, cst_s3]
private lemma cst_s3q : √3 ^ 4 = 9 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, cst_s3]; norm_num

/-- Normalize a polynomial identity in `√3`, using `√3² = 3`. -/
local macro "cst_ring" : tactic =>
  `(tactic| ((try ring_nf); (try simp only [cst_s3, cst_s3c, cst_s3q]); (try ring_nf)))

/-! ### The margins as linear coordinates on matrices -/

theorem cst_margin_add (j : Fin 3) (A B : Mat2) : margin j (A + B) = margin j A + margin j B := by
  simp only [margin, traceForm, Matrix.mul_add, Matrix.trace_add]; ring

theorem cst_margin_sub (j : Fin 3) (A B : Mat2) : margin j (A - B) = margin j A - margin j B := by
  simp only [margin, traceForm, Matrix.mul_sub, Matrix.trace_sub]; ring

theorem cst_margin_neg (j : Fin 3) (A : Mat2) : margin j (-A) = -margin j A := by
  simp only [margin, traceForm, Matrix.mul_neg, Matrix.trace_neg]; ring

theorem cst_margin_smul (j : Fin 3) (c : ℝ) (A : Mat2) : margin j (c • A) = c * margin j A := by
  simp only [margin, traceForm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]; ring

/-- The margins of a matrix differentiable entrywise are differentiable. -/
theorem cst_hasDerivAt_margin (j : Fin 3) {f : ℝ → Mat2} {f' : Mat2} {t : ℝ}
    (h : Matrix.HasDerivAtEntrywise f f' t) :
    HasDerivAt (fun s ↦ margin j (f s)) (margin j f') t := by
  have := ((h.const_mul (controlMatrix (vertex j))).trace).const_mul (-√3)
  simpa only [margin, traceForm] using this

/-- **The vertex brackets in margin coordinates.** For every matrix `F`:
`p_i([Z_i, F]) = 0`, `p_{i+1}([Z_i, F]) = -(2/√3)(p_i(F) + p_{i+1}(F))` and
`p_{i-1}([Z_i, F]) = (2/√3)(p_{i-1}(F) + p_i(F))`. -/
theorem cst_margin_bracket (i : Fin 3) (F : Mat2) :
    margin i (controlMatrix (vertex i) * F - F * controlMatrix (vertex i)) = 0 ∧
      margin (i + 1) (controlMatrix (vertex i) * F - F * controlMatrix (vertex i)) =
        -(2 / √3) * (margin i F + margin (i + 1) F) ∧
      margin (i - 1) (controlMatrix (vertex i) * F - F * controlMatrix (vertex i)) =
        2 / √3 * (margin (i - 1) F + margin i F) := by
  have h := cst_s3pos
  rw [Matrix.eta_fin_two F]
  fin_cases i
  · simp only [Fin.zero_eta, show (0 : Fin 3) + 1 = 1 from rfl,
      show (0 : Fin 3) - 1 = 2 from rfl]
    rw [controlMatrix_vertex_zero]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [margin_zero_apply, margin_one_apply, margin_two_apply] <;>
      simp <;> field_simp <;> cst_ring
  · simp only [Fin.mk_one, show (1 : Fin 3) + 1 = 2 from rfl,
      show (1 : Fin 3) - 1 = 0 from rfl]
    rw [controlMatrix_vertex_one]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [margin_zero_apply, margin_one_apply, margin_two_apply] <;>
      simp <;> field_simp <;> cst_ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      show (2 : Fin 3) - 1 = 1 from rfl]
    rw [controlMatrix_vertex_two]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [margin_zero_apply, margin_one_apply, margin_two_apply] <;>
      simp <;> field_simp <;> cst_ring

/-- **The cost bracket in margin coordinates**:
`p_j((3/2)[J, F]) = √3 (p_{j+1}(F) - p_{j-1}(F))`. -/
theorem cst_margin_J_bracket (j : Fin 3) (F : Mat2) :
    margin j ((3 / 2 : ℝ) • (J * F - F * J)) = √3 * (margin (j + 1) F - margin (j - 1) F) := by
  have h := cst_s3pos
  rw [Matrix.eta_fin_two F]
  fin_cases j
  · simp only [Fin.zero_eta, show (0 : Fin 3) + 1 = 1 from rfl,
      show (0 : Fin 3) - 1 = 2 from rfl]
    simp only [margin_zero_apply, margin_one_apply, margin_two_apply]
    simp [J]; field_simp; cst_ring
  · simp only [Fin.mk_one, show (1 : Fin 3) + 1 = 2 from rfl,
      show (1 : Fin 3) - 1 = 0 from rfl]
    simp only [margin_zero_apply, margin_one_apply, margin_two_apply]
    simp [J]; field_simp; cst_ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      show (2 : Fin 3) - 1 = 1 from rfl]
    simp only [margin_zero_apply, margin_one_apply, margin_two_apply]
    simp [J]; field_simp; cst_ring

/-- The trace form in margin coordinates: for traceless `M`, `X`,
`∑_{j ≠ l} p_j(M) p_l(X) = -4 ⟨M, X⟩`. -/
theorem cst_margin_pair (M X : Mat2) (hM : M.trace = 0) (hX : X.trace = 0) :
    margin 0 M * (margin 1 X + margin 2 X) + margin 1 M * (margin 0 X + margin 2 X) +
      margin 2 M * (margin 0 X + margin 1 X) = -4 * traceForm M X := by
  have h := cst_s3pos
  rw [Matrix.trace_fin_two] at hM hX
  have hM' : M 1 1 = -M 0 0 := by linarith
  have hX' : X 1 1 = -X 0 0 := by linarith
  simp only [margin_zero_apply, margin_one_apply, margin_two_apply, traceForm,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hM', hX']
  field_simp
  cst_ring

/-! ### The costate matrices and the vertex Hamiltonians -/

/-- The shifted primary costate `L = Λ₁ - (3/2) λ J = Λ₁ + (3/2) J` of a normal lift (`λ = -1`). -/
noncomputable def costateL (Λ₁ : Mat2) : Mat2 := Λ₁ + (3 / 2 : ℝ) • J

/-- The first costate matrix `Â = X L X`; its margins `α_j = p_j(Â)` are the first costate
coordinates. -/
noncomputable def costateA (Λ₁ X : Mat2) : Mat2 := X * costateL Λ₁ * X

/-- The second costate matrix `B̂ = -(Λ_R + 2 L + ⟨L, X⟩ X)`; its margins `β_j = p_j(B̂)` are the
second costate coordinates. -/
noncomputable def costateB (Λ₁ ΛR X : Mat2) : Mat2 :=
  -(ΛR + (2 : ℝ) • costateL Λ₁ + traceForm (costateL Λ₁) X • X)

theorem cst_trace_J : J.trace = 0 := by simp [J, Matrix.trace_fin_two]

theorem trace_costateL {Λ₁ : Mat2} (h : Λ₁.trace = 0) : (costateL Λ₁).trace = 0 := by
  rw [costateL, Matrix.trace_add, Matrix.trace_smul, h, cst_trace_J, smul_zero, add_zero]

/-- `X Λ X = ⟨Λ, X⟩ X + Λ` for traceless `Λ` and a traceless `X` of determinant one. -/
theorem cst_mul_mul_self {X Λ : Mat2} (hX : X.trace = 0) (hdet : X.det = 1) (hΛ : Λ.trace = 0) :
    X * Λ * X = traceForm Λ X • X + Λ := by
  rw [Matrix.trace_fin_two] at hX hΛ
  rw [Matrix.det_fin_two] at hdet
  have hX' : X 1 1 = -X 0 0 := by linarith
  have hΛ' : Λ 1 1 = -Λ 0 0 := by linarith
  rw [hX'] at hdet
  have hd : -(X 0 0 * X 0 0) - X 0 1 * X 1 0 = 1 := by linarith
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, traceForm, Matrix.trace_fin_two, hX', hΛ']
  · linear_combination Λ 0 0 * hd
  · linear_combination Λ 0 1 * hd
  · linear_combination Λ 1 0 * hd
  · linear_combination -Λ 0 0 * hd

/-- **The vertex Hamiltonians in costate coordinates.** For a star state `X` and a traceless `Λ₁`,
`p_j(X) H_j = 2 α_j + β_j`, where `H_j = H(Λ₁, Λ_R, X; e_j)` is the vertex Hamiltonian with
`λ = -1`, `α_j = p_j(X L X)` and `β_j = p_j(B̂)`. In particular `H_j` has the sign of
`σ_j = 2 α_j + β_j`. -/
theorem margin_mul_hamiltonian {Λ₁ ΛR X : Mat2} (hX : IsStarState X) (hΛ₁ : Λ₁.trace = 0)
    (j : Fin 3) :
    margin j X * hamiltonian (-1) Λ₁ ΛR X (vertex j) =
      2 * margin j (costateA Λ₁ X) + margin j (costateB Λ₁ ΛR X) := by
  have h3 := cst_s3pos
  have hp : margin j X ≠ 0 := (margin_pos_of_isStarState hX j).ne'
  have hL : Λ₁ - (3 / 2 * (-1) : ℝ) • J = costateL Λ₁ := by
    rw [costateL, show (3 / 2 * (-1) : ℝ) = -(3 / 2) by norm_num, neg_smul, sub_neg_eq_add]
  have hXZ : traceForm X (controlMatrix (vertex j)) = -(margin j X / √3) := by
    rw [traceForm, Matrix.trace_mul_comm, ← traceForm, traceForm_controlMatrix_vertex]
  have hRZ : traceForm ΛR (controlMatrix (vertex j)) = -(margin j ΛR / √3) := by
    rw [traceForm, Matrix.trace_mul_comm, ← traceForm, traceForm_controlMatrix_vertex]
  rw [hamiltonian, hL, hXZ, hRZ, costateA, cst_mul_mul_self hX.1 hX.2.1 (trace_costateL hΛ₁),
    costateB]
  simp only [cst_margin_add, cst_margin_neg, cst_margin_smul]
  field_simp
  ring

/-- `⟨B̂, X⟩ = 0` in margin coordinates: `∑_{j ≠ l} β_j p_l = 0`, when `⟨Λ_R, X⟩ = 0`. -/
theorem costateB_perp {Λ₁ ΛR X : Mat2} (hX : IsStarState X) (hΛ₁ : Λ₁.trace = 0)
    (hΛR : ΛR.trace = 0) (hRX : traceForm ΛR X = 0) :
    margin 0 (costateB Λ₁ ΛR X) * (margin 1 X + margin 2 X) +
      margin 1 (costateB Λ₁ ΛR X) * (margin 0 X + margin 2 X) +
      margin 2 (costateB Λ₁ ΛR X) * (margin 0 X + margin 1 X) = 0 := by
  have hL := trace_costateL hΛ₁
  have hBtr : (costateB Λ₁ ΛR X).trace = 0 := by
    rw [costateB, Matrix.trace_neg, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, hΛR, hL, hX.1]
    simp
  rw [cst_margin_pair _ _ hBtr hX.1]
  have hXX : traceForm X X = -2 := by
    rw [traceForm, mul_self_eq_neg_one X hX.1 hX.2.1]; simp
  have : traceForm (costateB Λ₁ ΛR X) X = 0 := by
    rw [costateB]
    simp only [traceForm, Matrix.neg_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.trace_neg,
      Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    simp only [traceForm] at hRX hXX
    rw [hRX, hXX]; ring
  rw [this, mul_zero]

/-! ### The twist -/

theorem costateL_conj (Λ₁ : Mat2) : costateL (R⁻¹ * Λ₁ * R) = R⁻¹ * costateL Λ₁ * R := by
  have hJ : R⁻¹ * J * R = J := by simpa using poly_conj_pow_J 1
  rw [costateL, costateL, poly_conj_add, poly_conj_smul, hJ]

theorem costateA_conj (Λ₁ X : Mat2) :
    costateA (R⁻¹ * Λ₁ * R) (R⁻¹ * X * R) = R⁻¹ * costateA Λ₁ X * R := by
  rw [costateA, costateA, costateL_conj, poly_conj_mul poly_R_mul_inv,
    poly_conj_mul poly_R_mul_inv]

theorem costateB_conj (Λ₁ ΛR X : Mat2) :
    costateB (R⁻¹ * Λ₁ * R) (R⁻¹ * ΛR * R) (R⁻¹ * X * R) = R⁻¹ * costateB Λ₁ ΛR X * R := by
  rw [costateB, costateB, costateL_conj, poly_traceForm_conj poly_R_mul_inv, poly_conj_neg,
    poly_conj_add, poly_conj_add, poly_conj_smul, poly_conj_smul]

/-! ### The costate equations on a vertex piece (pure algebra) -/

/-- **Derivative of `Â`.** If `X' = [P, X]`, `Λ₁' = [Λ₁, X]`, with `X² = -I` and
`⟨P, X⟩ = 1`, then `Â' = 2 [P, Â] - (3/2) [J, X]`. -/
theorem costateA_deriv_eq {X P Λ₁ : Mat2} (hX : X.trace = 0) (hdet : X.det = 1)
    (hP : P.trace = 0) (hΛ₁ : Λ₁.trace = 0) (hPX : traceForm P X = 1) :
    ((P * X - X * P) * costateL Λ₁ + X * (Λ₁ * X - X * Λ₁)) * X +
        X * costateL Λ₁ * (P * X - X * P) =
      (2 : ℝ) • (P * costateA Λ₁ X - costateA Λ₁ X * P) -
        ((3 / 2 : ℝ) • J * X - X * (3 / 2 : ℝ) • J) := by
  rw [Matrix.trace_fin_two] at hX hP hΛ₁
  rw [Matrix.det_fin_two] at hdet
  have hX' : X 1 1 = -X 0 0 := by linarith
  have hP' : P 1 1 = -P 0 0 := by linarith
  have hΛ' : Λ₁ 1 1 = -Λ₁ 0 0 := by linarith
  rw [hX'] at hdet
  have hg1 : X 0 0 ^ 2 + X 0 1 * X 1 0 + 1 = 0 := by linarith
  have hg2 : 2 * P 0 0 * X 0 0 + P 0 1 * X 1 0 + P 1 0 * X 0 1 - 1 = 0 := by
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hX', hP']
      at hPX
    linarith
  rw [Matrix.eta_fin_two X, Matrix.eta_fin_two P, Matrix.eta_fin_two Λ₁]
  simp only [hX', hP', hΛ']
  set x := X 0 0; set y := X 0 1; set z := X 1 0
  set p := P 0 0; set r := P 0 1; set s := P 1 0
  set l := Λ₁ 0 0; set m := Λ₁ 0 1; set n := Λ₁ 1 0
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [costateA, costateL, J] <;> ring_nf
  · linear_combination (-m * z + n * y) * hg1 + ((-2 * m * z + 2 * n * y + 3 * y + 3 * z) / 2) * hg2
  · linear_combination (2 * (-l * y + m * x)) * hg1 + (-2 * l * y + 2 * m * x - 3 * x) * hg2
  · linear_combination (-2 * (-l * z + n * x)) * hg1 + (2 * l * z - 2 * n * x - 3 * x) * hg2
  · linear_combination (m * z - n * y) * hg1 + (-(-2 * m * z + 2 * n * y + 3 * y + 3 * z) / 2) * hg2

/-- **Derivative of `B̂`.** If `X' = [P, X]`, `Λ₁' = [Λ₁, X]` and `Λ_R'` is the costate right-hand
side with `λ = -1`, with `X² = -I` and `⟨P, X⟩ = 1`, then
`B̂' = [P, B̂] + 3 [J, X] - (⟨L, X⟩ - ⟨Λ_R, P⟩) [P, X]`. -/
theorem costateB_deriv_eq {X P Λ₁ ΛR : Mat2} (hX : X.trace = 0) (hdet : X.det = 1)
    (hP : P.trace = 0) (hΛ₁ : Λ₁.trace = 0) (hΛR : ΛR.trace = 0) (hPX : traceForm P X = 1) :
    -((P * ΛR - ΛR * P - traceForm ΛR P • (P * X - X * P) +
          ((-Λ₁ + (3 / 2 * (-1) : ℝ) • J) * X - X * (-Λ₁ + (3 / 2 * (-1) : ℝ) • J))) +
        (2 : ℝ) • (Λ₁ * X - X * Λ₁) +
        (traceForm (costateL Λ₁) X • (P * X - X * P) +
          ((Λ₁ * X - X * Λ₁) * X + costateL Λ₁ * (P * X - X * P)).trace • X)) =
      (P * costateB Λ₁ ΛR X - costateB Λ₁ ΛR X * P) +
        (2 : ℝ) • ((3 / 2 : ℝ) • J * X - X * (3 / 2 : ℝ) • J) -
        (traceForm (costateL Λ₁) X - traceForm ΛR P) • (P * X - X * P) := by
  rw [Matrix.trace_fin_two] at hX hP hΛ₁ hΛR
  rw [Matrix.det_fin_two] at hdet
  have hX' : X 1 1 = -X 0 0 := by linarith
  have hP' : P 1 1 = -P 0 0 := by linarith
  have hΛ' : Λ₁ 1 1 = -Λ₁ 0 0 := by linarith
  have hR' : ΛR 1 1 = -ΛR 0 0 := by linarith
  rw [hX'] at hdet
  have hg1 : X 0 0 ^ 2 + X 0 1 * X 1 0 + 1 = 0 := by linarith
  have hg2 : 2 * P 0 0 * X 0 0 + P 0 1 * X 1 0 + P 1 0 * X 0 1 - 1 = 0 := by
    simp only [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hX', hP']
      at hPX
    linarith
  rw [Matrix.eta_fin_two X, Matrix.eta_fin_two P, Matrix.eta_fin_two Λ₁, Matrix.eta_fin_two ΛR]
  simp only [hX', hP', hΛ', hR']
  set x := X 0 0; set y := X 0 1; set z := X 1 0
  set p := P 0 0; set r := P 0 1; set s := P 1 0
  set l := Λ₁ 0 0; set m := Λ₁ 0 1; set n := Λ₁ 1 0
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [costateB, costateL, J, traceForm, Matrix.trace_fin_two] <;> ring_nf
  · linear_combination (-2 * m * s + 2 * n * r + 3 * r + 3 * s) * hg1 +
      (-(-2 * m * z + 2 * n * y + 3 * y + 3 * z) / 2) * hg2
  · linear_combination (2 * (-2 * l * r + 2 * m * p - 3 * p)) * hg1 +
      (2 * l * y - 2 * m * x + 3 * x) * hg2
  · linear_combination (-2 * (-2 * l * s + 2 * n * p + 3 * p)) * hg1 +
      (-2 * l * z + 2 * n * x + 3 * x) * hg2
  · linear_combination (2 * m * s - 2 * n * r - 3 * r - 3 * s) * hg1 +
      ((-2 * m * z + 2 * n * y + 3 * y + 3 * z) / 2) * hg2

/-- `[P, F]` in margin coordinates for `P = -(√3/a) Z_i` (the matrix `P` of a vertex piece with
active margin `a`). -/
theorem cst_margin_bracket_P (i : Fin 3) {a : ℝ} (ha : a ≠ 0) (F : Mat2) :
    margin i ((-(√3 / a)) • controlMatrix (vertex i) * F -
        F * (-(√3 / a)) • controlMatrix (vertex i)) = 0 ∧
      margin (i + 1) ((-(√3 / a)) • controlMatrix (vertex i) * F -
          F * (-(√3 / a)) • controlMatrix (vertex i)) = 2 / a * (margin i F + margin (i + 1) F) ∧
      margin (i - 1) ((-(√3 / a)) • controlMatrix (vertex i) * F -
          F * (-(√3 / a)) • controlMatrix (vertex i)) =
        -(2 / a) * (margin (i - 1) F + margin i F) := by
  have h3 := cst_s3pos
  have e : (-(√3 / a)) • controlMatrix (vertex i) * F - F * (-(√3 / a)) • controlMatrix (vertex i) =
      (-(√3 / a)) • (controlMatrix (vertex i) * F - F * controlMatrix (vertex i)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  obtain ⟨h0, h1, h2⟩ := cst_margin_bracket i F
  rw [e, cst_margin_smul, cst_margin_smul, cst_margin_smul, h0, h1, h2]
  refine ⟨by ring, ?_, ?_⟩ <;> field_simp

theorem cst_fin_add_one_add_one (i : Fin 3) : i + 1 + 1 = i - 1 := by revert i; decide

theorem cst_fin_sub_one_sub_one (i : Fin 3) : i - 1 - 1 = i + 1 := by revert i; decide

/-! ### The active Hamiltonian on a vertex piece -/

/-- On a vertex piece `[s₀, s₁]`, `s₀ < s₁`, with control `e_i`, the active vertex Hamiltonian
`H_i` vanishes at every time (the maximum condition holds almost everywhere, and `H_i` is
continuous). -/
theorem vertexPiece_hamiltonian_eq_zero {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀)
    (h01 : s₀ < s₁) (h1 : s₁ ≤ T) {i : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo s₀ s₁ → u t = vertex i) :
    ∀ t ∈ Icc s₀ s₁, hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex i) = 0 := by
  have hc := (IsPontryaginExtremal.continuousOn_vertexHamiltonian h i).mono
    (Icc_subset_Icc h0 h1)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hmax⟩ := h
  have hae : ∀ᵐ t, t ∈ Ioo s₀ s₁ → hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex i) = 0 := by
    filter_upwards [hmax, hu] with t ht hut hmem
    have hmem' : t ∈ Ioo 0 T := ⟨h0.trans_lt hmem.1, hmem.2.trans_le h1⟩
    rw [← hut hmem]
    exact (ht hmem').1
  have hIoo : EqOn (fun t ↦ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex i)) (fun _ ↦ 0)
      (Ioo s₀ s₁) :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' measurableSet_Ioo).mpr hae) isOpen_Ioo
      (hc.mono Ioo_subset_Icc_self) continuousOn_const
  have hIcc := hIoo.of_subset_closure hc continuousOn_const Ioo_subset_Icc_self
    (by rw [closure_Ioo h01.ne])
  exact fun t ht ↦ hIcc ht

/-! ### The costate equations on a vertex piece -/

/-- **Costate derivatives on a vertex piece.** On a vertex piece `[s₀, s₁]` of a normal extremal
with control `e_i` and active margin `a`, the costate is the vertex flow of
`iso_arc_eq_vertexFlow`, which is differentiable everywhere; at each time of the piece the
coordinates `α_j = p_j(Â)`, `β_j = p_j(B̂)` of the flow have the derivatives
`α_j' = 2 p_j([P, Â]) - √3 (p_{j+1}(X) - p_{j-1}(X))`,
`β_j' = p_j([P, B̂]) + 2√3 (p_{j+1}(X) - p_{j-1}(X))`, `P = -(√3/a) Z_i`. -/
theorem vertexPiece_costate_deriv {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR (-1)) {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀) (h01 : s₀ < s₁)
    (h1 : s₁ ≤ T) {i : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo s₀ s₁ → u t = vertex i) :
    ∃ Af Bf : ℝ → Mat2, (∀ t ∈ Icc s₀ s₁, Af t = costateA (Λ₁ t) (X t) ∧
        Bf t = costateB (Λ₁ t) (ΛR t) (X t)) ∧
      ∀ t ∈ Icc s₀ s₁, ∀ j : Fin 3,
        HasDerivAt (fun r ↦ margin j (Af r))
          (2 * margin j ((-(√3 / margin i (X s₀))) • controlMatrix (vertex i) *
              costateA (Λ₁ t) (X t) -
            costateA (Λ₁ t) (X t) * (-(√3 / margin i (X s₀))) • controlMatrix (vertex i)) -
            √3 * (margin (j + 1) (X t) - margin (j - 1) (X t))) t ∧
        HasDerivAt (fun r ↦ margin j (Bf r))
          (margin j ((-(√3 / margin i (X s₀))) • controlMatrix (vertex i) *
              costateB (Λ₁ t) (ΛR t) (X t) -
            costateB (Λ₁ t) (ΛR t) (X t) * (-(√3 / margin i (X s₀))) • controlMatrix (vertex i)) +
            2 * (√3 * (margin (j + 1) (X t) - margin (j - 1) (X t)))) t := by
  have h3 := cst_s3pos
  set q₀ : iso_PhasePt := (X s₀, Λ₁ s₀, ΛR s₀) with hq₀
  have hflow := iso_arc_eq_vertexFlow h h0 h01.le h1 i hu
  have hXeq : ∀ s ∈ Icc s₀ s₁, iso_vfX i q₀ (s - s₀) = X s := fun s hs ↦
    (congrArg Prod.fst (hflow s hs)).symm
  have hLeq : ∀ s ∈ Icc s₀ s₁, iso_vfΛ₁ i q₀ (s - s₀) = Λ₁ s := fun s hs ↦
    (congrArg (fun p : iso_PhasePt ↦ p.2.1) (hflow s hs)).symm
  have hReq : ∀ s ∈ Icc s₀ s₁, iso_vfΛR i q₀ (s - s₀) = ΛR s := fun s hs ↦
    (congrArg (fun p : iso_PhasePt ↦ p.2.2) (hflow s hs)).symm
  have hsc : ∀ {φ φ' : ℝ → Mat2}, (∀ s, Matrix.HasDerivAtEntrywise φ (φ' s) s) →
      ∀ s, Matrix.HasDerivAtEntrywise (fun r ↦ φ (r - s₀)) (φ' (s - s₀)) s := fun {φ φ'} hφ s ↦ by
    have := (hφ (s - s₀)).scomp (h := fun r ↦ r - s₀) ((hasDerivAt_id' s).sub_const s₀)
    rwa [one_smul] at this
  have hXd := hsc (ivf_vfX_hasDerivAt i q₀)
  have hLd := hsc (ivf_vfΛ₁_hasDerivAt i q₀)
  have hRd := hsc (ivf_vfΛR_hasDerivAt i q₀)
  have hPf : ∀ s, controlP (vertex i) (iso_vfX i q₀ s) = controlP (vertex i) (X s₀) := fun s ↦
    ivf_controlP_vfX i q₀ s
  -- facts on the piece
  have hsub : ∀ s ∈ Icc s₀ s₁, s ∈ Icc 0 T := fun s hs ↦ ⟨h0.trans hs.1, hs.2.trans h1⟩
  have hstar : ∀ s ∈ Icc s₀ s₁, IsStarState (X s) := fun s hs ↦
    (h.1.2.2.2.1 s (hsub s hs)).2
  have hpt : ∀ s ∈ Icc s₀ s₁, (Λ₁ s).trace = 0 ∧ (ΛR s).trace = 0 := fun s hs ↦
    ⟨(h.2.2.2.2.2.2.2.1 s (hsub s hs)).1, (h.2.2.2.2.2.2.2.1 s (hsub s hs)).2.1⟩
  have hmarg := vertexPiece_margin h.1 h0 h01.le h1 hu
  have hH := vertexPiece_hamiltonian_eq_zero h h0 h01 h1 hu
  set a := margin i (X s₀) with ha_def
  have ha : 0 < a := margin_pos_of_isStarState (hstar s₀ ⟨le_rfl, h01.le⟩) i
  have hP₀ : controlP (vertex i) (X s₀) = (-(√3 / a)) • controlMatrix (vertex i) :=
    controlP_vertex i (X s₀)
  have hPtr : ((-(√3 / a)) • controlMatrix (vertex i)).trace = 0 := by
    rw [Matrix.trace_smul, trace_controlMatrix_vertex, smul_zero]
  have hPX : ∀ s ∈ Icc s₀ s₁, traceForm ((-(√3 / a)) • controlMatrix (vertex i)) (X s) = 1 := by
    intro s hs
    rw [traceForm, Matrix.smul_mul, Matrix.trace_smul, ← traceForm,
      traceForm_controlMatrix_vertex, (hmarg s hs).1, smul_eq_mul]
    field_simp
  refine ⟨fun r ↦ costateA (iso_vfΛ₁ i q₀ (r - s₀)) (iso_vfX i q₀ (r - s₀)),
    fun r ↦ costateB (iso_vfΛ₁ i q₀ (r - s₀)) (iso_vfΛR i q₀ (r - s₀)) (iso_vfX i q₀ (r - s₀)),
    fun t ht ↦ ⟨by simp only [hXeq t ht, hLeq t ht], by simp only [hXeq t ht, hLeq t ht,
      hReq t ht]⟩, fun t ht j ↦ ⟨?_, ?_⟩⟩
  · -- `Â`
    have hA := ((hXd t).mul ((hLd t).add_const ((3 / 2 : ℝ) • J))).mul (hXd t)
    have key := costateA_deriv_eq (hstar t ht).1 (hstar t ht).2.1 hPtr (hpt t ht).1 (hPX t ht)
    have hAd : Matrix.HasDerivAtEntrywise
        (fun r ↦ costateA (iso_vfΛ₁ i q₀ (r - s₀)) (iso_vfX i q₀ (r - s₀)))
        ((2 : ℝ) • ((-(√3 / a)) • controlMatrix (vertex i) * costateA (Λ₁ t) (X t) -
            costateA (Λ₁ t) (X t) * (-(√3 / a)) • controlMatrix (vertex i)) -
          ((3 / 2 : ℝ) • J * X t - X t * (3 / 2 : ℝ) • J)) t := by
      refine hA.congr_deriv ?_
      rw [← key, hPf, hP₀, hXeq t ht, hLeq t ht]
      rfl
    refine (cst_hasDerivAt_margin j hAd).congr_deriv ?_
    rw [cst_margin_sub, cst_margin_smul, show (3 / 2 : ℝ) • J * X t - X t * (3 / 2 : ℝ) • J =
      (3 / 2 : ℝ) • (J * X t - X t * J) by rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub],
      cst_margin_J_bracket]
  · -- `B̂`
    have hLc := (hLd t).add_const ((3 / 2 : ℝ) • J)
    have hB := (((hRd t).add (hLc.const_smul (2 : ℝ))).add
      (Matrix.HasDerivAtEntrywise.smul ((hLc.mul (hXd t)).trace) (hXd t))).neg
    have key := costateB_deriv_eq (hstar t ht).1 (hstar t ht).2.1 hPtr (hpt t ht).1 (hpt t ht).2
      (hPX t ht)
    have hHt : traceForm (costateL (Λ₁ t)) (X t) -
        traceForm (ΛR t) ((-(√3 / a)) • controlMatrix (vertex i)) = 0 := by
      have := hH t ht
      rw [hamiltonian, show Λ₁ t - (3 / 2 * (-1) : ℝ) • J = costateL (Λ₁ t) by
        rw [costateL, show (3 / 2 * (-1) : ℝ) = -(3 / 2) by norm_num, neg_smul, sub_neg_eq_add]]
        at this
      have hXZ : traceForm (X t) (controlMatrix (vertex i)) = -(a / √3) := by
        rw [traceForm, Matrix.trace_mul_comm, ← traceForm, traceForm_controlMatrix_vertex,
          (hmarg t ht).1]
      rw [hXZ] at this
      have e1 : traceForm (ΛR t) ((-(√3 / a)) • controlMatrix (vertex i)) =
          (-(√3 / a)) * traceForm (ΛR t) (controlMatrix (vertex i)) := by
        simp only [traceForm, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
      have e2 : traceForm (ΛR t) (controlMatrix (vertex i)) / -(a / √3) =
          (-(√3 / a)) * traceForm (ΛR t) (controlMatrix (vertex i)) := by
        field_simp
      rw [e1, ← e2]
      exact this
    rw [hHt, zero_smul, sub_zero] at key
    have hBd : Matrix.HasDerivAtEntrywise
        (fun r ↦ costateB (iso_vfΛ₁ i q₀ (r - s₀)) (iso_vfΛR i q₀ (r - s₀)) (iso_vfX i q₀ (r - s₀)))
        (((-(√3 / a)) • controlMatrix (vertex i) * costateB (Λ₁ t) (ΛR t) (X t) -
            costateB (Λ₁ t) (ΛR t) (X t) * (-(√3 / a)) • controlMatrix (vertex i)) +
          (2 : ℝ) • ((3 / 2 : ℝ) • J * X t - X t * (3 / 2 : ℝ) • J)) t := by
      refine hB.congr_deriv ?_
      rw [← key, costateRHS, hPf, hP₀, hXeq t ht, hLeq t ht, hReq t ht]
      simp only [costateL, traceForm]
    refine (cst_hasDerivAt_margin j hBd).congr_deriv ?_
    rw [cst_margin_add, cst_margin_smul, show (3 / 2 : ℝ) • J * X t - X t * (3 / 2 : ℝ) • J =
      (3 / 2 : ℝ) • (J * X t - X t * J) by rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub],
      cst_margin_J_bracket]

/-! ### The one-arc costate map -/

/-- The costate coordinates `α_j = p_j(X L X)`. -/
noncomputable def costateAlpha (Λ₁ X : Mat2) (j : Fin 3) : ℝ := margin j (costateA Λ₁ X)

/-- The costate coordinates `β_j = p_j(B̂)`. -/
noncomputable def costateBeta (Λ₁ ΛR X : Mat2) (j : Fin 3) : ℝ := margin j (costateB Λ₁ ΛR X)

/-- Increment of the active coordinate `α_i` along a piece with active margin `a`, growing margin
`b`, decreasing margin `c` and factor `q`: `(√3 a/2)((a + c)(1 - q⁻¹) - (a + b)(q - 1))`; the
active `β_i` moves by `-2` times it, so `σ_i = 2 α_i + β_i` is constant. -/
noncomputable def costateAct (a b c q : ℝ) : ℝ :=
  √3 * a / 2 * ((a + c) * (1 - q⁻¹) - (a + b) * (q - 1))

/-- Inhomogeneous part of `α_i + α_{i+1} ↦ q² (α_i + α_{i+1}) + …`. -/
noncomputable def costateAGrow (a b q : ℝ) : ℝ :=
  √3 * a / 2 * (a * (q ^ 2 - 1) - (a + b) * (q ^ 2 - q))

/-- Inhomogeneous part of `α_i + α_{i-1} ↦ q⁻² (α_i + α_{i-1}) + …`. -/
noncomputable def costateADecr (a c q : ℝ) : ℝ :=
  √3 * a / 2 * ((a + c) * (q⁻¹ - q⁻¹ ^ 2) - a * (1 - q⁻¹ ^ 2))

/-- Inhomogeneous part of `β_i + β_{i+1} ↦ q (β_i + β_{i+1}) + …`. -/
noncomputable def costateBGrow (a b q : ℝ) : ℝ :=
  √3 * a * ((a + b) * q * Real.log q - 2 * a * (q - 1))

/-- Inhomogeneous part of `β_i + β_{i-1} ↦ q⁻¹ (β_i + β_{i-1}) + …`. -/
noncomputable def costateBDecr (a c q : ℝ) : ℝ :=
  √3 * a * q⁻¹ * (2 * a * (q - 1) - (a + c) * Real.log q)

/-- A scalar linear equation `y' = κ y + f` on `[s₀, s₁]`, integrated with a factor `E`,
`E' = -κ E`, and an antiderivative `F` of `E f`. -/
theorem cst_ode {y E f F : ℝ → ℝ} {κ s₀ s₁ : ℝ} (_h01 : s₀ ≤ s₁)
    (hy : ∀ t ∈ Icc s₀ s₁, HasDerivAt y (κ * y t + f t) t)
    (hE : ∀ t ∈ Icc s₀ s₁, HasDerivAt E (-κ * E t) t)
    (hF : ∀ t ∈ Icc s₀ s₁, HasDerivAt F (E t * f t) t) :
    ∀ t ∈ Icc s₀ s₁, E t * y t = E s₀ * y s₀ + F t - F s₀ := by
  have hφ : ∀ t ∈ Icc s₀ s₁, HasDerivAt (fun r ↦ E r * y r - F r) 0 t := by
    intro t ht
    refine (((hE t ht).mul (hy t ht)).sub (hF t ht)).congr_deriv ?_
    ring
  have hc : ContinuousOn (fun r ↦ E r * y r - F r) (Icc s₀ s₁) := fun t ht ↦
    (hφ t ht).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hc
    (fun t ht ↦ (hφ t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
  intro t ht
  have := hconst t ht
  linarith

private lemma cst_hasDerivAt_Q (a s₀ r : ℝ) :
    HasDerivAt (fun r ↦ Real.exp (2 * (r - s₀) / a)) (2 / a * Real.exp (2 * (r - s₀) / a)) r := by
  have hl : HasDerivAt (fun r : ℝ ↦ 2 * (r - s₀) / a) (2 / a) r := by
    simpa using (((hasDerivAt_id r).sub_const s₀).const_mul 2).div_const a
  exact ((Real.hasDerivAt_exp _).comp r hl).congr_deriv (by ring)

private lemma cst_hasDerivAt_Qinv (a s₀ r : ℝ) :
    HasDerivAt (fun r ↦ (Real.exp (2 * (r - s₀) / a))⁻¹)
      (-(2 / a) * (Real.exp (2 * (r - s₀) / a))⁻¹) r := by
  have hQ := cst_hasDerivAt_Q a s₀ r
  have hne : Real.exp (2 * (r - s₀) / a) ≠ 0 := (Real.exp_pos _).ne'
  refine (hQ.fun_inv hne).congr_deriv ?_
  field_simp

/-- **The costate on a vertex piece, explicitly.** On a vertex piece `[s₀, s₁]` (`s₀ < s₁`) of a
normal extremal with control `e_i`, with margins `(a, b, c) = (p_i, p_{i+1}, p_{i-1})` at `s₀` and
`q = exp(2 (t - s₀)/a)` at time `t` of the piece, the coordinates `α_j(t) = p_j(Â(t))`,
`β_j(t) = p_j(B̂(t))` are
* `α_i ↦ α_i + costateAct a b c q`, `β_i ↦ β_i - 2 costateAct a b c q`;
* `α_i + α_{i+1} ↦ q² (α_i + α_{i+1}) + costateAGrow a b q`,
  `α_i + α_{i-1} ↦ q⁻² (α_i + α_{i-1}) + costateADecr a c q`;
* `β_i + β_{i+1} ↦ q (β_i + β_{i+1}) + costateBGrow a b q`,
  `β_i + β_{i-1} ↦ q⁻¹ (β_i + β_{i-1}) + costateBDecr a c q`. -/
theorem vertexPiece_costate {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR (-1)) {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀) (h01 : s₀ < s₁)
    (h1 : s₁ ≤ T) {i : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo s₀ s₁ → u t = vertex i) {a b c : ℝ}
    (ha : margin i (X s₀) = a) (hb : margin (i + 1) (X s₀) = b) (hc : margin (i - 1) (X s₀) = c)
    {t q : ℝ} (ht : t ∈ Icc s₀ s₁) (hq : Real.exp (2 * (t - s₀) / a) = q) :
    let α := costateAlpha (Λ₁ s₀) (X s₀)
    let β := costateBeta (Λ₁ s₀) (ΛR s₀) (X s₀)
    let α' := costateAlpha (Λ₁ t) (X t)
    let β' := costateBeta (Λ₁ t) (ΛR t) (X t)
    α' i = α i + costateAct a b c q ∧
      α' i + α' (i + 1) = q ^ 2 * (α i + α (i + 1)) + costateAGrow a b q ∧
      α' i + α' (i - 1) = q⁻¹ ^ 2 * (α i + α (i - 1)) + costateADecr a c q ∧
      β' i = β i - 2 * costateAct a b c q ∧
      β' i + β' (i + 1) = q * (β i + β (i + 1)) + costateBGrow a b q ∧
      β' i + β' (i - 1) = q⁻¹ * (β i + β (i - 1)) + costateBDecr a c q := by
  intro α β α' β'
  have h3 := cst_s3pos
  obtain ⟨Af, Bf, hAB, hd⟩ := vertexPiece_costate_deriv h h0 h01 h1 hu
  have hmarg := vertexPiece_margin h.1 h0 h01.le h1 hu
  have hs0 : s₀ ∈ Icc s₀ s₁ := ⟨le_rfl, h01.le⟩
  have hapos : 0 < a := ha ▸ margin_pos_of_isStarState (h.1.2.2.2.1 s₀ ⟨h0, h01.le.trans h1⟩).2 i
  have ha0 : a ≠ 0 := hapos.ne'
  subst ha hb hc
  set a := margin i (X s₀) with ha_def
  set b := margin (i + 1) (X s₀) with hb_def
  set c := margin (i - 1) (X s₀) with hc_def
  obtain ⟨Q, hQ_def⟩ : ∃ Q : ℝ → ℝ, Q = fun r ↦ Real.exp (2 * (r - s₀) / a) := ⟨_, rfl⟩
  have hQ : ∀ r, HasDerivAt Q (2 / a * Q r) r := by rw [hQ_def]; exact cst_hasDerivAt_Q a s₀
  have hQi : ∀ r, HasDerivAt (fun r ↦ (Q r)⁻¹) (-(2 / a) * (Q r)⁻¹) r := by
    rw [hQ_def]; exact cst_hasDerivAt_Qinv a s₀
  have hQ0 : Q s₀ = 1 := by simp [hQ_def]
  have hQpos : ∀ r, 0 < Q r := fun r ↦ by rw [hQ_def]; exact Real.exp_pos _
  have hQt : Q t = q := by rw [hQ_def]; exact hq
  have hlog : Real.log q = 2 * (t - s₀) / a := by rw [← hq, Real.log_exp]
  -- the derivatives of the six combinations
  have hm : ∀ s ∈ Icc s₀ s₁, margin i (X s) = a ∧ margin (i + 1) (X s) = (a + b) * Q s - a ∧
      margin (i - 1) (X s) = (a + c) / Q s - a := by rw [hQ_def]; exact hmarg
  clear hQ_def
  have e11 : i + 1 - 1 = i := add_sub_cancel_right i 1
  have e22 : i - 1 + 1 = i := sub_add_cancel i 1
  have hA : ∀ s ∈ Icc s₀ s₁, ∀ j, margin j (Af s) = costateAlpha (Λ₁ s) (X s) j := fun s hs j ↦ by
    rw [(hAB s hs).1]; rfl
  have hB : ∀ s ∈ Icc s₀ s₁, ∀ j, margin j (Bf s) = costateBeta (Λ₁ s) (ΛR s) (X s) j :=
    fun s hs j ↦ by rw [(hAB s hs).2]; rfl
  -- (1) `α_i`
  have r1 := cst_ode (y := fun r ↦ margin i (Af r)) (E := fun _ ↦ 1) (κ := 0)
    (f := fun r ↦ -(√3 * ((a + b) * Q r - (a + c) / Q r)))
    (F := fun r ↦ -(√3 * ((a + b) * (a / 2) * Q r + (a + c) * (a / 2) * (Q r)⁻¹))) h01.le
    (fun s hs ↦ by
      refine (hd s hs i).1.congr_deriv ?_
      obtain ⟨b0, -, -⟩ := cst_margin_bracket_P i ha0 (costateA (Λ₁ s) (X s))
      rw [b0, (hm s hs).2.1, (hm s hs).2.2]
      ring)
    (fun s _ ↦ (hasDerivAt_const s (1 : ℝ)).congr_deriv (by ring))
    (fun s _ ↦ by
      refine ((((hQ s).const_mul ((a + b) * (a / 2))).add
        ((hQi s).const_mul ((a + c) * (a / 2)))).const_mul √3).neg.congr_deriv ?_
      have hQs := (hQpos s).ne'
      field_simp [hQs]; ring) t ht
  -- (2) `α_i + α_{i+1}`
  have r2 := cst_ode (y := fun r ↦ margin i (Af r) + margin (i + 1) (Af r))
    (E := fun r ↦ (Q r)⁻¹ ^ 2) (κ := 4 / a)
    (f := fun r ↦ -(√3 * ((a + b) * Q r - 2 * a)))
    (F := fun r ↦ √3 * ((a + b) * (a / 2) * (Q r)⁻¹ - a ^ 2 / 2 * (Q r)⁻¹ ^ 2)) h01.le
    (fun s hs ↦ by
      refine ((hd s hs i).1.add (hd s hs (i + 1)).1).congr_deriv ?_
      obtain ⟨b0, b1, -⟩ := cst_margin_bracket_P i ha0 (costateA (Λ₁ s) (X s))
      rw [b0, b1, cst_fin_add_one_add_one, e11, (hm s hs).1, (hm s hs).2.1, (hm s hs).2.2,
        (hAB s hs).1]
      have hQs := (hQpos s).ne'
      field_simp [hQs]; ring)
    (fun s _ ↦ ((hQi s).pow 2).congr_deriv (by
      have hQs := (hQpos s).ne'
      try simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      field_simp [hQs]; ring))
    (fun s _ ↦ by
      refine (((hQi s).const_mul ((a + b) * (a / 2))).sub
        (((hQi s).pow 2).const_mul (a ^ 2 / 2))).const_mul √3 |>.congr_deriv ?_
      have hQs := (hQpos s).ne'
      try simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      field_simp [hQs]; ring) t ht
  -- (3) `α_i + α_{i-1}`
  have r3 := cst_ode (y := fun r ↦ margin i (Af r) + margin (i - 1) (Af r))
    (E := fun r ↦ Q r ^ 2) (κ := -(4 / a))
    (f := fun r ↦ -(√3 * (2 * a - (a + c) / Q r)))
    (F := fun r ↦ -(√3 * (a ^ 2 / 2 * Q r ^ 2 - (a + c) * (a / 2) * Q r))) h01.le
    (fun s hs ↦ by
      refine ((hd s hs i).1.add (hd s hs (i - 1)).1).congr_deriv ?_
      obtain ⟨b0, -, b2⟩ := cst_margin_bracket_P i ha0 (costateA (Λ₁ s) (X s))
      rw [b0, b2, cst_fin_sub_one_sub_one, e22, (hm s hs).1, (hm s hs).2.1, (hm s hs).2.2,
        (hAB s hs).1]
      have hQs := (hQpos s).ne'
      field_simp [hQs]; ring)
    (fun s _ ↦ ((hQ s).pow 2).congr_deriv (by
      have hQs := (hQpos s).ne'
      try simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      field_simp [hQs]; ring))
    (fun s _ ↦ by
      refine ((((hQ s).pow 2).const_mul (a ^ 2 / 2)).sub
        ((hQ s).const_mul ((a + c) * (a / 2)))).const_mul √3 |>.neg.congr_deriv ?_
      have hQs := (hQpos s).ne'
      try simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      field_simp [hQs]; ring) t ht
  -- (4) `β_i`
  have r4 := cst_ode (y := fun r ↦ margin i (Bf r)) (E := fun _ ↦ 1) (κ := 0)
    (f := fun r ↦ 2 * (√3 * ((a + b) * Q r - (a + c) / Q r)))
    (F := fun r ↦ 2 * (√3 * ((a + b) * (a / 2) * Q r + (a + c) * (a / 2) * (Q r)⁻¹))) h01.le
    (fun s hs ↦ by
      refine (hd s hs i).2.congr_deriv ?_
      obtain ⟨b0, -, -⟩ := cst_margin_bracket_P i ha0 (costateB (Λ₁ s) (ΛR s) (X s))
      rw [b0, (hm s hs).2.1, (hm s hs).2.2]
      ring)
    (fun s _ ↦ (hasDerivAt_const s (1 : ℝ)).congr_deriv (by ring))
    (fun s _ ↦ by
      refine ((((hQ s).const_mul ((a + b) * (a / 2))).add
        ((hQi s).const_mul ((a + c) * (a / 2)))).const_mul √3).const_mul 2 |>.congr_deriv ?_
      have hQs := (hQpos s).ne'
      field_simp [hQs]; ring) t ht
  -- (5) `β_i + β_{i+1}`
  have r5 := cst_ode (y := fun r ↦ margin i (Bf r) + margin (i + 1) (Bf r))
    (E := fun r ↦ (Q r)⁻¹) (κ := 2 / a)
    (f := fun r ↦ 2 * (√3 * ((a + b) * Q r - 2 * a)))
    (F := fun r ↦ 2 * (√3 * ((a + b) * r + a ^ 2 * (Q r)⁻¹))) h01.le
    (fun s hs ↦ by
      refine ((hd s hs i).2.add (hd s hs (i + 1)).2).congr_deriv ?_
      obtain ⟨b0, b1, -⟩ := cst_margin_bracket_P i ha0 (costateB (Λ₁ s) (ΛR s) (X s))
      rw [b0, b1, cst_fin_add_one_add_one, e11, (hm s hs).1, (hm s hs).2.1, (hm s hs).2.2,
        (hAB s hs).2]
      have hQs := (hQpos s).ne'
      field_simp [hQs]; ring)
    (fun s _ ↦ (hQi s).congr_deriv (by ring))
    (fun s _ ↦ by
      refine ((((hasDerivAt_id s).const_mul (a + b)).add
        ((hQi s).const_mul (a ^ 2))).const_mul √3).const_mul 2 |>.congr_deriv ?_
      have hQs := (hQpos s).ne'
      field_simp [hQs]; ring) t ht
  -- (6) `β_i + β_{i-1}`
  have r6 := cst_ode (y := fun r ↦ margin i (Bf r) + margin (i - 1) (Bf r))
    (E := fun r ↦ Q r) (κ := -(2 / a))
    (f := fun r ↦ 2 * (√3 * (2 * a - (a + c) / Q r)))
    (F := fun r ↦ 2 * (√3 * (a ^ 2 * Q r - (a + c) * r))) h01.le
    (fun s hs ↦ by
      refine ((hd s hs i).2.add (hd s hs (i - 1)).2).congr_deriv ?_
      obtain ⟨b0, -, b2⟩ := cst_margin_bracket_P i ha0 (costateB (Λ₁ s) (ΛR s) (X s))
      rw [b0, b2, cst_fin_sub_one_sub_one, e22, (hm s hs).1, (hm s hs).2.1, (hm s hs).2.2,
        (hAB s hs).2]
      have hQs := (hQpos s).ne'
      field_simp [hQs]; ring)
    (fun s _ ↦ (hQ s).congr_deriv (by ring))
    (fun s _ ↦ by
      refine ((((hQ s).const_mul (a ^ 2)).sub
        ((hasDerivAt_id s).const_mul (a + c))).const_mul √3).const_mul 2 |>.congr_deriv ?_
      have hQs := (hQpos s).ne'
      field_simp [hQs]) t ht
  simp only [hQ0, hA t ht, hA s₀ hs0, hB t ht, hB s₀ hs0, hQt, one_pow, inv_one, one_mul]
    at r1 r2 r3 r4 r5 r6
  have hq0 : 0 < q := hQt ▸ hQpos t
  have hts : t - s₀ = a / 2 * Real.log q := by rw [hlog]; field_simp
  have hqne : q ≠ 0 := hq0.ne'
  simp only [α, β, α', β']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [costateAct]; linear_combination r1
  · simp only [costateAGrow]
    field_simp
    field_simp at r2
    linear_combination r2
  · rw [show costateAlpha (Λ₁ t) (X t) i + costateAlpha (Λ₁ t) (X t) (i - 1) =
      q ^ 2 * (costateAlpha (Λ₁ t) (X t) i + costateAlpha (Λ₁ t) (X t) (i - 1)) / q ^ 2 by
        field_simp, r3]
    simp only [costateADecr]
    field_simp
    ring
  · simp only [costateAct]; linear_combination r4
  · rw [show costateBeta (Λ₁ t) (ΛR t) (X t) i + costateBeta (Λ₁ t) (ΛR t) (X t) (i + 1) =
      q * (q⁻¹ * (costateBeta (Λ₁ t) (ΛR t) (X t) i + costateBeta (Λ₁ t) (ΛR t) (X t) (i + 1))) by
        field_simp, r5, show t = s₀ + a / 2 * Real.log q by linarith]
    simp only [costateBGrow]
    field_simp
    ring
  · rw [show costateBeta (Λ₁ t) (ΛR t) (X t) i + costateBeta (Λ₁ t) (ΛR t) (X t) (i - 1) =
      q⁻¹ * (q * (costateBeta (Λ₁ t) (ΛR t) (X t) i + costateBeta (Λ₁ t) (ΛR t) (X t) (i - 1))) by
        field_simp, r6, show t = s₀ + a / 2 * Real.log q by linarith]
    simp only [costateBDecr]
    field_simp
    ring

/-! ### Closed vertex cycles with a normal costate -/

/-- **A closed vertex cycle with its normal costate**: the data of `Term.Cycle` (labels, factors,
switch margins `m k`, tangent closure) together with the costate coordinates `α k j`, `β k j` at the
switching times, indexed by `ℤ` through the twist, transported along each piece by the one-arc
costate map, with the switching conditions of the maximum principle: `σ_j = 2 α_j + β_j` (which is
`p_j H_j`) vanishes for the active label of each piece, at both of its ends, and is `≤ 0` for every
label at every switch and, along the piece, for the two inactive labels. -/
structure CostateCycle (N : ℕ) extends Term.Cycle N where
  /-- `α k j = p_j(X L X)` at the switch `k`. -/
  α : ℤ → Fin 3 → ℝ
  /-- `β k j = p_j(B̂)` at the switch `k`. -/
  β : ℤ → Fin 3 → ℝ
  α_add : ∀ k j, α (k + N) j = α k (j - 1)
  β_add : ∀ k j, β (k + N) j = β k (j - 1)
  α_act : ∀ k, α (k + 1) (lab k) =
    α k (lab k) + costateAct (m k (lab k)) (m k (lab k + 1)) (m k (lab k - 1)) (q k)
  α_grow : ∀ k, α (k + 1) (lab k) + α (k + 1) (lab k + 1) =
    q k ^ 2 * (α k (lab k) + α k (lab k + 1)) + costateAGrow (m k (lab k)) (m k (lab k + 1)) (q k)
  α_decr : ∀ k, α (k + 1) (lab k) + α (k + 1) (lab k - 1) =
    (q k)⁻¹ ^ 2 * (α k (lab k) + α k (lab k - 1)) +
      costateADecr (m k (lab k)) (m k (lab k - 1)) (q k)
  β_act : ∀ k, β (k + 1) (lab k) =
    β k (lab k) - 2 * costateAct (m k (lab k)) (m k (lab k + 1)) (m k (lab k - 1)) (q k)
  β_grow : ∀ k, β (k + 1) (lab k) + β (k + 1) (lab k + 1) =
    q k * (β k (lab k) + β k (lab k + 1)) + costateBGrow (m k (lab k)) (m k (lab k + 1)) (q k)
  β_decr : ∀ k, β (k + 1) (lab k) + β (k + 1) (lab k - 1) =
    (q k)⁻¹ * (β k (lab k) + β k (lab k - 1)) + costateBDecr (m k (lab k)) (m k (lab k - 1)) (q k)
  /-- The active Hamiltonian vanishes: `σ_{i_k} = 0` at the start of piece `k`. -/
  sig_act : ∀ k, 2 * α k (lab k) + β k (lab k) = 0
  /-- The maximum condition at the switches: `σ_j ≤ 0`. -/
  sig_le : ∀ k j, 2 * α k j + β k j ≤ 0
  /-- `⟨Λ_R, X⟩ = 0`: `∑_{j ≠ l} β_j m_l = 0`. -/
  perp : ∀ k, β k 0 * (m k 1 + m k 2) + β k 1 * (m k 0 + m k 2) + β k 2 * (m k 0 + m k 1) = 0
  /-- The maximum condition along piece `k`, for the growing label `i_k + 1`, at the intermediate
  factor `s ∈ [1, q_k]`. -/
  sig_grow_le : ∀ k, ∀ s ∈ Icc 1 (q k),
    2 * (s ^ 2 * (α k (lab k) + α k (lab k + 1)) + costateAGrow (m k (lab k)) (m k (lab k + 1)) s) +
      (s * (β k (lab k) + β k (lab k + 1)) + costateBGrow (m k (lab k)) (m k (lab k + 1)) s) ≤ 0
  /-- The maximum condition along piece `k`, for the decreasing label `i_k - 1`. -/
  sig_decr_le : ∀ k, ∀ s ∈ Icc 1 (q k),
    2 * (s⁻¹ ^ 2 * (α k (lab k) + α k (lab k - 1)) +
        costateADecr (m k (lab k)) (m k (lab k - 1)) s) +
      (s⁻¹ * (β k (lab k) + β k (lab k - 1)) + costateBDecr (m k (lab k)) (m k (lab k - 1)) s) ≤ 0

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

/-- `σ_j = 2 α_j + β_j` at the switch `k` (`p_j H_j`). -/
def sig (k : ℤ) (j : Fin 3) : ℝ := 2 * C.α k j + C.β k j

/-- The active Hamiltonian also vanishes at the end of each piece: `σ_{i_k} = 0` at switch
`k + 1`. -/
theorem sig_act_succ (k : ℤ) : C.sig (k + 1) (C.lab k) = 0 := by
  have h := C.sig_act k
  simp only [sig, C.α_act, C.β_act]
  linarith

theorem sig_act' (k : ℤ) : C.sig k (C.lab k) = 0 := C.sig_act k

theorem sig_le' (k : ℤ) (j : Fin 3) : C.sig k j ≤ 0 := C.sig_le k j

/-- The active margin `a_k = m_k(i_k)` of piece `k`. -/
def act (k : ℤ) : ℝ := C.m k (C.lab k)

theorem act_add (k : ℤ) : C.act (k + N) = C.act k := by
  simp only [act, C.lab_add, C.m_add, add_sub_cancel_right]

theorem act_pos (k : ℤ) : 0 < C.act k := C.m_pos k _

theorem act_emod (k : ℤ) : C.act (k % N) = C.act k := by
  have hper : Function.Periodic C.act (N : ℤ) := C.act_add
  have e : k % N = k - (k / N : ℤ) * N := by rw [Int.emod_def]; ring
  rw [e]
  exact hper.sub_int_mul_eq (k / N)

/-- A piece whose active margin is a global minimum of the (periodic) active margins. -/
theorem exists_act_min (hN : 0 < N) : ∃ m : ℤ, ∀ k, C.act m ≤ C.act k := by
  obtain ⟨m, -, hm⟩ := (Finset.range N).exists_min_image (fun j : ℕ ↦ C.act j)
    ⟨0, Finset.mem_range.2 hN⟩
  refine ⟨m, fun k ↦ ?_⟩
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  have h0 := Int.emod_nonneg k hN'.ne'
  have h1 := Int.emod_lt_of_pos k hN'
  have := hm (k % N).toNat (Finset.mem_range.2 (by omega))
  rw [Int.toNat_of_nonneg h0, C.act_emod k] at this
  exact this

/-- **The transport along piece `k`, for a given label `i = i_k`**: margins, `α` and `β`. -/
theorem transport (k : ℤ) {i : Fin 3} (hi : C.lab k = i) :
    C.m (k + 1) i = C.m k i ∧
      C.m (k + 1) (i + 1) = (C.m k i + C.m k (i + 1)) * C.q k - C.m k i ∧
      C.m (k + 1) (i - 1) = (C.m k i + C.m k (i - 1)) / C.q k - C.m k i ∧
      C.α (k + 1) i = C.α k i + costateAct (C.m k i) (C.m k (i + 1)) (C.m k (i - 1)) (C.q k) ∧
      C.α (k + 1) i + C.α (k + 1) (i + 1) =
        C.q k ^ 2 * (C.α k i + C.α k (i + 1)) + costateAGrow (C.m k i) (C.m k (i + 1)) (C.q k) ∧
      C.α (k + 1) i + C.α (k + 1) (i - 1) =
        (C.q k)⁻¹ ^ 2 * (C.α k i + C.α k (i - 1)) + costateADecr (C.m k i) (C.m k (i - 1)) (C.q k) ∧
      C.β (k + 1) i = C.β k i - 2 * costateAct (C.m k i) (C.m k (i + 1)) (C.m k (i - 1)) (C.q k) ∧
      C.β (k + 1) i + C.β (k + 1) (i + 1) =
        C.q k * (C.β k i + C.β k (i + 1)) + costateBGrow (C.m k i) (C.m k (i + 1)) (C.q k) ∧
      C.β (k + 1) i + C.β (k + 1) (i - 1) =
        (C.q k)⁻¹ * (C.β k i + C.β k (i - 1)) + costateBDecr (C.m k i) (C.m k (i - 1)) (C.q k) := by
  subst hi
  exact ⟨C.m_act k, C.m_grow k, C.m_decr k, C.α_act k, C.α_grow k, C.α_decr k, C.β_act k,
    C.β_grow k, C.β_decr k⟩

/-- `⟨Λ_R, X⟩ = 0` in the label order `i, i + 1, i - 1`. -/
theorem perp_rot (k : ℤ) (i : Fin 3) :
    C.β k i * (C.m k (i + 1) + C.m k (i - 1)) + C.β k (i + 1) * (C.m k i + C.m k (i - 1)) +
      C.β k (i - 1) * (C.m k i + C.m k (i + 1)) = 0 := by
  have h := C.perp k
  fin_cases i
  · simp only [Fin.zero_eta, zero_add, show (0 : Fin 3) - 1 = 2 from rfl]
    linear_combination h
  · simp only [Fin.mk_one, show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) - 1 = 0 from rfl]
    linear_combination h
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      show (2 : Fin 3) - 1 = 1 from rfl]
    linear_combination h

end CostateCycle

/-! ### The costate cycle of a normal period -/

namespace NormalPeriod

variable (P : NormalPeriod)

private lemma cst_emod_eq (k N : ℤ) : k % N = k - ((k / N : ℤ) : ℤ) * N := by
  rw [Int.emod_def]; ring

private lemma cst_label_incr (k : ℤ) :
    P.rep.label (k + 1) - P.rep.label k =
      P.rep.label (k % P.N + 1) - P.rep.label (k % P.N) := by
  have hper : Function.Periodic (fun k : ℤ ↦ P.rep.label (k + 1) - P.rep.label k) (P.N : ℤ) := by
    intro k
    simp only [show k + P.N + 1 = k + 1 + P.N by ring, P.rep.label_add_period]
    abel
  have := hper.sub_int_mul_eq (x := k) (k / P.N)
  rw [cst_emod_eq]
  exact this.symm

/-- The relabeling `i_k - i_{k mod N}` of the twisted extension at the switch `k`. -/
noncomputable def cutShift (k : ℤ) : Fin 3 := P.rep.label k - P.rep.label (k % P.N)

theorem cutShift_add_N (k : ℤ) : P.cutShift (k + P.N) = P.cutShift k + 1 := by
  simp only [cutShift, Int.add_emod_right, P.rep.label_add_period]
  abel

/-- A labeled quantity `v t j` at the switching times, relabeled through the twist: if
`v(τ_N) j = v(0) (j - 1)`, then
`v(τ_{(k+1) mod N}) (j - shift (k + 1)) = v(τ_{k mod N + 1}) (j - shift k)`. -/
theorem cutShift_succ (v : ℝ → Fin 3 → ℝ) (hv : ∀ j, v (P.rep.τ P.N) j = v 0 (j - 1)) (k : ℤ)
    (j : Fin 3) :
    v (P.rep.τ ((k + 1) % P.N)) (j - P.cutShift (k + 1)) =
      v (P.rep.τ (k % P.N + 1)) (j - P.cutShift k) := by
  have h0 := term_emod_nonneg P k
  have h1 := term_emod_lt P k
  have hincr := cst_label_incr P k
  have hmod1 : (k + 1) % P.N = (k % P.N + 1) % P.N := (Int.emod_add_emod k P.N 1).symm
  rcases lt_or_eq_of_le (show k % P.N + 1 ≤ P.N by omega) with hlt | heq
  · have hmod : (k + 1) % P.N = k % P.N + 1 := by
      rw [hmod1, Int.emod_eq_of_lt (by omega) hlt]
    rw [cutShift, cutShift, hmod]
    congr 1
    rw [sub_eq_iff_eq_add] at hincr
    rw [hincr]
    abel
  · have hmod : (k + 1) % P.N = 0 := by
      rw [hmod1, heq, Int.emod_self]
    rw [cutShift, cutShift, hmod, heq, hv, P.rep.τ_zero]
    have hN : P.rep.label P.N = P.rep.label 0 + 1 := by
      simpa using P.rep.label_add_period 0
    rw [heq, hN, sub_eq_iff_eq_add] at hincr
    congr 1
    rw [hincr]
    abel

theorem termMargin_eq_cut (k : ℤ) (j : Fin 3) :
    P.termMargin k j = margin (j - P.cutShift k) (P.X (P.rep.τ (k % P.N))) := rfl

/-- The costate coordinate `α` at the switch `k` of the twisted extension. -/
noncomputable def cutAlpha (k : ℤ) (j : Fin 3) : ℝ :=
  costateAlpha (P.Λ₁ (P.rep.τ (k % P.N))) (P.X (P.rep.τ (k % P.N))) (j - P.cutShift k)

/-- The costate coordinate `β` at the switch `k` of the twisted extension. -/
noncomputable def cutBeta (k : ℤ) (j : Fin 3) : ℝ :=
  costateBeta (P.Λ₁ (P.rep.τ (k % P.N))) (P.ΛR (P.rep.τ (k % P.N))) (P.X (P.rep.τ (k % P.N)))
    (j - P.cutShift k)

theorem Λ₁_T : P.Λ₁ P.T = R⁻¹ * P.Λ₁ 0 * R := P.extremal.2.2.2.2.1

/-- **`Λ₁` is conserved in the spatial frame** (Corollary 6.5.3): `Λ₁(t) = g(t)⁻¹ Λ₁(0) g(t)` on
`[0, T]`, so `g Λ₁ g⁻¹` is constant and `det Λ₁` is constant. -/
theorem Λ₁_eq_conj {t : ℝ} (ht : t ∈ Icc 0 P.T) :
    P.Λ₁ t = (P.g t)⁻¹ * P.Λ₁ 0 * P.g t ∧ (P.Λ₁ t).det = (P.Λ₁ 0).det := by
  obtain ⟨⟨-, -, -, hst, hgI, hXI⟩, hg0, -, -, -, -, -, -, hΛ, -, -⟩ := P.extremal
  have hXc : ContinuousOn P.X (Icc 0 P.T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hgc : ContinuousOn P.g (Icc 0 P.T) := Matrix.continuousOn_of_eq_add_integral hgI
  have hΛc : ContinuousOn P.Λ₁ (Icc 0 P.T) := Matrix.continuousOn_of_eq_add_integral hΛ
  have hg : ∀ t ∈ Icc 0 P.T, Matrix.HasDerivWithinAtEntrywise P.g (P.g t * P.X t) (Icc 0 P.T) t :=
    fun t ht ↦ Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hgI ht ((hgc.mul hXc) t ht)
  have hΛ' : ∀ t ∈ Icc 0 P.T, Matrix.HasDerivWithinAtEntrywise P.Λ₁
      (P.Λ₁ t * P.X t - P.X t * P.Λ₁ t) (Icc 0 P.T) t :=
    fun t ht ↦ Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hΛ ht
      (((hΛc.mul hXc).sub (hXc.mul hΛc)) t ht)
  exact corollary6_5_3 P.T P.g P.X P.Λ₁ hg hg0 (fun t ht ↦ (hst t ht).1) hΛ' t ht

theorem ΛR_T : P.ΛR P.T = R⁻¹ * P.ΛR 0 * R := P.extremal.2.2.2.2.2.1

theorem costateAlpha_τ_N (j : Fin 3) :
    costateAlpha (P.Λ₁ (P.rep.τ P.N)) (P.X (P.rep.τ P.N)) j =
      costateAlpha (P.Λ₁ 0) (P.X 0) (j - 1) := by
  rw [P.rep.τ_N, P.Λ₁_T, P.X_T, costateAlpha, costateA_conj, margin_Rinv_conj]; rfl

theorem costateBeta_τ_N (j : Fin 3) :
    costateBeta (P.Λ₁ (P.rep.τ P.N)) (P.ΛR (P.rep.τ P.N)) (P.X (P.rep.τ P.N)) j =
      costateBeta (P.Λ₁ 0) (P.ΛR 0) (P.X 0) (j - 1) := by
  rw [P.rep.τ_N, P.Λ₁_T, P.ΛR_T, P.X_T, costateBeta, costateB_conj, margin_Rinv_conj]; rfl

theorem cutAlpha_succ (k : ℤ) (j : Fin 3) :
    P.cutAlpha (k + 1) j = costateAlpha (P.Λ₁ (P.rep.τ (k % P.N + 1)))
      (P.X (P.rep.τ (k % P.N + 1))) (j - P.cutShift k) :=
  P.cutShift_succ (fun t j ↦ costateAlpha (P.Λ₁ t) (P.X t) j) (fun j ↦ P.costateAlpha_τ_N j) k j

theorem cutBeta_succ (k : ℤ) (j : Fin 3) :
    P.cutBeta (k + 1) j = costateBeta (P.Λ₁ (P.rep.τ (k % P.N + 1))) (P.ΛR (P.rep.τ (k % P.N + 1)))
      (P.X (P.rep.τ (k % P.N + 1))) (j - P.cutShift k) :=
  P.cutShift_succ (fun t j ↦ costateBeta (P.Λ₁ t) (P.ΛR t) (P.X t) j)
    (fun j ↦ P.costateBeta_τ_N j) k j

theorem termMargin_succ (k : ℤ) (j : Fin 3) :
    P.termMargin (k + 1) j = margin (j - P.cutShift k) (P.X (P.rep.τ (k % P.N + 1))) :=
  P.cutShift_succ (fun t j ↦ margin j (P.X t)) (fun j ↦ P.margin_τ_N j) k j

theorem cutShift_label (k : ℤ) (j : Fin 3) :
    P.rep.label k + j - P.cutShift k = P.rep.label (k % P.N) + j := by
  rw [cutShift]; abel

theorem cutShift_label' (k : ℤ) : P.rep.label k - P.cutShift k = P.rep.label (k % P.N) := by
  rw [cutShift]; abel

theorem cutShift_label_sub (k : ℤ) :
    P.rep.label k - 1 - P.cutShift k = P.rep.label (k % P.N) - 1 := by
  rw [cutShift]; abel

/-- `σ_j = 2 α_j + β_j ≤ 0` at every time of the period, and `= p_j H_j`. -/
theorem sig_le_of_mem {t : ℝ} (ht : t ∈ Icc 0 P.T) (j : Fin 3) :
    2 * costateAlpha (P.Λ₁ t) (P.X t) j + costateBeta (P.Λ₁ t) (P.ΛR t) (P.X t) j ≤ 0 := by
  have hst := P.isStarState ht
  have htr := (P.extremal.2.2.2.2.2.2.2.1 t ht).1
  have hH := ((IsPontryaginExtremal.vertexHamiltonian_max_eq_zero P.extremal) t ht).1 j
  have hm := margin_mul_hamiltonian (ΛR := P.ΛR t) hst htr j
  have hp := margin_pos_of_isStarState hst j
  simp only [costateAlpha, costateBeta]
  rw [← hm]
  exact mul_nonpos_of_nonneg_of_nonpos hp.le hH

/-- On piece `r`, `σ_{i_r} = 0` at every time. -/
theorem sig_act_of_mem {r : ℤ} (hr0 : 0 ≤ r) (hrN : r < P.N) {t : ℝ}
    (ht : t ∈ Icc (P.rep.τ r) (P.rep.τ (r + 1))) :
    2 * costateAlpha (P.Λ₁ t) (P.X t) (P.rep.label r) +
      costateBeta (P.Λ₁ t) (P.ΛR t) (P.X t) (P.rep.label r) = 0 := by
  obtain ⟨h0, -, h1⟩ := P.rep.piece_subset hr0 hrN
  have htT : t ∈ Icc 0 P.T := ⟨h0.trans ht.1, ht.2.trans h1⟩
  have hst := P.isStarState htT
  have htr := (P.extremal.2.2.2.2.2.2.2.1 t htT).1
  have hH := vertexPiece_hamiltonian_eq_zero P.extremal h0 (P.rep.τ_lt_succ r) h1
    (P.ae_eq_vertex hr0 hrN) t ht
  have hm := margin_mul_hamiltonian (ΛR := P.ΛR t) hst htr (P.rep.label r)
  simp only [costateAlpha, costateBeta]
  rw [← hm, hH, mul_zero]

private lemma cst_perp_shift (f g : Fin 3 → ℝ) (s : Fin 3) :
    f (0 - s) * (g (1 - s) + g (2 - s)) + f (1 - s) * (g (0 - s) + g (2 - s)) +
        f (2 - s) * (g (0 - s) + g (1 - s)) =
      f 0 * (g 1 + g 2) + f 1 * (g 0 + g 2) + f 2 * (g 0 + g 1) := by
  fin_cases s
  · simp
  · simp only [Fin.mk_one, show (0 : Fin 3) - 1 = 2 from rfl, show (1 : Fin 3) - 1 = 0 from rfl,
      show (2 : Fin 3) - 1 = 1 from rfl]
    ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (0 : Fin 3) - 2 = 1 from rfl,
      show (1 : Fin 3) - 2 = 2 from rfl, show (2 : Fin 3) - 2 = 0 from rfl]
    ring

/-- **Transport of the costate cut data along piece `k`** (any `k : ℤ`, through the twist). -/
theorem cut_transport (k : ℤ) :
    P.cutAlpha (k + 1) (P.rep.label k) = P.cutAlpha k (P.rep.label k) +
        costateAct (P.termMargin k (P.rep.label k)) (P.termMargin k (P.rep.label k + 1))
          (P.termMargin k (P.rep.label k - 1)) (P.factor k) ∧
      P.cutAlpha (k + 1) (P.rep.label k) + P.cutAlpha (k + 1) (P.rep.label k + 1) =
        P.factor k ^ 2 * (P.cutAlpha k (P.rep.label k) + P.cutAlpha k (P.rep.label k + 1)) +
          costateAGrow (P.termMargin k (P.rep.label k)) (P.termMargin k (P.rep.label k + 1))
            (P.factor k) ∧
      P.cutAlpha (k + 1) (P.rep.label k) + P.cutAlpha (k + 1) (P.rep.label k - 1) =
        (P.factor k)⁻¹ ^ 2 * (P.cutAlpha k (P.rep.label k) + P.cutAlpha k (P.rep.label k - 1)) +
          costateADecr (P.termMargin k (P.rep.label k)) (P.termMargin k (P.rep.label k - 1))
            (P.factor k) ∧
      P.cutBeta (k + 1) (P.rep.label k) = P.cutBeta k (P.rep.label k) -
        2 * costateAct (P.termMargin k (P.rep.label k)) (P.termMargin k (P.rep.label k + 1))
          (P.termMargin k (P.rep.label k - 1)) (P.factor k) ∧
      P.cutBeta (k + 1) (P.rep.label k) + P.cutBeta (k + 1) (P.rep.label k + 1) =
        P.factor k * (P.cutBeta k (P.rep.label k) + P.cutBeta k (P.rep.label k + 1)) +
          costateBGrow (P.termMargin k (P.rep.label k)) (P.termMargin k (P.rep.label k + 1))
            (P.factor k) ∧
      P.cutBeta (k + 1) (P.rep.label k) + P.cutBeta (k + 1) (P.rep.label k - 1) =
        (P.factor k)⁻¹ * (P.cutBeta k (P.rep.label k) + P.cutBeta k (P.rep.label k - 1)) +
          costateBDecr (P.termMargin k (P.rep.label k)) (P.termMargin k (P.rep.label k - 1))
            (P.factor k) := by
  have hr0 := term_emod_nonneg P k
  have hrN := term_emod_lt P k
  have hlt := P.rep.τ_lt_succ (k % P.N)
  obtain ⟨h0, -, h1⟩ := P.rep.piece_subset hr0 hrN
  have key := vertexPiece_costate P.extremal h0 hlt h1 (P.ae_eq_vertex hr0 hrN)
    (P.activeMargin_eq hr0 hrN).symm rfl rfl (t := P.rep.τ (k % P.N + 1)) (q := P.factor (k % P.N))
    ⟨hlt.le, le_rfl⟩ rfl
  dsimp only at key
  rw [← term_factor_emod P k]
  simp only [cutAlpha_succ, cutBeta_succ]
  simp only [cutAlpha, cutBeta, termMargin_eq_cut, cutShift_label', cutShift_label,
    cutShift_label_sub]
  rw [← P.activeMargin_eq hr0 hrN]
  exact key

/-- The growing inactive Hamiltonian along piece `k`, at the intermediate factor `s`. -/
theorem cut_sig_grow_le (k : ℤ) {s : ℝ} (hs : s ∈ Icc 1 (P.factor k)) :
    2 * (s ^ 2 * (P.cutAlpha k (P.rep.label k) + P.cutAlpha k (P.rep.label k + 1)) +
        costateAGrow (P.termMargin k (P.rep.label k)) (P.termMargin k (P.rep.label k + 1)) s) +
      (s * (P.cutBeta k (P.rep.label k) + P.cutBeta k (P.rep.label k + 1)) +
        costateBGrow (P.termMargin k (P.rep.label k)) (P.termMargin k (P.rep.label k + 1)) s) ≤
      0 := by
  have hr0 := term_emod_nonneg P k
  have hrN := term_emod_lt P k
  set r := k % P.N with hr
  have hlt := P.rep.τ_lt_succ r
  obtain ⟨h0, -, h1⟩ := P.rep.piece_subset hr0 hrN
  have ha := P.activeMargin_pos r
  rw [← term_factor_emod] at hs
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs.1
  set t := P.rep.τ r + P.activeMargin r / 2 * Real.log s with ht_def
  have hlogq := P.log_factor r
  have hlog0 : 0 ≤ Real.log s := Real.log_nonneg hs.1
  have hlog1 : Real.log s ≤ Real.log (P.factor r) := Real.log_le_log hs0 hs.2
  have ht : t ∈ Icc (P.rep.τ r) (P.rep.τ (r + 1)) := by
    constructor
    · rw [ht_def]; have := mul_nonneg (div_nonneg ha.le zero_le_two) hlog0; linarith
    · rw [ht_def, hlogq] at *
      have : P.activeMargin r / 2 * Real.log s ≤ P.activeMargin r / 2 *
          (2 * (P.rep.τ (r + 1) - P.rep.τ r) / P.activeMargin r) :=
        mul_le_mul_of_nonneg_left hlog1 (div_nonneg ha.le zero_le_two)
      rw [show P.activeMargin r / 2 * (2 * (P.rep.τ (r + 1) - P.rep.τ r) / P.activeMargin r) =
        P.rep.τ (r + 1) - P.rep.τ r by field_simp] at this
      linarith
  have hq : Real.exp (2 * (t - P.rep.τ r) / P.activeMargin r) = s := by
    rw [ht_def, show 2 * (P.rep.τ r + P.activeMargin r / 2 * Real.log s - P.rep.τ r) /
      P.activeMargin r = Real.log s by field_simp; ring, Real.exp_log hs0]
  have key := vertexPiece_costate P.extremal h0 hlt h1 (P.ae_eq_vertex hr0 hrN)
    (P.activeMargin_eq hr0 hrN).symm rfl rfl ht hq
  dsimp only at key
  obtain ⟨-, k2, -, -, k5, -⟩ := key
  have hT : t ∈ Icc 0 P.T := ⟨h0.trans ht.1, ht.2.trans h1⟩
  have hsig := P.sig_le_of_mem hT (P.rep.label r + 1)
  have hact := P.sig_act_of_mem hr0 hrN ht
  simp only [cutAlpha, cutBeta, termMargin_eq_cut, cutShift_label', cutShift_label]
  simp only [← hr]
  rw [← P.activeMargin_eq hr0 hrN, ← k2, ← k5]
  linarith

/-- The decreasing inactive Hamiltonian along piece `k`, at the intermediate factor `s`. -/
theorem cut_sig_decr_le (k : ℤ) {s : ℝ} (hs : s ∈ Icc 1 (P.factor k)) :
    2 * (s⁻¹ ^ 2 * (P.cutAlpha k (P.rep.label k) + P.cutAlpha k (P.rep.label k - 1)) +
        costateADecr (P.termMargin k (P.rep.label k)) (P.termMargin k (P.rep.label k - 1)) s) +
      (s⁻¹ * (P.cutBeta k (P.rep.label k) + P.cutBeta k (P.rep.label k - 1)) +
        costateBDecr (P.termMargin k (P.rep.label k)) (P.termMargin k (P.rep.label k - 1)) s) ≤
      0 := by
  have hr0 := term_emod_nonneg P k
  have hrN := term_emod_lt P k
  set r := k % P.N with hr
  have hlt := P.rep.τ_lt_succ r
  obtain ⟨h0, -, h1⟩ := P.rep.piece_subset hr0 hrN
  have ha := P.activeMargin_pos r
  rw [← term_factor_emod] at hs
  have hs0 : 0 < s := lt_of_lt_of_le one_pos hs.1
  set t := P.rep.τ r + P.activeMargin r / 2 * Real.log s with ht_def
  have hlogq := P.log_factor r
  have hlog0 : 0 ≤ Real.log s := Real.log_nonneg hs.1
  have hlog1 : Real.log s ≤ Real.log (P.factor r) := Real.log_le_log hs0 hs.2
  have ht : t ∈ Icc (P.rep.τ r) (P.rep.τ (r + 1)) := by
    constructor
    · rw [ht_def]; have := mul_nonneg (div_nonneg ha.le zero_le_two) hlog0; linarith
    · rw [ht_def, hlogq] at *
      have : P.activeMargin r / 2 * Real.log s ≤ P.activeMargin r / 2 *
          (2 * (P.rep.τ (r + 1) - P.rep.τ r) / P.activeMargin r) :=
        mul_le_mul_of_nonneg_left hlog1 (div_nonneg ha.le zero_le_two)
      rw [show P.activeMargin r / 2 * (2 * (P.rep.τ (r + 1) - P.rep.τ r) / P.activeMargin r) =
        P.rep.τ (r + 1) - P.rep.τ r by field_simp] at this
      linarith
  have hq : Real.exp (2 * (t - P.rep.τ r) / P.activeMargin r) = s := by
    rw [ht_def, show 2 * (P.rep.τ r + P.activeMargin r / 2 * Real.log s - P.rep.τ r) /
      P.activeMargin r = Real.log s by field_simp; ring, Real.exp_log hs0]
  have key := vertexPiece_costate P.extremal h0 hlt h1 (P.ae_eq_vertex hr0 hrN)
    (P.activeMargin_eq hr0 hrN).symm rfl rfl ht hq
  dsimp only at key
  obtain ⟨-, -, k3, -, -, k6⟩ := key
  have hT : t ∈ Icc 0 P.T := ⟨h0.trans ht.1, ht.2.trans h1⟩
  have hsig := P.sig_le_of_mem hT (P.rep.label r - 1)
  have hact := P.sig_act_of_mem hr0 hrN ht
  simp only [cutAlpha, cutBeta, termMargin_eq_cut, cutShift_label', cutShift_label_sub]
  simp only [← hr]
  rw [← P.activeMargin_eq hr0 hrN, ← k3, ← k6]
  linarith

/-- **The costate cycle of a normal period.** -/
noncomputable def costateCycle : CostateCycle P.N where
  toCycle := P.termCycle
  α := P.cutAlpha
  β := P.cutBeta
  α_add k j := by
    simp only [cutAlpha, Int.add_emod_right, P.cutShift_add_N]
    congr 1; abel
  β_add k j := by
    simp only [cutBeta, Int.add_emod_right, P.cutShift_add_N]
    congr 1; abel
  α_act k := (P.cut_transport k).1
  α_grow k := (P.cut_transport k).2.1
  α_decr k := (P.cut_transport k).2.2.1
  β_act k := (P.cut_transport k).2.2.2.1
  β_grow k := (P.cut_transport k).2.2.2.2.1
  β_decr k := (P.cut_transport k).2.2.2.2.2
  sig_act k := by
    have hr0 := term_emod_nonneg P k
    have hrN := term_emod_lt P k
    have := P.sig_act_of_mem hr0 hrN ⟨le_rfl, (P.rep.τ_lt_succ _).le⟩
    simp only [termCycle, cutAlpha, cutBeta, cutShift_label']
    exact this
  sig_le k j := by
    simp only [cutAlpha, cutBeta]
    exact P.sig_le_of_mem ⟨P.rep.τ_nonneg (term_emod_nonneg P k),
      P.rep.τ_le_T (term_emod_lt P k).le⟩ _
  perp k := by
    have hr0 := term_emod_nonneg P k
    have hrN := term_emod_lt P k
    have hT : P.rep.τ (k % P.N) ∈ Icc 0 P.T :=
      ⟨P.rep.τ_nonneg hr0, P.rep.τ_le_T hrN.le⟩
    have hpt := P.extremal.2.2.2.2.2.2.2.1 _ hT
    have h := costateB_perp (P.isStarState hT) hpt.1 hpt.2.1 hpt.2.2.1
    simp only [termCycle, cutBeta, termMargin_eq_cut]
    rw [cst_perp_shift (fun j ↦ costateBeta (P.Λ₁ (P.rep.τ (k % P.N))) (P.ΛR (P.rep.τ (k % P.N)))
      (P.X (P.rep.τ (k % P.N))) j) (fun j ↦ margin j (P.X (P.rep.τ (k % P.N))))]
    exact h
  sig_grow_le k s hs := P.cut_sig_grow_le k hs
  sig_decr_le k s hs := P.cut_sig_decr_le k hs

theorem costateCycle_lab (k : ℤ) : P.costateCycle.lab k = P.rep.label k := rfl

theorem costateCycle_m (k : ℤ) (j : Fin 3) : P.costateCycle.m k j = P.termMargin k j := rfl

theorem costateCycle_q (k : ℤ) : P.costateCycle.q k = P.factor k := rfl

/-- The switch margin of the active label is the active margin: `m_k(i_k) = a_k`. -/
theorem costateCycle_m_lab (k : ℤ) :
    P.costateCycle.m k (P.costateCycle.lab k) = P.activeMargin k := by
  rw [costateCycle_m, costateCycle_lab, termMargin_eq_cut, cutShift_label', activeMargin]

end NormalPeriod

end SmoothedOctagon
