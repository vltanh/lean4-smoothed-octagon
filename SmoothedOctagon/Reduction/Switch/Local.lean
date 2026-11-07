module

public import Basic.Analysis.Calculus.MatrixFTC
public import SmoothedOctagon.Period.Hamiltonian
public import SmoothedOctagon.Reduction.Defs
public import SmoothedOctagon.Reduction.CompactDomain

/-!
# Local exclusion of a vertex

The analytic half of the switch count (`Reduction/SwitchCount.lean`).

Main API:

* `qrsb_singularGapSq_pos`: under the clearance `‖𝒫‖² ≤ 251² Q²`, nontriviality gives `Q(t) > 0`.
* `qrsb_exists_excluded_vertex`: if the costate is off the singular locus at `t₀` (`Q(t₀) > 0`),
  there are `δ > 0` and vertices `j`, `k` with `H_j < 0` on `(t₀, t₀ + δ)` and `H_k < 0` on
  `(t₀ - δ, t₀)` (within `[0, T]`).
* `qrsb_ae_coord_eq_zero`: where a vertex Hamiltonian is negative, that control coordinate
  vanishes a.e.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set Filter
open scoped Topology

/-! ### Frobenius norms -/

private theorem frobSq_nonneg' (M : Mat2) : 0 ≤ frobSq M := by unfold frobSq; positivity

private theorem frobSq_pos' {M : Mat2} (h : M ≠ 0) : 0 < frobSq M := by
  rcases (frobSq_nonneg' M).lt_or_eq with h' | h'
  · exact h'
  · exfalso
    apply h
    unfold frobSq at h'
    have e0 := sq_nonneg (M 0 0)
    have e1 := sq_nonneg (M 0 1)
    have e2 := sq_nonneg (M 1 0)
    have e3 := sq_nonneg (M 1 1)
    have h0 : M 0 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have h1 : M 0 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have h2 : M 1 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    have h3 : M 1 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (by linarith)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, h3]

private theorem sq_apply_le_frobSq (M : Mat2) (i j : Fin 2) : M i j ^ 2 ≤ frobSq M := by
  unfold frobSq
  have e0 := sq_nonneg (M 0 0)
  have e1 := sq_nonneg (M 0 1)
  have e2 := sq_nonneg (M 1 0)
  have e3 := sq_nonneg (M 1 1)
  fin_cases i <;> fin_cases j <;> simp <;> linarith

private theorem frobSq_sub_le (A B : Mat2) : frobSq (A - B) ≤ 2 * frobSq A + 2 * frobSq B := by
  simp only [frobSq, Matrix.sub_apply]
  nlinarith [sq_nonneg (A 0 0 + B 0 0), sq_nonneg (A 0 1 + B 0 1), sq_nonneg (A 1 0 + B 1 0),
    sq_nonneg (A 1 1 + B 1 1)]

private theorem frobSq_smul' (c : ℝ) (A : Mat2) : frobSq (c • A) = c ^ 2 * frobSq A := by
  simp only [frobSq, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem traceForm_eq' (A B : Mat2) :
    traceForm A B = A 0 0 * B 0 0 + A 0 1 * B 1 0 + A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  simp [traceForm, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem traceForm_sq_le' (A B : Mat2) : traceForm A B ^ 2 ≤ frobSq A * frobSq B := by
  rw [traceForm_eq']
  unfold frobSq
  nlinarith [sq_nonneg (A 0 0 * B 1 0 - A 0 1 * B 0 0), sq_nonneg (A 0 0 * B 0 1 - A 1 0 * B 0 0),
    sq_nonneg (A 0 0 * B 1 1 - A 1 1 * B 0 0), sq_nonneg (A 0 1 * B 0 1 - A 1 0 * B 1 0),
    sq_nonneg (A 0 1 * B 1 1 - A 1 1 * B 1 0), sq_nonneg (A 1 0 * B 1 1 - A 1 1 * B 0 1)]

private theorem frobSq_mul_le' (A B : Mat2) : frobSq (A * B) ≤ frobSq A * frobSq B := by
  unfold frobSq
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  nlinarith [sq_nonneg (A 0 0 * B 1 0 - A 0 1 * B 0 0), sq_nonneg (A 0 0 * B 1 1 - A 0 1 * B 0 1),
    sq_nonneg (A 1 0 * B 1 0 - A 1 1 * B 0 0), sq_nonneg (A 1 0 * B 1 1 - A 1 1 * B 0 1),
    sq_nonneg (A 0 0 * A 1 1), sq_nonneg (A 0 1 * A 1 0), sq_nonneg (B 0 0 * B 1 1),
    sq_nonneg (B 0 1 * B 1 0), sq_nonneg (A 0 0 * B 0 0), sq_nonneg (A 1 1 * B 1 1)]

private theorem continuous_frobSq : Continuous frobSq := by
  unfold frobSq
  fun_prop

/-- The part of the costate field that depends on `Λ_R` is quadratically small in `‖Λ_R‖`:
`‖[P, W] - ⟨W, P⟩[P, X]‖² ≤ 8 ‖P‖² ‖W‖² (1 + ‖P‖² ‖X‖²)`. -/
private theorem frobSq_drift_le (P W X : Mat2) :
    frobSq ((P * W - W * P) - traceForm W P • (P * X - X * P)) ≤
      8 * frobSq P * frobSq W * (1 + frobSq P * frobSq X) := by
  have h1 := frobSq_sub_le (P * W - W * P) (traceForm W P • (P * X - X * P))
  have h2 := frobSq_sub_le (P * W) (W * P)
  have h3 := frobSq_mul_le' P W
  have h4 := frobSq_mul_le' W P
  have h5 := frobSq_sub_le (P * X) (X * P)
  have h6 := frobSq_mul_le' P X
  have h7 := frobSq_mul_le' X P
  have h8 := traceForm_sq_le' W P
  rw [frobSq_smul'] at h1
  have nP := frobSq_nonneg' P
  have nW := frobSq_nonneg' W
  have nX := frobSq_nonneg' X
  have h9 : traceForm W P ^ 2 * frobSq (P * X - X * P) ≤
      frobSq W * frobSq P * (4 * (frobSq P * frobSq X)) :=
    mul_le_mul h8 (by nlinarith) (frobSq_nonneg' _) (by positivity)
  nlinarith

private theorem traceForm_zero_left (M : Mat2) : traceForm 0 M = 0 := by simp [traceForm]

/-! ### Bounds on `𝔥**` -/

private theorem frobSq_controlMatrix_le {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    frobSq (controlMatrix u) ≤ 3 := by
  obtain ⟨hb, -⟩ := hu
  obtain ⟨a0, b0⟩ := hb 0
  obtain ⟨a1, b1⟩ := hb 1
  obtain ⟨a2, b2⟩ := hb 2
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [frobSq, controlMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, div_pow, h3]
  nlinarith [mul_nonneg a1 a2, mul_nonneg a0 (sub_nonneg.2 b0), mul_nonneg a1 (sub_nonneg.2 b1),
    mul_nonneg a2 (sub_nonneg.2 b2), mul_nonneg a0 a1, mul_nonneg a0 a2]

private theorem traceForm_vertex_bound {X : Mat2} (hX : Cited.HalesVajjha.InCompactDomain X)
    (i : Fin 3) : √3 * traceForm X (controlMatrix (vertex i)) ≤ -(2 / 15) := by
  have := two_div_fifteen_le_margin hX i
  rw [margin, traceForm, Matrix.trace_mul_comm, ← traceForm] at this
  linarith

private theorem traceForm_vertex_neg {X : Mat2} (hX : Cited.HalesVajjha.InCompactDomain X)
    (i : Fin 3) : traceForm X (controlMatrix (vertex i)) < 0 := by
  have h := traceForm_vertex_bound hX i
  have hs : 0 < √3 := by positivity
  by_contra hc
  push Not at hc
  have := mul_nonneg hs.le hc
  linarith

/-- On `𝔥**` the matrix `P_u(X) = Z_u / ⟨Z_u, X⟩` is bounded uniformly in the control. -/
private theorem frobSq_controlP_le {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) {X : Mat2}
    (hX : Cited.HalesVajjha.InCompactDomain X) : frobSq (controlP u X) ≤ 507 := by
  have hD : traceForm (controlMatrix u) X =
      ∑ i : Fin 3, u i * traceForm X (controlMatrix (vertex i)) := by
    rw [traceForm, Matrix.trace_mul_comm, ← traceForm, traceForm_controlMatrix_eq_vertex_sum]
  have hs3 : √3 * traceForm (controlMatrix u) X ≤ -(2 / 15) := by
    rw [hD, Finset.mul_sum, Fin.sum_univ_three]
    obtain ⟨hb, hsum⟩ := hu
    have e : ∀ i : Fin 3, √3 * (u i * traceForm X (controlMatrix (vertex i))) ≤
        u i * (-(2 / 15)) := fun i ↦ by
      rw [mul_left_comm]
      exact mul_le_mul_of_nonneg_left (traceForm_vertex_bound hX i) (hb i).1
    linarith [e 0, e 1, e 2]
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set D := traceForm (controlMatrix u) X with hDdef
  have hsq : (√3 * D) ^ 2 = 3 * D ^ 2 := by rw [mul_pow, h3]
  have hD2 : 4 / 675 ≤ D ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ -(√3 * D) - 2 / 15)
      (by linarith : (0 : ℝ) ≤ -(√3 * D) + 2 / 15)]
  rw [controlP, frobSq_smul', ← hDdef]
  have hinv : (D⁻¹) ^ 2 ≤ 675 / 4 := by
    rw [inv_pow]
    calc (D ^ 2)⁻¹ ≤ (4 / 675)⁻¹ := inv_anti₀ (by norm_num) hD2
      _ = 675 / 4 := by norm_num
  have hZ := frobSq_controlMatrix_le hu
  have := mul_le_mul hinv hZ (frobSq_nonneg' _) (by norm_num)
  linarith

/-! ### The costate field at a zero of `Λ_R` -/

/-- At a time `t₀` where `Λ_R` vanishes, the right-hand side of the costate equation for `Λ_R`
is continuous within `[0, T]` at `t₀` (although the control need not be): the terms involving
the control are `O(‖Λ_R‖)`. -/
private theorem costateRHS_continuousWithinAt {T : ℝ} {u : ℝ → Fin 3 → ℝ} {X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (hu : ∀ t ∈ Icc 0 T, u t ∈ controlSimplex)
    (hK : ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t))
    (hXc : ContinuousOn X (Icc 0 T)) (hΛc : ContinuousOn Λ₁ (Icc 0 T))
    (hWc : ContinuousOn ΛR (Icc 0 T)) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (hW0 : ΛR t₀ = 0) :
    ContinuousWithinAt (fun t ↦
      (controlP (u t) (X t) * ΛR t - ΛR t * controlP (u t) (X t)) -
        traceForm (ΛR t) (controlP (u t) (X t)) •
          (controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) +
        ((-Λ₁ t + (3 / 2 * lam) • J) * X t - X t * (-Λ₁ t + (3 / 2 * lam) • J))) (Icc 0 T) t₀ := by
  have hF : ContinuousWithinAt (fun t ↦
      (-Λ₁ t + (3 / 2 * lam) • J) * X t - X t * (-Λ₁ t + (3 / 2 * lam) • J)) (Icc 0 T) t₀ :=
    (((hΛc.neg.add continuousOn_const).mul hXc).sub
      (hXc.mul (hΛc.neg.add continuousOn_const))) t₀ ht₀
  have hE : ContinuousWithinAt (fun t ↦
      (controlP (u t) (X t) * ΛR t - ΛR t * controlP (u t) (X t)) -
        traceForm (ΛR t) (controlP (u t) (X t)) •
          (controlP (u t) (X t) * X t - X t * controlP (u t) (X t))) (Icc 0 T) t₀ := by
    rw [Matrix.continuousWithinAt_iff_entrywise]
    intro i j
    have hc : ContinuousWithinAt (fun t ↦ √(8 * 507 * (1 + 507 * 81) * frobSq (ΛR t)))
        (Icc 0 T) t₀ :=
      (continuousWithinAt_const.mul ((continuous_frobSq.comp_continuousOn hWc) t₀ ht₀)).sqrt
    have hlim : Tendsto (fun t ↦ √(8 * 507 * (1 + 507 * 81) * frobSq (ΛR t)))
        (𝓝[Icc 0 T] t₀) (𝓝 0) := by
      convert hc.tendsto using 2
      simp [hW0, frobSq]
    have hT0 : Tendsto (fun t ↦ ((controlP (u t) (X t) * ΛR t - ΛR t * controlP (u t) (X t)) -
        traceForm (ΛR t) (controlP (u t) (X t)) •
          (controlP (u t) (X t) * X t - X t * controlP (u t) (X t))) i j)
        (𝓝[Icc 0 T] t₀) (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [Real.norm_eq_abs]
      apply Real.abs_le_sqrt
      have hP := frobSq_controlP_le (hu t ht) (hK t ht)
      have hX := (frobSq_lt_of_inCompactDomain (hK t ht)).le
      have nP := frobSq_nonneg' (controlP (u t) (X t))
      have nW := frobSq_nonneg' (ΛR t)
      have nX := frobSq_nonneg' (X t)
      have h1 : frobSq (controlP (u t) (X t)) * frobSq (X t) ≤ 507 * 81 :=
        mul_le_mul hP hX nX (by norm_num)
      have h2 : 8 * frobSq (controlP (u t) (X t)) *
          (1 + frobSq (controlP (u t) (X t)) * frobSq (X t)) ≤ 8 * 507 * (1 + 507 * 81) := by
        nlinarith
      calc _ ≤ frobSq _ := sq_apply_le_frobSq _ i j
        _ ≤ _ := frobSq_drift_le _ _ _
        _ ≤ 8 * 507 * (1 + 507 * 81) * frobSq (ΛR t) := by nlinarith
    rw [ContinuousWithinAt]
    convert hT0 using 2
    simp [hW0, traceForm]
  exact hE.add hF

/-! ### Commutators -/

/-- For a traceless `X` with `det X = 1` and a traceless `A` with `tr(AX) = 0`, `[X, A] = 0`
forces `A = 0` (QUANTITATIVE_REGULAR_SWITCH_BOUND (11): `[X, [X, A]] = -4A - 2⟨A, X⟩X`). -/
private theorem eq_zero_of_commutator_eq_zero {X A : Mat2} (hXtr : X.trace = 0)
    (hdet : X.det = 1) (hAtr : A.trace = 0) (hAX : traceForm A X = 0)
    (hc : X * A - A * X = 0) : A = 0 := by
  rw [Matrix.trace_fin_two] at hXtr hAtr
  rw [Matrix.det_fin_two] at hdet
  have hX11 : X 1 1 = -X 0 0 := by linarith
  have hA11 : A 1 1 = -A 0 0 := by linarith
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, hX11,
    hA11] at e00 e01 e10
  rw [traceForm_eq', hX11, hA11] at hAX
  rw [hX11] at hdet
  have hp : A 0 0 = 0 := by
    linear_combination (-(A 0 0)) * hdet - (X 0 0 / 2) * hAX + (X 1 0 / 4) * e01 -
      (X 0 1 / 4) * e10
  have hq : A 0 1 = 0 := by
    linear_combination (X 0 1 / 2) * e00 - (X 0 0 / 2) * e01 - (X 0 1 / 2) * hAX -
      (A 0 1) * hdet
  have hr : A 1 0 = 0 := by
    linear_combination (-(X 1 0 / 2)) * e00 + (X 0 0 / 2) * e10 - (X 1 0 / 2) * hAX -
      (A 1 0) * hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, hA11]

/-! ### Positivity of the singular gap -/

/-- Under the clearance `‖𝒫‖² ≤ 251² Q²`, the nontriviality of the costate gives `Q > 0`: the
costate is off the singular locus. -/
theorem qrsb_singularGapSq_pos {lam : ℝ} {Λ₁ ΛR : Mat2} (hnt : lam ≠ 0 ∨ Λ₁ ≠ 0 ∨ ΛR ≠ 0)
    (hclear : covectorNormSq lam Λ₁ ΛR ≤ 251 ^ 2 * singularGapSq lam Λ₁ ΛR) :
    0 < singularGapSq lam Λ₁ ΛR := by
  have hpos : 0 < covectorNormSq lam Λ₁ ΛR := by
    have h1 := frobSq_nonneg' Λ₁
    have h2 := frobSq_nonneg' ΛR
    unfold covectorNormSq
    rcases hnt with h | h | h
    · have := pow_pos (abs_pos.mpr h) 2
      rw [sq_abs] at this
      linarith
    · have := frobSq_pos' h
      nlinarith [sq_nonneg lam]
    · have := frobSq_pos' h
      nlinarith [sq_nonneg lam]
  nlinarith

/-! ### Support of the control -/

/-- Where the vertex Hamiltonian `H_j` is negative, the control coordinate `u_j` vanishes
almost everywhere (`maximizing_control_support`). -/
theorem qrsb_ae_coord_eq_zero {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ T)
    {j : Fin 3} (hj : ∀ t ∈ Ioo a b, hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex j) < 0) :
    ∀ᵐ t, t ∈ Ioo a b → u t j = 0 := by
  obtain ⟨htraj, -, -, -, -, -, -, -, -, -, hmax⟩ := hext
  filter_upwards [hmax] with t ht hmem
  have hmem' : t ∈ Ioo 0 T := ⟨ha.trans_lt hmem.1, hmem.2.trans_le hb⟩
  obtain ⟨hzero, hle⟩ := ht hmem'
  have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self hmem'
  have hu := htraj.2.2.1 t htc
  by_contra hne
  have hpos : 0 < u t j := lt_of_le_of_ne (hu.1 j).1 (Ne.symm hne)
  have := maximizing_control_support lam _ _ (htraj.2.2.2.1 t htc).2 hu hle j hpos
  linarith [hj t hmem]

/-! ### The local exclusion -/

/-- **Local exclusion of a vertex.** Let `t₀ ∈ [0, T]` with `Q(t₀) > 0`. Then for some `δ > 0`
one vertex Hamiltonian `H_j` is negative on `(t₀, t₀ + δ)` and one `H_k` is negative on
`(t₀ - δ, t₀)` (within `[0, T]`).

If some `H_i(t₀) < 0`, continuity gives `j = k = i`. Otherwise the three vertex Hamiltonians tie
at `t₀`, which forces `Λ_R(t₀) = 0` (Lemma 8.2.1,
`hamiltonian_vertices_equal_iff_reducedCostate_eq_zero`) and `tr(A X) = 0`, `A = Λ₁ - (3/2)λJ`; `Q(t₀) > 0` gives `A ≠ 0`, so `b = [X, A] ≠ 0` with `b`
traceless and `⊥ X`. The costate equation is continuous at `t₀` (its control-dependent part is
`O(‖Λ_R‖)`), so `Λ_R'(t₀) = b`, and `h_i = ⟨Λ_R, Z_i⟩/⟨X, Z_i⟩` has derivative
`c_i = ⟨b, Z_i⟩/⟨X, Z_i⟩` at `t₀`. Lemma 8.2.1 applied to `b` shows that the `c_i` are not all
equal; with `c_k < c_j`, `H_j - H_k = h_k - h_j` changes sign at `t₀` from positive to negative.

Route: QUANTITATIVE_REGULAR_SWITCH_BOUND §§3-6 make this quantitative with three guard lines
transported along the flow (its Cases II and III); qualitatively only Case II occurs at a tie,
and the first-order expansion `Λ_R(t) = (t - t₀) b + o(t - t₀)` replaces the guard lines. -/
theorem qrsb_exists_excluded_vertex {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam)
    (hK : ∀ t ∈ Icc 0 T, Cited.HalesVajjha.InCompactDomain (X t)) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T)
    (hQ : 0 < singularGapSq lam (Λ₁ t₀) (ΛR t₀)) :
    ∃ δ > 0, ∃ j k : Fin 3,
      (∀ t ∈ Icc 0 T, t₀ < t → t < t₀ + δ →
        hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex j) < 0) ∧
      (∀ t ∈ Icc 0 T, t₀ - δ < t → t < t₀ →
        hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex k) < 0) := by
  have hmax := IsPontryaginExtremal.vertexHamiltonian_max_eq_zero hext
  have hHc := IsPontryaginExtremal.continuousOn_vertexHamiltonian hext
  obtain ⟨htraj, -, -, -, -, -, -, hcos, hL₁I, hLRI, -⟩ := hext
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral htraj.2.2.2.2.2
  have hΛc : ContinuousOn Λ₁ (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hL₁I
  have hWc : ContinuousOn ΛR (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hLRI
  by_cases hlt : ∃ i, hamiltonian lam (Λ₁ t₀) (ΛR t₀) (X t₀) (vertex i) < 0
  · -- a vertex is strictly below the maximum at `t₀`, hence near `t₀`
    obtain ⟨i, hi⟩ := hlt
    have hev : ∀ᶠ t in 𝓝[Icc 0 T] t₀, hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex i) < 0 :=
      Tendsto.eventually (hHc i t₀ ht₀) (Iio_mem_nhds hi)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
    refine ⟨δ, hδ, i, i, fun t ht h1 h2 ↦ hball ⟨?_, ht⟩, fun t ht h1 h2 ↦ hball ⟨?_, ht⟩⟩ <;>
    · rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
  -- a three-way tie at `t₀`
  push Not at hlt
  have hzero : ∀ i, hamiltonian lam (Λ₁ t₀) (ΛR t₀) (X t₀) (vertex i) = 0 :=
    fun i ↦ le_antisymm ((hmax t₀ ht₀).1 i) (hlt i)
  obtain ⟨hL₁tr, hWtr, hWX, -⟩ := hcos t₀ ht₀
  have hX₀ : IsStarState (X t₀) := (htraj.2.2.2.1 t₀ ht₀).2
  -- the tie forces `Λ_R(t₀) = 0`
  have hW0 : ΛR t₀ = 0 :=
    (hamiltonian_vertices_equal_iff_reducedCostate_eq_zero lam (Λ₁ t₀) hX₀ hWtr hWX).1
      (fun i ↦ (hzero i).trans (hzero 0).symm)
  -- `A = Λ₁ - (3/2)λJ` is nonzero, traceless and `⊥ X`
  obtain ⟨A, hA⟩ : ∃ A : Mat2, A = Λ₁ t₀ - (3 / 2 * lam) • J := ⟨_, rfl⟩
  have hAX : traceForm A (X t₀) = 0 := by
    have h := hzero 0
    rw [hamiltonian, hW0, traceForm_zero_left, zero_div, sub_zero, ← hA] at h
    exact h
  have hA0 : A ≠ 0 := by
    intro h
    rw [singularGapSq, ← hA, h, hW0] at hQ
    simp [frobSq] at hQ
  have hAtr : A.trace = 0 := by
    rw [hA, Matrix.trace_sub, Matrix.trace_smul, hL₁tr]
    simp [J, Matrix.trace_fin_two]
  -- `b = [X, A]`, the derivative of `Λ_R` at `t₀`
  obtain ⟨b, hb⟩ : ∃ b : Mat2,
      b = (-Λ₁ t₀ + (3 / 2 * lam) • J) * X t₀ - X t₀ * (-Λ₁ t₀ + (3 / 2 * lam) • J) :=
    ⟨_, rfl⟩
  have hbA : b = X t₀ * A - A * X t₀ := by
    have hneg : -Λ₁ t₀ + (3 / 2 * lam) • J = -A := by rw [hA]; abel
    rw [hb, hneg, Matrix.neg_mul, Matrix.mul_neg]
    abel
  have hbtr : b.trace = 0 := by rw [hbA, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  have hbX : traceForm b (X t₀) = 0 := by
    rw [hbA, traceForm_eq']
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hbne : b ≠ 0 := fun hb0 ↦
    hA0 (eq_zero_of_commutator_eq_zero hX₀.1 hX₀.2.1 hAtr hAX (hbA ▸ hb0))
  -- the vertex comparisons of `b` are not all equal
  obtain ⟨c, hc⟩ : ∃ c : Fin 3 → ℝ, ∀ i, c i = traceForm b (controlMatrix (vertex i)) /
      traceForm (X t₀) (controlMatrix (vertex i)) := ⟨_, fun _ ↦ rfl⟩
  have hnot : ¬ ∀ i : Fin 3, hamiltonian lam (Λ₁ t₀) b (X t₀) (vertex i) =
      hamiltonian lam (Λ₁ t₀) b (X t₀) (vertex 0) := fun h ↦
    hbne ((hamiltonian_vertices_equal_iff_reducedCostate_eq_zero lam (Λ₁ t₀) hX₀ hbtr hbX).1 h)
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  have hci : c i ≠ c 0 := by
    intro h
    apply hi
    simp only [hamiltonian]
    rw [← hc i, ← hc 0, h]
  obtain ⟨j, k, hjk⟩ : ∃ j k : Fin 3, c k < c j := by
    rcases lt_or_gt_of_ne hci with h | h
    · exact ⟨0, i, h⟩
    · exact ⟨i, 0, h⟩
  -- `Λ_R'(t₀) = b`
  have hRHS := costateRHS_continuousWithinAt (lam := lam) htraj.2.2.1 hK hXc hΛc hWc ht₀ hW0
  have hW' : Matrix.HasDerivWithinAtEntrywise ΛR b (Icc 0 T) t₀ := by
    refine (Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hLRI ht₀ hRHS).congr_deriv ?_
    rw [hb, hW0]
    simp [traceForm]
  -- the slopes of `h_i = ⟨Λ_R, Z_i⟩/⟨X, Z_i⟩` at `t₀` tend to `c_i`
  have hslope : ∀ i : Fin 3, Tendsto (fun t ↦ slope (fun s ↦ traceForm (ΛR s)
      (controlMatrix (vertex i)) / traceForm (X s) (controlMatrix (vertex i))) t₀ t)
      (𝓝[Icc 0 T \ {t₀}] t₀) (𝓝 (c i)) := by
    intro i
    have hg : HasDerivWithinAt (fun t ↦ traceForm (ΛR t) (controlMatrix (vertex i)))
        (traceForm b (controlMatrix (vertex i))) (Icc 0 T) t₀ := (hW'.mul_const _).trace
    have hD : ContinuousWithinAt (fun t ↦ (traceForm (X t) (controlMatrix (vertex i)))⁻¹)
        (Icc 0 T) t₀ := by
      have h1 : ContinuousOn (fun t ↦ traceForm (X t) (controlMatrix (vertex i))) (Icc 0 T) :=
        (continuous_id.matrix_trace).comp_continuousOn (hXc.mul continuousOn_const)
      exact (h1 t₀ ht₀).inv₀ (traceForm_vertex_neg (hK t₀ ht₀) i).ne
    have h2 := (hasDerivWithinAt_iff_tendsto_slope.1 hg).mul (hD.mono sdiff_subset).tendsto
    rw [hc i, div_eq_mul_inv]
    refine h2.congr (fun t ↦ ?_)
    simp only [slope_def_field, hW0, traceForm_zero_left]
    ring
  -- `h_k - h_j` has negative slopes near `t₀`
  have hev : ∀ᶠ t in 𝓝[Icc 0 T \ {t₀}] t₀,
      slope (fun s ↦ traceForm (ΛR s) (controlMatrix (vertex k)) /
        traceForm (X s) (controlMatrix (vertex k))) t₀ t -
      slope (fun s ↦ traceForm (ΛR s) (controlMatrix (vertex j)) /
        traceForm (X s) (controlMatrix (vertex j))) t₀ t < 0 :=
    Tendsto.eventually ((hslope k).sub (hslope j)) (Iio_mem_nhds (sub_neg.2 hjk))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
  have hmem : ∀ t ∈ Icc 0 T, t ≠ t₀ → |t - t₀| < δ →
      (traceForm (ΛR t) (controlMatrix (vertex k)) / traceForm (X t) (controlMatrix (vertex k)) -
        traceForm (ΛR t) (controlMatrix (vertex j)) /
          traceForm (X t) (controlMatrix (vertex j))) / (t - t₀) < 0 := by
    intro t ht hne hd
    have := hball ⟨by rwa [Metric.mem_ball, Real.dist_eq], ht, hne⟩
    simp only [mem_ofPred_eq, slope_def_field, hW0, traceForm_zero_left, zero_div,
      sub_zero] at this
    rwa [← sub_div] at this
  refine ⟨δ, hδ, j, k, fun t ht h1 h2 ↦ ?_, fun t ht h1 h2 ↦ ?_⟩
  · have h := hmem t ht (ne_of_gt h1) (by rw [abs_lt]; constructor <;> linarith)
    rw [div_lt_iff₀ (by linarith), zero_mul] at h
    have hk := (hmax t ht).1 k
    simp only [hamiltonian] at hk ⊢
    linarith
  · have h := hmem t ht (ne_of_lt h2) (by rw [abs_lt]; constructor <;> linarith)
    rw [div_lt_iff_of_neg (by linarith), zero_mul] at h
    have hj := (hmax t ht).1 j
    simp only [hamiltonian] at hj ⊢
    linarith

end SmoothedOctagon.Reduction
