module

public import SmoothedOctagon.Reduction.Defs
public import SmoothedOctagon.Reduction.Normal.Bridge

/-!
# Normality of closed finite vertex extremals

A Pontryagin extremal whose control has a finite vertex representation (distinct neighbouring
labels, also across the twisted seam) has a nonzero cost multiplier; by positive homogeneity of
`IsPontryaginExtremal` it can be rescaled to `λ = -1`.

Main API:

* `lam_lt_zero_of_vertexRepresentation`: `λ < 0`.
* `traceForm_smul_left`, `isIntegralCurve_smul`, `hamiltonian_smul`: homogeneity of the trace
  form, of Carathéodory solutions and of the Hamiltonian.
* `isPontryaginExtremal_smul`: `(Λ₁, Λ_R, λ) ↦ (cΛ₁, cΛ_R, cλ)` for `c > 0`.
* `exists_normal_lift`: a lift with `λ < 0` rescales to `λ = -1`.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

/-- **Closed finite vertex extremals are normal**. If a global minimizer `(T, u, g, X)` carries a
Pontryagin lift `(Λ₁, Λ_R, λ)` and its control has a finite vertex representation, then `λ < 0`.

Minimality is not used (nor a cost budget, rank, or `N ≥ 6`): the hypothesis `_hmin` is unused.
Proof: suppose `λ = 0`. Extend the lift by the twist (`remark6_6_1`) and read the bi-infinite word
`i_{j+N} = i_j + 1`, `i_{j+1} ≠ i_j` from a genuine switch; its switch signs are `N`-periodic. Every
vertex piece transports the coordinates `μ_j(a)`, `μ_j(b)` of `a = -XΛ₁X`,
`b = Λ_R + 2Λ₁ + ⟨Λ₁, X⟩X` by the one-arc margin map (`Normal/Flow.lean`, `gn_piece`), and the
maximum condition at the switching times gives the missing-vertex inequalities. Scalar lemmas on the
resulting sequence (`Normal/Word.lean`) show: no three consecutive equal signs; `σσ` flanked by `-σ`
forces triple ties at both ends of the middle arc, which no arc can have. Both triple-tie
implications follow from one forward identity (`GnSeq.bounce`). Hence the signs alternate,
`i_{j+2} = i_j`, only two labels occur; but the label set is invariant under `+1`. -/
theorem lam_lt_zero_of_vertexRepresentation {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    {lam : ℝ} (_hmin : IsReinhardtMinimizer T u g X)
    (hext : IsPontryaginExtremal T u g X Λ₁ ΛR lam) (ρ : VertexRepresentation T u) : lam < 0 := by
  rcases (hext.2.2.2.2.2.2.1 : lam ≤ 0).lt_or_eq with h | h
  · exact h
  · subst h
    obtain ⟨S, hS⟩ := gn_abnormal_seq hext ρ
    exact (S.false_of_twist hS).elim

/-! ### Positive homogeneity of Pontryagin extremals -/

/-- The trace form is linear in its first argument: `⟨cA, B⟩ = c⟨A, B⟩`. -/
theorem traceForm_smul_left (c : ℝ) (A B : Mat2) : traceForm (c • A) B = c * traceForm A B := by
  simp [traceForm, Matrix.trace_smul]

/-- Carathéodory solutions scale: if `f' = v` then `(cf)' = cv`. -/
theorem isIntegralCurve_smul {f v : ℝ → Mat2} {T : ℝ} (h : IsIntegralCurve f v T) (c : ℝ) :
    IsIntegralCurve (fun t ↦ c • f t) (fun t ↦ c • v t) T := by
  intro i j
  obtain ⟨hint, heq⟩ := h i j
  refine ⟨by simpa using hint.const_mul c, fun t ht ↦ ?_⟩
  simp only [Matrix.smul_apply, smul_eq_mul, intervalIntegral.integral_const_mul, heq t ht]
  ring

/-- The Hamiltonian is linear in the extended covector `(λ, Λ₁, Λ_R)`. -/
theorem hamiltonian_smul (c lam : ℝ) (Λ₁ ΛR X : Mat2) (v : Fin 3 → ℝ) :
    hamiltonian (c * lam) (c • Λ₁) (c • ΛR) X v = c * hamiltonian lam Λ₁ ΛR X v := by
  have e : c • Λ₁ - (3 / 2 * (c * lam)) • J = c • (Λ₁ - (3 / 2 * lam) • J) := by
    rw [smul_sub, smul_smul]; ring_nf
  simp only [hamiltonian, e, traceForm_smul_left]
  ring

/-- **Positive homogeneity**: a Pontryagin lift scaled by `c > 0` is a Pontryagin lift. The
state and costate equations are linear in the costate, and the Hamiltonian is scaled by `c`. -/
theorem isPontryaginExtremal_smul {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) {c : ℝ} (hc : 0 < c) :
    IsPontryaginExtremal T u g X (fun t ↦ c • Λ₁ t) (fun t ↦ c • ΛR t) (c * lam) := by
  obtain ⟨hst, hg0, hgT, hXT, hΛ₁T, hΛRT, hlam, hcost, hΛ₁I, hΛRI, hH⟩ := h
  refine ⟨hst, hg0, hgT, hXT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hΛ₁T, Matrix.mul_smul, Matrix.smul_mul]
  · simp only [hΛRT, Matrix.mul_smul, Matrix.smul_mul]
  · exact mul_nonpos_of_nonneg_of_nonpos hc.le hlam
  · intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hcost t ht
    refine ⟨by simp [Matrix.trace_smul, h1], by simp [Matrix.trace_smul, h2],
      by rw [traceForm_smul_left, h3, mul_zero], ?_⟩
    rcases h4 with h4 | h4 | h4
    · exact Or.inl (mul_ne_zero hc.ne' h4)
    · exact Or.inr (Or.inl (smul_ne_zero hc.ne' h4))
    · exact Or.inr (Or.inr (smul_ne_zero hc.ne' h4))
  · convert isIntegralCurve_smul hΛ₁I c using 2 with t
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  · convert isIntegralCurve_smul hΛRI c using 2 with t
    have e : -(c • Λ₁ t) + (3 / 2 * (c * lam)) • J = c • (-Λ₁ t + (3 / 2 * lam) • J) := by
      rw [smul_add, smul_neg, smul_smul]; ring_nf
    rw [e, traceForm_smul_left, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul]
    module
  · filter_upwards [hH] with t ht hti
    obtain ⟨h0, hmax⟩ := ht hti
    refine ⟨by rw [hamiltonian_smul, h0, mul_zero], fun v hv ↦ ?_⟩
    rw [hamiltonian_smul, hamiltonian_smul]
    exact mul_le_mul_of_nonneg_left (hmax v hv) hc.le

/-- **Rescaling to `λ = -1`**: a Pontryagin lift with `λ < 0`, divided by `-λ`, is a normal lift
with `λ = -1`. -/
theorem exists_normal_lift {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) (hlam : lam < 0) :
    ∃ Λ₁' ΛR' : ℝ → Mat2, IsPontryaginExtremal T u g X Λ₁' ΛR' (-1) := by
  have hc : 0 < (-lam)⁻¹ := inv_pos.2 (neg_pos.2 hlam)
  have e : (-lam)⁻¹ * lam = -1 := by have := hlam.ne; field_simp
  exact ⟨_, _, e ▸ isPontryaginExtremal_smul h hc⟩

end SmoothedOctagon.Reduction
