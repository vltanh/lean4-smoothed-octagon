module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Foundations.SingularLocus

/-!
# The vertex Hamiltonians of a Pontryagin extremal

For an extremal `(T, u, g, X, Λ₁, Λ_R, λ)` the three vertex Hamiltonians
`H_i(t) = H(Λ₁(t), Λ_R(t), X(t); e_i)` are continuous on `[0, T]`, and at every time (not only
almost every time) all of them are `≤ 0` and one of them is `0`. The maximum principle gives this
for almost every time, the maximum of the Hamiltonian over the simplex is attained at a vertex
(`hamiltonian_isMax_iff_vertexwise`), and continuity extends it to all of `[0, T]`.

Used by the singular clearance, the switch count and normality.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons MeasureTheory Set

private theorem ham_vertex_mem (i : Fin 3) : vertex i ∈ controlSimplex := by
  refine ⟨fun j ↦ ?_, ?_⟩
  · by_cases h : j = i
    · subst j; simp [vertex]
    · simp [vertex, h]
  · fin_cases i <;> simp [vertex]

/-- The vertex Hamiltonians of an extremal are continuous on `[0, T]`. -/
theorem IsPontryaginExtremal.continuousOn_vertexHamiltonian {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) (i : Fin 3) :
    ContinuousOn (fun t ↦ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex i)) (Icc 0 T) := by
  obtain ⟨htraj, _, _, _, _, _, _, _, hL₁I, hLRI, _⟩ := h
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral htraj.2.2.2.2.2
  have hL₁c : ContinuousOn Λ₁ (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hL₁I
  have hLRc : ContinuousOn ΛR (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hLRI
  have htr : ∀ {A B : ℝ → Mat2}, ContinuousOn A (Icc 0 T) → ContinuousOn B (Icc 0 T) →
      ContinuousOn (fun t ↦ traceForm (A t) (B t)) (Icc 0 T) := fun hA hB ↦
    (continuous_id.matrix_trace).comp_continuousOn (hA.mul hB)
  refine (htr (hL₁c.sub continuousOn_const) hXc).sub
    ((htr hLRc continuousOn_const).div (htr hXc continuousOn_const) ?_)
  intro t ht
  have hstar := (htraj.2.2.2.1 t ht).2
  rw [traceForm, Matrix.trace_mul_comm, ← traceForm]
  exact ((lemma3_3_4 _ hstar.1).mp hstar.2.2 _ (ham_vertex_mem i)).ne

/-- **The maximum condition at every time.** For an extremal, at every `t ∈ [0, T]` every vertex
Hamiltonian is `≤ 0` and one of them vanishes. -/
theorem IsPontryaginExtremal.vertexHamiltonian_max_eq_zero {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, (∀ i, hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex i) ≤ 0) ∧
      ∃ i, hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex i) = 0 := by
  set H : Fin 3 → ℝ → ℝ := fun i t ↦ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex i)
  set M : ℝ → ℝ := fun t ↦ max (H 0 t) (max (H 1 t) (H 2 t))
  have hMc : ContinuousOn M (Icc 0 T) :=
    ContinuousOn.sup (continuousOn_vertexHamiltonian h 0)
      (ContinuousOn.sup (continuousOn_vertexHamiltonian h 1) (continuousOn_vertexHamiltonian h 2))
  have hT : 0 < T := h.1.1
  obtain ⟨htraj, _, _, _, _, _, _, _, _, _, hmax⟩ := h
  -- almost every time, the maximum over the vertices is `0`
  have hae : ∀ᵐ t, t ∈ Ioo 0 T → M t = 0 := by
    filter_upwards [hmax] with t ht hmem
    obtain ⟨hzero, hle⟩ := ht hmem
    have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self hmem
    have hX := (htraj.2.2.2.1 t htc).2
    have hu := htraj.2.2.1 t htc
    have hvle : ∀ i, H i t ≤ 0 := fun i ↦ hzero ▸ hle _ (ham_vertex_mem i)
    obtain ⟨i, hi⟩ : ∃ i, 0 < u t i := by
      by_contra hcon
      push Not at hcon
      have := hu.2
      linarith [hcon 0, hcon 1, hcon 2]
    have hHi : H i t = 0 :=
      (maximizing_control_support lam _ _ hX hu hle i hi).trans hzero
    have hM0 : M t ≤ 0 := max_le (hvle 0) (max_le (hvle 1) (hvle 2))
    refine le_antisymm hM0 ?_
    rw [← hHi]
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hIoo : EqOn M (fun _ ↦ 0) (Ioo 0 T) :=
    Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' measurableSet_Ioo).mpr hae) isOpen_Ioo
      (hMc.mono Ioo_subset_Icc_self) continuousOn_const
  have hIcc : EqOn M (fun _ ↦ 0) (Icc 0 T) :=
    hIoo.of_subset_closure hMc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hT.ne])
  intro t ht
  have hMt : M t = 0 := hIcc ht
  refine ⟨fun i ↦ ?_, ?_⟩
  · change H i t ≤ 0
    rw [← hMt]
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · have hMt' : max (H 0 t) (max (H 1 t) (H 2 t)) = 0 := hMt
    rcases max_choice (H 0 t) (max (H 1 t) (H 2 t)) with h0 | h0
    · exact ⟨0, by rw [h0] at hMt'; exact hMt'⟩
    · rcases max_choice (H 1 t) (H 2 t) with h1 | h1
      · exact ⟨1, by rw [h0, h1] at hMt'; exact hMt'⟩
      · exact ⟨2, by rw [h0, h1] at hMt'; exact hMt'⟩

end SmoothedOctagon
