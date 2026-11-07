module

public import SmoothedPolygons.Ch3.LieAlgebraDynamics
public import SmoothedPolygons.Ch7.Faces
public import Mathlib.Tactic

/-!
# The control-independent Hamiltonian locus

This is the pointwise algebra of Hales–Vajjha, *Packings of Smoothed Polygons*,
Lemma 8.2.1. For an arbitrary star state `X` and a traceless reduced costate
`ΛR` perpendicular to `X`, the Hamiltonian is constant on the control simplex
if and only if `ΛR = 0`. If `ΛR ≠ 0`, all maximizing controls lie in one proper
edge of the simplex. No prescribed polygon or normalized constant-control lift
is assumed.

The denominator-weighted vertex identity also gives an explicit support rule:
every vertex with positive weight in a maximizing control is itself maximizing.
The star inequalities make all denominator weights positive after negation.

These are pointwise statements. They do not construct a Pontryagin lift of a
minimizer, eliminate singular intervals, or bound the number of switches.
Source draft only: compilation and kernel validation have not been run.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Matrix SmoothedPolygons

private lemma singular_vertex_mem (i : Fin 3) : vertex i ∈ controlSimplex := by
  refine ⟨fun j ↦ ?_, ?_⟩
  · by_cases h : j = i
    · subst j; simp [vertex]
    · simp [vertex, h]
  · fin_cases i <;> simp [vertex]

private lemma singular_denominator_neg {X : Mat2} (hX : IsStarState X)
    {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    traceForm X (controlMatrix u) < 0 := by
  rw [traceForm, Matrix.trace_mul_comm, ← traceForm]
  exact (lemma3_3_4 X hX.1).mp hX.2.2 u hu

/-- Linearity of the control matrix, expressed using the three simplex vertices. -/
theorem traceForm_controlMatrix_eq_vertex_sum (A : Mat2) (u : Fin 3 → ℝ) :
    traceForm A (controlMatrix u) =
      ∑ i : Fin 3, u i * traceForm A (controlMatrix (vertex i)) := by
  simp [Fin.sum_univ_three, traceForm, controlMatrix, vertex, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- The three vertex control matrices separate traceless matrices under the trace form. -/
theorem eq_zero_of_traceForm_control_vertices_eq_zero {A : Mat2}
    (htr : A.trace = 0)
    (hzero : ∀ i : Fin 3, traceForm A (controlMatrix (vertex i)) = 0) : A = 0 := by
  have h11 : A 1 1 = -A 0 0 := by
    rw [Matrix.trace_fin_two] at htr
    linarith
  have heval :
      traceForm A (controlMatrix (vertex 0)) = A 0 1 + A 1 0 / 3 ∧
      traceForm A (controlMatrix (vertex 1)) = 2 * A 0 0 / √3 - 2 * A 1 0 / 3 ∧
      traceForm A (controlMatrix (vertex 2)) = -(2 * A 0 0 / √3) - 2 * A 1 0 / 3 := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [traceForm, controlMatrix, vertex, Matrix.trace_fin_two,
        Matrix.mul_apply, Fin.sum_univ_two, h11] <;> ring
  have h0 := hzero 0
  have h1 := hzero 1
  have h2 := hzero 2
  rw [heval.1] at h0
  rw [heval.2.1] at h1
  rw [heval.2.2] at h2
  have hc : A 1 0 = 0 := by
    linear_combination (-3 / 4) * h1 + (-3 / 4) * h2
  have haq : A 0 0 / √3 = 0 := by
    linear_combination (1 / 4) * h1 - (1 / 4) * h2
  have hsqrt : (√3 : ℝ) ≠ 0 := by positivity
  have ha : A 0 0 = 0 := by
    rcases div_eq_zero_iff.mp haq with h | h
    · exact h
    · exact absurd h hsqrt
  have hb : A 0 1 = 0 := by linarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, h11]

/-- A denominator-weighted Hamiltonian is the corresponding sum of its three
vertex values. The multipliers are linear in the control. -/
theorem hamiltonian_denominator_mul_eq_vertex_sum (lam : ℝ) (Λ₁ ΛR : Mat2)
    {X : Mat2} (hX : IsStarState X) {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    traceForm X (controlMatrix u) * hamiltonian lam Λ₁ ΛR X u =
      ∑ i : Fin 3, u i *
        (traceForm X (controlMatrix (vertex i)) * hamiltonian lam Λ₁ ΛR X (vertex i)) := by
  let D := fun v ↦ traceForm X (controlMatrix v)
  let N := fun v ↦ traceForm ΛR (controlMatrix v)
  let K := traceForm (Λ₁ - (3 / 2 * lam) • J) X
  have hmul : ∀ v ∈ controlSimplex,
      D v * hamiltonian lam Λ₁ ΛR X v = D v * K - N v := by
    intro v hv
    have hD : D v ≠ 0 := (singular_denominator_neg hX hv).ne
    change D v * (K - N v / D v) = D v * K - N v
    field_simp [hD] <;> ring
  calc
    _ = D u * K - N u := hmul u hu
    _ = ∑ i : Fin 3, u i * (D (vertex i) * K - N (vertex i)) := by
      dsimp [D, N]
      rw [traceForm_controlMatrix_eq_vertex_sum X u,
        traceForm_controlMatrix_eq_vertex_sum ΛR u]
      simp only [Fin.sum_univ_three]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hmul (vertex i) (singular_vertex_mem i)]

/-- An exact nonnegative-gap formula for comparing a control with a proposed
upper bound on the three vertex Hamiltonians. -/
theorem hamiltonian_gap_eq_vertex_sum (lam : ℝ) (Λ₁ ΛR : Mat2)
    {X : Mat2} (hX : IsStarState X) {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex)
    (M : ℝ) :
    -traceForm X (controlMatrix u) * (M - hamiltonian lam Λ₁ ΛR X u) =
      ∑ i : Fin 3, u i * (-traceForm X (controlMatrix (vertex i))) *
        (M - hamiltonian lam Λ₁ ΛR X (vertex i)) := by
  have hH := hamiltonian_denominator_mul_eq_vertex_sum lam Λ₁ ΛR hX hu
  have hD := traceForm_controlMatrix_eq_vertex_sum X u
  simp only [Fin.sum_univ_three] at hH hD ⊢
  linear_combination hH - M * hD

/-- Bounding the three vertex values bounds the Hamiltonian on the whole simplex. -/
theorem hamiltonian_le_of_vertex_le (lam : ℝ) (Λ₁ ΛR : Mat2)
    {X : Mat2} (hX : IsStarState X) {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex)
    {M : ℝ} (hM : ∀ i : Fin 3, hamiltonian lam Λ₁ ΛR X (vertex i) ≤ M) :
    hamiltonian lam Λ₁ ΛR X u ≤ M := by
  have hnonneg : 0 ≤ -traceForm X (controlMatrix u) *
      (M - hamiltonian lam Λ₁ ΛR X u) := by
    rw [hamiltonian_gap_eq_vertex_sum lam Λ₁ ΛR hX hu M]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg
      (mul_nonneg (hu.1 i).1 (neg_nonneg.mpr (singular_denominator_neg hX
        (singular_vertex_mem i)).le)) (sub_nonneg.mpr (hM i))
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hnonneg
    (neg_pos.mpr (singular_denominator_neg hX hu)))

/-- The maximum condition on the whole simplex is equivalent to its three
vertex comparisons; this statement does not require costate orthogonality. -/
theorem hamiltonian_isMax_iff_vertexwise (lam : ℝ) (Λ₁ ΛR : Mat2)
    {X : Mat2} (hX : IsStarState X) {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex) :
    (∀ v ∈ controlSimplex, hamiltonian lam Λ₁ ΛR X v ≤ hamiltonian lam Λ₁ ΛR X u) ↔
      ∀ i : Fin 3, hamiltonian lam Λ₁ ΛR X (vertex i) ≤ hamiltonian lam Λ₁ ΛR X u := by
  constructor
  · intro h i
    exact h _ (singular_vertex_mem i)
  · intro h v hv
    exact hamiltonian_le_of_vertex_le lam Λ₁ ΛR hX hv h

/-- Every positive coordinate of a maximizing control is supported on a vertex
whose Hamiltonian also attains the maximum. -/
theorem maximizing_control_support (lam : ℝ) (Λ₁ ΛR : Mat2)
    {X : Mat2} (hX : IsStarState X) {u : Fin 3 → ℝ} (hu : u ∈ controlSimplex)
    (hmax : ∀ v ∈ controlSimplex,
      hamiltonian lam Λ₁ ΛR X v ≤ hamiltonian lam Λ₁ ΛR X u)
    (i : Fin 3) (hui : 0 < u i) :
    hamiltonian lam Λ₁ ΛR X (vertex i) = hamiltonian lam Λ₁ ΛR X u := by
  let gap := fun j : Fin 3 ↦ u j * (-traceForm X (controlMatrix (vertex j))) *
    (hamiltonian lam Λ₁ ΛR X u - hamiltonian lam Λ₁ ΛR X (vertex j))
  have hgap : ∀ j, 0 ≤ gap j := by
    intro j
    exact mul_nonneg
      (mul_nonneg (hu.1 j).1 (neg_nonneg.mpr (singular_denominator_neg hX
        (singular_vertex_mem j)).le))
      (sub_nonneg.mpr (hmax _ (singular_vertex_mem j)))
  have hsum : ∑ j : Fin 3, gap j = 0 := by
    have h := hamiltonian_gap_eq_vertex_sum lam Λ₁ ΛR hX hu
      (hamiltonian lam Λ₁ ΛR X u)
    simpa [gap] using h.symm
  have hi := Finset.single_le_sum (fun j _ ↦ hgap j) (Finset.mem_univ i)
  rw [hsum] at hi
  have hi0 : gap i = 0 := le_antisymm hi (hgap i)
  have hpos : 0 < u i * (-traceForm X (controlMatrix (vertex i))) :=
    mul_pos hui (neg_pos.mpr (singular_denominator_neg hX (singular_vertex_mem i)))
  have heq := (mul_eq_zero.mp hi0).resolve_left hpos.ne'
  exact (sub_eq_zero.mp heq).symm

/-- **Lemma 8.2.1**, tested only at the three vertices. For a traceless reduced
costate perpendicular to the star state, a three-way Hamiltonian tie occurs
exactly when the reduced costate vanishes. -/
theorem hamiltonian_vertices_equal_iff_reducedCostate_eq_zero (lam : ℝ) (Λ₁ : Mat2)
    {ΛR X : Mat2} (hX : IsStarState X) (htr : ΛR.trace = 0)
    (hperp : traceForm ΛR X = 0) :
    (∀ i : Fin 3, hamiltonian lam Λ₁ ΛR X (vertex i) =
      hamiltonian lam Λ₁ ΛR X (vertex 0)) ↔ ΛR = 0 := by
  constructor
  · intro h
    let c := traceForm ΛR (controlMatrix (vertex 0)) /
      traceForm X (controlMatrix (vertex 0))
    have hratio : ∀ i : Fin 3, traceForm ΛR (controlMatrix (vertex i)) /
        traceForm X (controlMatrix (vertex i)) = c := by
      intro i
      have hi := h i
      simp only [hamiltonian] at hi
      dsimp [c]
      linarith
    have hmatch : ∀ i : Fin 3, traceForm ΛR (controlMatrix (vertex i)) =
        c * traceForm X (controlMatrix (vertex i)) := by
      intro i
      exact (div_eq_iff (singular_denominator_neg hX (singular_vertex_mem i)).ne).mp
        (hratio i)
    have hdiff : ΛR - c • X = 0 := by
      apply eq_zero_of_traceForm_control_vertices_eq_zero
      · simp [Matrix.trace_sub, Matrix.trace_smul, htr, hX.1]
      · intro i
        simp only [traceForm, Matrix.sub_mul, Matrix.smul_mul, Matrix.trace_sub,
          Matrix.trace_smul, smul_eq_mul]
        change traceForm ΛR (controlMatrix (vertex i)) -
          c * traceForm X (controlMatrix (vertex i)) = 0
        rw [hmatch i, sub_self]
    have hΛ : ΛR = c • X := sub_eq_zero.mp hdiff
    have hXX : traceForm X X = -2 := by
      rw [lemma3_4_1.1 X hX.1, hX.2.1]
      norm_num
    have horth : c * traceForm X X = 0 := by
      rw [hΛ] at hperp
      simpa only [traceForm, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] using hperp
    rw [hXX] at horth
    have hc : c = 0 := by linarith
    simpa [hc] using hΛ
  · rintro rfl i
    simp [hamiltonian, traceForm]

/-- **Lemma 8.2.1** for the full simplex. All state and reduced-costate
hypotheses are explicit; no extremal or minimizing property is assumed. -/
theorem hamiltonian_constant_on_simplex_iff_reducedCostate_eq_zero (lam : ℝ) (Λ₁ : Mat2)
    {ΛR X : Mat2} (hX : IsStarState X) (htr : ΛR.trace = 0)
    (hperp : traceForm ΛR X = 0) :
    (∀ u ∈ controlSimplex, ∀ v ∈ controlSimplex,
      hamiltonian lam Λ₁ ΛR X u = hamiltonian lam Λ₁ ΛR X v) ↔ ΛR = 0 := by
  constructor
  · intro h
    apply (hamiltonian_vertices_equal_iff_reducedCostate_eq_zero lam Λ₁ hX htr hperp).mp
    intro i
    exact h _ (singular_vertex_mem i) _ (singular_vertex_mem 0)
  · rintro rfl u _ v _
    simp [hamiltonian, traceForm]

/-- If the reduced costate is nonzero, one fixed simplex coordinate vanishes
at every maximizing control. Thus the maximizing face is contained in a proper
edge, with no possibility of a full-simplex maximizing face. -/
theorem hamiltonian_maximizers_in_proper_edge (lam : ℝ) (Λ₁ : Mat2)
    {ΛR X : Mat2} (hX : IsStarState X) (htr : ΛR.trace = 0)
    (hperp : traceForm ΛR X = 0) (hne : ΛR ≠ 0) :
    ∃ i : Fin 3, ∀ u ∈ controlSimplex,
      (∀ v ∈ controlSimplex,
        hamiltonian lam Λ₁ ΛR X v ≤ hamiltonian lam Λ₁ ΛR X u) → u i = 0 := by
  have hnot : ¬ ∀ i : Fin 3, hamiltonian lam Λ₁ ΛR X (vertex i) =
      hamiltonian lam Λ₁ ΛR X (vertex 0) := fun h ↦ hne
    ((hamiltonian_vertices_equal_iff_reducedCostate_eq_zero lam Λ₁ hX htr hperp).mp h)
  push_neg at hnot
  obtain ⟨i, hi⟩ := hnot
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · refine ⟨i, fun u hu hmax ↦ ?_⟩
    by_contra hui
    have hpos : 0 < u i := lt_of_le_of_ne (hu.1 i).1 (Ne.symm hui)
    have heq := maximizing_control_support lam Λ₁ ΛR hX hu hmax i hpos
    have hbound := hmax _ (singular_vertex_mem 0)
    linarith
  · refine ⟨0, fun u hu hmax ↦ ?_⟩
    by_contra hu0
    have hpos : 0 < u 0 := lt_of_le_of_ne (hu.1 0).1 (Ne.symm hu0)
    have heq := maximizing_control_support lam Λ₁ ΛR hX hu hmax 0 hpos
    have hbound := hmax _ (singular_vertex_mem i)
    linarith

end SmoothedOctagon
