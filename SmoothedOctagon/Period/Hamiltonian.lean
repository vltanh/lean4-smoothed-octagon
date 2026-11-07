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

open SmoothedPolygons Set

/-- The vertex Hamiltonians of an extremal are continuous on `[0, T]`. -/
theorem IsPontryaginExtremal.continuousOn_vertexHamiltonian {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) (i : Fin 3) :
    ContinuousOn (fun t ↦ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex i)) (Icc 0 T) := by
  sorry

/-- **The maximum condition at every time.** For an extremal, at every `t ∈ [0, T]` every vertex
Hamiltonian is `≤ 0` and one of them vanishes. -/
theorem IsPontryaginExtremal.vertexHamiltonian_max_eq_zero {T : ℝ} {u : ℝ → Fin 3 → ℝ}
    {g X Λ₁ ΛR : ℝ → Mat2} {lam : ℝ} (h : IsPontryaginExtremal T u g X Λ₁ ΛR lam) :
    ∀ t ∈ Icc 0 T, (∀ i, hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex i) ≤ 0) ∧
      ∃ i, hamiltonian lam (Λ₁ t) (ΛR t) (X t) (vertex i) = 0 := by
  sorry

end SmoothedOctagon
