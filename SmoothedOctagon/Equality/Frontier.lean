module

public import SmoothedOctagon.Foundations.Problem

/-!
# A centrally symmetric convex disk is determined by its frontier

`MINIMIZER_WINDOW_AUDIT` §6 and `GLOBAL_COST_EQUALITY_ASSEMBLY` §6 transport the boundary arcs of
the octagon to the boundary of the normalized worst disk and conclude equality of the disks.

## Main API

* `eq_disk_eq_of_frontier_eq`: two centrally symmetric convex disks with the same frontier are
  equal.

Route: instead of the radial hull of the frontier, the interior of each disk is a connected set
avoiding the common frontier and containing the origin, so the interiors agree; a convex body is the
closure of its interior.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set

/-- If two centrally symmetric convex disks share their frontier, the interior of the second lies
in the interior of the first. -/
private theorem interior_subset_of_frontier_eq {A B : Set (Fin 2 → ℝ)} (hA : IsCCSDisk A)
    (hB : IsCCSDisk B) (h : frontier A = frontier B) : interior B ⊆ interior A := by
  have hconn : IsPreconnected (interior B) := hB.1.interior.isPreconnected
  have hsub : interior B ⊆ interior A ∪ (closure A)ᶜ := by
    intro x hx
    by_cases hxA : x ∈ closure A
    · left
      by_contra hxi
      have hfr : x ∈ frontier A := ⟨hxA, hxi⟩
      rw [h] at hfr
      exact hfr.2 hx
    · exact Or.inr hxA
  rcases hconn.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset_closure) hsub with h1 | h1
  · exact h1
  · exact absurd (interior_subset_closure (bdy_zero_mem_interior hA))
      (h1 (bdy_zero_mem_interior hB))

/-- **A centrally symmetric convex disk is determined by its frontier.** -/
theorem eq_disk_eq_of_frontier_eq {A B : Set (Fin 2 → ℝ)} (hA : IsCCSDisk A) (hB : IsCCSDisk B)
    (h : frontier A = frontier B) : A = B := by
  have hint : interior A = interior B :=
    (interior_subset_of_frontier_eq hB hA h.symm).antisymm
      (interior_subset_of_frontier_eq hA hB h)
  rw [← hA.2.1.isClosed.closure_eq, ← hB.2.1.isClosed.closure_eq,
    ← hA.1.closure_interior_eq_closure_of_nonempty_interior hA.2.2.1,
    ← hB.1.closure_interior_eq_closure_of_nonempty_interior hB.2.2.1, hint]

end SmoothedOctagon
