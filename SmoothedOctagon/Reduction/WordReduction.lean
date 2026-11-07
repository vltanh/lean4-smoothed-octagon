module

public import SmoothedOctagon.Reduction.Defs

/-!
# Reduced vertex words: merging, and rebasing at a genuine switch

VERTEX_WORD_REDUCTION §2 and SWITCHING_WORDS (inventory A2, §1.6 "word", §2.1, §2.9 (2)).
A control that is a.e. a concatenation of `n` vertex pieces on `[0, T]` has, after extending it
by the twist (labels go up by one per period), deleting nothing (all pieces have positive length)
and merging equal neighbours, also across the twisted seam, a cyclically reduced word with
`1 ≤ N ≤ n` letters per period. Rebased at one of its genuine switches, the control has a
`VertexRepresentation` with `N` pieces.

Route: no optimality and no PMP is used. In particular the existence of a genuine switch does not
need SWITCHING_WORDS (fixed-edge exclusion): the twist adds `+1` to the labels per period, so the
increments `i_{k+1} - i_k` of one period sum to `1 ≠ 0` in `ℤ/3`, and some increment is nonzero.
Nor is `N ≥ 4` (VERTEX_WORD_REDUCTION, Theorem 3) needed by the target.

Main API:

* `exists_rebase_vertexRepresentation`: rebasing at a genuine switch gives a vertex
  representation with at most `n` pieces.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

/-- **Merging and rebasing at a genuine switch** (VERTEX_WORD_REDUCTION §2; inventory A2, §2.9 (2)).
If on `[0, T]` the control is a.e. a concatenation of `n` vertex pieces, there is a time
`s ∈ [0, T)` such that the rebased control `û(t) = v(s + t)` (twisted extension `v`) has a vertex
representation (distinct neighbouring labels, also across the twisted seam) with at most `n`
pieces.

Proof outline: extend the pieces to a bi-infinite sequence by the twist, `τ_{k+n} = τ_k + T`,
`l_{k+n} = l_k + 1`. The boundaries `τ_k` with `l_k ≠ l_{k-1}` (genuine switches) form a set that
is invariant under `+T` and nonempty (the increments of one period sum to `1` in `ℤ/3`), so one,
`s`, lies in `[0, T)`. Take as `τ̂` the genuine switches after `s`, shifted by `-s`, and as labels
the common labels of the merged runs; there are `N ≤ n` of them per period, neighbours differ, and
`û = e_{label}` a.e. on each merged piece (a finite union of the original pieces up to their
endpoints, a null set). -/
theorem exists_rebase_vertexRepresentation {T : ℝ} (hT : 0 < T) {u : ℝ → Fin 3 → ℝ} {n : ℕ}
    (hu : IsPiecewiseVertex u 0 T n) :
    ∃ s : ℝ, 0 ≤ s ∧ s < T ∧ ∃ ρ : VertexRepresentation T (rebaseControl T u s), ρ.N ≤ n := by
  sorry

end SmoothedOctagon.Reduction
