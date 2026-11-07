module

public import SmoothedOctagon.Foundations.Problem

/-!
# The smoothed octagon in the vocabulary of `Challenge.lean`

`Challenge.lean` writes the density of the smoothed octagon as `(8 - 4√2 - log 2)/(2√2 - 1)` and
the octagon as the convex hull of the six arcs `g([0, t_f]) s_j` of its trajectory. This module
identifies both with the library's `octagonDensity` and `octagon`.

For the hull: the trajectory is unique (`polygon_trajectory_unique`), so `g = smoothedPolygonG 1`
on `[0, t_f]` and the arcs are `σ_j([0, t_f])`. Each lies in `frontier K`
(`smoothedPolygonDisk_isBalancedPair`), and since `σ₀(s + n t_f) = σ_n(s)` they cover
`frontier K = σ₀([0, 6 t_f))`. Every point
`r σ₀(t)`, `0 ≤ r ≤ 1`, of `K` lies on the segment between the boundary points `±σ₀(t)`, so
`K` is the convex hull of its frontier.

## Main API

* `bridge_octagonDensity_eq`: `(8 - 4√2 - log 2)/(2√2 - 1) = octagonDensity`.
* `bridge_curve_mem_frontier`: `σ_j(t) ∈ frontier octagon`.
* `bridge_frontier_octagon_subset`: `frontier octagon ⊆ ⋃ j, σ_j([0, t_f])`.
* `bridge_octagon_subset_convexHull_frontier`: `octagon ⊆ convexHull (frontier octagon)`.
* `bridge_convexHull_arcs`: for every octagon trajectory `g`,
  `convexHull (⋃ j, g([0, t_f]) s_j) = octagon`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set

/-- The constant of `Challenge.lean` is `δ_oct`: `√32 = 4√2` and `√8 = 2√2`. -/
theorem bridge_octagonDensity_eq :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) = octagonDensity := by
  rw [octagonDensity, poly_sqrt32, poly_sqrt8]

/-- Every point of every arc `σ_j` lies on the boundary of the octagon. -/
theorem bridge_curve_mem_frontier (j : ZMod 6) (t : ℝ) :
    smoothedPolygonCurve 1 j t ∈ frontier octagon := by
  have hP := oct_P_pos (k := 1) le_rfl
  rw [octagon, ← oct_curve_image le_rfl j, ← oct_periodic_red (oct_curve_periodic le_rfl j) t]
  exact mem_image_of_mem _ (oct_red_mem hP t)

/-- The six arcs `σ_j([0, t_f])` cover the boundary of the octagon. -/
theorem bridge_frontier_octagon_subset :
    frontier octagon ⊆ ⋃ j : ZMod 6, smoothedPolygonCurve 1 j '' Icc 0 (tf 1) := by
  have htf : 0 < tf 1 := oct_tf_pos le_rfl
  intro p hp
  rw [octagon, ← oct_curve_image le_rfl 0] at hp
  obtain ⟨t, ⟨ht0, -⟩, rfl⟩ := hp
  set n := ⌊t / tf 1⌋₊
  have h1 : (n : ℝ) * tf 1 ≤ t := by
    have := Nat.floor_le (div_nonneg ht0 htf.le)
    rwa [le_div_iff₀ htf] at this
  have h2 : t < (n + 1) * tf 1 := by
    have := Nat.lt_floor_add_one (t / tf 1)
    rwa [div_lt_iff₀ htf] at this
  refine mem_iUnion.2 ⟨(n : ZMod 6), t - n * tf 1, ⟨by linarith, by linarith⟩, ?_⟩
  rw [← oct_curve_add_nat_tf le_rfl n, sub_add_cancel]

/-- The octagon is the convex hull of its boundary: `r σ₀(t)` lies between `σ₀(t)` and
`-σ₀(t)`. -/
theorem bridge_octagon_subset_convexHull_frontier :
    octagon ⊆ convexHull ℝ (frontier octagon) := by
  intro x hx
  obtain ⟨t, -, r, ⟨hr0, hr1⟩, rfl⟩ := hx
  have hp := bridge_curve_mem_frontier 0 t
  have hnp := bdy_neg_mem_frontier octagon_isCCSDisk hp
  have hmem := convex_convexHull ℝ (frontier octagon) (subset_convexHull ℝ _ hp)
    (subset_convexHull ℝ _ hnp) (a := (1 + r) / 2) (b := (1 - r) / 2) (by linarith)
    (by linarith) (by ring)
  convert hmem using 1
  rw [smul_neg, ← sub_eq_add_neg, ← sub_smul]
  congr 1
  ring

/-- **The octagon is the convex hull of the six arcs of its trajectory.** -/
theorem bridge_convexHull_arcs (g X : ℝ → Mat2)
    (h : IsStateTrajectory (tf 1) (polygonControl 1) g X) (hg0 : g 0 = 1)
    (hX0 : X 0 = Φ 0 (y₀ 1)) :
    convexHull ℝ (⋃ j : ZMod 6, (fun t ↦ Matrix.mulVec (g t) (sixthRoot j)) '' Icc 0 (tf 1)) =
      octagon := by
  have hS : (⋃ j : ZMod 6, (fun t ↦ Matrix.mulVec (g t) (sixthRoot j)) '' Icc 0 (tf 1)) =
      ⋃ j : ZMod 6, smoothedPolygonCurve 1 j '' Icc 0 (tf 1) := by
    refine iUnion_congr fun j ↦ image_congr fun t ht ↦ ?_
    rw [smoothedPolygonCurve, oct_G_of_nonneg le_rfl ht.1,
      (polygon_trajectory_unique 1 le_rfl g X h hg0 hX0 t ht).1]
  rw [hS]
  refine Subset.antisymm (convexHull_min ?_ octagon_isCCSDisk.1)
    (bridge_octagon_subset_convexHull_frontier.trans
      (convexHull_mono bridge_frontier_octagon_subset))
  refine iUnion_subset fun j ↦ ?_
  rintro _ ⟨t, -, rfl⟩
  exact frontier_subset_iff_isClosed.2 octagon_isCCSDisk.2.1.isClosed
    (bridge_curve_mem_frontier j t)

end SmoothedOctagon
