module

public import SmoothedOctagon.Foundations.Problem

/-!
# Every linear image of the smoothed octagon packs as badly

An invertible linear map carries lattice packings to lattice packings and scales area and
covolume by the same factor, so it preserves the greatest lattice packing density; Fejes Tóth's
theorem identifies lattice and general packing densities for centrally symmetric convex disks
(`GLOBAL_COST_EQUALITY_ASSEMBLY` §6). Orientation-reversing maps are covered too: congruent copies
include reflections.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons

/-- **The converse.** Every invertible linear image of the smoothed octagon has greatest packing
density `δ_oct`. -/
theorem greatestPackingDensity_linear_image_octagon (A : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ)) :
    greatestPackingDensity (A '' octagon) = octagonDensity := by
  sorry

end SmoothedOctagon
