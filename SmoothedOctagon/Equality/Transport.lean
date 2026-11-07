module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.LowerBound

/-!
# The equality case

`GLOBAL_COST_EQUALITY_ASSEMBLY` §6 and `MINIMIZER_WINDOW_AUDIT` §6.

* A worst disk is a linear image of the smoothed octagon. Normalize the worst disk, realize it by
  its own boundary trajectory (a global control minimizer by the reverse comparison), rebase and
  relabel it to the octagon's trajectory by the terminal equality, and transport the six contact
  arcs back: `K = e⁻¹ G(s) C (K_oct)`.

The converse (every invertible linear image of the octagon has density `δ_oct`) is in
`Equality/Converse.lean`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons

/-- **Rigidity.** Every worst disk is an invertible linear image of the smoothed octagon. -/
theorem worstDisk_eq_linear_image (h502 : Cited.HalesVajjha.Theorem5_0_2)
    (hcov : Certificates.IntervalCovers) : AffineRigidity := by
  sorry

end SmoothedOctagon
