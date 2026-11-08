module

public import SmoothedOctagon.Exclusion.Mixed.Window

/-!
# Case M2: the smaller-short window and its six-variable cover

`MIXED_SMALLER_SHORT_PERIOD_EXCLUSION` and `MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION`
(inventory E1, R1-R29). The actual data of a smaller-short window (`M2Short`) give the point
`(r, δ, α, ρ, v, E) = (a/(a + C), B/C - 1, A/a, a²/(a² + 4), v, E)` of the root box
`B₀ = [1/10, 1/2] × [0, 2] × [1, 631/100] × [1/226, 3/20] × [3/4, 1] × [-23/16, 9/20]` at which
all 28 residuals `f₀, …, f₂₇` of the cover are nonnegative (E1 §3.1, "necessity" column), which
`CertSmallerShort` excludes.

## Main API

* `m2_short_point`: the actual point lies in `B₀` and satisfies every residual (E1 R1-R27: the
  continuation path and the strengthened order (S) (R4-R8), the convex-chord bound `R̄` (R9), the
  outer root (R10), `E_L < 3ρ_A` (R11), the opposite-turn elimination (R20), the root box (R22),
  the Gram transport (R24) and the defect inequality in its centred form (R27 (iii))).
* `m2_short_exclusion`: no smaller-short window exists (given the cover).
-/

@[expose] public section

namespace SmoothedOctagon

open Certificates

/-- **The six-variable reduction** (`MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION` §§1-6, inventory
E1 R1-R27): the actual point of a smaller-short window lies in the root box `B₀` and every residual
of the cover is nonnegative there. -/
theorem m2_short_point (D : M2Short) :
    D.a / (D.a + D.C) ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) ∧ D.B / D.C - 1 ∈ Set.Icc (0 : ℝ) 2 ∧
      D.A / D.a ∈ Set.Icc (1 : ℝ) (631 / 100) ∧
      D.a ^ 2 / (D.a ^ 2 + 4) ∈ Set.Icc (1 / 226 : ℝ) (3 / 20) ∧ D.v ∈ Set.Icc (3 / 4 : ℝ) 1 ∧
      D.E ∈ Set.Icc (-23 / 16 : ℝ) (9 / 20) ∧
      (⟨D.a / (D.a + D.C), D.B / D.C - 1, D.A / D.a, D.a ^ 2 / (D.a ^ 2 + 4), D.v, D.E⟩ :
        SmallerShort.Point).AllResidualsNonneg := by
  sorry

/-- **The smaller-short window is excluded** (`MIXED_SMALLER_SHORT_PERIOD_EXCLUSION`). -/
theorem m2_short_exclusion (hcert : CertSmallerShort) (D : M2Short) : False := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := m2_short_point D
  exact hcert _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7

end SmoothedOctagon
