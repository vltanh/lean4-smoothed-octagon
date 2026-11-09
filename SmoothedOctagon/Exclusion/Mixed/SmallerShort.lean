module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Displacement
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost

/-!
# Case M2: the smaller-short window

The smaller-short window is excluded by seven bounds on its normalized data, each proved from the
previous ones (the modules `SmallerShort/LargeRatio`, …, `SmallerShort/Cost`):
the large ratio `x < 12/5`; the lower ratio `x > 2`; the upper ratio `x < 13/6`; the displacement
`δ < 1/19`; the upper order `α ≤ 1 + 3δ` and the Casimir floor `Γ > 1829/10000`. The strong order
gives `α ≥ 1 + 13δ/5`, so the window lies in the common small-shape domain
(`SmallerShortData.SmallShape`); there the root forces a negative physical shear with
`-hR > 5A/2`, and then the window cost plus completion exceeds `A_oct`, contradicting the
window-defect inequality (`M2Short.defect`).

## Main API

* `m2_smallerShort_exclusion`: no smaller-short window exists.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The smaller-short window is excluded**: the seven bounds applied in order, and the
window-defect inequality. -/
theorem m2_smallerShort_exclusion (D : M2Short) : False := by
  obtain ⟨h0, -, -⟩ := D.ratio_lt_twelve_fifths
  have h1 := D.two_lt_ratio
  have h2 := D.ratio_lt_thirteen_sixths h0
  have h3 := D.displacement_lt h1.le h2.le
  have hδ : 0 ≤ D.B / D.C - 1 := D.ss_box_delta.1
  obtain ⟨hU, hΓ⟩ := D.upper_order_casimir_floor h1.le h2.le h3.le
  have hL := D.ss_strong_box h1.le
  obtain ⟨-, -, hh, hhR⟩ := D.shear_neg h1.le h2.le hδ h3.le hL hU
  have h6 := D.octagonCost_lt_completion h1.le h2.le hδ h3.le hL hU hΓ hh hhR
  exact absurd D.ss_defect.2.2.2.2 (not_le.2 h6)

end SmoothedOctagon
