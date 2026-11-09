module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.FaceValue

/-!
# Smaller-short window, upper ratio: definitions

The two incoming ceilings of the upper-ratio bound, kept apart from `SmallerShort/UpperRatio` so
that the modules of `SmallerShort/UpperRatio/` can state their signs with them.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The central ceiling `u_C(x, β) = 3/4 + (680(x - 1)³ + 3S²(β - x))/(9600S²(β - 1))`,
`S = 1 + x`. -/
noncomputable def ssUC (x be : ℝ) : ℝ :=
  3 / 4 + (680 * (x - 1) ^ 3 + 3 * (1 + x) ^ 2 * (be - x)) / (9600 * (1 + x) ^ 2 * (be - 1))

/-- The outer ceiling `u_s(x, β) = 3/4 + (17(x - 1)³/(240S²) + (β - x)/1200)/(β - 1)`,
`S = 1 + x`. -/
noncomputable def ssUs (x be : ℝ) : ℝ :=
  3 / 4 + (17 * (x - 1) ^ 3 / (240 * (1 + x) ^ 2) + (be - x) / 1200) / (be - 1)

end SmoothedOctagon
