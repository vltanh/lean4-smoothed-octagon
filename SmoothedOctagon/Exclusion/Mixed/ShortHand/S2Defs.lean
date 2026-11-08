module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs02.Common

/-!
# Gate S2: definitions

The two incoming ceilings of gate S2, kept apart from `S2.lean` so that the modules
`Heavy/S2*.lean` can state their signs with them and `S2.lean` can import those modules.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The central ceiling `u_C(x, β) = 3/4 + (680(x - 1)³ + 3S²(β - x))/(9600S²(β - 1))`,
`S = 1 + x`. -/
noncomputable def hsUC (x be : ℝ) : ℝ :=
  3 / 4 + (680 * (x - 1) ^ 3 + 3 * (1 + x) ^ 2 * (be - x)) / (9600 * (1 + x) ^ 2 * (be - 1))

/-- The outer ceiling `u_s(x, β) = 3/4 + (17(x - 1)³/(240S²) + (β - x)/1200)/(β - 1)`,
`S = 1 + x`. -/
noncomputable def hsUs (x be : ℝ) : ℝ :=
  3 / 4 + (17 * (x - 1) ^ 3 / (240 * (1 + x) ^ 2) + (be - x) / 1200) / (be - 1)

end SmoothedOctagon
