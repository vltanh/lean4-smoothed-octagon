module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Interface
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Angle
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.ExactConcavity
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.CentralShear
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.VarianceFloor

/-!
# S6: physical central quantities and exact comparison coordinates
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set MeasureTheory

noncomputable def costJ0 (x u : ℝ) : ℝ := 3 * u / (2 * m2U (1 / (1 + x)))

/-- `K = A + 2 + 2κ₀/J₀`, `κ₀ = 40/27`. -/
noncomputable def costK (x be al u : ℝ) : ℝ := ssAn x be al + 2 + 2 * (40 / 27) / costJ0 x u

/-- The fixed lower-row angle `ψ = arctan(R/√3) + arctan(T_s/√3)`. -/
noncomputable def costpsi (x be al : ℝ) : ℝ := arctan (ssRr x / √3) + arctan (ssTs al be / √3)

/-- `Z = 2U₁Q₀/(x(x + 2)) - R - (1 + A)T_s = -√3 h_c`, `Q₀ = 2βx - x - αβ`. -/
noncomputable def costZ (x be al : ℝ) : ℝ :=
  2 * m2U (1 / (1 + x)) * (2 * be * x - x - al * be) / (x * (x + 2)) - ssRr x -
    (1 + ssAn x be al) * ssTs al be

/-- The central angle `ω_c = 2 arctan((√(H² + A²) + H)/(K + √(K² - A²)))`, `H = Z/√3`
(the angle `δ(h)` of the tangent curve at the central shear `h = h_c = -H`). -/
noncomputable def costomega (x be al u : ℝ) : ℝ :=
  2 * arctan ((√((costZ x be al / √3) ^ 2 + ssAn x be al ^ 2) + costZ x be al / √3) /
    (costK x be al u + √(costK x be al u ^ 2 - ssAn x be al ^ 2)))

/-- The central-scale window cost `C_c = √3{uQ₀/(x(x + 2)) + (R + T_s)/2}`. -/
noncomputable def costCc (x be al u : ℝ) : ℝ :=
  √3 * (u * (2 * be * x - x - al * be) / (x * (x + 2)) + (ssRr x + ssTs al be) / 2)

/-- **The central-scale score** `𝓕_c = C_c + c(π/3 - ψ - ω_c)`, `c = κ₀ + 3/2 = 161/54`. -/
noncomputable def costFc (x be al u : ℝ) : ℝ :=
  costCc x be al u + 161 / 54 * (π / 3 - costpsi x be al - costomega x be al u)

noncomputable def costZU (R d : ℝ) : ℝ :=
  2 * R ^ 2 * (1 + R) / (3 - R) + (1 + 2 * R) / (3 * (1 - R)) * d - 3 / 2 * d ^ 2

/-- `Z_L = (2R²(1 + R)/(3 - R))(1 + 11d/2)`. -/
noncomputable def costZL (R d : ℝ) : ℝ := 2 * R ^ 2 * (1 + R) / (3 - R) * (1 + 11 * d / 2)

noncomputable def costT (R d e : ℝ) : ℝ :=
  (2 * R + ((e + 1) * R - (e - 1)) * d) / (2 + (e + 1 - (e - 1) * R) * d)

end SmoothedOctagon
