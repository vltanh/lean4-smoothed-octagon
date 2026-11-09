module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Interface
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Angle
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.ExactConcavity
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.CentralShear

/-!
# Smaller-short window, cost: definitions

The scalar functions of the cost bound, kept apart from `SmallerShort/Cost` so that the modules
of `SmallerShort/Cost/` can state their signs with them.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real SmallerShort

/-! ### Central-scale objects -/

/-- `J₀ = 3u/(2U₁)`, `U₁ = U(r) = (x² + x + 1)/(1 + x)²`. -/
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

/-- `L(z) = z/162 + 161z³/1458 - 161z⁵/7290`. -/
noncomputable def costL (z : ℝ) : ℝ := z / 162 + 161 * z ^ 3 / 1458 - 161 * z ^ 5 / 7290

/-- The quadratic incoming floor `u_q = 3/4 + H_R/(15(2 + R)³)·{R² - R(1 + R)d/2 +
19(1 + R)²d²/84}`, `H_R = 3R² + 10R + 10`. -/
noncomputable def costuq (R d : ℝ) : ℝ :=
  3 / 4 + (3 * R ^ 2 + 10 * R + 10) / (15 * (2 + R) ^ 3) *
    (R ^ 2 - R * (1 + R) * d / 2 + 19 * (1 + R) ^ 2 * d ^ 2 / 84)

/-- `Z_U = 2R²(1 + R)/(3 - R) + (1 + 2R)d/(3(1 - R)) - 3d²/2`. -/
noncomputable def costZU (R d : ℝ) : ℝ :=
  2 * R ^ 2 * (1 + R) / (3 - R) + (1 + 2 * R) / (3 * (1 - R)) * d - 3 / 2 * d ^ 2

/-- `Z_L = (2R²(1 + R)/(3 - R))(1 + 11d/2)`. -/
noncomputable def costZL (R d : ℝ) : ℝ := 2 * R ^ 2 * (1 + R) / (3 - R) * (1 + 11 * d / 2)

/-- **The polynomial bound** `𝓑(u; R, T, d) = L(R) + L(T) - (b₁R + b₂T)/2 - (b₁ + b₂)Z_U/8 -
cA²/(8Z_L)` with `U₁ = (3 + R²)/4`, `U₂ = (3 + T²)/4`, `b_i = 1 - u/U_i`, `A = U₁/U₂ - 1`. -/
noncomputable def costB (R T d u : ℝ) : ℝ :=
  costL R + costL T - ((1 - u / ((3 + R ^ 2) / 4)) * R + (1 - u / ((3 + T ^ 2) / 4)) * T) / 2 -
    ((1 - u / ((3 + R ^ 2) / 4)) + (1 - u / ((3 + T ^ 2) / 4))) * costZU R d / 8 -
    161 / 54 * ((3 + R ^ 2) / (3 + T ^ 2) - 1) ^ 2 / (8 * costZL R d)

/-- `T_s` at `α = 1 + ed`, `β = x(1 + d)`, `x = (1 + R)/(1 - R)`:
`T = (2R + ((e + 1)R - (e - 1))d)/(2 + (e + 1 - (e - 1)R)d)`. -/
noncomputable def costT (R d e : ℝ) : ℝ :=
  (2 * R + ((e + 1) * R - (e - 1)) * d) / (2 + (e + 1 - (e - 1) * R) * d)

/-- `b* = (A₀ - cπ₀/3 + 1/800000)/ℓ = 792669623/356040000000`. -/
noncomputable def costbstar : ℝ := 792669623 / 356040000000

end SmoothedOctagon
