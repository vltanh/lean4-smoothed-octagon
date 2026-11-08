module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs6.Angle
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs6.Concave
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs6.Shear

/-!
# Gate S6: definitions

The scalar functions of gate S6, kept apart from `S6.lean` so that the certificate modules
`Heavy/S6*.lean` can state their signs with them and `S6.lean` can import those certificates.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real Certificates.SmallerShort

/-! ### Central-scale objects -/

/-- `J₀ = 3u/(2U₁)`, `U₁ = U(r) = (x² + x + 1)/(1 + x)²` (`SHEAR_COST_REDUCTION` §2). -/
noncomputable def hs6J0 (x u : ℝ) : ℝ := 3 * u / (2 * m2U (1 / (1 + x)))

/-- `K = A + 2 + 2κ₀/J₀`, `κ₀ = 40/27` (`SHEAR_COST_REDUCTION` (8)). -/
noncomputable def hs6K (x be al u : ℝ) : ℝ := hsAn x be al + 2 + 2 * (40 / 27) / hs6J0 x u

/-- The fixed lower-row angle `ψ = arctan(R/√3) + arctan(T_s/√3)` (`SCALE_ANGLE_BARRIER` §3). -/
noncomputable def hs6psi (x be al : ℝ) : ℝ := arctan (hsRr x / √3) + arctan (hsTs al be / √3)

/-- `Z = 2U₁Q₀/(x(x + 2)) - R - (1 + A)T_s = -√3 h_c`, `Q₀ = 2βx - x - αβ`
(`CENTRAL_COST_SHAPE_BOUNDS` (2)). -/
noncomputable def hs6Z (x be al : ℝ) : ℝ :=
  2 * m2U (1 / (1 + x)) * (2 * be * x - x - al * be) / (x * (x + 2)) - hsRr x -
    (1 + hsAn x be al) * hsTs al be

/-- The central angle `ω_c = 2 arctan((√(H² + A²) + H)/(K + √(K² - A²)))`, `H = Z/√3`
(`SHEAR_COST_REDUCTION` (9) at `h = h_c`; `SMALL_SHAPE_COST_EXCLUSION` (4)). -/
noncomputable def hs6omega (x be al u : ℝ) : ℝ :=
  2 * arctan ((√((hs6Z x be al / √3) ^ 2 + hsAn x be al ^ 2) + hs6Z x be al / √3) /
    (hs6K x be al u + √(hs6K x be al u ^ 2 - hsAn x be al ^ 2)))

/-- The central-scale window cost `C_c = √3{uQ₀/(x(x + 2)) + (R + T_s)/2}`
(`SMALL_SHAPE_COST_EXCLUSION` (5)). -/
noncomputable def hs6Cc (x be al u : ℝ) : ℝ :=
  √3 * (u * (2 * be * x - x - al * be) / (x * (x + 2)) + (hsRr x + hsTs al be) / 2)

/-- **The central-scale score** `𝓕_c = C_c + c(π/3 - ψ - ω_c)`, `c = κ₀ + 3/2 = 161/54`
(`SMALL_SHAPE_COST_EXCLUSION` (5)). -/
noncomputable def hs6Fc (x be al u : ℝ) : ℝ :=
  hs6Cc x be al u + 161 / 54 * (π / 3 - hs6psi x be al - hs6omega x be al u)

/-- `L(z) = z/162 + 161z³/1458 - 161z⁵/7290` (`SMALL_SHAPE_COST_EXCLUSION` (13)). -/
noncomputable def hs6L (z : ℝ) : ℝ := z / 162 + 161 * z ^ 3 / 1458 - 161 * z ^ 5 / 7290

/-- The quadratic incoming floor `u_q = 3/4 + H_R/(15(2 + R)³)·{R² - R(1 + R)d/2 +
19(1 + R)²d²/84}`, `H_R = 3R² + 10R + 10` (`CENTRAL_COST_SHAPE_BOUNDS` (6)). -/
noncomputable def hs6uq (R d : ℝ) : ℝ :=
  3 / 4 + (3 * R ^ 2 + 10 * R + 10) / (15 * (2 + R) ^ 3) *
    (R ^ 2 - R * (1 + R) * d / 2 + 19 * (1 + R) ^ 2 * d ^ 2 / 84)

/-- `Z_U = 2R²(1 + R)/(3 - R) + (1 + 2R)d/(3(1 - R)) - 3d²/2` (`SMALL_SHAPE_COST_EXCLUSION` (12)). -/
noncomputable def hs6ZU (R d : ℝ) : ℝ :=
  2 * R ^ 2 * (1 + R) / (3 - R) + (1 + 2 * R) / (3 * (1 - R)) * d - 3 / 2 * d ^ 2

/-- `Z_L = (2R²(1 + R)/(3 - R))(1 + 11d/2)` (`SMALL_SHAPE_COST_EXCLUSION` (12)). -/
noncomputable def hs6ZL (R d : ℝ) : ℝ := 2 * R ^ 2 * (1 + R) / (3 - R) * (1 + 11 * d / 2)

/-- **The polynomial bound** `𝓑(u; R, T, d) = L(R) + L(T) - (b₁R + b₂T)/2 - (b₁ + b₂)Z_U/8 -
cA²/(8Z_L)` with `U₁ = (3 + R²)/4`, `U₂ = (3 + T²)/4`, `b_i = 1 - u/U_i`, `A = U₁/U₂ - 1`
(`SMALL_SHAPE_COST_EXCLUSION` (15)). -/
noncomputable def hs6B (R T d u : ℝ) : ℝ :=
  hs6L R + hs6L T - ((1 - u / ((3 + R ^ 2) / 4)) * R + (1 - u / ((3 + T ^ 2) / 4)) * T) / 2 -
    ((1 - u / ((3 + R ^ 2) / 4)) + (1 - u / ((3 + T ^ 2) / 4))) * hs6ZU R d / 8 -
    161 / 54 * ((3 + R ^ 2) / (3 + T ^ 2) - 1) ^ 2 / (8 * hs6ZL R d)

/-- `T_s` at `α = 1 + ed`, `β = x(1 + d)`, `x = (1 + R)/(1 - R)`:
`T = (2R + ((e + 1)R - (e - 1))d)/(2 + (e + 1 - (e - 1)R)d)` (`SMALL_SHAPE_COST_EXCLUSION` (21)). -/
noncomputable def hs6T (R d e : ℝ) : ℝ :=
  (2 * R + ((e + 1) * R - (e - 1)) * d) / (2 + (e + 1 - (e - 1) * R) * d)

/-- `b* = (A₀ - cπ₀/3 + 1/800000)/ℓ = 792669623/356040000000` (`SMALL_SHAPE_COST_EXCLUSION` (20)). -/
noncomputable def hs6bstar : ℝ := 792669623 / 356040000000

end SmoothedOctagon
