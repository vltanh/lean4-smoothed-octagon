module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface

/-!
# Hand proof of the smaller-short case, gate S6: the completion cost is too large

`MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION` (1)-(31), with `SHEAR_COST_REDUCTION`,
`ROOT_AND_ANGLE_REDUCTION` §§3-5, `SCALE_ANGLE_BARRIER` §§4-5, `CENTRAL_COST_SHAPE_BOUNDS`;
inventory HS-S567 Part III (SH.1-SH.5, AC.1, AB1, AB2, AL, CS.1-CS.3, SB.1-SB.3, S6.1-S6.8), on its
recommended route (no critical-angle classification; the barrier is applied pointwise along the
continuation in the angle `δ`). On the small-shape domain with `Γ > 1829/10000`, `h < 0`,
`-hR > 5A/2`: the window cost plus completion `C_br + (κ + 3/2)(π/3 - θ_br)` is at least the
central-scale score `𝓕_c` (`HsData.hs6_continuation`), `𝓕_c > cπ/3 + √3𝓑(u_q) - 1/800000`
(`hs6_Fc_gt`), `𝓑(u_q) > b*` (`hs6_B_concave`, `hs6_B_endpoint`, heavy), and the constants
(`hs6_constants`) give `> A_oct`, contradicting the window defect.

## Main API

* Central-scale objects: `hs6J0`, `hs6K`, `hs6psi`, `hs6Z`, `hs6omega`, `hs6Cc`, `hs6Fc`; the
  polynomial bound `hs6B` with `hs6uq`, `hs6ZU`, `hs6ZL`, `hs6T`, `hs6L`; `hs6bstar`.
* Stable scalar leaves: `hs6_kappa`, `hs6_shape`, `hs6_u_bounds`, `hs6_central_shear`,
  `hs6_tangent_inv`, `hs6_tangent_anti`, `hs6_score_deriv`, `hs6_barrier_sin`, `hs6_barrier`,
  `hs6_Fc_gt`, `hs6_T_eq`, `hs6_B_concave`, `hs6_constants`.
* Stable actual-data leaves: `HsData.hs6_angle` (AL), `HsData.hs6_continuation` (S6.2).
* Heavy: `hs6_B_endpoint` (`SMALL_SHAPE_COST_EXCLUSION` (20)-(31)).
* Gate: `HsData.s6`, `M2Short.hs_S6`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

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

/-! ### Scalar leaves -/

/-- **Lowering `κ`** (`SMALL_SHAPE_COST_EXCLUSION` §2; inventory HS-S567 S6.1):
`12·1829/10000 - (40/27)² = 23/1822500 > 0`, so `Γ > 1829/10000 ⇒ √(12Γ) > 40/27`.
Status: stable. -/
theorem hs6_kappa {Γ : ℝ} (hΓ : 1829 / 10000 < Γ) : 40 / 27 < √(12 * Γ) := by
  sorry

/-- **The angle coordinates** (`CENTRAL_COST_SHAPE_BOUNDS` (3)-(4); inventory HS-S567 CS.1): on
`2 ≤ x ≤ 13/6`, `0 ≤ δ ≤ 1/19`, `13δ/5 ≤ α - 1 ≤ 3δ`, `β = x(1 + δ)`: `1/3 ≤ R ≤ 7/19`,
`9/31 ≤ T_s ≤ R`, `0 ≤ A < 1/100`, and `(βx - α)((x + 2)α + (2x + 1)β)/(S²K_A) = R + (1 + A)T_s`.
Status: stable. -/
theorem hs6_shape {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    1 / 3 ≤ hsRr x ∧ hsRr x ≤ 7 / 19 ∧ 9 / 31 ≤ hsTs al (x * (1 + δ)) ∧
      hsTs al (x * (1 + δ)) ≤ hsRr x ∧ 0 ≤ hsAn x (x * (1 + δ)) al ∧
      hsAn x (x * (1 + δ)) al < 1 / 100 ∧
      (x * (1 + δ) * x - al) * ((x + 2) * al + (2 * x + 1) * (x * (1 + δ))) /
          ((1 + x) ^ 2 * (al ^ 2 + al * (x * (1 + δ)) + (x * (1 + δ)) ^ 2)) =
        hsRr x + (1 + hsAn x (x * (1 + δ)) al) * hsTs al (x * (1 + δ)) := by
  sorry

/-- **The incoming norm, two-sided** (`CENTRAL_COST_SHAPE_BOUNDS` (5)-(8); inventory HS-S567 CS.2):
on the box of `hs6_shape`, `u_q(R, δ) < Sec(1, x, β) ≤ 3/4 + R²/12`. Status: stable. -/
theorem hs6_u_bounds {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    hs6uq (hsRr x) δ < m2Sec 1 x (x * (1 + δ)) ∧
      m2Sec 1 x (x * (1 + δ)) ≤ 3 / 4 + hsRr x ^ 2 / 12 := by
  sorry

/-- **The central shear bounds** (`CENTRAL_COST_SHAPE_BOUNDS` (9)-(13); inventory HS-S567 CS.3): on the
box of `hs6_shape`, `1/9 ≤ Z_L ≤ Z ≤ Z_U < 1/5`. Status: stable. -/
theorem hs6_central_shear {x δ al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) :
    1 / 9 ≤ hs6ZL (hsRr x) δ ∧ hs6ZL (hsRr x) δ ≤ hs6Z x (x * (1 + δ)) al ∧
      hs6Z x (x * (1 + δ)) al ≤ hs6ZU (hsRr x) δ ∧ hs6ZU (hsRr x) δ < 1 / 5 := by
  sorry

/-- **The tangent curve inverts the half-angle formula** (`SHEAR_COST_REDUCTION` (8)-(10)(c);
inventory HS-S567 SH.4): for `A ≥ 0`, `K > A`, `𝒟 = √(K² - A²)` and `h < 0`, the angle
`δ = 2 arctan((√(h² + A²) - h)/(K + 𝒟))` lies in `(0, π)` and `(K cos δ - 𝒟)/sin δ = h`.
Status: stable. -/
theorem hs6_tangent_inv {A K h : ℝ} (hA : 0 ≤ A) (hK : A < K) (hh : h < 0) :
    0 < 2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2))) ∧
      2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2))) < π ∧
      (K * cos (2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2)))) - √(K ^ 2 - A ^ 2)) /
          sin (2 * arctan ((√(h ^ 2 + A ^ 2) - h) / (K + √(K ^ 2 - A ^ 2)))) = h := by
  sorry

/-- **The tangent curve is decreasing** (`SHEAR_COST_REDUCTION` (10)(a)-(b); inventory HS-S567 SH.4):
for `A ≥ 0`, `K > A`, `h̃(δ) = (K cos δ - 𝒟)/sin δ` is strictly decreasing on `(0, π)`
(`h̃' = (𝒟 cos δ - K)/sin²δ < 0`), and `K sin δ + h̃(δ) cos δ = √(h̃(δ)² + A²)`. Status: stable. -/
theorem hs6_tangent_anti {A K δ₁ δ₂ : ℝ} (hA : 0 ≤ A) (hK : A < K) (h1 : 0 < δ₁) (h12 : δ₁ < δ₂)
    (h2 : δ₂ < π) :
    (K * cos δ₂ - √(K ^ 2 - A ^ 2)) / sin δ₂ < (K * cos δ₁ - √(K ^ 2 - A ^ 2)) / sin δ₁ ∧
      K * sin δ₁ + (K * cos δ₁ - √(K ^ 2 - A ^ 2)) / sin δ₁ * cos δ₁ =
        √(((K * cos δ₁ - √(K ^ 2 - A ^ 2)) / sin δ₁) ^ 2 + A ^ 2) := by
  sorry

/-- **The score derivative** (`SHEAR_COST_REDUCTION` (11)-(13); inventory HS-S567 SH.5): for
`A ≥ 0`, `K > A`, `J₀, c` real and `0 < δ < π`, `F̃(δ) = -J₀h̃(δ) - cδ` has derivative
`(J₀√(h̃(δ)² + A²) - c sin δ)/sin δ`. Status: stable. -/
theorem hs6_score_deriv {A K J₀ c δ : ℝ} (hA : 0 ≤ A) (hK : A < K) (h0 : 0 < δ) (hπ : δ < π) :
    HasDerivAt (fun s => -J₀ * ((K * cos s - √(K ^ 2 - A ^ 2)) / sin s) - c * s)
      ((J₀ * √(((K * cos δ - √(K ^ 2 - A ^ 2)) / sin δ) ^ 2 + A ^ 2) - c * sin δ) / sin δ) δ := by
  sorry

/-- **The barrier criterion** (`SCALE_ANGLE_BARRIER` (21); inventory HS-S567 SB.2): with
`0 ≤ b₁ < 1`, `A ≥ 0`, `b₂ = b₁ - (1 - b₁)A`, `c > 3/2`, `3(b₁ + b₂)/2 < c`, `J₀ = 3(1 - b₁)/2`,
`K = A + 2 + 2(c - 3/2)/J₀`, `H > 0` and `δ = 2 arctan((√(H² + A²) + H)/(K + √(K² - A²)))`: if
`Q_c(H²) = J₀²H⁴ + (-3c(b₁ + b₂) + (9/2)(b₁² + b₂²))H² + A²(c - 3(b₁ + b₂)/2)² < 0` then
`J₀√(H² + A²) < c sin δ`. Status: stable. -/
theorem hs6_barrier_sin {b₁ A c H : ℝ} (hb₁ : 0 ≤ b₁) (hb₁1 : b₁ < 1) (hA : 0 ≤ A) (hc : 3 / 2 < c)
    (hcb : 3 * (b₁ + (b₁ - (1 - b₁) * A)) / 2 < c) (hH : 0 < H)
    (hQ : (3 * (1 - b₁) / 2) ^ 2 * (H ^ 2) ^ 2 +
        (-3 * c * (b₁ + (b₁ - (1 - b₁) * A)) + 9 / 2 * (b₁ ^ 2 + (b₁ - (1 - b₁) * A) ^ 2)) * H ^ 2 +
        A ^ 2 * (c - 3 * (b₁ + (b₁ - (1 - b₁) * A)) / 2) ^ 2 < 0) :
    3 * (1 - b₁) / 2 * √(H ^ 2 + A ^ 2) <
      c * sin (2 * arctan ((√(H ^ 2 + A ^ 2) + H) /
        ((A + 2 + 2 * (c - 3 / 2) / (3 * (1 - b₁) / 2)) +
          √((A + 2 + 2 * (c - 3 / 2) / (3 * (1 - b₁) / 2)) ^ 2 - A ^ 2)))) := by
  sorry

/-- **The barrier lemma** (`SCALE_ANGLE_BARRIER` (24)-(30); inventory HS-S567 SB.3): for
`0 < R ≤ 7/17`, `v₀ = 2R²/(3(3 + R²)) ≤ b₁ ≤ 49/916`, `0 ≤ A ≤ R²/3`, `b₂ = b₁ - (1 - b₁)A ≥ 0`,
`21/8 ≤ c ≤ 3`, `0 < H < 7R²/6`, `HR ≥ 5A/2`: `Q_c(H²) < 0`. Status: stable. -/
theorem hs6_barrier {R b₁ A c H : ℝ} (hR : 0 < R) (hR7 : R ≤ 7 / 17)
    (hb₁ : 2 * R ^ 2 / (3 * (3 + R ^ 2)) ≤ b₁) (hb₁' : b₁ ≤ 49 / 916) (hA : 0 ≤ A)
    (hA' : A ≤ R ^ 2 / 3) (hb₂ : 0 ≤ b₁ - (1 - b₁) * A) (hc : 21 / 8 ≤ c) (hc' : c ≤ 3) (hH : 0 < H)
    (hH' : H < 7 * R ^ 2 / 6) (hHR : 5 / 2 * A ≤ H * R) :
    (3 * (1 - b₁) / 2) ^ 2 * (H ^ 2) ^ 2 +
        (-3 * c * (b₁ + (b₁ - (1 - b₁) * A)) + 9 / 2 * (b₁ ^ 2 + (b₁ - (1 - b₁) * A) ^ 2)) * H ^ 2 +
        A ^ 2 * (c - 3 * (b₁ + (b₁ - (1 - b₁) * A)) / 2) ^ 2 < 0 := by
  sorry

/-- **The central score against the polynomial bound** (`SMALL_SHAPE_COST_EXCLUSION` (6)-(15);
inventory HS-S567 S6.3, S6.4): on the box of `hs6_shape`, for `u_q(R, δ) ≤ u ≤ 3/4 + R²/12` with
`u ≤ U₂ = (3 + T_s²)/4`: `𝓕_c(u) > cπ/3 + √3·𝓑(u_q; R, T_s, δ) - 1/800000` (cancellation (8), the
bound (9)-(11) on `ω_c`, the `arctan` majorant, `𝓑_u > 0`). Status: stable. -/
theorem hs6_Fc_gt {x δ al u : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1 / 19)
    (hal : 13 / 5 * δ ≤ al - 1) (hal' : al - 1 ≤ 3 * δ) (hu : hs6uq (hsRr x) δ ≤ u)
    (hu' : u ≤ 3 / 4 + hsRr x ^ 2 / 12) (hu2 : u ≤ (3 + hsTs al (x * (1 + δ)) ^ 2) / 4) :
    161 / 54 * π / 3 + √3 * hs6B (hsRr x) (hsTs al (x * (1 + δ))) δ (hs6uq (hsRr x) δ) -
        1 / 800000 < hs6Fc x (x * (1 + δ)) al u := by
  sorry

/-- The angle coordinate on the box in the variables `(R, δ, η)` (`SMALL_SHAPE_COST_EXCLUSION` (21)):
for `x > 1`, `δ ≥ 0`, `T_s(1 + ηδ, x(1 + δ)) = hs6T R δ η`, `R = (x - 1)/(x + 1)`. Status: stable. -/
theorem hs6_T_eq {x δ η : ℝ} (hx : 1 < x) (hδ : 0 ≤ δ) (hη : 0 ≤ η) :
    hsTs (1 + η * δ) (x * (1 + δ)) = hs6T (hsRr x) δ η := by
  sorry

/-- **Concavity in `T` removes `η`** (`SMALL_SHAPE_COST_EXCLUSION` (16)-(19); inventory HS-S567
S6.5): for `1/3 ≤ R ≤ 7/19`, `0 ≤ δ ≤ 1/19`, `13/5 ≤ η ≤ 3`: `𝓑(u_q; R, T(η), δ) ≥
min{𝓑(u_q; R, T(13/5), δ), 𝓑(u_q; R, T(3), δ)}`. Status: stable. -/
theorem hs6_B_concave {R δ η : ℝ} (hR : 1 / 3 ≤ R) (hR' : R ≤ 7 / 19) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (hη : 13 / 5 ≤ η) (hη' : η ≤ 3) :
    min (hs6B R (hs6T R δ (13 / 5)) δ (hs6uq R δ)) (hs6B R (hs6T R δ 3) δ (hs6uq R δ)) ≤
      hs6B R (hs6T R δ η) δ (hs6uq R δ) := by
  sorry

/-- **The two endpoint polynomials** (`SMALL_SHAPE_COST_EXCLUSION` (20)-(31); inventory HS-S567
S6.6, S6.7): for `1/3 ≤ R ≤ 7/19`, `0 ≤ δ ≤ 1/19` and `e ∈ {13/5, 3}`:
`𝓑(u_q; R, T(e), δ) > b*`. Status: heavy. -/
theorem hs6_B_endpoint {R δ e : ℝ} (hR : 1 / 3 ≤ R) (hR' : R ≤ 7 / 19) (hδ : 0 ≤ δ)
    (hδ2 : δ ≤ 1 / 19) (he : e = 13 / 5 ∨ e = 3) :
    hs6bstar < hs6B R (hs6T R δ e) δ (hs6uq R δ) := by
  sorry

/-- **The constants** (`SMALL_SHAPE_COST_EXCLUSION` §7; inventory HS-S567 S6.8):
`A_oct < 3126055/10⁶`, `π > 314159265/10⁸`, `√3 > 989/571`. Status: stable. -/
theorem hs6_constants :
    octagonCost < 3126055 / 1000000 ∧ (314159265 / 100000000 : ℝ) < π ∧ (989 / 571 : ℝ) < √3 := by
  sorry

/-! ### Actual-data leaves and gate S6 -/

namespace HsData

variable (H : HsData)

/-- **The angle bound at `κ₀`** (`ROOT_AND_ANGLE_REDUCTION` (14)-(25), `MIXED_GENERAL_SHORT_DEFECT_INTERFACE`
(5)-(8); inventory HS-S567 AC.1, AB1, AB2, AL): for actual data with `40/27 ≤ κ = pt.kap`,
`K = A + 2 + 2κ₀/J₀`, `h` the actual shear, and `0 < δ < π/2 - ψ` with
`K sin δ + h cos δ ≥ √(A² + h²)`: `θ_br = arctan(√3ℬ/𝒜) ≤ ψ + δ`. Status: stable. -/
theorem hs6_angle (hκ : 40 / 27 ≤ H.pt.kap) {δ : ℝ} (hδ : 0 < δ)
    (hδψ : δ < π / 2 - hs6psi H.x H.be H.al)
    (hsup : √(hsAn H.x H.be H.al ^ 2 + hsShear H.x H.be H.al H.rho ^ 2) ≤
      hs6K H.x H.be H.al H.u * sin δ + hsShear H.x H.be H.al H.rho * cos δ) :
    arctan (√3 * H.pt.BB / H.pt.AA) ≤ hs6psi H.x H.be H.al + δ := by
  sorry

/-- **The continuation to the central scale** (`SMALL_SHAPE_COST_EXCLUSION` (3)-(5); inventory HS-S567
S6.1, S6.2, recommended route): on the small-shape domain, with `Γ > 1829/10000`, `h < 0`,
`-hR > 5A/2`: `C_br + (κ + 3/2)(π/3 - θ_br) ≥ 𝓕_c(u)` (`hs6_kappa`, `hs6_angle` at `δ_a = δ(h)`,
`hs6_tangent_inv`, `hs6_tangent_anti`, the cost-shear identity `C_br = H₀ - J₀h`, `hs6_score_deriv`
with `hs6_barrier_sin`, `hs6_barrier` pointwise on `[δ_a, δ_c]` (`hs6_shape`, `hs6_u_bounds`,
`hs6_central_shear`, `q_le_qc`)). Status: stable. -/
theorem hs6_continuation (hS : H.SmallShape) (hΓ : 1829 / 10000 < H.Γ)
    (hh : hsShear H.x H.be H.al H.rho < 0)
    (hhR : 5 / 2 * hsAn H.x H.be H.al < -hsShear H.x H.be H.al H.rho * hsRr H.x) :
    hs6Fc H.x H.be H.al H.u ≤
      H.pt.cost + (H.pt.kap + 3 / 2) * (π / 3 - arctan (√3 * H.pt.BB / H.pt.AA)) := by
  sorry

/-- **Gate S6** (`SMALL_SHAPE_COST_EXCLUSION` (2); inventory HS-S567 S6.8): on the small-shape domain,
with `Γ > 1829/10000`, `h < 0`, `-hR > 5A/2`: `C_br + (κ + 3/2)(π/3 - θ_br) > A_oct`.
Proof plan: `hs6_continuation`; `hs6_Fc_gt` (with `hs6_u_bounds`, `u_le_rA`); `hs6_T_eq`,
`hs6_B_concave`, `hs6_B_endpoint` give `𝓑(u_q) > b* > 0`; `hs6_constants`:
`cπ/3 + √3𝓑 - 1/800000 > cπ₀/3 + ℓb* - 1/800000 = A₀ > A_oct`.
Status: assembly (to be proved from the leaves above). -/
theorem s6 (hS : H.SmallShape) (hΓ : 1829 / 10000 < H.Γ) (hh : hsShear H.x H.be H.al H.rho < 0)
    (hhR : 5 / 2 * hsAn H.x H.be H.al < -hsShear H.x H.be H.al H.rho * hsRr H.x) :
    octagonCost < H.pt.cost + (H.pt.kap + 3 / 2) * (π / 3 - arctan (√3 * H.pt.BB / H.pt.AA)) := by
  sorry

end HsData

/-- **Gate S6 for the actual window** (`SMALL_SHAPE_COST_EXCLUSION` (2)): on the small-shape
domain, with `Γ > 1829/10000`, `h < 0`, `-hR > 5A/2`, the window cost and completion exceed
`A_oct`. -/
theorem M2Short.hs_S6 (D : M2Short) (h1 : 2 ≤ D.C / D.a) (h2 : D.C / D.a ≤ 13 / 6)
    (h3 : 0 ≤ D.B / D.C - 1) (h4 : D.B / D.C - 1 ≤ 1 / 19)
    (h5 : 1 + 13 / 5 * (D.B / D.C - 1) ≤ D.A / D.a) (h6 : D.A / D.a ≤ 1 + 3 * (D.B / D.C - 1))
    (hΓ : 1829 / 10000 < D.Γ)
    (hh : hsShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) < 0)
    (hhR : 5 / 2 * hsAn (D.C / D.a) (D.B / D.a) (D.A / D.a) <
      -hsShear (D.C / D.a) (D.B / D.a) (D.A / D.a) (D.a ^ 2 / (D.a ^ 2 + 4)) *
        hsRr (D.C / D.a)) :
    octagonCost <
      D.ss_pt.cost + (D.ss_pt.kap + 3 / 2) * (π / 3 - arctan (√3 * D.ss_pt.BB / D.ss_pt.AA)) := by
  rw [← D.toHs_x, ← D.toHs_be, ← D.toHs_al, ← D.toHs_rho] at hh hhR
  have h := D.toHs.s6 (D.hs_smallShape h1 h2 h3 h4 h5 h6) (by rwa [D.toHs_Γ]) hh hhR
  rwa [D.toHs_pt] at h

end SmoothedOctagon
