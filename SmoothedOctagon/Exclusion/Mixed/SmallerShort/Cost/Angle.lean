module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Basic

/-!
# Gate S6 helper: the angle bound at the normalized point

The window's endpoint traces `𝒜 = Point.AA`, `ℬ = Point.BB` at the normalized point
`⟨1/(1 + x), β/x - 1, α, ρ, v, E⟩` are compared with the fixed lower row `(n, √3μ)`, `μ = βx - α`,
`n = (2x + 1)α + (x + 2)β`, of the relative frame.

The frame `m` and the costate are rotated by `O' = [[x + 2, -√3x], [√3x, x + 2]]` (`O'ᵀO' = 4K_x`).
The traces become a bilinear identity in the rotated entries (`hs6_rot_traces`, 172 monomials, atoms
`m_ij`, `h_ij`), and the point enters only through four short facts: the lower row
(`hs6_rot_lower`), the shear row (`hs6_rot_shear`), `det m = 1` (`hs6_m_det`, from `det P = -2U`,
`det F = 1`, `det Q⁻¹ = -1/(2U)`) and the costate in the rotated basis with its Casimir
(`hs6_rot_costate`). The angle comparison is the quadratic-in-`ξ` supporting-line bound `hs6_ab2`.

## Main API

* `hs6_pt_coords`, `hs6_m_closed`, `hs6_m_det`: the coordinates and frame of `Point` at the
  normalized point.
* `hs6Rb1`, `hs6Rb2`, `hs6Ra1`, `hs6Ra2`, `hs6Rk1`, `hs6Rk2`, `hs6Rk3`, `hs6_rot_traces`.
* `hs6_rot_lower`, `hs6_rot_shear`, `hs6_rot_costate`, `hs6_ab2`.
* `hs6_angle_core`: `√3 cos δ (nℬ - μ𝒜) - sin δ (n𝒜 + 3μℬ) ≤ 0` when
  `√(A² + h²) ≤ K_κ sin δ + h cos δ`, `K_κ = A + 2 + 2κ/J₀`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Certificates.SmallerShort

section Closed

variable {x be al ρ v E : ℝ}

/-- The derived coordinates of `Point` at the normalized point
`⟨1/(1 + x), β/x - 1, α, ρ, v, E⟩`. -/
theorem hs6_pt_coords (hx : 1 < x) :
    (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).x = x ∧
    (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).be = be ∧
    (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).S = 1 + x ∧
    (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).A = al + be ∧
    (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).B = be + x ∧
    (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).U = (1 - ρ) / ρ := by
  have hx0 : x ≠ 0 := by positivity
  have hx' : (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).x = x := by
    simp only [Point.x]; field_simp; ring
  have hb' : (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).be = be := by
    rw [Point.be, hx']; field_simp; ring
  refine ⟨hx', hb', by rw [Point.S, hx'], by rw [Point.A, hb'], by rw [Point.B, hb', hx'], rfl⟩

/-- **The frame `m = P F Q⁻¹` of `Point` in closed form** at the normalized point (common
denominator `2(α + β)(1 - ρ)(1 + x)`). -/
theorem hs6_m_closed (hx : 1 < x) (hal : 0 < al) (hbe : 0 < be) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m00 =
        (-al ^ 2 * be * ρ * x - 2 * al ^ 2 * be * ρ + 2 * al * be * ρ * x ^ 2 + 4 * al * be * ρ * x -
          al * ρ * x ^ 2 - 4 * al * ρ * x - 3 * al * ρ + 2 * al * x + 3 * al - be * ρ * x -
          2 * be * ρ + be * x + 2 * be) / (2 * (al + be) * (1 - ρ) * (1 + x)) ∧
    (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m01 =
        -(-al ^ 2 * be * ρ * x - 2 * al ^ 2 * be * ρ - 2 * al * be ^ 2 * ρ * x - 4 * al * be ^ 2 * ρ +
          2 * al * be * ρ * x ^ 2 + 4 * al * be * ρ * x - al * ρ * x ^ 2 - 2 * al * ρ * x + al * ρ -
          al + 4 * be ^ 2 * ρ * x ^ 2 + 8 * be ^ 2 * ρ * x - 2 * be * ρ * x ^ 2 - 5 * be * ρ * x +
          be * x) / (2 * (al + be) * (1 - ρ) * (1 + x)) ∧
    (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m10 =
        (-al ^ 2 * be * ρ * x + 2 * al * be * ρ * x ^ 2 - al * ρ * x ^ 2 + al * ρ - al - be * ρ * x +
          be * x) / (2 * (al + be) * (1 - ρ) * (1 + x)) ∧
    (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m11 =
        -(-al ^ 2 * be * ρ * x - 2 * al * be ^ 2 * ρ * x + 2 * al * be * ρ * x ^ 2 - al * ρ * x ^ 2 +
          2 * al * ρ * x + al * ρ - 2 * al * x - al + 4 * be ^ 2 * ρ * x ^ 2 - 2 * be * ρ * x ^ 2 +
          3 * be * ρ * x + 2 * be * ρ - 3 * be * x - 2 * be) / (2 * (al + be) * (1 - ρ) * (1 + x)) := by
  obtain ⟨hx', hb', hS, hA, hB, hU⟩ := hs6_pt_coords (be := be) (al := al) (ρ := ρ) (v := v) (E := E) hx
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < al + be := by linarith
  have h3 : 0 < 1 + x := by linarith
  simp only [Point.m00, Point.m01, Point.m10, Point.m11, Point.PF00, Point.PF01, Point.PF10,
    Point.PF11, Point.P00, Point.P01, Point.P10, Point.P11, Point.Qi00, Point.Qi01, Point.Qi10,
    Point.Qi11, Point.F00, Point.F01, Point.F10, Point.F11, Point.N, Point.Z, hx', hb', hS, hA,
    hB, hU]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **`det m = 1`** at the normalized point (`det P = -2U`, `det F = 1`, `det Q⁻¹ = -1/(2U)`). -/
theorem hs6_m_det (hx : 1 < x) (hal : 0 < al) (hbe : 0 < be) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m00 *
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m11 -
      (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m01 *
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m10 = 1 := by
  obtain ⟨hx', hb', hS, hA, hB, hU⟩ := hs6_pt_coords (be := be) (al := al) (ρ := ρ) (v := v) (E := E) hx
  set p : Point := ⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩
  have e1 : p.m00 * p.m11 - p.m01 * p.m10 =
      (p.PF00 * p.PF11 - p.PF01 * p.PF10) * (p.Qi00 * p.Qi11 - p.Qi01 * p.Qi10) := by
    simp only [Point.m00, Point.m01, Point.m10, Point.m11]; ring
  have e2 : p.PF00 * p.PF11 - p.PF01 * p.PF10 =
      (p.P00 * p.P11 - p.P01 * p.P10) * (p.F00 * p.F11 - p.F01 * p.F10) := by
    simp only [Point.PF00, Point.PF01, Point.PF10, Point.PF11]; ring
  have hU0 : 0 < p.U := by rw [hU]; exact div_pos (by linarith) hρ
  have hA0 : 0 < p.A := by rw [hA]; linarith
  have hS0 : 0 < p.S := by rw [hS]; linarith
  have e3 : p.P00 * p.P11 - p.P01 * p.P10 = -2 * p.U := by
    simp only [Point.P00, Point.P01, Point.P10, Point.P11, Point.N, hx']
    rw [hS]; field_simp; ring
  have e4 : p.F00 * p.F11 - p.F01 * p.F10 = 1 := by
    simp only [Point.F00, Point.F01, Point.F10, Point.F11]; field_simp; ring
  have e5 : p.Qi00 * p.Qi11 - p.Qi01 * p.Qi10 = -1 / (2 * p.U) := by
    simp only [Point.Qi00, Point.Qi01, Point.Qi10, Point.Qi11, Point.Z, hb']
    rw [hA]
    have : 0 < al + be := by linarith
    field_simp; ring
  rw [e1, e2, e3, e4, e5]
  field_simp

end Closed

/-! ### The rotated frame -/

/-- The upper-left entry `b₁` of `O'ᵀMO'`, `O' = [[x + 2, -√3x], [√3x, x + 2]]`,
`M = diag(1/√3, 1) m diag(√3, 1)`. -/
noncomputable def hs6Rb1 (x m00 m01 m10 m11 : ℝ) : ℝ :=
  (x + 2) ^ 2 * m00 + (x + 2) * x * m01 + 3 * (x + 2) * x * m10 + 3 * x ^ 2 * m11

/-- The upper-right entry of `O'ᵀMO'`, divided by `√3`. -/
noncomputable def hs6Rb2 (x m00 m01 m10 m11 : ℝ) : ℝ :=
  -((x + 2) * x * m00) + (x + 2) ^ 2 / 3 * m01 - 3 * x ^ 2 * m10 + (x + 2) * x * m11

/-- The lower-left entry of `O'ᵀMO'`, divided by `√3`. -/
noncomputable def hs6Ra1 (x m00 m01 m10 m11 : ℝ) : ℝ :=
  -((x + 2) * x * m00) - x ^ 2 * m01 + (x + 2) ^ 2 * m10 + (x + 2) * x * m11

/-- The lower-right entry of `O'ᵀMO'`. -/
noncomputable def hs6Ra2 (x m00 m01 m10 m11 : ℝ) : ℝ :=
  3 * x ^ 2 * m00 - (x + 2) * x * m01 - 3 * (x + 2) * x * m10 + (x + 2) ^ 2 * m11

/-- The upper-left entry of `O'ᵀ𝓚O'`, `𝓚 = [[-3h₂₁, -√3h₁₁], [-√3h₁₁, h₁₂]]`. -/
noncomputable def hs6Rk1 (x h11 h12 h21 : ℝ) : ℝ :=
  3 * x ^ 2 * h12 - 6 * x * (x + 2) * h11 - 3 * (x + 2) ^ 2 * h21

/-- The off-diagonal entry of `O'ᵀ𝓚O'`, divided by `√3`. -/
noncomputable def hs6Rk2 (x h11 h12 h21 : ℝ) : ℝ :=
  2 * h11 * x ^ 2 - 4 * h11 * x - 4 * h11 + h12 * x * (x + 2) + 3 * h21 * x * (x + 2)

/-- The lower-right entry of `O'ᵀ𝓚O'`. -/
noncomputable def hs6Rk3 (x h11 h12 h21 : ℝ) : ℝ :=
  6 * h11 * x * (x + 2) + h12 * (x + 2) ^ 2 - 9 * h21 * x ^ 2

/-- **The rotated trace identity** (at the matrix level): with
`𝒜 = T_κ tr m + h₁₂m₁₁ - h₁₁(m₀₁ + 3m₁₀) - 3h₂₁m₀₀` and
`ℬ = h₁₁(m₁₁ - m₀₀) + h₁₂m₁₀ + h₂₁m₀₁ + (T_κ/3)(3m₁₀ - m₀₁)` (`Point.AA`, `Point.BB`), the rotated
entries `a₁ = √3·hs6Ra1`, `a₂ = hs6Ra2`, `Δ = a₂b₁ - a₁b₂`, `σ = (a₁b₁ + a₂b₂)/√3`,
`Λ = a₁² + a₂²`, `c = 4K_xT_κ`: `(a₂ - ia₁)(𝒜 + i√3ℬ)·16K_x² = (c + k₁)Δ + k₂Σ + (c + k₃)Λ +
i(k₂(Δ - Λ) - (c + k₁)Σ)`, in rational form. -/
theorem hs6_rot_traces (x m00 m01 m10 m11 h11 h12 h21 Tk : ℝ) :
    16 * (x ^ 2 + x + 1) ^ 2 * (hs6Ra2 x m00 m01 m10 m11 *
        (Tk * (m00 + m11) + h12 * m11 - h11 * (m01 + 3 * m10) - 3 * h21 * m00) +
      3 * hs6Ra1 x m00 m01 m10 m11 *
        (h11 * (m11 - m00) + h12 * m10 + h21 * m01 + Tk / 3 * (3 * m10 - m01))) =
      (4 * (x ^ 2 + x + 1) * Tk + hs6Rk1 x h11 h12 h21) *
          (hs6Ra2 x m00 m01 m10 m11 * hs6Rb1 x m00 m01 m10 m11 -
            3 * hs6Ra1 x m00 m01 m10 m11 * hs6Rb2 x m00 m01 m10 m11) +
        3 * hs6Rk2 x h11 h12 h21 * (hs6Ra1 x m00 m01 m10 m11 * hs6Rb1 x m00 m01 m10 m11 +
          hs6Ra2 x m00 m01 m10 m11 * hs6Rb2 x m00 m01 m10 m11) +
        (4 * (x ^ 2 + x + 1) * Tk + hs6Rk3 x h11 h12 h21) *
          (3 * hs6Ra1 x m00 m01 m10 m11 ^ 2 + hs6Ra2 x m00 m01 m10 m11 ^ 2) ∧
    16 * (x ^ 2 + x + 1) ^ 2 * (hs6Ra2 x m00 m01 m10 m11 *
        (h11 * (m11 - m00) + h12 * m10 + h21 * m01 + Tk / 3 * (3 * m10 - m01)) -
      hs6Ra1 x m00 m01 m10 m11 *
        (Tk * (m00 + m11) + h12 * m11 - h11 * (m01 + 3 * m10) - 3 * h21 * m00)) =
      hs6Rk2 x h11 h12 h21 * (hs6Ra2 x m00 m01 m10 m11 * hs6Rb1 x m00 m01 m10 m11 -
          3 * hs6Ra1 x m00 m01 m10 m11 * hs6Rb2 x m00 m01 m10 m11 -
          (3 * hs6Ra1 x m00 m01 m10 m11 ^ 2 + hs6Ra2 x m00 m01 m10 m11 ^ 2)) -
        (4 * (x ^ 2 + x + 1) * Tk + hs6Rk1 x h11 h12 h21) *
          (hs6Ra1 x m00 m01 m10 m11 * hs6Rb1 x m00 m01 m10 m11 +
            hs6Ra2 x m00 m01 m10 m11 * hs6Rb2 x m00 m01 m10 m11) ∧
    hs6Ra2 x m00 m01 m10 m11 * hs6Rb1 x m00 m01 m10 m11 -
        3 * hs6Ra1 x m00 m01 m10 m11 * hs6Rb2 x m00 m01 m10 m11 =
      16 * (x ^ 2 + x + 1) ^ 2 * (m00 * m11 - m01 * m10) ∧
    hs6Rk1 x h11 h12 h21 * hs6Rk3 x h11 h12 h21 - 3 * hs6Rk2 x h11 h12 h21 ^ 2 =
      16 * (x ^ 2 + x + 1) ^ 2 * (-3 * h21 * h12 - 3 * h11 ^ 2) := by
  unfold hs6Ra1 hs6Ra2 hs6Rb1 hs6Rb2 hs6Rk1 hs6Rk2 hs6Rk3
  refine ⟨by ring, by ring, by ring, by ring⟩

/-- **The supporting line for every costate** (real form):
with `t = c + k₁`, `k₁ > 0`, `k₁k₃ = c² + k₂²` (`det = 1`), `sin δ > 0` and
`A² + h² ≤ (K_s sin δ + h cos δ)²`, `K_s = A + 2 + 2c/k₁`:
`cos δ (k₂A - th) - sin δ (t(1 + A) + k₂h + c + k₃) ≤ 0`. The left side times `4k₁ sin δ` is
`-(2k₂ sin δ - k₁(A cos δ - h sin δ))² - (k₁K_s sin δ + k₁h cos δ)² + k₁²(A² + h²)`. -/
theorem hs6_ab2 {A h c k₁ k₂ k₃ s co : ℝ} (hk1 : 0 < k₁) (hs : 0 < s) (hsc : s ^ 2 + co ^ 2 = 1)
    (hdet : k₁ * k₃ = c ^ 2 + k₂ ^ 2)
    (hsup : A ^ 2 + h ^ 2 ≤ ((A + 2 + 2 * c / k₁) * s + h * co) ^ 2) :
    co * (k₂ * A - (c + k₁) * h) - s * ((c + k₁) * (1 + A) + k₂ * h + c + k₃) ≤ 0 := by
  have hw : k₁ * ((A + 2 + 2 * c / k₁) * s + h * co) = (k₁ * (A + 2) + 2 * c) * s + k₁ * h * co := by
    field_simp
  have hsup' : k₁ ^ 2 * (A ^ 2 + h ^ 2) ≤ ((k₁ * (A + 2) + 2 * c) * s + k₁ * h * co) ^ 2 := by
    rw [← hw, mul_pow]; exact mul_le_mul_of_nonneg_left hsup (by positivity)
  have key : 4 * s * k₁ * (co * (k₂ * A - (c + k₁) * h) - s * ((c + k₁) * (1 + A) + k₂ * h + c + k₃)) =
      -(2 * s * k₂ - k₁ * (A * co - h * s)) ^ 2 - ((k₁ * (A + 2) + 2 * c) * s + k₁ * h * co) ^ 2 +
        k₁ ^ 2 * (A ^ 2 + h ^ 2) := by
    linear_combination (-4 * s ^ 2) * hdet + k₁ ^ 2 * (A ^ 2 + h ^ 2) * hsc
  have hpos : 0 < 4 * s * k₁ := by positivity
  have : 4 * s * k₁ * (co * (k₂ * A - (c + k₁) * h) - s * ((c + k₁) * (1 + A) + k₂ * h + c + k₃)) ≤ 0 := by
    rw [key]; linarith [sq_nonneg (2 * s * k₂ - k₁ * (A * co - h * s))]
  by_contra hc
  push Not at hc
  have := mul_pos hpos hc
  linarith

/-! ### The rotated frame at the normalized point -/

section Point

variable {x be al ρ v E u : ℝ}

/-- **The fixed lower row**: at the normalized point,
`a₁/√3 = 2S(βx - α)/(α + β)` and `a₂ = 2S((2x + 1)α + (x + 2)β)/(α + β)`. -/
theorem hs6_rot_lower (hx : 1 < x) (hal : 0 < al) (hbe : 0 < be) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hs6Ra1 x (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m00
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m01
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m10
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m11 =
      2 * (1 + x) * (be * x - al) / (al + be) ∧
    hs6Ra2 x (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m00
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m01
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m10
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m11 =
      2 * (1 + x) * ((2 * x + 1) * al + (x + 2) * be) / (al + be) := by
  obtain ⟨h00, h01, h10, h11⟩ := hs6_m_closed (v := v) (E := E) hx hal hbe hρ hρ1
  rw [h00, h01, h10, h11]
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < al + be := by linarith
  have h3 : 0 < 1 + x := by linarith
  unfold hs6Ra1 hs6Ra2
  constructor <;> field_simp <;> ring

/-- **The shear row**: at the normalized point,
`(βx - α)b₁ + ((2x + 1)α + (x + 2)β)b₂/√3 = 8SK_xK_A η/(α + β)` with `η = h/√3`,
`h` the physical shear (`hsShear`). -/
theorem hs6_rot_shear (hx : 1 < x) (hal : 0 < al) (hbe : 0 < be) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (be * x - al) * hs6Rb1 x (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m00
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m01
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m10
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m11 +
      ((2 * x + 1) * al + (x + 2) * be) * hs6Rb2 x (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m00
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m01
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m10
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m11 =
      8 * (1 + x) * (x ^ 2 + x + 1) * (al ^ 2 + al * be + be ^ 2) / (al + be) *
        (1 / 3 * ((be * x - al) * ((x + 2) * al + (2 * x + 1) * be) /
          ((1 + x) ^ 2 * (al ^ 2 + al * be + be ^ 2)) -
          2 * ((x ^ 2 + x + 1) / (1 + x) ^ 2) * (2 * be * x - x - al * be) * (ρ / (1 - ρ)))) := by
  obtain ⟨h00, h01, h10, h11⟩ := hs6_m_closed (v := v) (E := E) hx hal hbe hρ hρ1
  rw [h00, h01, h10, h11]
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < al + be := by linarith
  have h3 : 0 < 1 + x := by linarith
  have h4 : 0 < al ^ 2 + al * be + be ^ 2 := by positivity
  unfold hs6Rb1 hs6Rb2
  field_simp
  ring

/-- **The costate in the rotated basis**: at the normalized point with incoming norm `u`,
`k₁ = 12uS²(1 - ρ)²`, `k₂/√3 = 4(1 - ρ)(uSW - EK_x)` with `W = 1 - x + ρS(2x + 1)`, and
`-(h₂₁h₁₂ + h₁₁²) = (4uv - E²)(1 - ρ)²`. -/
theorem hs6_rot_costate (hx : 1 < x)
    (hu : (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).u = u) :
    hs6Rk1 x (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h11
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h12
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h21 = 12 * u * (1 + x) ^ 2 * (1 - ρ) ^ 2 ∧
    hs6Rk2 x (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h11
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h12
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h21 =
      4 * (1 - ρ) * (u * (1 + x) * (1 - x + ρ * (1 + x) * (2 * x + 1)) - E * (x ^ 2 + x + 1)) ∧
    -((⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h21 *
          (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h12 +
        (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h11 ^ 2) =
      (4 * u * v - E ^ 2) * (1 - ρ) ^ 2 := by
  obtain ⟨-, -, hS, -, -, -⟩ := hs6_pt_coords (be := be) (al := al) (ρ := ρ) (v := v) (E := E) hx
  have h3 : 0 < 1 + x := by linarith
  simp only [Point.h11, Point.h12, Point.h21, hu, hS]
  unfold hs6Rk1 hs6Rk2
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **The angle inequality at the normalized point**: if
`√(A² + h²) ≤ K_κ sin δ + h cos δ` with `K_κ = A + 2 + 2κ/J₀`, `J₀ = 3u/(2U₁)`, `sin δ > 0`, then
`√3 cos δ (n ℬ - μ 𝒜) - sin δ (n 𝒜 + 3μ ℬ) ≤ 0`, where `μ = βx - α`, `n = (2x + 1)α + (x + 2)β`
(so `(n, √3μ)` is the direction of the fixed lower row, angle `ψ`).
The proof uses the rotated trace identity `hs6_rot_traces` and the quadratic-in-`ξ` bound
`hs6_ab2`. -/
theorem hs6_angle_core (hx : 1 < x) (hal : 0 < al) (hbe : 0 < be) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hu0 : 0 < u) (hu : (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).u = u)
    (hk : 0 < (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).kap) {δ : ℝ} (hs : 0 < sin δ)
    (hsup : √(hsAn x be al ^ 2 + hsShear x be al ρ ^ 2) ≤
      (hsAn x be al + 2 + 2 * (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).kap /
        (3 * u / (2 * m2U (1 / (1 + x))))) * sin δ + hsShear x be al ρ * cos δ) :
    √3 * cos δ * (((2 * x + 1) * al + (x + 2) * be) * (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).BB -
        (be * x - al) * (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).AA) -
      sin δ * (((2 * x + 1) * al + (x + 2) * be) * (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).AA +
        3 * (be * x - al) * (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).BB) ≤ 0 := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have hab : 0 < al + be := by linarith
  have hS : 0 < 1 + x := by linarith
  have hKx : 0 < x ^ 2 + x + 1 := by positivity
  have hKA : 0 < al ^ 2 + al * be + be ^ 2 := by positivity
  -- the facts at the point
  have hdetm := hs6_m_det (v := v) (E := E) hx hal hbe hρ hρ1
  obtain ⟨hl1, hl2⟩ := hs6_rot_lower (v := v) (E := E) hx hal hbe hρ hρ1
  have hsh := hs6_rot_shear (v := v) (E := E) hx hal hbe hρ hρ1
  obtain ⟨hk1, hk2, hcas⟩ := hs6_rot_costate hx hu
  have hgam : (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).gam =
      (4 * u * v - E ^ 2) / (16 * (1 - ρ) ^ 2) := by rw [Point.gam, hu]
  have hkap2 : (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).kap ^ 2 =
      12 * (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).gam :=
    Real.sq_sqrt (le_of_lt (Real.sqrt_pos.1 hk))
  have hkap2' : (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).kap ^ 2 * (1 - ρ) ^ 2 =
      3 * (4 * u * v - E ^ 2) / 4 := by
    rw [hkap2, hgam]; field_simp; ring
  have hTk : (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).Tk =
      2 * (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).kap * (1 - ρ) ^ 2 := rfl
  rw [Point.AA, Point.BB]
  generalize (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m00 = m00 at *
  generalize (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m01 = m01 at *
  generalize (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m10 = m10 at *
  generalize (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).m11 = m11 at *
  generalize (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h11 = h11 at *
  generalize (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h12 = h12 at *
  generalize (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).h21 = h21 at *
  generalize (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).Tk = Tk at *
  generalize (⟨1 / (1 + x), be / x - 1, al, ρ, v, E⟩ : Point).kap = kap at *
  obtain ⟨hRe, hIm, hΔ, hdK⟩ := hs6_rot_traces x m00 m01 m10 m11 h11 h12 h21 Tk
  rw [hdetm] at hΔ
  rw [hl1, hl2] at hRe hIm hΔ
  rw [hk1] at hRe hIm hdK
  -- the shear `h = √3 η`
  set η := 1 / 3 * ((be * x - al) * ((x + 2) * al + (2 * x + 1) * be) /
    ((1 + x) ^ 2 * (al ^ 2 + al * be + be ^ 2)) -
      2 * ((x ^ 2 + x + 1) / (1 + x) ^ 2) * (2 * be * x - x - al * be) * (ρ / (1 - ρ))) with hη
  have hsh3 : hsShear x be al ρ = √3 * η := by rw [hsShear, hη]; ring
  have hs3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  -- the lower-row identities
  set A := hsAn x be al with hA
  have hAΛ : (1 + A) * (3 * (2 * (1 + x) * (be * x - al) / (al + be)) ^ 2 +
      (2 * (1 + x) * ((2 * x + 1) * al + (x + 2) * be) / (al + be)) ^ 2) =
      16 * (x ^ 2 + x + 1) ^ 2 := by
    rw [hA, hsAn]; field_simp; ring
  have hGΛ : 2 * (1 + x) / (al + be) * (8 * (1 + x) * (x ^ 2 + x + 1) *
      (al ^ 2 + al * be + be ^ 2) / (al + be)) =
      3 * (2 * (1 + x) * (be * x - al) / (al + be)) ^ 2 +
        (2 * (1 + x) * ((2 * x + 1) * al + (x + 2) * be) / (al + be)) ^ 2 := by
    field_simp; ring
  have hKs : A + 2 + 2 * (4 * (x ^ 2 + x + 1) * Tk) / (12 * u * (1 + x) ^ 2 * (1 - ρ) ^ 2) =
      A + 2 + 2 * kap / (3 * u / (2 * m2U (1 / (1 + x)))) := by
    rw [hTk, m2U]; field_simp; ring
  -- generalize the atoms
  generalize hb1 : hs6Rb1 x m00 m01 m10 m11 = b₁ at hRe hIm hΔ hsh
  generalize hb2 : hs6Rb2 x m00 m01 m10 m11 = b₂ at hRe hIm hΔ hsh
  generalize hκ2 : hs6Rk2 x h11 h12 h21 = κ₂ at hRe hIm hdK hk2
  generalize hk3 : hs6Rk3 x h11 h12 h21 = k₃ at hRe hIm hdK
  have hdet : 12 * u * (1 + x) ^ 2 * (1 - ρ) ^ 2 * k₃ =
      (4 * (x ^ 2 + x + 1) * Tk) ^ 2 + (√3 * κ₂) ^ 2 := by
    rw [hTk, mul_pow √3, hs3]
    linear_combination hdK + 48 * (x ^ 2 + x + 1) ^ 2 * hcas -
      64 * (x ^ 2 + x + 1) ^ 2 * (1 - ρ) ^ 2 * hkap2'
  have hsup2 : A ^ 2 + hsShear x be al ρ ^ 2 ≤
      ((A + 2 + 2 * (4 * (x ^ 2 + x + 1) * Tk) / (12 * u * (1 + x) ^ 2 * (1 - ρ) ^ 2)) * sin δ +
        hsShear x be al ρ * cos δ) ^ 2 := by
    rw [hKs, ← Real.sqrt_le_left]
    · exact hsup
    · exact le_trans (Real.sqrt_nonneg _) hsup
  have hg := hs6_ab2 (k₂ := √3 * κ₂) (by positivity) hs (sin_sq_add_cos_sq δ) hdet hsup2
  rw [hsh3] at hg
  generalize Tk * (m00 + m11) + h12 * m11 - h11 * (m01 + 3 * m10) - 3 * h21 * m00 = AA at hRe hIm ⊢
  generalize h11 * (m11 - m00) + h12 * m10 + h21 * m01 + Tk / 3 * (3 * m10 - m01) = BB at hRe hIm ⊢
  set Λ := 3 * (2 * (1 + x) * (be * x - al) / (al + be)) ^ 2 +
    (2 * (1 + x) * ((2 * x + 1) * al + (x + 2) * be) / (al + be)) ^ 2 with hΛ
  have hΔ' : 2 * (1 + x) * ((2 * x + 1) * al + (x + 2) * be) / (al + be) * b₁ -
      3 * (2 * (1 + x) * (be * x - al) / (al + be)) * b₂ = (1 + A) * Λ := by
    rw [hΔ, hAΛ]; ring
  have hσ' : 2 * (1 + x) * (be * x - al) / (al + be) * b₁ +
      2 * (1 + x) * ((2 * x + 1) * al + (x + 2) * be) / (al + be) * b₂ = η * Λ := by
    rw [← hGΛ]
    linear_combination 2 * (1 + x) / (al + be) * hsh
  set c := 4 * (x ^ 2 + x + 1) * Tk
  set k₁ := 12 * u * (1 + x) ^ 2 * (1 - ρ) ^ 2
  have hfin : 16 * (x ^ 2 + x + 1) ^ 2 * (2 * (1 + x) / (al + be)) *
      (√3 * cos δ * (((2 * x + 1) * al + (x + 2) * be) * BB - (be * x - al) * AA) -
        sin δ * (((2 * x + 1) * al + (x + 2) * be) * AA + 3 * (be * x - al) * BB)) =
      Λ * (cos δ * (√3 * κ₂ * A - (c + k₁) * (√3 * η)) -
        sin δ * ((c + k₁) * (1 + A) + √3 * κ₂ * (√3 * η) + c + k₃)) := by
    linear_combination √3 * cos δ * hIm - sin δ * hRe +
      (√3 * cos δ * κ₂ - sin δ * (c + k₁)) * hΔ' -
      (√3 * cos δ * (c + k₁) + 3 * sin δ * κ₂) * hσ' + sin δ * κ₂ * η * Λ * hs3
  have hΛ0 : 0 < Λ := by
    rw [hΛ]
    have : 0 < 2 * (1 + x) * ((2 * x + 1) * al + (x + 2) * be) / (al + be) := by positivity
    positivity
  have hpos : 0 < 16 * (x ^ 2 + x + 1) ^ 2 * (2 * (1 + x) / (al + be)) := by positivity
  have hrhs : Λ * (cos δ * (√3 * κ₂ * A - (c + k₁) * (√3 * η)) -
      sin δ * ((c + k₁) * (1 + A) + √3 * κ₂ * (√3 * η) + c + k₃)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hΛ0.le hg
  rw [← hfin] at hrhs
  by_contra hcon
  push Not at hcon
  have := mul_pos hpos hcon
  linarith

end Point

end SmoothedOctagon
