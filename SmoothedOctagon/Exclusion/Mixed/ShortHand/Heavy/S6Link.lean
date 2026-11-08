module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S6Defs

/-!
# Heavy leaf `hs6_B_endpoint`: clearing the denominators of `𝓑 - b*`

`SMALL_SHAPE_COST_EXCLUSION` (21)-(24). In the atoms `b`, `n` with `T = n/b` and `nu`, `du` with
`u = nu/du`, `𝓑(u; R, T, d) - b* = hh46S6St/hh46S6Dn` with the denominator
`hh46S6Dn = b⁵K₁K₂²du(3 - R)(1 - R)R²(1 + R)(2 + 11d)`, `K₁ = 3 + R²`, `K₂ = 3b² + n²`. The identity is
formal in the atoms (no expansion): each of the six summands of `𝓑 - b*` is put over its own factor
of the denominator.

## Main API

`hh46S6St`, `hh46S6Dn`, `hh46_s6_link`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The cleared numerator of `𝓑 - b*` in the atoms `b, n` (`T = n/b`) and `nu, du` (`u = nu/du`)
(`SMALL_SHAPE_COST_EXCLUSION` (24), with `K₂ = 3b² + n²`, `N₁ = K₁du - 4nu`, `N₂ = K₂du - 4b²nu`,
`N_A = K₁b² - K₂`, `N_Z = 12R²(1 + R)(1 - R) + 2(1 + 2R)(3 - R)d - 9(3 - R)(1 - R)d²`). -/
noncomputable def hh46S6St (R d b n nu du : ℝ) : ℝ :=
  b ^ (5 : ℕ) * (3 + R ^ (2 : ℕ)) * (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) ^ (2 : ℕ) * du *
      ((3 - R) * (1 - R) * R ^ (2 : ℕ) * (1 + R) * (2 + 11 * d)) * (hs6L R - hs6bstar) +
    (3 + R ^ (2 : ℕ)) * (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) ^ (2 : ℕ) * du *
      ((3 - R) * (1 - R) * R ^ (2 : ℕ) * (1 + R) * (2 + 11 * d)) *
      (n * b ^ (4 : ℕ) / 162 + 161 * n ^ (3 : ℕ) * b ^ (2 : ℕ) / 1458 - 161 * n ^ (5 : ℕ) / 7290) -
    b ^ (5 : ℕ) * (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) ^ (2 : ℕ) *
      ((3 - R) * (1 - R) * R ^ (2 : ℕ) * (1 + R) * (2 + 11 * d)) *
      ((3 + R ^ (2 : ℕ)) * du - 4 * nu) * R / 2 -
    b ^ (4 : ℕ) * (3 + R ^ (2 : ℕ)) * (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) *
      ((3 - R) * (1 - R) * R ^ (2 : ℕ) * (1 + R) * (2 + 11 * d)) *
      ((3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) * du - 4 * b ^ (2 : ℕ) * nu) * n / 2 -
    b ^ (5 : ℕ) * (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) * R ^ (2 : ℕ) * (1 + R) * (2 + 11 * d) *
      (12 * R ^ (2 : ℕ) * (1 + R) * (1 - R) + 2 * (1 + 2 * R) * (3 - R) * d -
        9 * (3 - R) * (1 - R) * d ^ (2 : ℕ)) *
      (((3 + R ^ (2 : ℕ)) * du - 4 * nu) * (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) +
        ((3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) * du - 4 * b ^ (2 : ℕ) * nu) * (3 + R ^ (2 : ℕ))) / 48 -
    b ^ (5 : ℕ) * (3 + R ^ (2 : ℕ)) * du * (3 - R) * (1 - R) * 161 * (3 - R) *
      ((3 + R ^ (2 : ℕ)) * b ^ (2 : ℕ) - (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ))) ^ (2 : ℕ) / 432

/-- The denominator `b⁵K₁K₂²du(3 - R)(1 - R)R²(1 + R)(2 + 11d)`. -/
noncomputable def hh46S6Dn (R d b n du : ℝ) : ℝ :=
  b ^ (5 : ℕ) * (3 + R ^ (2 : ℕ)) * (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) ^ (2 : ℕ) * du *
    ((3 - R) * (1 - R) * R ^ (2 : ℕ) * (1 + R) * (2 + 11 * d))

theorem hh46_s6_Dn_pos {R d b n du : ℝ} (hR : 0 < R) (hR1 : R < 1) (hd : 0 ≤ d) (hb : 0 < b)
    (hdu : 0 < du) : 0 < hh46S6Dn R d b n du := by
  unfold hh46S6Dn
  have h1 : 0 < 3 - R := by linarith
  have h2 : 0 < 1 - R := by linarith
  have h3 : 0 < 1 + R := by linarith
  have h4 : 0 < 2 + 11 * d := by linarith
  positivity

/-- **Clearing the denominators** (`SMALL_SHAPE_COST_EXCLUSION` (22)-(24)): for `0 < R < 1`,
`d ≥ 0`, `b, du > 0`: `𝓑(nu/du; R, n/b, d) - b* = hh46S6St/hh46S6Dn`. -/
theorem hh46_s6_link {R d b n nu du : ℝ} (hR : 0 < R) (hR1 : R < 1) (hd : 0 ≤ d) (hb : 0 < b)
    (hdu : 0 < du) :
    hs6B R (n / b) d (nu / du) - hs6bstar = hh46S6St R d b n nu du / hh46S6Dn R d b n du := by
  have hK1 : (3 + R ^ (2 : ℕ)) ≠ 0 := by positivity
  have hK2 : (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) ≠ 0 := by positivity
  have hb0 : b ≠ 0 := hb.ne'
  have hdu0 : du ≠ 0 := hdu.ne'
  have h3R : (3 - R) ≠ 0 := by linarith
  have h1R : (1 - R) ≠ 0 := by linarith
  have hR0 : R ≠ 0 := hR.ne'
  have h1pR : (1 + R) ≠ 0 := by linarith
  have h11 : (2 + 11 * d) ≠ 0 := by linarith
  have eT : (3 + (n / b) ^ 2) = (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) / b ^ (2 : ℕ) := by
    field_simp
  have eL : hs6L (n / b) =
      (n * b ^ (4 : ℕ) / 162 + 161 * n ^ (3 : ℕ) * b ^ (2 : ℕ) / 1458 - 161 * n ^ (5 : ℕ) / 7290) /
        b ^ (5 : ℕ) := by
    unfold hs6L; field_simp
  have e1 : 1 - nu / du / ((3 + R ^ 2) / 4) =
      ((3 + R ^ (2 : ℕ)) * du - 4 * nu) / ((3 + R ^ (2 : ℕ)) * du) := by
    field_simp
  have e2 : 1 - nu / du / ((3 + (n / b) ^ 2) / 4) =
      ((3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) * du - 4 * b ^ (2 : ℕ) * nu) /
        ((3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) * du) := by
    rw [eT]; field_simp
  have eA : (3 + R ^ 2) / (3 + (n / b) ^ 2) - 1 =
      ((3 + R ^ (2 : ℕ)) * b ^ (2 : ℕ) - (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ))) /
        (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) := by
    rw [eT]; field_simp
  have eZU : hs6ZU R d = (12 * R ^ (2 : ℕ) * (1 + R) * (1 - R) + 2 * (1 + 2 * R) * (3 - R) * d -
      9 * (3 - R) * (1 - R) * d ^ (2 : ℕ)) / (6 * (3 - R) * (1 - R)) := by
    unfold hs6ZU; field_simp; ring
  have eZL : hs6ZL R d = R ^ (2 : ℕ) * (1 + R) * (2 + 11 * d) / (3 - R) := by
    unfold hs6ZL; field_simp
  unfold hs6B hh46S6St hh46S6Dn
  rw [eL, e1, e2, eA, eZU, eZL]
  generalize ((3 + R ^ (2 : ℕ)) * du - 4 * nu) = N1
  generalize ((3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) * du - 4 * b ^ (2 : ℕ) * nu) = N2
  generalize ((3 + R ^ (2 : ℕ)) * b ^ (2 : ℕ) - (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ))) = NA
  generalize (12 * R ^ (2 : ℕ) * (1 + R) * (1 - R) + 2 * (1 + 2 * R) * (3 - R) * d -
      9 * (3 - R) * (1 - R) * d ^ (2 : ℕ)) = NZ
  generalize (n * b ^ (4 : ℕ) / 162 + 161 * n ^ (3 : ℕ) * b ^ (2 : ℕ) / 1458 -
      161 * n ^ (5 : ℕ) / 7290) = P
  generalize hk1 : (3 + R ^ (2 : ℕ)) = k1 at hK1 ⊢
  generalize hk2 : (3 * b ^ (2 : ℕ) + n ^ (2 : ℕ)) = k2 at hK2 ⊢
  generalize hs6L R = LR
  generalize hs6bstar = bs
  rw [eq_div_iff (by positivity)]
  field_simp
  ring

end SmoothedOctagon
