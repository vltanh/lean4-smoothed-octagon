module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.Reductions

/-!
# Smaller-short window, upper ratio: the outer tests in the reciprocal shape

The two outer duration tests `H₀`, `H₁` (the face value at `τ = 2` and the bound at the end of
the duration range), written as functions of the reciprocal shape `r = 1/α` at fixed `x`,
`c = (β - x)/(α - 1)` and incoming norm `u`, with their first three `r`-derivatives.

## Main API

* `urDr` (`D_r = D/α²`), `urWr` (`W = 49w`), `urELr` (`E_L`), `urZr` (`Z = (α + β)/α`),
  `urHt` (the test with multiplier `m`), `urH0` (`m₀ = 4 - Z/2`), `urH1` (`m₁ = 7/Z + 1/4`).
* The quartic coefficients `urW0`-`urW4` of `W` in `r`, and `urWr_eq`.
* `ur_face_H0`, `ur_face_H1`: the two outer duration tests at `q = 1/7` are `urH0`, `urH1` at
  `r = 1/α`.
* `ur_hd_H0`, `ur_hd_H0d1`, `ur_hd_H0d2`, `ur_hd_H1`, `ur_hd_H1d1`, `ur_hd_H1d2`: the
  derivatives `urH0d1`-`urH0d3`, `urH1d1`-`urH1d3`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `d₁ = 2(x - cS)`. -/
noncomputable def urd1 (x c : ℝ) : ℝ := 2 * (x - c * (1 + x))

/-- `d₂ = 1 + 2x - 2x² + 2cx`. -/
noncomputable def urd2 (x c : ℝ) : ℝ := 1 + 2 * x - 2 * x ^ 2 + 2 * c * x

/-- `J₂ = E₀ + 2S - 1 = Su + S - 1 + S⁻¹`. -/
noncomputable def urJ2 (x u : ℝ) : ℝ := ssE0 x u + 2 * (1 + x) - 1

/-- `D_r = d₀ + d₁r + d₂r²`, `d₀ = 1 + 2c`. -/
noncomputable def urDr (x c r : ℝ) : ℝ := 1 + 2 * c + urd1 x c * r + urd2 x c * r ^ 2

/-- `W = 49w`. -/
noncomputable def urWr (x c u r : ℝ) : ℝ :=
  (6 + r ^ 2) ^ 2 - (6 + r ^ 2) * (1 + x) * r ^ 2 + (1 + x) ^ 2 * r ^ 4 + u * urDr x c r ^ 2 -
    urDr x c r * ((6 + r ^ 2) * ssE0 x u + (2 * (1 + x) - 1) * r ^ 2)

/-- `E_L = (2uD_r - 6E₀ - J₂r²)/7`. -/
noncomputable def urELr (x c u r : ℝ) : ℝ :=
  (2 * u * urDr x c r - 6 * ssE0 x u - urJ2 x u * r ^ 2) / 7

/-- `Z = d + er = (α + β)/α`, `d = 1 + c`, `e = x - c`. -/
noncomputable def urZr (x c r : ℝ) : ℝ := 1 + c + (x - c) * r

/-- The outer test with multiplier `m`. -/
noncomputable def urHt (m x c u r : ℝ) : ℝ :=
  6 / 7 + (u - 1) * urZr x c r + 1 / urZr x c r - urELr x c u r +
    m * (urWr x c u r / 49 - 3 / 4) + log (2 * urZr x c r / 7)

/-- `H₀`, multiplier `4 - Z/2`. -/
noncomputable def urH0 (x c u r : ℝ) : ℝ := urHt (4 - urZr x c r / 2) x c u r

/-- `H₁`, multiplier `7/Z + 1/4`. -/
noncomputable def urH1 (x c u r : ℝ) : ℝ := urHt (7 / urZr x c r + 1 / 4) x c u r

/-! ### The quartic coefficients of `W` in `r` -/

noncomputable def urW0 (x c u : ℝ) : ℝ := 36 + u * (1 + 2 * c) ^ 2 - 6 * (1 + 2 * c) * ssE0 x u

noncomputable def urW1 (x c u : ℝ) : ℝ := urd1 x c * (2 * u * (1 + 2 * c) - 6 * ssE0 x u)

noncomputable def urW2 (x c u : ℝ) : ℝ :=
  12 - 6 * (1 + x) + u * (urd1 x c ^ 2 + 2 * (1 + 2 * c) * urd2 x c) -
    6 * urd2 x c * ssE0 x u - (1 + 2 * c) * urJ2 x u

noncomputable def urW3 (x c u : ℝ) : ℝ := urd1 x c * (2 * u * urd2 x c - urJ2 x u)

noncomputable def urW4 (x c u : ℝ) : ℝ :=
  (1 + x) ^ 2 - (1 + x) + 1 + u * urd2 x c ^ 2 - urJ2 x u * urd2 x c

/-- `W'`. -/
noncomputable def urWd1 (x c u r : ℝ) : ℝ :=
  urW1 x c u + 2 * urW2 x c u * r + 3 * urW3 x c u * r ^ 2 + 4 * urW4 x c u * r ^ 3

/-- `W''`. -/
noncomputable def urWd2 (x c u r : ℝ) : ℝ :=
  2 * urW2 x c u + 6 * urW3 x c u * r + 12 * urW4 x c u * r ^ 2

/-- `W'''`. -/
noncomputable def urWd3 (x c u r : ℝ) : ℝ := 6 * urW3 x c u + 24 * urW4 x c u * r

/-- `E_L'`. -/
noncomputable def urELd1 (x c u r : ℝ) : ℝ :=
  (2 * u * (urd1 x c + 2 * urd2 x c * r) - 2 * urJ2 x u * r) / 7

/-- `E_L''`. -/
noncomputable def urELd2 (x c u : ℝ) : ℝ := (4 * u * urd2 x c - 2 * urJ2 x u) / 7

theorem urWr_eq (x c u r : ℝ) :
    urWr x c u r = urW0 x c u + urW1 x c u * r + urW2 x c u * r ^ 2 + urW3 x c u * r ^ 3 +
      urW4 x c u * r ^ 4 := by
  unfold urWr urDr urW0 urW1 urW2 urW3 urW4 urJ2
  ring

/-! ### The derivatives -/

noncomputable def urH0d1 (x c u r : ℝ) : ℝ :=
  (u - 1) * (x - c) - (x - c) / urZr x c r ^ 2 - urELd1 x c u r -
    (x - c) / 2 * (urWr x c u r / 49 - 3 / 4) + (4 - urZr x c r / 2) * urWd1 x c u r / 49 +
    (x - c) / urZr x c r

noncomputable def urH0d2 (x c u r : ℝ) : ℝ :=
  2 * (x - c) ^ 2 / urZr x c r ^ 3 - (x - c) ^ 2 / urZr x c r ^ 2 - urELd2 x c u -
    (x - c) * urWd1 x c u r / 49 + (4 - urZr x c r / 2) * urWd2 x c u r / 49

noncomputable def urH0d3 (x c u r : ℝ) : ℝ :=
  -6 * (x - c) ^ 3 / urZr x c r ^ 4 + 2 * (x - c) ^ 3 / urZr x c r ^ 3 -
    3 * (x - c) / 2 * urWd2 x c u r / 49 + (4 - urZr x c r / 2) * urWd3 x c u r / 49

noncomputable def urH1d1 (x c u r : ℝ) : ℝ :=
  (u - 1) * (x - c) - (x - c) / urZr x c r ^ 2 - urELd1 x c u r -
    7 * (x - c) / urZr x c r ^ 2 * (urWr x c u r / 49 - 3 / 4) +
    (7 / urZr x c r + 1 / 4) * urWd1 x c u r / 49 + (x - c) / urZr x c r

noncomputable def urH1d2 (x c u r : ℝ) : ℝ :=
  2 * (x - c) ^ 2 / urZr x c r ^ 3 - urELd2 x c u +
    14 * (x - c) ^ 2 / urZr x c r ^ 3 * (urWr x c u r / 49 - 3 / 4) -
    2 * (7 * (x - c) / urZr x c r ^ 2) * urWd1 x c u r / 49 +
    (7 / urZr x c r + 1 / 4) * urWd2 x c u r / 49 - (x - c) ^ 2 / urZr x c r ^ 2

noncomputable def urH1d3 (x c u r : ℝ) : ℝ :=
  -6 * (x - c) ^ 3 / urZr x c r ^ 4 -
    42 * (x - c) ^ 3 / urZr x c r ^ 4 * (urWr x c u r / 49 - 3 / 4) +
    3 * (14 * (x - c) ^ 2 / urZr x c r ^ 3) * urWd1 x c u r / 49 -
    3 * (7 * (x - c) / urZr x c r ^ 2) * urWd2 x c u r / 49 +
    (7 / urZr x c r + 1 / 4) * urWd3 x c u r / 49 + 2 * (x - c) ^ 3 / urZr x c r ^ 3

/-- Derivative of a polynomial of degree at most four. -/
theorem ur_hd_poly4 (a0 a1 a2 a3 a4 r : ℝ) :
    HasDerivAt (fun s => a0 + a1 * s + a2 * s ^ 2 + a3 * s ^ 3 + a4 * s ^ 4)
      (a1 + 2 * a2 * r + 3 * a3 * r ^ 2 + 4 * a4 * r ^ 3) r := by
  have := ((((hasDerivAt_id r).const_mul a1).add ((hasDerivAt_pow 2 r).const_mul a2)).add
    ((hasDerivAt_pow 3 r).const_mul a3)).add ((hasDerivAt_pow 4 r).const_mul a4)
  convert this.const_add a0 using 1
  · funext s; simp only [Pi.add_apply, id]; ring
  · norm_num
    ring

theorem ur_hd_Z (x c r : ℝ) : HasDerivAt (urZr x c) (x - c) r := by
  have := ((hasDerivAt_id r).const_mul (x - c)).const_add (1 + c)
  convert this using 1
  · funext s; simp [urZr]
  · simp

/-- `K/Z` has derivative `-Ke/Z²`. -/
theorem ur_hd_inv1 {x c r : ℝ} (K : ℝ) (hZ : 0 < urZr x c r) :
    HasDerivAt (fun s => K / urZr x c s) (-(K * (x - c)) / urZr x c r ^ 2) r := by
  have := ((ur_hd_Z x c r).inv hZ.ne').const_mul K
  convert this using 1
  · funext s; simp only [div_eq_mul_inv, Pi.inv_apply]
  · ring

/-- `K/Z²` has derivative `-2Ke/Z³`. -/
theorem ur_hd_inv2 {x c r : ℝ} (K : ℝ) (hZ : 0 < urZr x c r) :
    HasDerivAt (fun s => K / urZr x c s ^ 2) (-(2 * K * (x - c)) / urZr x c r ^ 3) r := by
  have := (((ur_hd_Z x c r).mul (ur_hd_Z x c r)).inv
    (by simp only [Pi.mul_apply]; positivity)).const_mul K
  convert this using 1
  · funext s; simp only [div_eq_mul_inv, sq, Pi.inv_apply, Pi.mul_apply]
  · simp only [Pi.mul_apply]; field_simp; ring

/-- `K/Z³` has derivative `-3Ke/Z⁴`. -/
theorem ur_hd_inv3 {x c r : ℝ} (K : ℝ) (hZ : 0 < urZr x c r) :
    HasDerivAt (fun s => K / urZr x c s ^ 3) (-(3 * K * (x - c)) / urZr x c r ^ 4) r := by
  have := ((((ur_hd_Z x c r).mul (ur_hd_Z x c r)).mul (ur_hd_Z x c r)).inv
    (by simp only [Pi.mul_apply]; positivity)).const_mul K
  convert this using 1
  · funext s; simp only [div_eq_mul_inv, pow_succ, pow_zero, one_mul, Pi.inv_apply, Pi.mul_apply]
  · simp only [Pi.mul_apply]; field_simp; ring

theorem ur_hd_logZ {x c r : ℝ} (hZ : 0 < urZr x c r) :
    HasDerivAt (fun s => log (2 * urZr x c s / 7)) ((x - c) / urZr x c r) r := by
  have h := (((ur_hd_Z x c r).const_mul 2).div_const 7).log (by positivity)
  convert h using 1
  field_simp

theorem ur_hd_W (x c u r : ℝ) : HasDerivAt (urWr x c u) (urWd1 x c u r) r := by
  have := ur_hd_poly4 (urW0 x c u) (urW1 x c u) (urW2 x c u) (urW3 x c u) (urW4 x c u) r
  convert this using 1
  · funext s; exact urWr_eq x c u s
  · rfl

theorem ur_hd_Wd1 (x c u r : ℝ) : HasDerivAt (urWd1 x c u) (urWd2 x c u r) r := by
  have := ur_hd_poly4 (urW1 x c u) (2 * urW2 x c u) (3 * urW3 x c u) (4 * urW4 x c u) 0 r
  convert this using 1
  · funext s; unfold urWd1; ring
  · unfold urWd2; ring

theorem ur_hd_Wd2 (x c u r : ℝ) : HasDerivAt (urWd2 x c u) (urWd3 x c u r) r := by
  have := ur_hd_poly4 (2 * urW2 x c u) (6 * urW3 x c u) (12 * urW4 x c u) 0 0 r
  convert this using 1
  · funext s; unfold urWd2; ring
  · unfold urWd3; ring

theorem ur_hd_EL (x c u r : ℝ) : HasDerivAt (urELr x c u) (urELd1 x c u r) r := by
  have := ur_hd_poly4 ((2 * u * (1 + 2 * c) - 6 * ssE0 x u) / 7) (2 * u * urd1 x c / 7)
    ((2 * u * urd2 x c - urJ2 x u) / 7) 0 0 r
  convert this using 1
  · funext s; unfold urELr urDr; ring
  · unfold urELd1; ring

theorem ur_hd_ELd1 (x c u r : ℝ) : HasDerivAt (urELd1 x c u) (urELd2 x c u) r := by
  have := ur_hd_poly4 (2 * u * urd1 x c / 7) ((4 * u * urd2 x c - 2 * urJ2 x u) / 7) 0 0 0 r
  convert this using 1
  · funext s; unfold urELd1; ring
  · unfold urELd2; ring

/-- The multiplier `4 - Z/2`. -/
theorem ur_hd_m0 (x c r : ℝ) :
    HasDerivAt (fun s => 4 - urZr x c s / 2) (-((x - c) / 2)) r := by
  have := ((ur_hd_Z x c r).div_const 2).const_sub 4
  convert this using 1

/-- The multiplier `7/Z + 1/4`. -/
theorem ur_hd_m1 {x c r : ℝ} (hZ : 0 < urZr x c r) :
    HasDerivAt (fun s => 7 / urZr x c s + 1 / 4) (-(7 * (x - c)) / urZr x c r ^ 2) r :=
  (ur_hd_inv1 7 hZ).add_const (1 / 4)

/-- The first derivative of the test with a differentiable multiplier. -/
theorem ur_hd_Ht {x c u r m' : ℝ} {m : ℝ → ℝ} (hm : HasDerivAt m m' r) (hZ : 0 < urZr x c r) :
    HasDerivAt (fun s => urHt (m s) x c u s)
      ((u - 1) * (x - c) - (x - c) / urZr x c r ^ 2 - urELd1 x c u r +
        m' * (urWr x c u r / 49 - 3 / 4) + m r * (urWd1 x c u r / 49) + (x - c) / urZr x c r)
      r := by
  have h1 := (ur_hd_Z x c r).const_mul (u - 1)
  have h2 := ur_hd_inv1 1 hZ
  have h3 := ur_hd_EL x c u r
  have h4 := hm.mul (((ur_hd_W x c u r).div_const 49).sub_const (3 / 4))
  have h5 := ur_hd_logZ hZ
  have := ((((h1.const_add (6 / 7)).add h2).sub h3).add h4).add h5
  convert this using 1
  · funext s; simp [urHt]
  · ring

theorem ur_hd_H0 {x c u r : ℝ} (hZ : 0 < urZr x c r) :
    HasDerivAt (urH0 x c u) (urH0d1 x c u r) r := by
  convert ur_hd_Ht (u := u) (ur_hd_m0 x c r) hZ using 1
  · rfl
  · unfold urH0d1; ring

theorem ur_hd_H1 {x c u r : ℝ} (hZ : 0 < urZr x c r) :
    HasDerivAt (urH1 x c u) (urH1d1 x c u r) r := by
  convert ur_hd_Ht (u := u) (ur_hd_m1 hZ) hZ using 1
  · rfl
  · unfold urH1d1; ring

theorem ur_hd_H0d1 {x c u r : ℝ} (hZ : 0 < urZr x c r) :
    HasDerivAt (urH0d1 x c u) (urH0d2 x c u r) r := by
  have hW := ((((ur_hd_W x c u r).div_const 49).sub_const (3 / 4)).const_mul ((x - c) / 2))
  have hW1 := (ur_hd_m0 x c r).mul ((ur_hd_Wd1 x c u r).div_const 49)
  have := (((((ur_hd_inv2 (x - c) hZ).const_sub ((u - 1) * (x - c))).sub
    (ur_hd_ELd1 x c u r)).sub hW).add hW1).add (ur_hd_inv1 (x - c) hZ)
  convert this using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; unfold urH0d1; ring
  · unfold urH0d2; field_simp; ring

theorem ur_hd_H0d2 {x c u r : ℝ} (hZ : 0 < urZr x c r) :
    HasDerivAt (urH0d2 x c u) (urH0d3 x c u r) r := by
  have hW := ((ur_hd_Wd1 x c u r).const_mul (x - c)).div_const 49
  have hW2 := (ur_hd_m0 x c r).mul ((ur_hd_Wd2 x c u r).div_const 49)
  have := ((((ur_hd_inv3 (2 * (x - c) ^ 2) hZ).sub (ur_hd_inv2 ((x - c) ^ 2) hZ)).sub_const
    (urELd2 x c u)).sub hW).add hW2
  convert this using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; unfold urH0d2; ring
  · unfold urH0d3; field_simp; ring

theorem ur_hd_H1d1 {x c u r : ℝ} (hZ : 0 < urZr x c r) :
    HasDerivAt (urH1d1 x c u) (urH1d2 x c u r) r := by
  have hW := (ur_hd_inv2 (7 * (x - c)) hZ).mul
    (((ur_hd_W x c u r).div_const 49).sub_const (3 / 4))
  have hW1 := (ur_hd_m1 hZ).mul ((ur_hd_Wd1 x c u r).div_const 49)
  have := (((((ur_hd_inv2 (x - c) hZ).const_sub ((u - 1) * (x - c))).sub
    (ur_hd_ELd1 x c u r)).sub hW).add hW1).add (ur_hd_inv1 (x - c) hZ)
  convert this using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; unfold urH1d1; ring
  · unfold urH1d2; field_simp; ring

theorem ur_hd_H1d2 {x c u r : ℝ} (hZ : 0 < urZr x c r) :
    HasDerivAt (urH1d2 x c u) (urH1d3 x c u r) r := by
  have hA := (ur_hd_inv3 (14 * (x - c) ^ 2) hZ).mul
    (((ur_hd_W x c u r).div_const 49).sub_const (3 / 4))
  have hB := (ur_hd_inv2 (2 * (7 * (x - c))) hZ).mul ((ur_hd_Wd1 x c u r).div_const 49)
  have hC := (ur_hd_m1 hZ).mul ((ur_hd_Wd2 x c u r).div_const 49)
  have := (((((ur_hd_inv3 (2 * (x - c) ^ 2) hZ).sub_const (urELd2 x c u)).add hA).sub hB).add
    hC).sub (ur_hd_inv2 ((x - c) ^ 2) hZ)
  convert this using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; unfold urH1d2; ring
  · unfold urH1d3; field_simp; ring

/-! ### The bridge to the outer face -/

theorem ur_Dg {x c al be : ℝ} (hal : al ≠ 0) (hbe : be = x + c * (al - 1)) :
    ssDg x be al = al ^ 2 * urDr x c (1 / al) := by
  subst hbe
  unfold ssDg urDr urd1 urd2
  field_simp
  ring

theorem ur_Ws {x c al be u : ℝ} (hal : al ≠ 0) (hbe : be = x + c * (al - 1)) :
    ssWs x be al u (1 / 7) = urWr x c u (1 / al) / 49 := by
  unfold ssWs ssA1 ssA2
  rw [ur_Dg hal hbe]
  unfold urWr
  generalize urDr x c (1 / al) = Dr
  generalize ssE0 x u = E
  field_simp
  ring

theorem ur_ELs {x c al be u : ℝ} (hal : al ≠ 0) (hbe : be = x + c * (al - 1)) :
    ssELs x be al u (1 / 7) = urELr x c u (1 / al) := by
  unfold ssELs ssA3
  rw [ur_Dg hal hbe]
  unfold urELr urJ2
  generalize urDr x c (1 / al) = Dr
  generalize ssE0 x u = E
  field_simp
  ring

theorem ur_RA {x c al be : ℝ} (hal : 0 < al) (hbe : be = x + c * (al - 1))
    (hB : 0 < al + be) : ssRA al be = 1 / urZr x c (1 / al) := by
  subst hbe
  unfold ssRA urZr
  rw [show 1 + c + (x - c) * (1 / al) = (al + (x + c * (al - 1))) / al by field_simp; ring,
    one_div_div]

/-- **The first outer test**: `G₂ = H₀(r)`, `r = 1/α`. -/
theorem ur_face_H0 {x c al be u : ℝ} (hal : 0 < al) (hbe : be = x + c * (al - 1))
    (hB : 0 < al + be) :
    (ssWs x be al u (1 / 7) - 1) * 2 + 1 / 2 +
        ((u - 1) / ssRA al be + ssRA al be + 1 - 1 / 7 - ssELs x be al u (1 / 7)) +
        log (2 * (1 / 7 / ssRA al be)) +
        (2 - 7 * 2 * (1 / 7 / ssRA al be) / 4) * (ssWs x be al u (1 / 7) - 3 / 4) =
      urH0 x c u (1 / al) := by
  have hZ : 0 < urZr x c (1 / al) := by
    have : 0 < ssRA al be := by unfold ssRA; positivity
    rw [ur_RA hal hbe hB] at this
    exact one_div_pos.1 this
  rw [ur_Ws hal.ne' hbe, ur_ELs hal.ne' hbe, ur_RA hal hbe hB]
  unfold urH0 urHt
  have e : 2 * (1 / 7 / (1 / urZr x c (1 / al))) = 2 * urZr x c (1 / al) / 7 := by
    field_simp
  rw [e]
  field_simp
  ring

/-- **The second outer test**: `G₂ + (T - 2)A = H₁(r)`. -/
theorem ur_face_H1 {x c al be u : ℝ} (hal : 0 < al) (hbe : be = x + c * (al - 1))
    (hB : 0 < al + be) :
    (ssWs x be al u (1 / 7) - 1) * 2 + 1 / 2 +
        ((u - 1) / ssRA al be + ssRA al be + 1 - 1 / 7 - ssELs x be al u (1 / 7)) +
        log (2 * (1 / 7 / ssRA al be)) +
        (2 - 7 * 2 * (1 / 7 / ssRA al be) / 4) * (ssWs x be al u (1 / 7) - 3 / 4) +
        (1 / (1 / 7 / ssRA al be) - 2) *
          ((1 - 7 * (1 / 7 / ssRA al be) / 4) * (ssWs x be al u (1 / 7) - 3 / 4)) =
      urH1 x c u (1 / al) := by
  have hZ : 0 < urZr x c (1 / al) := by
    have : 0 < ssRA al be := by unfold ssRA; positivity
    rw [ur_RA hal hbe hB] at this
    exact one_div_pos.1 this
  rw [ur_Ws hal.ne' hbe, ur_ELs hal.ne' hbe, ur_RA hal hbe hB]
  unfold urH1 urHt
  have e : 2 * (1 / 7 / (1 / urZr x c (1 / al))) = 2 * urZr x c (1 / al) / 7 := by
    field_simp
  rw [e]
  field_simp
  ring

end SmoothedOctagon
