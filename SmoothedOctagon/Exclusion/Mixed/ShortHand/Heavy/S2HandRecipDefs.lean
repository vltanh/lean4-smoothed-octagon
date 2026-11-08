module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandBase

/-!
# S2 hand signs: the outer tests in the reciprocal shape

The two outer duration tests `H₀`, `H₁` of `archive/lighter-proofs/SHORT_RATIO_OUTER_COMPLETE.md`
(6), written as functions of the reciprocal shape `r = 1/α` at fixed `x`, `c = (β - x)/(α - 1)`
and incoming norm `u` (`SHORT_RATIO_OUTER_RECIPROCAL.md` §1, (5)-(7)), with their first three
`r`-derivatives.

## Main API

* `hl2Dr` (`D_r = D/α²`), `hl2Wr` (`W = 49w`), `hl2ELr` (`E_L`), `hl2Zr` (`Z = (α + β)/α`),
  `hl2Ht` (the test with multiplier `m`), `hl2H0` (`m₀ = 4 - Z/2`), `hl2H1` (`m₁ = 7/Z + 1/4`).
* The quartic coefficients `hl2W0`-`hl2W4` (`RECIPROCAL` (6)) and `hl2Wr_eq`.
* `hl2_face_H0`, `hl2_face_H1`: the two outer duration tests at `q = 1/7` are `hl2H0`, `hl2H1` at
  `r = 1/α`.
* `hl2_hd_H0`, `hl2_hd_H0d1`, `hl2_hd_H0d2`, `hl2_hd_H1`, `hl2_hd_H1d1`, `hl2_hd_H1d2`: the
  derivatives `hl2H0d1`-`hl2H0d3`, `hl2H1d1`-`hl2H1d3`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `d₁ = 2(x - cS)`. -/
noncomputable def hl2d1 (x c : ℝ) : ℝ := 2 * (x - c * (1 + x))

/-- `d₂ = 1 + 2x - 2x² + 2cx`. -/
noncomputable def hl2d2 (x c : ℝ) : ℝ := 1 + 2 * x - 2 * x ^ 2 + 2 * c * x

/-- `J₂ = E₀ + 2S - 1 = Su + S - 1 + S⁻¹`. -/
noncomputable def hl2J2 (x u : ℝ) : ℝ := hsE0 x u + 2 * (1 + x) - 1

/-- `D_r = d₀ + d₁r + d₂r²`, `d₀ = 1 + 2c`. -/
noncomputable def hl2Dr (x c r : ℝ) : ℝ := 1 + 2 * c + hl2d1 x c * r + hl2d2 x c * r ^ 2

/-- `W = 49w` (`SHORT_RATIO_OUTER_RECIPROCAL` (5)). -/
noncomputable def hl2Wr (x c u r : ℝ) : ℝ :=
  (6 + r ^ 2) ^ 2 - (6 + r ^ 2) * (1 + x) * r ^ 2 + (1 + x) ^ 2 * r ^ 4 + u * hl2Dr x c r ^ 2 -
    hl2Dr x c r * ((6 + r ^ 2) * hsE0 x u + (2 * (1 + x) - 1) * r ^ 2)

/-- `E_L = (2uD_r - 6E₀ - J₂r²)/7` (`SHORT_RATIO_OUTER_RECIPROCAL` (5)). -/
noncomputable def hl2ELr (x c u r : ℝ) : ℝ :=
  (2 * u * hl2Dr x c r - 6 * hsE0 x u - hl2J2 x u * r ^ 2) / 7

/-- `Z = d + er = (α + β)/α`, `d = 1 + c`, `e = x - c`. -/
noncomputable def hl2Zr (x c r : ℝ) : ℝ := 1 + c + (x - c) * r

/-- The outer test with multiplier `m` (`SHORT_RATIO_OUTER_RECIPROCAL` (7)). -/
noncomputable def hl2Ht (m x c u r : ℝ) : ℝ :=
  6 / 7 + (u - 1) * hl2Zr x c r + 1 / hl2Zr x c r - hl2ELr x c u r +
    m * (hl2Wr x c u r / 49 - 3 / 4) + log (2 * hl2Zr x c r / 7)

/-- `H₀`, multiplier `4 - Z/2`. -/
noncomputable def hl2H0 (x c u r : ℝ) : ℝ := hl2Ht (4 - hl2Zr x c r / 2) x c u r

/-- `H₁`, multiplier `7/Z + 1/4`. -/
noncomputable def hl2H1 (x c u r : ℝ) : ℝ := hl2Ht (7 / hl2Zr x c r + 1 / 4) x c u r

/-! ### The quartic coefficients (`SHORT_RATIO_OUTER_RECIPROCAL` (6)) -/

noncomputable def hl2W0 (x c u : ℝ) : ℝ := 36 + u * (1 + 2 * c) ^ 2 - 6 * (1 + 2 * c) * hsE0 x u

noncomputable def hl2W1 (x c u : ℝ) : ℝ := hl2d1 x c * (2 * u * (1 + 2 * c) - 6 * hsE0 x u)

noncomputable def hl2W2 (x c u : ℝ) : ℝ :=
  12 - 6 * (1 + x) + u * (hl2d1 x c ^ 2 + 2 * (1 + 2 * c) * hl2d2 x c) -
    6 * hl2d2 x c * hsE0 x u - (1 + 2 * c) * hl2J2 x u

noncomputable def hl2W3 (x c u : ℝ) : ℝ := hl2d1 x c * (2 * u * hl2d2 x c - hl2J2 x u)

noncomputable def hl2W4 (x c u : ℝ) : ℝ :=
  (1 + x) ^ 2 - (1 + x) + 1 + u * hl2d2 x c ^ 2 - hl2J2 x u * hl2d2 x c

/-- `W'`. -/
noncomputable def hl2Wd1 (x c u r : ℝ) : ℝ :=
  hl2W1 x c u + 2 * hl2W2 x c u * r + 3 * hl2W3 x c u * r ^ 2 + 4 * hl2W4 x c u * r ^ 3

/-- `W''`. -/
noncomputable def hl2Wd2 (x c u r : ℝ) : ℝ :=
  2 * hl2W2 x c u + 6 * hl2W3 x c u * r + 12 * hl2W4 x c u * r ^ 2

/-- `W'''`. -/
noncomputable def hl2Wd3 (x c u r : ℝ) : ℝ := 6 * hl2W3 x c u + 24 * hl2W4 x c u * r

/-- `E_L'`. -/
noncomputable def hl2ELd1 (x c u r : ℝ) : ℝ :=
  (2 * u * (hl2d1 x c + 2 * hl2d2 x c * r) - 2 * hl2J2 x u * r) / 7

/-- `E_L''`. -/
noncomputable def hl2ELd2 (x c u : ℝ) : ℝ := (4 * u * hl2d2 x c - 2 * hl2J2 x u) / 7

theorem hl2Wr_eq (x c u r : ℝ) :
    hl2Wr x c u r = hl2W0 x c u + hl2W1 x c u * r + hl2W2 x c u * r ^ 2 + hl2W3 x c u * r ^ 3 +
      hl2W4 x c u * r ^ 4 := by
  unfold hl2Wr hl2Dr hl2W0 hl2W1 hl2W2 hl2W3 hl2W4 hl2J2
  ring

/-! ### The derivatives -/

noncomputable def hl2H0d1 (x c u r : ℝ) : ℝ :=
  (u - 1) * (x - c) - (x - c) / hl2Zr x c r ^ 2 - hl2ELd1 x c u r -
    (x - c) / 2 * (hl2Wr x c u r / 49 - 3 / 4) + (4 - hl2Zr x c r / 2) * hl2Wd1 x c u r / 49 +
    (x - c) / hl2Zr x c r

noncomputable def hl2H0d2 (x c u r : ℝ) : ℝ :=
  2 * (x - c) ^ 2 / hl2Zr x c r ^ 3 - (x - c) ^ 2 / hl2Zr x c r ^ 2 - hl2ELd2 x c u -
    (x - c) * hl2Wd1 x c u r / 49 + (4 - hl2Zr x c r / 2) * hl2Wd2 x c u r / 49

noncomputable def hl2H0d3 (x c u r : ℝ) : ℝ :=
  -6 * (x - c) ^ 3 / hl2Zr x c r ^ 4 + 2 * (x - c) ^ 3 / hl2Zr x c r ^ 3 -
    3 * (x - c) / 2 * hl2Wd2 x c u r / 49 + (4 - hl2Zr x c r / 2) * hl2Wd3 x c u r / 49

noncomputable def hl2H1d1 (x c u r : ℝ) : ℝ :=
  (u - 1) * (x - c) - (x - c) / hl2Zr x c r ^ 2 - hl2ELd1 x c u r -
    7 * (x - c) / hl2Zr x c r ^ 2 * (hl2Wr x c u r / 49 - 3 / 4) +
    (7 / hl2Zr x c r + 1 / 4) * hl2Wd1 x c u r / 49 + (x - c) / hl2Zr x c r

noncomputable def hl2H1d2 (x c u r : ℝ) : ℝ :=
  2 * (x - c) ^ 2 / hl2Zr x c r ^ 3 - hl2ELd2 x c u +
    14 * (x - c) ^ 2 / hl2Zr x c r ^ 3 * (hl2Wr x c u r / 49 - 3 / 4) -
    2 * (7 * (x - c) / hl2Zr x c r ^ 2) * hl2Wd1 x c u r / 49 +
    (7 / hl2Zr x c r + 1 / 4) * hl2Wd2 x c u r / 49 - (x - c) ^ 2 / hl2Zr x c r ^ 2

noncomputable def hl2H1d3 (x c u r : ℝ) : ℝ :=
  -6 * (x - c) ^ 3 / hl2Zr x c r ^ 4 -
    42 * (x - c) ^ 3 / hl2Zr x c r ^ 4 * (hl2Wr x c u r / 49 - 3 / 4) +
    3 * (14 * (x - c) ^ 2 / hl2Zr x c r ^ 3) * hl2Wd1 x c u r / 49 -
    3 * (7 * (x - c) / hl2Zr x c r ^ 2) * hl2Wd2 x c u r / 49 +
    (7 / hl2Zr x c r + 1 / 4) * hl2Wd3 x c u r / 49 + 2 * (x - c) ^ 3 / hl2Zr x c r ^ 3

/-- Derivative of a polynomial of degree at most four. -/
theorem hl2_hd_poly4 (a0 a1 a2 a3 a4 r : ℝ) :
    HasDerivAt (fun s => a0 + a1 * s + a2 * s ^ 2 + a3 * s ^ 3 + a4 * s ^ 4)
      (a1 + 2 * a2 * r + 3 * a3 * r ^ 2 + 4 * a4 * r ^ 3) r := by
  have := ((((hasDerivAt_id r).const_mul a1).add ((hasDerivAt_pow 2 r).const_mul a2)).add
    ((hasDerivAt_pow 3 r).const_mul a3)).add ((hasDerivAt_pow 4 r).const_mul a4)
  convert this.const_add a0 using 1
  · funext s; simp only [Pi.add_apply, id]; ring
  · norm_num
    ring

theorem hl2_hd_Z (x c r : ℝ) : HasDerivAt (hl2Zr x c) (x - c) r := by
  have := ((hasDerivAt_id r).const_mul (x - c)).const_add (1 + c)
  convert this using 1
  · funext s; simp [hl2Zr]
  · simp

/-- `K/Z` has derivative `-Ke/Z²`. -/
theorem hl2_hd_inv1 {x c r : ℝ} (K : ℝ) (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (fun s => K / hl2Zr x c s) (-(K * (x - c)) / hl2Zr x c r ^ 2) r := by
  have := ((hl2_hd_Z x c r).inv hZ.ne').const_mul K
  convert this using 1
  · funext s; simp only [div_eq_mul_inv, Pi.inv_apply]
  · ring

/-- `K/Z²` has derivative `-2Ke/Z³`. -/
theorem hl2_hd_inv2 {x c r : ℝ} (K : ℝ) (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (fun s => K / hl2Zr x c s ^ 2) (-(2 * K * (x - c)) / hl2Zr x c r ^ 3) r := by
  have := (((hl2_hd_Z x c r).mul (hl2_hd_Z x c r)).inv
    (by simp only [Pi.mul_apply]; positivity)).const_mul K
  convert this using 1
  · funext s; simp only [div_eq_mul_inv, sq, Pi.inv_apply, Pi.mul_apply]
  · simp only [Pi.mul_apply]; field_simp; ring

/-- `K/Z³` has derivative `-3Ke/Z⁴`. -/
theorem hl2_hd_inv3 {x c r : ℝ} (K : ℝ) (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (fun s => K / hl2Zr x c s ^ 3) (-(3 * K * (x - c)) / hl2Zr x c r ^ 4) r := by
  have := ((((hl2_hd_Z x c r).mul (hl2_hd_Z x c r)).mul (hl2_hd_Z x c r)).inv
    (by simp only [Pi.mul_apply]; positivity)).const_mul K
  convert this using 1
  · funext s; simp only [div_eq_mul_inv, pow_succ, pow_zero, one_mul, Pi.inv_apply, Pi.mul_apply]
  · simp only [Pi.mul_apply]; field_simp; ring

theorem hl2_hd_logZ {x c r : ℝ} (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (fun s => log (2 * hl2Zr x c s / 7)) ((x - c) / hl2Zr x c r) r := by
  have h := (((hl2_hd_Z x c r).const_mul 2).div_const 7).log (by positivity)
  convert h using 1
  field_simp

theorem hl2_hd_W (x c u r : ℝ) : HasDerivAt (hl2Wr x c u) (hl2Wd1 x c u r) r := by
  have := hl2_hd_poly4 (hl2W0 x c u) (hl2W1 x c u) (hl2W2 x c u) (hl2W3 x c u) (hl2W4 x c u) r
  convert this using 1
  · funext s; exact hl2Wr_eq x c u s
  · rfl

theorem hl2_hd_Wd1 (x c u r : ℝ) : HasDerivAt (hl2Wd1 x c u) (hl2Wd2 x c u r) r := by
  have := hl2_hd_poly4 (hl2W1 x c u) (2 * hl2W2 x c u) (3 * hl2W3 x c u) (4 * hl2W4 x c u) 0 r
  convert this using 1
  · funext s; unfold hl2Wd1; ring
  · unfold hl2Wd2; ring

theorem hl2_hd_Wd2 (x c u r : ℝ) : HasDerivAt (hl2Wd2 x c u) (hl2Wd3 x c u r) r := by
  have := hl2_hd_poly4 (2 * hl2W2 x c u) (6 * hl2W3 x c u) (12 * hl2W4 x c u) 0 0 r
  convert this using 1
  · funext s; unfold hl2Wd2; ring
  · unfold hl2Wd3; ring

theorem hl2_hd_EL (x c u r : ℝ) : HasDerivAt (hl2ELr x c u) (hl2ELd1 x c u r) r := by
  have := hl2_hd_poly4 ((2 * u * (1 + 2 * c) - 6 * hsE0 x u) / 7) (2 * u * hl2d1 x c / 7)
    ((2 * u * hl2d2 x c - hl2J2 x u) / 7) 0 0 r
  convert this using 1
  · funext s; unfold hl2ELr hl2Dr; ring
  · unfold hl2ELd1; ring

theorem hl2_hd_ELd1 (x c u r : ℝ) : HasDerivAt (hl2ELd1 x c u) (hl2ELd2 x c u) r := by
  have := hl2_hd_poly4 (2 * u * hl2d1 x c / 7) ((4 * u * hl2d2 x c - 2 * hl2J2 x u) / 7) 0 0 0 r
  convert this using 1
  · funext s; unfold hl2ELd1; ring
  · unfold hl2ELd2; ring

/-- The multiplier `4 - Z/2`. -/
theorem hl2_hd_m0 (x c r : ℝ) :
    HasDerivAt (fun s => 4 - hl2Zr x c s / 2) (-((x - c) / 2)) r := by
  have := ((hl2_hd_Z x c r).div_const 2).const_sub 4
  convert this using 1

/-- The multiplier `7/Z + 1/4`. -/
theorem hl2_hd_m1 {x c r : ℝ} (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (fun s => 7 / hl2Zr x c s + 1 / 4) (-(7 * (x - c)) / hl2Zr x c r ^ 2) r :=
  (hl2_hd_inv1 7 hZ).add_const (1 / 4)

/-- The first derivative of the test with a differentiable multiplier. -/
theorem hl2_hd_Ht {x c u r m' : ℝ} {m : ℝ → ℝ} (hm : HasDerivAt m m' r) (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (fun s => hl2Ht (m s) x c u s)
      ((u - 1) * (x - c) - (x - c) / hl2Zr x c r ^ 2 - hl2ELd1 x c u r +
        m' * (hl2Wr x c u r / 49 - 3 / 4) + m r * (hl2Wd1 x c u r / 49) + (x - c) / hl2Zr x c r)
      r := by
  have h1 := (hl2_hd_Z x c r).const_mul (u - 1)
  have h2 := hl2_hd_inv1 1 hZ
  have h3 := hl2_hd_EL x c u r
  have h4 := hm.mul (((hl2_hd_W x c u r).div_const 49).sub_const (3 / 4))
  have h5 := hl2_hd_logZ hZ
  have := ((((h1.const_add (6 / 7)).add h2).sub h3).add h4).add h5
  convert this using 1
  · funext s; simp [hl2Ht]
  · ring

theorem hl2_hd_H0 {x c u r : ℝ} (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (hl2H0 x c u) (hl2H0d1 x c u r) r := by
  convert hl2_hd_Ht (u := u) (hl2_hd_m0 x c r) hZ using 1
  · rfl
  · unfold hl2H0d1; ring

theorem hl2_hd_H1 {x c u r : ℝ} (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (hl2H1 x c u) (hl2H1d1 x c u r) r := by
  convert hl2_hd_Ht (u := u) (hl2_hd_m1 hZ) hZ using 1
  · rfl
  · unfold hl2H1d1; ring

theorem hl2_hd_H0d1 {x c u r : ℝ} (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (hl2H0d1 x c u) (hl2H0d2 x c u r) r := by
  have hW := ((((hl2_hd_W x c u r).div_const 49).sub_const (3 / 4)).const_mul ((x - c) / 2))
  have hW1 := (hl2_hd_m0 x c r).mul ((hl2_hd_Wd1 x c u r).div_const 49)
  have := (((((hl2_hd_inv2 (x - c) hZ).const_sub ((u - 1) * (x - c))).sub
    (hl2_hd_ELd1 x c u r)).sub hW).add hW1).add (hl2_hd_inv1 (x - c) hZ)
  convert this using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; unfold hl2H0d1; ring
  · unfold hl2H0d2; field_simp; ring

theorem hl2_hd_H0d2 {x c u r : ℝ} (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (hl2H0d2 x c u) (hl2H0d3 x c u r) r := by
  have hW := ((hl2_hd_Wd1 x c u r).const_mul (x - c)).div_const 49
  have hW2 := (hl2_hd_m0 x c r).mul ((hl2_hd_Wd2 x c u r).div_const 49)
  have := ((((hl2_hd_inv3 (2 * (x - c) ^ 2) hZ).sub (hl2_hd_inv2 ((x - c) ^ 2) hZ)).sub_const
    (hl2ELd2 x c u)).sub hW).add hW2
  convert this using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; unfold hl2H0d2; ring
  · unfold hl2H0d3; field_simp; ring

theorem hl2_hd_H1d1 {x c u r : ℝ} (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (hl2H1d1 x c u) (hl2H1d2 x c u r) r := by
  have hW := (hl2_hd_inv2 (7 * (x - c)) hZ).mul
    (((hl2_hd_W x c u r).div_const 49).sub_const (3 / 4))
  have hW1 := (hl2_hd_m1 hZ).mul ((hl2_hd_Wd1 x c u r).div_const 49)
  have := (((((hl2_hd_inv2 (x - c) hZ).const_sub ((u - 1) * (x - c))).sub
    (hl2_hd_ELd1 x c u r)).sub hW).add hW1).add (hl2_hd_inv1 (x - c) hZ)
  convert this using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; unfold hl2H1d1; ring
  · unfold hl2H1d2; field_simp; ring

theorem hl2_hd_H1d2 {x c u r : ℝ} (hZ : 0 < hl2Zr x c r) :
    HasDerivAt (hl2H1d2 x c u) (hl2H1d3 x c u r) r := by
  have hA := (hl2_hd_inv3 (14 * (x - c) ^ 2) hZ).mul
    (((hl2_hd_W x c u r).div_const 49).sub_const (3 / 4))
  have hB := (hl2_hd_inv2 (2 * (7 * (x - c))) hZ).mul ((hl2_hd_Wd1 x c u r).div_const 49)
  have hC := (hl2_hd_m1 hZ).mul ((hl2_hd_Wd2 x c u r).div_const 49)
  have := (((((hl2_hd_inv3 (2 * (x - c) ^ 2) hZ).sub_const (hl2ELd2 x c u)).add hA).sub hB).add
    hC).sub (hl2_hd_inv2 ((x - c) ^ 2) hZ)
  convert this using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]; unfold hl2H1d2; ring
  · unfold hl2H1d3; field_simp; ring

/-! ### The bridge to the outer face -/

theorem hl2_Dg {x c al be : ℝ} (hal : al ≠ 0) (hbe : be = x + c * (al - 1)) :
    hsDg x be al = al ^ 2 * hl2Dr x c (1 / al) := by
  subst hbe
  unfold hsDg hl2Dr hl2d1 hl2d2
  field_simp
  ring

theorem hl2_Ws {x c al be u : ℝ} (hal : al ≠ 0) (hbe : be = x + c * (al - 1)) :
    hsWs x be al u (1 / 7) = hl2Wr x c u (1 / al) / 49 := by
  unfold hsWs hsA1 hsA2
  rw [hl2_Dg hal hbe]
  unfold hl2Wr
  generalize hl2Dr x c (1 / al) = Dr
  generalize hsE0 x u = E
  field_simp
  ring

theorem hl2_ELs {x c al be u : ℝ} (hal : al ≠ 0) (hbe : be = x + c * (al - 1)) :
    hsELs x be al u (1 / 7) = hl2ELr x c u (1 / al) := by
  unfold hsELs hsA3
  rw [hl2_Dg hal hbe]
  unfold hl2ELr hl2J2
  generalize hl2Dr x c (1 / al) = Dr
  generalize hsE0 x u = E
  field_simp
  ring

theorem hl2_RA {x c al be : ℝ} (hal : 0 < al) (hbe : be = x + c * (al - 1))
    (hB : 0 < al + be) : hsRA al be = 1 / hl2Zr x c (1 / al) := by
  subst hbe
  unfold hsRA hl2Zr
  rw [show 1 + c + (x - c) * (1 / al) = (al + (x + c * (al - 1))) / al by field_simp; ring,
    one_div_div]

/-- **The first outer test** (`SHORT_RATIO_OUTER_COMPLETE` (6)): `G₂ = H₀(r)`, `r = 1/α`. -/
theorem hl2_face_H0 {x c al be u : ℝ} (hal : 0 < al) (hbe : be = x + c * (al - 1))
    (hB : 0 < al + be) :
    (hsWs x be al u (1 / 7) - 1) * 2 + 1 / 2 +
        ((u - 1) / hsRA al be + hsRA al be + 1 - 1 / 7 - hsELs x be al u (1 / 7)) +
        log (2 * (1 / 7 / hsRA al be)) +
        (2 - 7 * 2 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al u (1 / 7) - 3 / 4) =
      hl2H0 x c u (1 / al) := by
  have hZ : 0 < hl2Zr x c (1 / al) := by
    have : 0 < hsRA al be := by unfold hsRA; positivity
    rw [hl2_RA hal hbe hB] at this
    exact one_div_pos.1 this
  rw [hl2_Ws hal.ne' hbe, hl2_ELs hal.ne' hbe, hl2_RA hal hbe hB]
  unfold hl2H0 hl2Ht
  have e : 2 * (1 / 7 / (1 / hl2Zr x c (1 / al))) = 2 * hl2Zr x c (1 / al) / 7 := by
    field_simp
  rw [e]
  field_simp
  ring

/-- **The second outer test** (`SHORT_RATIO_OUTER_COMPLETE` (6)): `G₂ + (T - 2)A = H₁(r)`. -/
theorem hl2_face_H1 {x c al be u : ℝ} (hal : 0 < al) (hbe : be = x + c * (al - 1))
    (hB : 0 < al + be) :
    (hsWs x be al u (1 / 7) - 1) * 2 + 1 / 2 +
        ((u - 1) / hsRA al be + hsRA al be + 1 - 1 / 7 - hsELs x be al u (1 / 7)) +
        log (2 * (1 / 7 / hsRA al be)) +
        (2 - 7 * 2 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al u (1 / 7) - 3 / 4) +
        (1 / (1 / 7 / hsRA al be) - 2) *
          ((1 - 7 * (1 / 7 / hsRA al be) / 4) * (hsWs x be al u (1 / 7) - 3 / 4)) =
      hl2H1 x c u (1 / al) := by
  have hZ : 0 < hl2Zr x c (1 / al) := by
    have : 0 < hsRA al be := by unfold hsRA; positivity
    rw [hl2_RA hal hbe hB] at this
    exact one_div_pos.1 this
  rw [hl2_Ws hal.ne' hbe, hl2_ELs hal.ne' hbe, hl2_RA hal hbe hB]
  unfold hl2H1 hl2Ht
  have e : 2 * (1 / 7 / (1 / hl2Zr x c (1 / al))) = 2 * hl2Zr x c (1 / al) / 7 := by
    field_simp
  rw [e]
  field_simp
  ring

end SmoothedOctagon
