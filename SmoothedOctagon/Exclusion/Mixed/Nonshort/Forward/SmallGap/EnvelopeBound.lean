module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.NormDerivative
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen

/-!
# The envelope bound from the order imbalance

The envelope loses at most `(1 - 2t)² / 32` from `3/16`. After clearing
the secant denominator, its excess is a quadratic in `u = k - 1`. The
shape increment is a convex combination of two nonnegative polynomials.
On the unit face, two concavity bounds and elementary power estimates
leave `h²/12 - hj/16 - j² > 0`, with `h = 1 - 2t` and `j ≤ h/6`.
-/

@[expose] public section

namespace SmoothedOctagon

private def envBaseCoeff0 {R : Type*} [CommRing R] (h : R) : R :=
  h ^ 10 - 18 * h ^ 9 - 223 * h ^ 8 - 940 * h ^ 7 - 1425 * h ^ 6 + 54 * h ^ 5 + 1607 * h ^ 4 + 224 * h ^ 3 -
    1044 * h ^ 2 - 216 * h + 180

private def envBaseCoeff1 {R : Type*} [CommRing R] (h : R) : R :=
  h ^ 11 - 76 * h ^ 10 - 747 * h ^ 9 - 2942 * h ^ 8 - 4457 * h ^ 7 - 238 * h ^ 6 + 4727 * h ^ 5 + 1622 * h ^ 4
    - 2312 * h ^ 3 - 858 * h ^ 2 + 324 * h + 36

private def envBaseCoeff2 {R : Type*} [CommRing R] (h : R) : R :=
  -21 * h ^ 12 - 1132 * h ^ 11 - 9205 * h ^ 10 - 33780 * h ^ 9 - 50713 * h ^ 8 - 5498 * h ^ 7 + 53865 * h ^ 6
    + 29516 * h ^ 5 - 18194 * h ^ 4 - 13022 * h ^ 3 + 1308 * h ^ 2 + 1116 * h + 144

private def envBaseCoeff3 {R : Type*} [CommRing R] (h : R) : R :=
  -108 * h ^ 11 - 2372 * h ^ 10 - 14911 * h ^ 9 - 44077 * h ^ 8 - 42251 * h ^ 7 + 32755 * h ^ 6 + 65743 * h ^
    5 + 2613 * h ^ 4 - 25735 * h ^ 3 - 4381 * h ^ 2 + 2766 * h + 774

private def envBaseCoeff4 {R : Type*} [CommRing R] (h : R) : R :=
  -1834 * h ^ 11 - 26882 * h ^ 10 - 149866 * h ^ 9 - 409470 * h ^ 8 - 366143 * h ^ 7 + 339473 * h ^ 6 + 677464
    * h ^ 5 + 74520 * h ^ 4 - 288545 * h ^ 3 - 82169 * h ^ 2 + 39100 * h + 14448

private def envBaseCoeff5 {R : Type*} [CommRing R] (h : R) : R :=
  -1172 * h ^ 10 - 12244 * h ^ 9 - 55682 * h ^ 8 - 113360 * h ^ 7 - 14176 * h ^ 6 + 190810 * h ^ 5 + 110833 *
    h ^ 4 - 91928 * h ^ 3 - 60594 * h ^ 2 + 15922 * h + 10247

private def envBaseCoeff6 {R : Type*} [CommRing R] (h : R) : R :=
  -4004 * h ^ 10 - 35092 * h ^ 9 - 147999 * h ^ 8 - 255894 * h ^ 7 + 54510 * h ^ 6 + 524774 * h ^ 5 + 216066 *
    h ^ 4 - 319306 * h ^ 3 - 171838 * h ^ 2 + 73262 * h + 41137

private def envBaseCoeff7 {R : Type*} [CommRing R] (h : R) : R :=
  -2378 * h ^ 9 - 16478 * h ^ 8 - 57591 * h ^ 7 - 41303 * h ^ 6 + 132313 * h ^ 5 + 139209 * h ^ 4 - 109533 * h
    ^ 3 - 113069 * h ^ 2 + 35845 * h + 31065

private def envBaseCoeff8 {R : Type*} [CommRing R] (h : R) : R :=
  -7927 * h ^ 8 - 45750 * h ^ 7 - 123099 * h ^ 6 + 108512 * h ^ 5 + 424993 * h ^ 4 - 129150 * h ^ 3 - 438069 *
    h ^ 2 + 69716 * h + 140262

private def envBaseCoeff9 {R : Type*} [CommRing R] (h : R) : R :=
  1141 * h ^ 7 + 8441 * h ^ 6 + 23472 * h ^ 5 - 9222 * h ^ 4 - 72635 * h ^ 3 - 25931 * h ^ 2 + 49846 * h +
    28408

private def envBaseCoeff10 {R : Type*} [CommRing R] (h : R) : R :=
  867 * h ^ 6 + 7204 * h ^ 5 + 9749 * h ^ 4 - 36260 * h ^ 3 - 42511 * h ^ 2 + 29824 * h + 31383

private def envBaseCoeff11 {R : Type*} [CommRing R] (h : R) : R :=
  -49 * h ^ 4 - 646 * h ^ 3 - 332 * h ^ 2 + 3126 * h + 2765

private def envBaseCoeff12 {R : Type*} [CommRing R] (h : R) : R :=
  -5 * h ^ 3 - 143 * h ^ 2 + 193 * h + 555

private def envBaseCoeff13 {R : Type*} [CommRing R] (h : R) : R :=
  -h + 3

private noncomputable def envBaseTail (h j : ℝ) : ℝ :=
  (1 / 128) * (h + 1) ^ 4 * envBaseCoeff3 h * j ^ 3 +
  (1 / 512) * (h + 1) ^ 3 * envBaseCoeff4 h * j ^ 4 +
  (1 / 128) * (h + 1) ^ 3 * envBaseCoeff5 h * j ^ 5 +
  (1 / 256) * (h + 1) ^ 2 * envBaseCoeff6 h * j ^ 6 +
  (1 / 128) * (h + 1) ^ 2 * envBaseCoeff7 h * j ^ 7 +
  (1 / 512) * (h + 1) ^ 2 * envBaseCoeff8 h * j ^ 8 +
  (1 / 128) * (1 - h) * (h + 1) * envBaseCoeff9 h * j ^ 9 +
  (1 / 256) * (1 - h) * (h + 1) * envBaseCoeff10 h * j ^ 10 +
  (1 / 64) * (h + 1) * (1 - h) ^ 2 * envBaseCoeff11 h * j ^ 11 +
  (1 / 64) * (h + 1) * (1 - h) ^ 2 * envBaseCoeff12 h * j ^ 12 +
  (1 / 4) * (h + 1) * (1 - h) ^ 2 * envBaseCoeff13 h * j ^ 13

private def envShapeCoeff0 {R : Type*} [CommRing R] (h : R) : R :=
  -4 * h ^ 9 - 24 * h ^ 8 - 19 * h ^ 7 + 146 * h ^ 6 + 146 * h ^ 5 - 672 * h ^ 4 - 1373 * h ^ 3 - 606 * h ^ 2
    + 354 * h + 252

private def envShapeCoeff1 {R : Type*} [CommRing R] (h : R) : R :=
  -47 * h ^ 10 - 258 * h ^ 9 - 156 * h ^ 8 + 1817 * h ^ 7 + 1625 * h ^ 6 - 8460 * h ^ 5 - 16640 * h ^ 4 - 6813
    * h ^ 3 + 4998 * h ^ 2 + 3858 * h + 396

private def envShapeCoeff2 {R : Type*} [CommRing R] (h : R) : R :=
  -243 * h ^ 11 - 1203 * h ^ 10 - 421 * h ^ 9 + 9795 * h ^ 8 + 8241 * h ^ 7 - 45205 * h ^ 6 - 88465 * h ^ 5 -
    36259 * h ^ 4 + 29642 * h ^ 3 + 26880 * h ^ 2 + 5646 * h + 360

private def envShapeCoeff3 {R : Type*} [CommRing R] (h : R) : R :=
  -725 * h ^ 10 - 2465 * h ^ 9 + 2400 * h ^ 8 + 28108 * h ^ 7 - 1887 * h ^ 6 - 132909 * h ^ 5 - 140388 * h ^ 4
    + 19826 * h ^ 3 + 78358 * h ^ 2 + 29328 * h + 3618

private def envShapeCoeff4 {R : Type*} [CommRing R] (h : R) : R :=
  -1371 * h ^ 10 - 3926 * h ^ 9 + 6020 * h ^ 8 + 55517 * h ^ 7 + 4560 * h ^ 6 - 250837 * h ^ 5 - 294402 * h ^
    4 + 18763 * h ^ 3 + 180091 * h ^ 2 + 90627 * h + 15054

private def envShapeCoeff5 {R : Type*} [CommRing R] (h : R) : R :=
  -1687 * h ^ 9 - 2350 * h ^ 8 + 11539 * h ^ 7 + 64523 * h ^ 6 - 36257 * h ^ 5 - 272947 * h ^ 4 - 154915 * h ^
    3 + 133765 * h ^ 2 + 138376 * h + 34577

private def envShapeCoeff6 {R : Type*} [CommRing R] (h : R) : R :=
  -1309 * h ^ 9 - 1479 * h ^ 8 + 10074 * h ^ 7 + 65328 * h ^ 6 - 3932 * h ^ 5 - 245714 * h ^ 4 - 194170 * h ^
    3 + 108936 * h ^ 2 + 164889 * h + 48609

private def envShapeCoeff7 {R : Type*} [CommRing R] (h : R) : R :=
  -543 * h ^ 8 - 409 * h ^ 7 + 5895 * h ^ 6 + 44343 * h ^ 5 - 18735 * h ^ 4 - 134723 * h ^ 3 - 33499 * h ^ 2 +
    86309 * h + 43682

private def envShapeCoeff8 {R : Type*} [CommRing R] (h : R) : R :=
  -5 * h ^ 7 - 835 * h ^ 6 + 3345 * h ^ 5 + 23555 * h ^ 4 - 21715 * h ^ 3 - 47261 * h ^ 2 + 17095 * h + 25309

private def envShapeCoeff9 {R : Type*} [CommRing R] (h : R) : R :=
  -57 * h ^ 5 + 419 * h ^ 4 - 938 * h ^ 3 - 4498 * h ^ 2 + 2227 * h + 4607

private def envShapeCoeff10 {R : Type*} [CommRing R] (h : R) : R :=
  -13 * h ^ 4 + 100 * h ^ 3 - 272 * h ^ 2 - 268 * h + 485

private def envShapeCoeff11 {R : Type*} [CommRing R] (h : R) : R :=
  h ^ 2 - 8 * h + 23

private noncomputable def envShape (h j : ℝ) : ℝ :=
  (1 / 128) * (h) ^ 2 * (h + 1) ^ 5 * envShapeCoeff0 h +
  (1 / 128) * (h) * (h + 1) ^ 4 * envShapeCoeff1 h * j ^ 1 +
  (1 / 128) * (h + 1) ^ 3 * envShapeCoeff2 h * j ^ 2 +
  (1 / 128) * (h + 1) ^ 3 * envShapeCoeff3 h * j ^ 3 +
  (1 / 128) * (h + 1) ^ 2 * envShapeCoeff4 h * j ^ 4 +
  (1 / 128) * (h + 1) ^ 2 * envShapeCoeff5 h * j ^ 5 +
  (1 / 128) * (h + 1) * envShapeCoeff6 h * j ^ 6 +
  (1 / 128) * (h + 1) * envShapeCoeff7 h * j ^ 7 +
  (1 / 128) * (h + 1) * envShapeCoeff8 h * j ^ 8 +
  (1 / 64) * (1 - h) * (h + 1) * envShapeCoeff9 h * j ^ 9 +
  (1 / 32) * (1 - h) * (h + 1) * envShapeCoeff10 h * j ^ 10 +
  (1 / 16) * (h + 1) * (1 - h) ^ 2 * envShapeCoeff11 h * j ^ 11

private def envMidCoeff0 {R : Type*} [CommRing R] (h : R) : R :=
  -16 * h ^ 10 - 112 * h ^ 9 - 165 * h ^ 8 + 592 * h ^ 7 + 1486 * h ^ 6 - 1128 * h ^ 5 - 7573 * h ^ 4 - 9616 *
    h ^ 3 - 3652 * h ^ 2 + 1272 * h + 912

private def envMidCoeff1 {R : Type*} [CommRing R] (h : R) : R :=
  -94 * h ^ 11 - 610 * h ^ 10 - 787 * h ^ 9 + 3785 * h ^ 8 + 8594 * h ^ 7 - 9132 * h ^ 6 - 47107 * h ^ 5 -
    54271 * h ^ 4 - 16890 * h ^ 3 + 10348 * h ^ 2 + 7068 * h + 696

private def envMidCoeff2 {R : Type*} [CommRing R] (h : R) : R :=
  -972 * h ^ 12 - 5784 * h ^ 11 - 6071 * h ^ 10 + 41986 * h ^ 9 + 88151 * h ^ 8 - 110820 * h ^ 7 - 508805 * h
    ^ 6 - 553862 * h ^ 5 - 138883 * h ^ 4 + 150152 * h ^ 3 + 108756 * h ^ 2 + 22200 * h + 1632

private def envMidCoeff3 {R : Type*} [CommRing R] (h : R) : R :=
  -725 * h ^ 11 - 3190 * h ^ 10 + 256 * h ^ 9 + 33342 * h ^ 8 + 34152 * h ^ 7 - 120898 * h ^ 6 - 272366 * h ^
    5 - 150992 * h ^ 4 + 61889 * h ^ 3 + 91728 * h ^ 2 + 30938 * h + 4026

private def envMidCoeff4 {R : Type*} [CommRing R] (h : R) : R :=
  -5484 * h ^ 11 - 21188 * h ^ 10 + 10881 * h ^ 9 + 266435 * h ^ 8 + 293981 * h ^ 7 - 906769 * h ^ 6 - 2176821
    * h ^ 5 - 1271367 * h ^ 4 + 568931 * h ^ 3 + 967377 * h ^ 2 + 409120 * h + 65864

private def envMidCoeff5 {R : Type*} [CommRing R] (h : R) : R :=
  -3374 * h ^ 10 - 8074 * h ^ 9 + 20027 * h ^ 8 + 162661 * h ^ 7 + 76337 * h ^ 6 - 601303 * h ^ 5 - 873837 * h
    ^ 4 - 103817 * h ^ 3 + 492801 * h ^ 2 + 337061 * h + 74638

private def envMidCoeff6 {R : Type*} [CommRing R] (h : R) : R :=
  -5236 * h ^ 10 - 11152 * h ^ 9 + 37347 * h ^ 8 + 318580 * h ^ 7 + 275300 * h ^ 6 - 980484 * h ^ 5 - 1786974
    * h ^ 4 - 421268 * h ^ 3 + 1028520 * h ^ 2 + 850420 * h + 207267

private def envMidCoeff7 {R : Type*} [CommRing R] (h : R) : R :=
  -543 * h ^ 9 - 952 * h ^ 8 + 5936 * h ^ 7 + 52088 * h ^ 6 + 27538 * h ^ 5 - 153776 * h ^ 4 - 172024 * h ^ 3
    + 47224 * h ^ 2 + 129365 * h + 45944

private def envMidCoeff8 {R : Type*} [CommRing R] (h : R) : R :=
  -5 * h ^ 8 - 840 * h ^ 7 + 2686 * h ^ 6 + 27356 * h ^ 5 + 2018 * h ^ 4 - 69392 * h ^ 3 - 31274 * h ^ 2 +
    41948 * h + 26223

private def envMidCoeff9 {R : Type*} [CommRing R] (h : R) : R :=
  -57 * h ^ 6 + 362 * h ^ 5 - 539 * h ^ 4 - 5480 * h ^ 3 - 2311 * h ^ 2 + 6846 * h + 4699

private def envMidCoeff10 {R : Type*} [CommRing R] (h : R) : R :=
  -13 * h ^ 5 + 87 * h ^ 4 - 173 * h ^ 3 - 541 * h ^ 2 + 216 * h + 488

private def envMidCoeff11 {R : Type*} [CommRing R] (h : R) : R :=
  h ^ 2 - 8 * h + 23

private noncomputable def envMid (h j : ℝ) : ℝ :=
  (1 / 512) * (h) ^ 2 * (h + 1) ^ 4 * envMidCoeff0 h +
  (1 / 256) * (h) * (h + 1) ^ 3 * envMidCoeff1 h * j ^ 1 +
  (1 / 512) * (h + 1) ^ 2 * envMidCoeff2 h * j ^ 2 +
  (1 / 128) * (h + 1) ^ 2 * envMidCoeff3 h * j ^ 3 +
  (1 / 512) * (h + 1) * envMidCoeff4 h * j ^ 4 +
  (1 / 256) * (h + 1) * envMidCoeff5 h * j ^ 5 +
  (1 / 512) * envMidCoeff6 h * j ^ 6 +
  (1 / 128) * envMidCoeff7 h * j ^ 7 +
  (1 / 128) * envMidCoeff8 h * j ^ 8 +
  (1 / 64) * (1 - h) * envMidCoeff9 h * j ^ 9 +
  (1 / 32) * (1 - h) * envMidCoeff10 h * j ^ 10 +
  (1 / 16) * (h + 1) * (1 - h) ^ 2 * envMidCoeff11 h * j ^ 11

private noncomputable def envBase (h j : ℝ) : ℝ :=
  h ^ 2 * (h + 1) ^ 6 / 512 * envBaseCoeff0 h +
  h * (h + 1) ^ 5 / 128 * envBaseCoeff1 h * j +
  (h + 1) ^ 4 / 256 * envBaseCoeff2 h * j ^ 2 + envBaseTail h j

private noncomputable def gPoly : Polynomial ℝ := envBaseCoeff0 Polynomial.X
private noncomputable def fPoly : Polynomial ℝ := envBaseCoeff1 Polynomial.X

private theorem power_charge {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) (n : ℕ) :
    h ^ (n + 2) ≤ h ^ 2 * (1 / 3 : ℝ) ^ n := by
  have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh hh1 n) (sq_nonneg h)
  simpa [pow_add, mul_comm] using this

private theorem polynomial_floor {p : Polynomial ℝ} {h m : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3)
    (hp : ∀ z, 0 ≤ z → z ≤ 1 / 3 → p.derivative.derivative.eval z ≤ 0)
    (he0 : m ≤ p.eval 0) (he1 : m ≤ p.eval (1 / 3)) : m ≤ p.eval h := by
  have hc : ConcaveOn ℝ (Set.Icc 0 (1 / 3)) (fun z => p.eval z) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (fun z _ => (p.hasDerivAt z).continuousAt.continuousWithinAt)
      (fun z _ => (p.hasDerivAt z).hasDerivWithinAt)
      (fun z _ => (p.derivative.hasDerivAt z).hasDerivWithinAt)
    intro z hz
    rw [interior_Icc] at hz
    exact hp z hz.1.le hz.2.le
  have hmin := hc.min_le_of_mem_Icc (by norm_num : (0 : ℝ) ∈ Set.Icc 0 (1 / 3))
    (by norm_num : (1 / 3 : ℝ) ∈ Set.Icc 0 (1 / 3))
    (show h ∈ Set.Icc 0 (1 / 3) from ⟨hh, hh1⟩)
  exact (le_min he0 he1).trans hmin

/-- The boundary coefficient is concave and stays above sixteen. -/
private theorem env_boundary_floor {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) :
    16 ≤ envBaseCoeff0 h := by
  have hthird {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) :
      0 ≤ gPoly.derivative.derivative.derivative.eval h := by
    have h3 := power_charge hh hh1 1
    have h4 := power_charge hh hh1 2
    have h5 := power_charge hh hh1 3
    have h6 := power_charge hh hh1 4
    have h7 := power_charge hh hh1 5
    have h8 := power_charge hh hh1 6
    have h9 := power_charge hh hh1 7
    have h10 := power_charge hh hh1 8
    have h11 := power_charge hh hh1 9
    have h12 := power_charge hh hh1 10
    norm_num at h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    have hstep : h ^ 2 ≤ h / 3 := by nlinarith only [mul_nonneg hh (sub_nonneg.mpr hh1)]
    norm_num [gPoly, envBaseCoeff0, Polynomial.derivative_mul, Polynomial.derivative_pow]
    linarith only [hstep, hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3,
      pow_nonneg hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9,
      pow_nonneg hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
  have hm : MonotoneOn (fun z => gPoly.derivative.derivative.eval z) (Set.Icc 0 (1 / 3)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun z _ => (gPoly.derivative.derivative.hasDerivAt z).continuousAt.continuousWithinAt)
      (fun z _ => (gPoly.derivative.derivative.hasDerivAt z).hasDerivWithinAt)
    intro z hz
    rw [interior_Icc] at hz
    exact hthird hz.1.le hz.2.le
  have hc : ∀ z, 0 ≤ z → z ≤ 1 / 3 → gPoly.derivative.derivative.eval z ≤ 0 := by
    intro z hz hz1
    have hmax : gPoly.derivative.derivative.eval (1 / 3) ≤ 0 := by
      norm_num [gPoly, envBaseCoeff0, Polynomial.derivative_mul, Polynomial.derivative_pow]
    exact (hm ⟨hz, hz1⟩ (by norm_num) hz1).trans hmax
  have hfloor := polynomial_floor (p := gPoly) hh hh1 hc
    (by norm_num [gPoly, envBaseCoeff0] : (16 : ℝ) ≤ gPoly.eval 0)
    (by norm_num [gPoly, envBaseCoeff0] : (16 : ℝ) ≤ gPoly.eval (1 / 3))
  simpa [gPoly, envBaseCoeff0] using hfloor

/-- Concavity also controls the only unfavorable first-order term. -/
private theorem env_linear_floor {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) :
    -1 ≤ envBaseCoeff1 h := by
  have hc : ∀ z, 0 ≤ z → z ≤ 1 / 3 → fPoly.derivative.derivative.eval z ≤ 0 := by
    intro h hh hh1
    have h3 := power_charge hh hh1 1
    have h4 := power_charge hh hh1 2
    have h5 := power_charge hh hh1 3
    have h6 := power_charge hh hh1 4
    have h7 := power_charge hh hh1 5
    have h8 := power_charge hh hh1 6
    have h9 := power_charge hh hh1 7
    have h10 := power_charge hh hh1 8
    have h11 := power_charge hh hh1 9
    have h12 := power_charge hh hh1 10
    norm_num at h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    have hstep : h ^ 2 ≤ h / 3 := by nlinarith only [mul_nonneg hh (sub_nonneg.mpr hh1)]
    have hb : fPoly.derivative.derivative.eval h ≤ -1716 + 3200 * h := by
      norm_num [fPoly, envBaseCoeff1, Polynomial.derivative_mul, Polynomial.derivative_pow]
      linarith only [hstep, hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3,
        pow_nonneg hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9,
        pow_nonneg hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh1]
  have hfloor := polynomial_floor (p := fPoly) hh hh1 hc
    (by norm_num [fPoly, envBaseCoeff1] : (-1 : ℝ) ≤ fPoly.eval 0)
    (by norm_num [fPoly, envBaseCoeff1] : (-1 : ℝ) ≤ fPoly.eval (1 / 3))
  simpa [fPoly, envBaseCoeff1] using hfloor

/-- Higher powers are absorbed by `hⁿ ≤ h²/3ⁿ⁻²`. -/
private theorem envBase_coeffs_nonneg {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) :
    (-64 : ℝ) ≤ envBaseCoeff2 h ∧
    0 ≤ envBaseCoeff3 h ∧
    0 ≤ envBaseCoeff4 h ∧
    0 ≤ envBaseCoeff5 h ∧
    0 ≤ envBaseCoeff6 h ∧
    0 ≤ envBaseCoeff7 h ∧
    0 ≤ envBaseCoeff8 h ∧
    0 ≤ envBaseCoeff9 h ∧
    0 ≤ envBaseCoeff10 h ∧
    0 ≤ envBaseCoeff11 h ∧
    0 ≤ envBaseCoeff12 h ∧
    0 ≤ envBaseCoeff13 h := by
  have h3 := power_charge hh hh1 1
  have h4 := power_charge hh hh1 2
  have h5 := power_charge hh hh1 3
  have h6 := power_charge hh hh1 4
  have h7 := power_charge hh hh1 5
  have h8 := power_charge hh hh1 6
  have h9 := power_charge hh hh1 7
  have h10 := power_charge hh hh1 8
  have h11 := power_charge hh hh1 9
  have h12 := power_charge hh hh1 10
  norm_num at h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hstep : 0 ≤ h * (1 / 3 - h) := mul_nonneg hh (sub_nonneg.mpr hh1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hb : -5200 * h ^ 2 + 1116 * h + 144 ≤ envBaseCoeff2 h := by
      dsimp [envBaseCoeff2]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -13201 * h ^ 2 + 2766 * h + 774 ≤ envBaseCoeff3 h := by
      dsimp [envBaseCoeff3]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -180492 * h ^ 2 + 39100 * h + 14448 ≤ envBaseCoeff4 h := by
      dsimp [envBaseCoeff4]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -91961 * h ^ 2 + 15922 * h + 10247 ≤ envBaseCoeff5 h := by
      dsimp [envBaseCoeff5]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -279547 * h ^ 2 + 73262 * h + 41137 ≤ envBaseCoeff6 h := by
      dsimp [envBaseCoeff6]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -150351 * h ^ 2 + 35845 * h + 31065 ≤ envBaseCoeff7 h := by
      dsimp [envBaseCoeff7]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -482838 * h ^ 2 + 69716 * h + 140262 ≤ envBaseCoeff8 h := by
      dsimp [envBaseCoeff8]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -51168 * h ^ 2 + 49846 * h + 28408 ≤ envBaseCoeff9 h := by
      dsimp [envBaseCoeff9]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -54598 * h ^ 2 + 29824 * h + 31383 ≤ envBaseCoeff10 h := by
      dsimp [envBaseCoeff10]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -553 * h ^ 2 + 3126 * h + 2765 ≤ envBaseCoeff11 h := by
      dsimp [envBaseCoeff11]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -145 * h ^ 2 + 193 * h + 555 ≤ envBaseCoeff12 h := by
      dsimp [envBaseCoeff12]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -h + 3 ≤ envBaseCoeff13 h := by
      dsimp [envBaseCoeff13]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]

/-- Higher powers are absorbed by `hⁿ ≤ h²/3ⁿ⁻²`. -/
private theorem envShape_coeffs_nonneg {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) :
    0 ≤ envShapeCoeff0 h ∧
    0 ≤ envShapeCoeff1 h ∧
    0 ≤ envShapeCoeff2 h ∧
    0 ≤ envShapeCoeff3 h ∧
    0 ≤ envShapeCoeff4 h ∧
    0 ≤ envShapeCoeff5 h ∧
    0 ≤ envShapeCoeff6 h ∧
    0 ≤ envShapeCoeff7 h ∧
    0 ≤ envShapeCoeff8 h ∧
    0 ≤ envShapeCoeff9 h ∧
    0 ≤ envShapeCoeff10 h ∧
    0 ≤ envShapeCoeff11 h := by
  have h3 := power_charge hh hh1 1
  have h4 := power_charge hh hh1 2
  have h5 := power_charge hh hh1 3
  have h6 := power_charge hh hh1 4
  have h7 := power_charge hh hh1 5
  have h8 := power_charge hh hh1 6
  have h9 := power_charge hh hh1 7
  have h10 := power_charge hh hh1 8
  have h11 := power_charge hh hh1 9
  have h12 := power_charge hh hh1 10
  norm_num at h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hstep : 0 ≤ h * (1 / 3 - h) := mul_nonneg hh (sub_nonneg.mpr hh1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hb : -1139 * h ^ 2 + 354 * h + 252 ≤ envShapeCoeff0 h := by
      dsimp [envShapeCoeff0]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : 564 * h ^ 2 + 3858 * h + 396 ≤ envShapeCoeff1 h := by
      dsimp [envShapeCoeff1]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : 19016 * h ^ 2 + 5646 * h + 360 ≤ envShapeCoeff2 h := by
      dsimp [envShapeCoeff2]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : 57812 * h ^ 2 + 29328 * h + 3618 ≤ envShapeCoeff3 h := by
      dsimp [envShapeCoeff3]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : 138087 * h ^ 2 + 90627 * h + 15054 ≤ envShapeCoeff4 h := by
      dsimp [envShapeCoeff4]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : 50452 * h ^ 2 + 138376 * h + 34577 ≤ envShapeCoeff5 h := by
      dsimp [envShapeCoeff5]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : 16762 * h ^ 2 + 164889 * h + 48609 ≤ envShapeCoeff6 h := by
      dsimp [envShapeCoeff6]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -80491 * h ^ 2 + 86309 * h + 43682 ≤ envShapeCoeff7 h := by
      dsimp [envShapeCoeff7]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -54510 * h ^ 2 + 17095 * h + 25309 ≤ envShapeCoeff8 h := by
      dsimp [envShapeCoeff8]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -4813 * h ^ 2 + 2227 * h + 4607 ≤ envShapeCoeff9 h := by
      dsimp [envShapeCoeff9]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -274 * h ^ 2 - 268 * h + 485 ≤ envShapeCoeff10 h := by
      dsimp [envShapeCoeff10]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : h ^ 2 - 8 * h + 23 ≤ envShapeCoeff11 h := by
      dsimp [envShapeCoeff11]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]

/-- Higher powers are absorbed by `hⁿ ≤ h²/3ⁿ⁻²`. -/
private theorem envMid_coeffs_nonneg {h : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) :
    0 ≤ envMidCoeff0 h ∧
    0 ≤ envMidCoeff1 h ∧
    0 ≤ envMidCoeff2 h ∧
    0 ≤ envMidCoeff3 h ∧
    0 ≤ envMidCoeff4 h ∧
    0 ≤ envMidCoeff5 h ∧
    0 ≤ envMidCoeff6 h ∧
    0 ≤ envMidCoeff7 h ∧
    0 ≤ envMidCoeff8 h ∧
    0 ≤ envMidCoeff9 h ∧
    0 ≤ envMidCoeff10 h ∧
    0 ≤ envMidCoeff11 h := by
  have h3 := power_charge hh hh1 1
  have h4 := power_charge hh hh1 2
  have h5 := power_charge hh hh1 3
  have h6 := power_charge hh hh1 4
  have h7 := power_charge hh hh1 5
  have h8 := power_charge hh hh1 6
  have h9 := power_charge hh hh1 7
  have h10 := power_charge hh hh1 8
  have h11 := power_charge hh hh1 9
  have h12 := power_charge hh hh1 10
  norm_num at h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hstep : 0 ≤ h * (1 / 3 - h) := mul_nonneg hh (sub_nonneg.mpr hh1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hb : -7741 * h ^ 2 + 1272 * h + 912 ≤ envMidCoeff0 h := by
      dsimp [envMidCoeff0]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -3171 * h ^ 2 + 7068 * h + 696 ≤ envMidCoeff1 h := by
      dsimp [envMidCoeff1]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : 66072 * h ^ 2 + 22200 * h + 1632 ≤ envMidCoeff2 h := by
      dsimp [envMidCoeff2]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : 63370 * h ^ 2 + 30938 * h + 4026 ≤ envMidCoeff3 h := by
      dsimp [envMidCoeff3]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : 734292 * h ^ 2 + 409120 * h + 65864 ≤ envMidCoeff4 h := by
      dsimp [envMidCoeff4]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : 338827 * h ^ 2 + 337061 * h + 74638 ≤ envMidCoeff5 h := by
      dsimp [envMidCoeff5]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : 653224 * h ^ 2 + 850420 * h + 207267 ≤ envMidCoeff6 h := by
      dsimp [envMidCoeff6]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -27206 * h ^ 2 + 129365 * h + 45944 ≤ envMidCoeff7 h := by
      dsimp [envMidCoeff7]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -54409 * h ^ 2 + 41948 * h + 26223 ≤ envMidCoeff8 h := by
      dsimp [envMidCoeff8]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -4199 * h ^ 2 + 6846 * h + 4699 ≤ envMidCoeff9 h := by
      dsimp [envMidCoeff9]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : -600 * h ^ 2 + 216 * h + 488 ≤ envMidCoeff10 h := by
      dsimp [envMidCoeff10]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]
  · have hb : h ^ 2 - 8 * h + 23 ≤ envMidCoeff11 h := by
      dsimp [envMidCoeff11]
      linarith only [hh, sq_nonneg h, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, pow_nonneg hh 3, pow_nonneg
        hh 4, pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_nonneg hh 9, pow_nonneg
        hh 10, pow_nonneg hh 11, pow_nonneg hh 12]
    linarith only [hb, hh, hh1, hstep, sq_nonneg h]

private theorem envBaseTail_nonneg {h j : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) (hj : 0 ≤ j) :
    0 ≤ envBaseTail h j := by
  obtain ⟨hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13⟩ := envBase_coeffs_nonneg hh hh1
  have hgap : 0 ≤ 1 - h := by linarith only [hh1]
  unfold envBaseTail
  positivity

private theorem envShape_nonneg {h j : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) (hj : 0 ≤ j) :
    0 ≤ envShape h j := by
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11⟩ := envShape_coeffs_nonneg hh hh1
  have hgap : 0 ≤ 1 - h := by linarith only [hh1]
  unfold envShape
  positivity

private theorem envMid_nonneg {h j : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1 / 3) (hj : 0 ≤ j) :
    0 ≤ envMid h j := by
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11⟩ := envMid_coeffs_nonneg hh hh1
  have hgap : 0 ≤ 1 - h := by linarith only [hh1]
  unfold envMid
  positivity

private theorem envBase_lower {h j : ℝ} (hh : 1 / 5 ≤ h) (hh1 : h ≤ 1 / 3) (hj : 0 ≤ j) :
    h ^ 2 / 12 - h * j / 16 - j ^ 2 ≤ envBase h j := by
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hg := env_boundary_floor hh0 hh1
  have hf := env_linear_floor hh0 hh1
  obtain ⟨hb, _⟩ := envBase_coeffs_nonneg hh0 hh1
  have h6 : (8 / 3 : ℝ) ≤ (h + 1) ^ 6 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 6 / 5)
      (show (6 / 5 : ℝ) ≤ h + 1 by linarith only [hh]) 6
    norm_num at hp
    linarith only [hp]
  have h5 : (h + 1) ^ 5 ≤ 8 := by
    have hp := pow_le_pow_left₀ (show 0 ≤ h + 1 by positivity)
      (show h + 1 ≤ (4 / 3 : ℝ) by linarith only [hh1]) 5
    norm_num at hp
    linarith only [hp]
  have h4 : (h + 1) ^ 4 ≤ 4 := by
    have hp := pow_le_pow_left₀ (show 0 ≤ h + 1 by positivity)
      (show h + 1 ≤ (4 / 3 : ℝ) by linarith only [hh1]) 4
    norm_num at hp
    linarith only [hp]
  have hc0 : h ^ 2 / 12 ≤ h ^ 2 * (h + 1) ^ 6 / 512 * envBaseCoeff0 h := by
    have hm := mul_le_mul h6 hg (by norm_num : (0 : ℝ) ≤ 16) (by positivity : 0 ≤ (h + 1) ^ 6)
    have hm1 := mul_le_mul_of_nonneg_left hm (sq_nonneg h)
    nlinarith only [hm1, sq_nonneg h]
  have hc1 : -h / 16 ≤ h * (h + 1) ^ 5 / 128 * envBaseCoeff1 h := by
    have hm := mul_le_mul_of_nonneg_left hf (show 0 ≤ h * (h + 1) ^ 5 / 128 by positivity)
    have hm1 := mul_le_mul_of_nonneg_left h5 hh0
    nlinarith only [hm, hm1]
  have hc2 : -1 ≤ (h + 1) ^ 4 / 256 * envBaseCoeff2 h := by
    have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ (h + 1) ^ 4 / 256 by positivity)
    linarith only [hm, h4]
  have hj1 := mul_le_mul_of_nonneg_right hc1 hj
  have hj2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg j)
  have ht := envBaseTail_nonneg hh0 hh1 hj
  unfold envBase
  linarith only [hc0, hj1, hj2, ht]

private def envVNum (t x : ℝ) : ℝ :=
  (1 + x) * (x ^ 2 + 6 * x + 6) + (1 - t) ^ 2 * (x ^ 2 + 6 * x + 6) -
    3 * (1 - t) * (1 + x) * (x + 2)

private def envKNum (t x k : ℝ) : ℝ :=
  t * (k ^ 2 - k * t + t ^ 2) +
    (k * (-1 + t ^ 2) + t ^ 2 * (2 - t)) * (x * (x + 2))

private def envPNum (t x k : ℝ) : ℝ := x * (x + 2) * (k + t * x * (x + 2))

private def envD0Num (t x k : ℝ) : ℝ :=
  t * (k + 2 * t * x + x ^ 2) * (1 + x) * ((t + x) ^ 2 - (1 - t) * (1 + x)) +
    (1 + x) * (envKNum t x k - t * (k + 2 * t * x + x ^ 2) ^ 2) +
    t * (t + x) * (1 + x) ^ 2 * ((t + x) * (1 - t) - (k + 2 * t * x + x ^ 2)) +
    t * (k + 2 * t * x + x ^ 2) * (1 - t) * (t + x) ^ 2

private def envD1Num (t x k : ℝ) : ℝ :=
  t * (k + 2 * t * x + x ^ 2) * (1 + x) * (t + x + (1 + x)) + envPNum t x k

private noncomputable def envCleared (t x k : ℝ) : ℝ :=
  4 * envVNum t x * envKNum t x k *
      (t * (t + x) ^ 2 * (1 + x) ^ 3 * (x ^ 2 + 6 * x + 6)) +
    4 * (envVNum t x) ^ 2 * envPNum t x k * (t * (t + x) ^ 2 * (1 + x) ^ 2) -
    ((x ^ 2 + 6 * x + 6) * envD0Num t x k + envD1Num t x k * envVNum t x) ^ 2 -
    t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 *
      (16 * (k - t ^ 2) ^ 2 * (3 / 16 - (1 - 2 * t) ^ 2 / 32))

private theorem env_clear_norm {t x k : ℝ} (ht : 0 < t) (hx : 0 < x) :
    envCleared t x k =
      t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 *
        (nsfNen t x k (nsfVq t x) - 16 * (k - t ^ 2) ^ 2 * (3 / 16 - (1 - 2 * t) ^ 2 / 32)) := by
  have hp : 0 < t + x := by positivity
  have hW : 0 < 1 + x := by positivity
  have hD : 0 < x ^ 2 + 6 * x + 6 := by positivity
  have hv : envVNum t x = (1 + x) * (x ^ 2 + 6 * x + 6) * nsfVq t x := by
    unfold envVNum nsfVq
    field_simp
  have hk : envKNum t x k = t * nsfK0 t x k := by
    unfold envKNum nsfK0
    field_simp
  have hvp : envPNum t x k = t * nsfPv t x k := by
    unfold envPNum nsfPv
    field_simp
  have hd0 : envD0Num t x k = t * (t + x) * (1 + x) ^ 2 * nsfD0 t x k := by
    unfold envD0Num envKNum nsfD0 nsfK0 nsfg
    field_simp
    ring
  have hd1 : envD1Num t x k = t * (t + x) * (1 + x) * nsfDp t x k := by
    unfold envD1Num envPNum nsfDp nsfPv
    field_simp
  unfold envCleared
  rw [hv, hk, hvp, hd0, hd1]
  unfold nsfNen
  ring

private theorem env_decompose (t x k : ℝ) :
    envBase (1 - 2 * t) (2 * t + x - 1) + (k - 1) *
      ((1 - 2 * (k - 1)) * envShape (1 - 2 * t) (2 * t + x - 1) +
        2 * (k - 1) * envMid (1 - 2 * t) (2 * t + x - 1)) = envCleared t x k := by
  simp only [envBase, envBaseTail, envShape, envMid,
    envBaseCoeff0, envBaseCoeff1, envBaseCoeff2, envBaseCoeff3, envBaseCoeff4, envBaseCoeff5, envBaseCoeff6,
      envBaseCoeff7, envBaseCoeff8, envBaseCoeff9, envBaseCoeff10, envBaseCoeff11, envBaseCoeff12,
      envBaseCoeff13, envShapeCoeff0, envShapeCoeff1, envShapeCoeff2, envShapeCoeff3, envShapeCoeff4,
      envShapeCoeff5, envShapeCoeff6, envShapeCoeff7, envShapeCoeff8, envShapeCoeff9, envShapeCoeff10,
      envShapeCoeff11, envMidCoeff0, envMidCoeff1, envMidCoeff2, envMidCoeff3, envMidCoeff4, envMidCoeff5,
      envMidCoeff6, envMidCoeff7, envMidCoeff8, envMidCoeff9, envMidCoeff10, envMidCoeff11,
    envCleared, envVNum, envKNum, envPNum, envD0Num, envD1Num]
  ring

private theorem env_clearing {t x k : ℝ} (ht : 0 < t) (hx : 0 < x) :
    envBase (1 - 2 * t) (2 * t + x - 1) + (k - 1) *
      ((1 - 2 * (k - 1)) * envShape (1 - 2 * t) (2 * t + x - 1) +
        2 * (k - 1) * envMid (1 - 2 * t) (2 * t + x - 1)) =
      t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 *
        (nsfNen t x k (nsfVq t x) - 16 * (k - t ^ 2) ^ 2 * (3 / 16 - (1 - 2 * t) ^ 2 / 32)) :=
  (env_decompose t x k).trans (env_clear_norm ht hx)

/-- The geometric imbalance controls the loss from `3/16` at the norm ceiling. -/
theorem nsf_envelope_imbalance {t x k : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hj0 : 0 ≤ 2 * t + x - 1) (hj1 : 2 * t + x - 1 ≤ 1 / 30)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 3 / 2) :
    3 / 16 - (1 - 2 * t) ^ 2 / 32 <
      nsfNen t x k (nsfVq t x) / (16 * (k - t ^ 2) ^ 2) := by
  let h := 1 - 2 * t
  let j := 2 * t + x - 1
  let u := k - 1
  have hh : 1 / 5 ≤ h := by dsimp [h]; linarith only [ht1]
  have hh1 : h ≤ 1 / 3 := by dsimp [h]; linarith only [ht0]
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hj : 0 ≤ j := hj0
  have hjh : j ≤ h / 6 := by dsimp [h, j]; linarith only [ht1, hj1]
  have hu : 0 ≤ u := by dsimp [u]; linarith only [hk0]
  have hu1 : 0 ≤ 1 - 2 * u := by dsimp [u]; linarith only [hk1]
  have hlo := envBase_lower hh hh1 hj
  have hprod := mul_le_mul_of_nonneg_left hjh hh0
  have hj2 := mul_le_mul hjh hjh hj (by positivity : 0 ≤ h / 6)
  have hbase : h ^ 2 / 24 < envBase h j := by
    nlinarith only [hlo, hprod, hj2, sq_pos_of_pos (show 0 < h by linarith only [hh])]
  have hshape := envShape_nonneg hh0 hh1 hj
  have hmid := envMid_nonneg hh0 hh1 hj
  have hinc : 0 ≤ u * ((1 - 2 * u) * envShape h j + 2 * u * envMid h j) := by positivity
  have hpos : 0 < envBase h j + u * ((1 - 2 * u) * envShape h j + 2 * u * envMid h j) := by
    linarith only [hbase, hinc, sq_nonneg h]
  have ht : 0 < t := by linarith only [ht0]
  have hx : 0 < x := by linarith only [ht1, hj0]
  have hp : 0 < t + x := by positivity
  have hW : 0 < 1 + x := by positivity
  have hD : 0 < x ^ 2 + 6 * x + 6 := by positivity
  have heq := env_clearing (k := k) ht hx
  rw [heq] at hpos
  have hexcess := pos_of_mul_pos_right hpos (by positivity :
    0 ≤ t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2)
  have hs : 0 < 16 * (k - t ^ 2) ^ 2 := by
    have : 0 < k - t ^ 2 := by nlinarith only [hk0, ht0, ht1]
    positivity
  rw [lt_div_iff₀ hs]
  linarith only [hexcess]

end SmoothedOctagon
