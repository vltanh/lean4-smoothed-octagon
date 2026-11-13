module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# A boundary-gap inequality for the event factor

The event-factor quadratic is controlled by a boundary gap and a displacement.
After clearing positive denominators, their comparison is the polynomial below.
It is concave in the short gap. At gap zero it increases with the order parameter.
At the other end it decreases up to one quarter and is convex thereafter; a
positive supporting tangent proves the remaining sign.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The cleared comparison between the boundary gap and the event displacement. -/
def nsfEventBarrier {R : Type*} [CommRing R] (h j : R) : R :=
  (2 * (h + 1) ^ 5 * (30 * h ^ 7 + 211 * h ^ 6 + 604 * h ^ 5 + 559 * h ^ 4 - 50 * h ^ 3 - 139 * h ^ 2 + 66 * h - 6)) +
  ((h + 1) ^ 4 * (650 * h ^ 7 + 4358 * h ^ 6 + 12778 * h ^ 5 + 13411 * h ^ 4 - 780 * h ^ 3 - 6717 * h ^ 2 - 958 * h +
    498)) * j ^ 1 +
  (2 * (h + 1) ^ 3 * (1515 * h ^ 7 + 9868 * h ^ 6 + 29659 * h ^ 5 + 33352 * h ^ 4 - 1253 * h ^ 3 - 21895 * h ^ 2 -
    7636 * h + 920)) * j ^ 2 +
  ((h + 1) ^ 3 * (8050 * h ^ 6 + 43427 * h ^ 5 + 113209 * h ^ 4 + 69502 * h ^ 3 - 74390 * h ^ 2 - 65337 * h - 1521)) *
    j ^ 3 +
  (2 * (h + 1) ^ 2 * (6755 * h ^ 6 + 35777 * h ^ 5 + 92377 * h ^ 4 + 58528 * h ^ 3 - 62912 * h ^ 2 - 65667 * h -
    7918)) * j ^ 4 +
  ((h + 1) ^ 2 * (14910 * h ^ 5 + 61956 * h ^ 4 + 125906 * h ^ 3 - 10099 * h ^ 2 - 123100 * h - 28733)) * j ^ 5 +
  (2 * (h + 1) * (5425 * h ^ 5 + 20944 * h ^ 4 + 35439 * h ^ 3 - 5931 * h ^ 2 - 37232 * h - 10725)) * j ^ 6 +
  ((h + 1) * (5030 * h ^ 4 + 10871 * h ^ 3 + 4339 * h ^ 2 - 15619 * h - 3341)) * j ^ 7 +
  (2 * (h - 1) * (675 * h ^ 3 + 881 * h ^ 2 - 1831 * h - 2165)) * j ^ 8 +
  (4 * (h - 1) * (40 * h ^ 2 - 259 * h - 555)) * j ^ 9 +
  (-256 * (h - 1)) * j ^ 10
private noncomputable def pH (j : ℝ) : Polynomial ℝ := nsfEventBarrier Polynomial.X (Polynomial.C j)
private noncomputable def pJ (h : ℝ) : Polynomial ℝ := nsfEventBarrier (Polynomial.C h) Polynomial.X

private theorem pH_eval (h j : ℝ) : (pH j).eval h = nsfEventBarrier h j := by
  simp [pH, nsfEventBarrier]

private theorem pJ_eval (h j : ℝ) : (pJ h).eval j = nsfEventBarrier h j := by
  simp [pJ, nsfEventBarrier]

private theorem poly_convex {p : Polynomial ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (hp : ∀ z ∈ D, 0 ≤ p.derivative.derivative.eval z) :
    ConvexOn ℝ D (fun z => p.eval z) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg hD
    (fun z _ => (p.hasDerivAt z).continuousAt.continuousWithinAt)
    (fun z _ => (p.hasDerivAt z).hasDerivWithinAt)
    (fun z _ => (p.derivative.hasDerivAt z).hasDerivWithinAt)
  intro z hz
  exact hp z (interior_subset hz)

private def eventG {R : Type*} [CommRing R] (h : R) : R :=
  30 * h ^ 7 + 211 * h ^ 6 + 604 * h ^ 5 + 559 * h ^ 4 - 50 * h ^ 3 - 139 * h ^ 2 + 66 * h - 6

private noncomputable def gPoly : Polynomial ℝ := eventG Polynomial.X

private theorem eventG_curvature {h : ℝ} (hh : 1 / 5 ≤ h) :
    0 ≤ gPoly.derivative.derivative.eval h := by
  have hh0 : 0 ≤ h := by linarith only [hh]
  have h2 : h / 5 ≤ h ^ 2 := by nlinarith only [mul_nonneg hh0 (sub_nonneg.mpr hh)]
  have h3 : h ^ 2 / 5 ≤ h ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh)]
  have h2' : (1 / 25 : ℝ) ≤ h ^ 2 := by nlinarith only [hh, sq_nonneg (h - 1 / 5)]
  have hlo : 0 ≤ 12000 * h ^ 3 + 6700 * h ^ 2 - 300 * h - 280 := by linarith only [h2, h3, h2']
  have hrest : 0 ≤ gPoly.derivative.derivative.eval h -
      (12000 * h ^ 3 + 6700 * h ^ 2 - 300 * h - 280) := by
    norm_num [gPoly, eventG, Polynomial.derivative_mul, Polynomial.derivative_pow]
    apply le_of_sub_nonneg
    ring_nf
    positivity
  linarith only [hlo, hrest]

private theorem eventG_pos {h : ℝ} (hh : 1 / 5 ≤ h) : 0 < gPoly.eval h := by
  have hm' : MonotoneOn (fun z => gPoly.derivative.eval z) (Set.Ici (1 / 5)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
      (fun z _ => (gPoly.derivative.hasDerivAt z).continuousAt.continuousWithinAt)
      (fun z _ => (gPoly.derivative.hasDerivAt z).hasDerivWithinAt)
    intro z hz
    rw [interior_Ici] at hz
    exact eventG_curvature hz.le
  have hm : MonotoneOn (fun z => gPoly.eval z) (Set.Ici (1 / 5)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici _)
      (fun z _ => (gPoly.hasDerivAt z).continuousAt.continuousWithinAt)
      (fun z _ => (gPoly.hasDerivAt z).hasDerivWithinAt)
    intro z hz
    rw [interior_Ici] at hz
    have hbase : 0 ≤ gPoly.derivative.eval (1 / 5) := by
      norm_num [gPoly, eventG, Polynomial.derivative_mul, Polynomial.derivative_pow]
    exact hbase.trans (hm' (by simp) hz.le hz.le)
  have hbase : 0 < gPoly.eval (1 / 5) := by norm_num [gPoly, eventG]
  exact hbase.trans_le (hm (by simp) hh hh)

private theorem event_zero_pos {h : ℝ} (hh : 1 / 5 ≤ h) : 0 < nsfEventBarrier h 0 := by
  have hg := eventG_pos hh
  have heq : nsfEventBarrier h 0 = 2 * (h + 1) ^ 5 * gPoly.eval h := by
    simp [nsfEventBarrier, nsfEventBarrier, gPoly, eventG]
  rw [heq]
  have hh0 : 0 < h := by linarith only [hh]
  positivity

/-- A nonpositive slope on the left branch follows by absorbing the high powers. -/
private theorem event_endpoint_decreasing {h : ℝ} (hh : 1 / 5 ≤ h) (hh1 : h ≤ 1 / 4) :
    (pH (1 / 30)).derivative.eval h ≤ 0 := by
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hu (n : ℕ) : h ^ (n + 2) ≤ h ^ 2 * (1 / 4 : ℝ) ^ n := by
    have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh0 hh1 n) (sq_nonneg h)
    simpa [pow_add, mul_comm] using this
  have hupper : (pH (1 / 30)).derivative.eval h ≤
      100 - 180 * h - 4600 * h ^ 2 - 8000 * h ^ 3 + 25500 * h ^ 4 + 121000 * h ^ 5 + 210000 * h ^ 6 + 205000 * h ^ 7
       + 200000 * (h ^ 8 + h ^ 9 + h ^ 10 + h ^ 11) := by
    have e : 0 ≤ (100 - 180 * h - 4600 * h ^ 2 - 8000 * h ^ 3 + 25500 * h ^ 4 + 121000 * h ^ 5 + 210000 * h ^ 6 +
      205000 * h ^ 7
         + 200000 * (h ^ 8 + h ^ 9 + h ^ 10 + h ^ 11)) - (pH (1 / 30)).derivative.eval h := by
      norm_num [pH, nsfEventBarrier, Polynomial.derivative_mul, Polynomial.derivative_pow]
      apply le_of_sub_nonneg
      ring_nf
      positivity
    linarith only [e]
  have htail : 25500 * h ^ 4 + 121000 * h ^ 5 + 210000 * h ^ 6 + 205000 * h ^ 7
       + 200000 * (h ^ 8 + h ^ 9 + h ^ 10 + h ^ 11) ≤ 4600 * h ^ 2 := by
    have h2 := hu 2
    have h3 := hu 3
    have h4 := hu 4
    have h5 := hu 5
    have h6 := hu 6
    have h7 := hu 7
    have h8 := hu 8
    have h9 := hu 9
    norm_num at h2 h3 h4 h5 h6 h7 h8 h9
    linarith only [h2, h3, h4, h5, h6, h7, h8, h9, sq_nonneg h]
  have h2 : (1 / 25 : ℝ) ≤ h ^ 2 := by nlinarith only [hh, sq_nonneg (h - 1 / 5)]
  have h3 : (1 / 125 : ℝ) ≤ h ^ 3 := by
    have := mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh)
    nlinarith only [this, h2]
  linarith only [hupper, htail, hh, h3]

/-- On the right branch, the curvature is positive by the lower order powers alone. -/
private theorem event_endpoint_curvature {h : ℝ} (hh : 1 / 4 ≤ h) :
    0 ≤ (pH (1 / 30)).derivative.derivative.eval h := by
  have hh0 : 0 ≤ h := by linarith only [hh]
  have h2 : h / 4 ≤ h ^ 2 := by nlinarith only [mul_nonneg hh0 (sub_nonneg.mpr hh)]
  have h2' : (1 / 16 : ℝ) ≤ h ^ 2 := by nlinarith only [hh, sq_nonneg (h - 1 / 4)]
  have h3 : h ^ 2 / 4 ≤ h ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hh)]
  have h4 : h ^ 2 / 16 ≤ h ^ 4 := by nlinarith only [h2', sq_nonneg (h ^ 2 - 1 / 16)]
  have h5 : h ^ 2 / 64 ≤ h ^ 5 := by
    have := mul_nonneg (pow_nonneg hh0 4) (sub_nonneg.mpr hh)
    nlinarith only [this, h4]
  have hlo : 0 ≤ -200 - 10000 * h - 26000 * h ^ 2 + 100000 * h ^ 3 + 600000 * h ^ 4 + 1200000 * h ^ 5 := by
    linarith only [h2, h2', h3, h4, h5]
  have hrest : 0 ≤ (pH (1 / 30)).derivative.derivative.eval h -
      (-200 - 10000 * h - 26000 * h ^ 2 + 100000 * h ^ 3 + 600000 * h ^ 4 + 1200000 * h ^ 5) := by
    norm_num [pH, nsfEventBarrier, Polynomial.derivative_mul, Polynomial.derivative_pow]
    apply le_of_sub_nonneg
    ring_nf
    positivity
  linarith only [hlo, hrest]

private theorem event_endpoint_right_pos {h : ℝ} (hh : 1 / 4 ≤ h) :
    0 < (pH (1 / 30)).eval h := by
  let p := pH (1 / 30)
  have hconvex : ConvexOn ℝ (Set.Ici (1 / 4)) (fun z => p.eval z) :=
    poly_convex (convex_Ici _) (fun z hz => event_endpoint_curvature hz)
  have hv : 1 ≤ p.eval (2 / 7) := by norm_num [p, pH, nsfEventBarrier]
  have hd0 : 0 ≤ p.derivative.eval (2 / 7) := by
    norm_num [p, pH, nsfEventBarrier, Polynomial.derivative_mul, Polynomial.derivative_pow]
  have hd1 : p.derivative.eval (2 / 7) ≤ 12 := by
    norm_num [p, pH, nsfEventBarrier, Polynomial.derivative_mul, Polynomial.derivative_pow]
  rcases lt_trichotomy h (2 / 7) with hlt | heq | hgt
  · have hs := hconvex.slope_le_of_hasDerivAt hh (by norm_num : (1 / 4 : ℝ) ≤ 2 / 7) hlt (p.hasDerivAt (2 / 7))
    rw [slope_def_field, div_le_iff₀ (by linarith only [hlt] : 0 < 2 / 7 - h)] at hs
    have hm := mul_le_mul_of_nonneg_right hd1 (by linarith only [hlt] : 0 ≤ 2 / 7 - h)
    linarith only [hs, hm, hv, hh]
  · rw [heq]
    linarith only [hv]
  · have hs := hconvex.le_slope_of_hasDerivAt (by norm_num : (1 / 4 : ℝ) ≤ 2 / 7) hh hgt (p.hasDerivAt (2 / 7))
    rw [slope_def_field, le_div_iff₀ (by linarith only [hgt] : 0 < h - 2 / 7)] at hs
    have hm := mul_nonneg hd0 (by linarith only [hgt] : 0 ≤ h - 2 / 7)
    linarith only [hs, hm, hv]

private theorem event_endpoint_pos {h : ℝ} (hh : 1 / 5 ≤ h) : 0 < nsfEventBarrier h (1 / 30) := by
  rw [← pH_eval]
  by_cases hh1 : 1 / 4 ≤ h
  · exact event_endpoint_right_pos hh1
  · have hh1 : h ≤ 1 / 4 := (le_of_not_ge hh1)
    have hm : AntitoneOn (fun z => (pH (1 / 30)).eval z) (Set.Icc (1 / 5) (1 / 4)) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
        (fun z _ => ((pH (1 / 30)).hasDerivAt z).continuousAt.continuousWithinAt)
        (fun z _ => ((pH (1 / 30)).hasDerivAt z).hasDerivWithinAt)
      intro z hz
      rw [interior_Icc] at hz
      exact event_endpoint_decreasing hz.1.le hz.2.le
    exact (event_endpoint_right_pos (by norm_num : (1 / 4 : ℝ) ≤ 1 / 4)).trans_le
      (hm ⟨hh, hh1⟩ (by norm_num) hh1)

/-- Concavity in the short gap reduces the strip to its two ends. -/
private theorem event_gap_curvature {h j : ℝ} (hh : 1 / 5 ≤ h) (hh1 : h ≤ 1 / 3)
    (hj : 0 ≤ j) (hj1 : j ≤ 1 / 30) : (pJ h).derivative.derivative.eval j ≤ 0 := by
  have hh0 : 0 ≤ h := by linarith only [hh]
  have hu (n : ℕ) : h ^ n ≤ (1 / 3 : ℝ) ^ n := pow_le_pow_left₀ hh0 hh1 n
  have hr (n : ℕ) : h ^ (n + 2) ≤ h ^ 2 * (1 / 3 : ℝ) ^ n := by
    have := mul_le_mul_of_nonneg_left (hu n) (sq_nonneg h)
    simpa [pow_add, mul_comm] using this
  have hs (n : ℕ) : h ^ (n + 1) ≤ h * (1 / 3 : ℝ) ^ n := by
    have := mul_le_mul_of_nonneg_left (hu n) hh0
    simpa [pow_add, mul_comm] using this
  let b0 := 1515 * h ^ 7 + 9868 * h ^ 6 + 29659 * h ^ 5 + 33352 * h ^ 4 - 1253 * h ^ 3 - 21895 * h ^ 2 - 7636 * h +
    920
  let b1 := 8050 * h ^ 6 + 43427 * h ^ 5 + 113209 * h ^ 4 + 69502 * h ^ 3 - 74390 * h ^ 2 - 65337 * h - 1521
  let b2 := 6755 * h ^ 6 + 35777 * h ^ 5 + 92377 * h ^ 4 + 58528 * h ^ 3 - 62912 * h ^ 2 - 65667 * h - 7918
  let b3 := 14910 * h ^ 5 + 61956 * h ^ 4 + 125906 * h ^ 3 - 10099 * h ^ 2 - 123100 * h - 28733
  let b4 := 5425 * h ^ 5 + 20944 * h ^ 4 + 35439 * h ^ 3 - 5931 * h ^ 2 - 37232 * h - 10725
  let b5 := 5030 * h ^ 4 + 10871 * h ^ 3 + 4339 * h ^ 2 - 15619 * h - 3341
  have hb0 : b0 < 0 := by
    dsimp [b0]
    linarith only [hr 5, hr 4, hr 3, hr 2, hh, sq_nonneg h, pow_nonneg hh0 3]
  have hb1 : b1 ≤ 0 := by
    dsimp [b1]
    linarith only [hr 4, hr 3, hr 2, hr 1, hh0, sq_nonneg h]
  have hb2 : b2 ≤ 0 := by
    dsimp [b2]
    linarith only [hr 4, hr 3, hr 2, hr 1, hh0, sq_nonneg h]
  have hb3 : b3 ≤ 0 := by
    dsimp [b3]
    linarith only [hs 4, hs 3, hs 2, hh0, sq_nonneg h]
  have hb4 : b4 ≤ 0 := by
    dsimp [b4]
    linarith only [hs 4, hs 3, hs 2, hh0, sq_nonneg h]
  have hb5 : b5 ≤ -2500 := by
    dsimp [b5]
    linarith only [hs 3, hs 2, hs 1, hh0]
  have hc0 : 4 * (h + 1) ^ 3 * b0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hb0.le
  have hc1 : 6 * (h + 1) ^ 3 * b1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hb1
  have hc2 : 24 * (h + 1) ^ 2 * b2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hb2
  have hc3 : 20 * (h + 1) ^ 2 * b3 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hb3
  have hc4 : 60 * (h + 1) * b4 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hb4
  have hc5 : 42 * (h + 1) * b5 ≤ -100000 := by
    have := mul_le_mul_of_nonneg_left hb5 (show 0 ≤ 42 * (h + 1) by positivity)
    nlinarith only [this, hh0]
  have hc6 : 112 * (h - 1) * (675 * h ^ 3 + 881 * h ^ 2 - 1831 * h - 2165) ≤ 400000 := by
    have hb : 1831 * h + 2165 - 675 * h ^ 3 - 881 * h ^ 2 ≤ 2800 := by
      linarith only [hh1, pow_nonneg hh0 3, sq_nonneg h]
    have := mul_le_mul_of_nonneg_left hb (show 0 ≤ 112 * (1 - h) by linarith only [hh1])
    nlinarith only [this, hh0]
  have hc7 : 288 * (h - 1) * (40 * h ^ 2 - 259 * h - 555) ≤ 200000 := by
    have hb : 259 * h + 555 - 40 * h ^ 2 ≤ 650 := by linarith only [hh1, sq_nonneg h]
    have := mul_le_mul_of_nonneg_left hb (show 0 ≤ 288 * (1 - h) by linarith only [hh1])
    nlinarith only [this, hh0]
  have hc8 : -23040 * (h - 1) ≤ 30000 := by linarith only [hh0]
  have heq : (pJ h).derivative.derivative.eval j =
      4 * (h + 1) ^ 3 * b0 + 6 * (h + 1) ^ 3 * b1 * j + 24 * (h + 1) ^ 2 * b2 * j ^ 2 + 20 * (h + 1) ^ 2 * b3 * j ^ 3
       + 60 * (h + 1) * b4 * j ^ 4 + 42 * (h + 1) * b5 * j ^ 5
       + 112 * (h - 1) * (675 * h ^ 3 + 881 * h ^ 2 - 1831 * h - 2165) * j ^ 6
       + 288 * (h - 1) * (40 * h ^ 2 - 259 * h - 555) * j ^ 7 - 23040 * (h - 1) * j ^ 8 := by
    norm_num [pJ, nsfEventBarrier, Polynomial.derivative_mul, Polynomial.derivative_pow, b0, b1, b2, b3, b4, b5]
    ring
  have hbound : (pJ h).derivative.derivative.eval j ≤
      -100000 * j ^ 5 + 400000 * j ^ 6 + 200000 * j ^ 7 + 30000 * j ^ 8 := by
    have h1 := mul_nonpos_of_nonpos_of_nonneg hc1 hj
    have h2 := mul_nonpos_of_nonpos_of_nonneg hc2 (pow_nonneg hj 2)
    have h3 := mul_nonpos_of_nonpos_of_nonneg hc3 (pow_nonneg hj 3)
    have h4 := mul_nonpos_of_nonpos_of_nonneg hc4 (pow_nonneg hj 4)
    have h5 := mul_le_mul_of_nonneg_right hc5 (pow_nonneg hj 5)
    have h6 := mul_le_mul_of_nonneg_right hc6 (pow_nonneg hj 6)
    have h7 := mul_le_mul_of_nonneg_right hc7 (pow_nonneg hj 7)
    have h8 := mul_le_mul_of_nonneg_right hc8 (pow_nonneg hj 8)
    linarith only [heq, hc0, h1, h2, h3, h4, h5, h6, h7, h8]
  have hjcap : j ≤ 1 := by linarith only [hj1]
  have j6 : j ^ 6 ≤ j ^ 5 / 30 := by
    have := mul_le_mul_of_nonneg_left hj1 (pow_nonneg hj 5)
    nlinarith only [this]
  have j7 : j ^ 7 ≤ j ^ 6 := by
    have := mul_le_mul_of_nonneg_left hjcap (pow_nonneg hj 6)
    nlinarith only [this]
  have j8 : j ^ 8 ≤ j ^ 6 := by
    have := mul_le_mul_of_nonneg_left hjcap (pow_nonneg hj 7)
    nlinarith only [this, j7]
  linarith only [hbound, j6, j7, j8, pow_nonneg hj 5]

/-- The boundary gap controls the event displacement throughout the small-gap strip. -/
theorem nsfEventBarrier_pos {h j : ℝ} (hh : 1 / 5 ≤ h) (hh1 : h ≤ 1 / 3)
    (hj : 0 ≤ j) (hj1 : j ≤ 1 / 30) : 0 < nsfEventBarrier h j := by
  have hc : ConcaveOn ℝ (Set.Icc 0 (1 / 30)) (fun z => (pJ h).eval z) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (fun z _ => ((pJ h).hasDerivAt z).continuousAt.continuousWithinAt)
      (fun z _ => ((pJ h).hasDerivAt z).hasDerivWithinAt)
      (fun z _ => ((pJ h).derivative.hasDerivAt z).hasDerivWithinAt)
    intro z hz
    rw [interior_Icc] at hz
    exact event_gap_curvature hh hh1 hz.1.le hz.2.le
  have hmin := hc.min_le_of_mem_Icc (by norm_num : (0 : ℝ) ∈ Set.Icc 0 (1 / 30))
    (by norm_num : (1 / 30 : ℝ) ∈ Set.Icc 0 (1 / 30)) (show j ∈ Set.Icc 0 (1 / 30) from ⟨hj, hj1⟩)
  simp only [pJ_eval] at hmin
  exact (lt_min (event_zero_pos hh) (event_endpoint_pos hh)).trans_le hmin

end SmoothedOctagon
