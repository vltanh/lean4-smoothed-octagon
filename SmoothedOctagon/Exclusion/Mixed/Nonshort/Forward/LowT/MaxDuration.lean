module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Horner

/-!
# The low-scale circuit at maximum duration

The cleared face numerator `P` increases with the gap. Its gap derivative
is bounded below by its value at the outer gap, using a divided difference
whose derivative is concave in the scale. At the smallest gap, the same
endpoint argument gives `P ≥ 50`.

## Main API

* `nltPqL`, `nlt_Pq_eq`, `nlt_face_qmax`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The coefficients in `j` of the cleared maximum-duration numerator `P(h, j)`. -/
def nltPqL {R : Type*} [CommRing R] (h : R) : List R :=
  [(12 * h ^ 2 - 22762 * h ^ 3 - 38304 * h ^ 4 + 80212 * h ^ 5 + 116136 * h ^ 6 - 578049 * h ^ 7 - 1754001 * h ^ 8 - 2140842 * h ^ 9 - 1430898 * h ^ 10 - 552873 * h ^ 11 - 118887 * h ^ 12 - 11628 * h ^ 13 : R),
   (-2408 * h + 110558 * h ^ 2 + 97600 * h ^ 3 + 945162 * h ^ 4 + 3769971 * h ^ 5 + 4134198 * h ^ 6 - 2453427 * h ^ 7 - 10074486 * h ^ 8 - 10564929 * h ^ 9 - 5810568 * h ^ 10 - 1841121 * h ^ 11 - 322434 * h ^ 12 - 23256 * h ^ 13 : R),
   (12 - 21350 * h + 62196 * h ^ 2 - 2055456 * h ^ 3 + 2684664 * h ^ 4 + 20680851 * h ^ 5 + 26170965 * h ^ 6 + 4415583 * h ^ 7 - 16639725 * h ^ 8 - 16544076 * h ^ 9 - 7261710 * h ^ 10 - 1675542 * h ^ 11 - 170136 * h ^ 12 : R),
   (-42798 + 570408 * h - 1856220 * h ^ 2 - 18016574 * h ^ 3 - 5750376 * h ^ 4 + 53365412 * h ^ 5 + 77418402 * h ^ 6 + 36992574 * h ^ 7 - 1386072 * h ^ 8 - 7462464 * h ^ 9 - 2762316 * h ^ 10 - 399024 * h ^ 11 : R),
   (-479468 + 5559084 * h - 2262932 * h ^ 2 - 52062067 * h ^ 3 - 31873443 * h ^ 4 + 80610387 * h ^ 5 + 123127329 * h ^ 6 + 67169508 * h ^ 7 + 16571034 * h ^ 8 + 1631064 * h ^ 9 - 93024 * h ^ 10 : R),
   (-2643022 + 20052419 * h + 12903858 * h ^ 2 - 74774025 * h ^ 3 - 59330232 * h ^ 4 + 65560812 * h ^ 5 + 100739844 * h ^ 6 + 48612174 * h ^ 7 + 11265012 * h ^ 8 + 1153008 * h ^ 9 : R),
   (-8786580 + 36875433 * h + 41708145 * h ^ 2 - 62851071 * h ^ 3 - 70519173 * h ^ 4 + 14474358 * h ^ 5 + 35225268 * h ^ 6 + 13355964 * h ^ 7 + 2044080 * h ^ 8 : R),
   (-18285880 + 37322168 * h + 53759262 * h ^ 2 - 36739830 * h ^ 3 - 57636612 * h ^ 4 - 14090832 * h ^ 5 + 1718016 * h ^ 6 + 1008576 * h ^ 7 : R),
   (-23855858 + 21566391 * h + 39183213 * h ^ 2 - 15939723 * h ^ 3 - 27429555 * h ^ 4 - 8688660 * h ^ 5 - 935136 * h ^ 6 : R),
   (-19296978 + 8913549 * h + 19369812 * h ^ 2 - 3696549 * h ^ 3 - 6431010 * h ^ 4 - 1570392 * h ^ 5 : R),
   (-9383466 + 4241574 * h + 6422994 * h ^ 2 - 435318 * h ^ 3 - 845784 * h ^ 4 : R),
   (-2427636 + 1677000 * h + 919548 * h ^ 2 - 168912 * h ^ 3 : R),
   (-210936 + 210936 * h : R)]

/-- **The cleared face numerator**: `6 d⁶ S = W² P` on `q = W/d`. -/
theorem nlt_Pq_eq (h j : ℝ) :
    6 * nltSt0 ((1 - h) / 2) (h + j) * (h - j) ^ 0 * (1 + 2 * j) ^ 6 + 6 * nltSt1 ((1 - h) / 2) (h + j) * (h - j) ^ 1 * (1 + 2 * j) ^ 5 + 6 * nltSt2 ((1 - h) / 2) (h + j) * (h - j) ^ 2 * (1 + 2 * j) ^ 4 + 6 * nltSt3 ((1 - h) / 2) (h + j) * (h - j) ^ 3 * (1 + 2 * j) ^ 3 + 6 * nltSt4 ((1 - h) / 2) (h + j) * (h - j) ^ 4 * (1 + 2 * j) ^ 2 + 6 * nltSt5 ((1 - h) / 2) (h + j) * (h - j) ^ 5 * (1 + 2 * j) ^ 1 + 6 * nltSt6 ((1 - h) / 2) (h + j) * (h - j) ^ 6 * (1 + 2 * j) ^ 0 = (1 + h + j) ^ 2 * polyHorner (nltPqL h) j := by
  rw [nlt_St_h0, nlt_St_h1, nlt_St_h2, nlt_St_h3, nlt_St_h4, nlt_St_h5, nlt_St_h6]
  simp only [nltL0, nltL1, nltL2, nltL3, nltL4, nltL5, nltL6, nltPqL, polyHorner]
  ring

namespace LowTDuration

/-- Evaluate a coefficient list in any commutative ring. -/
private def evaluate {R : Type*} [CommRing R] : List R → R → R
  | [], _ => 0
  | c :: cs, x => c + x * evaluate cs x

private def weighted {R : Type*} [CommRing R] : ℕ → List R → List R
  | _, [] => []
  | n, c :: cs => (n : R) * c :: weighted (n + 1) cs

private def derivativeCoefficients {R : Type*} [CommRing R] (cs : List R) : List R :=
  weighted 1 cs.tail

/-- The divided difference `(P(x) - P(a))/(x-a)`, evaluated by Horner's rule. -/
private def secant {R : Type*} [CommRing R] : List R → R → R → R
  | [], _, _ => 0
  | _ :: cs, a, x => evaluate cs a + x * secant cs a x

private theorem secant_identity {R : Type*} [CommRing R] (cs : List R) (a x : R) :
    evaluate cs x - evaluate cs a = (x - a) * secant cs a x := by
  induction cs with
  | nil => simp [evaluate, secant]
  | cons c cs ih =>
    simp only [evaluate, secant]
    linear_combination x * ih

private def face {R : Type*} [CommRing R] (h j : R) : R := evaluate (nltPqL h) j

private def gapDerivative {R : Type*} [CommRing R] (h j : R) : R :=
  evaluate (derivativeCoefficients (nltPqL h)) j

/-- Compare the gap derivative at `j = 5sz` with its value at `j = 5s`.
The physical scale is `h = 7s`; this change of variable keeps the coefficients integral. -/
private def boundarySlope {R : Type*} [CommRing R] (s z : R) : R :=
  -secant (derivativeCoefficients (nltPqL (7 * s))) (5 * s) (5 * s * z)

private noncomputable def slopePoly (z : ℝ) : Polynomial ℝ :=
  boundarySlope Polynomial.X (Polynomial.C z)

private noncomputable def basePoly : Polynomial ℝ :=
  face Polynomial.X (Polynomial.C (1 / 30))

private noncomputable def gapPoly (h : ℝ) : Polynomial ℝ :=
  face (Polynomial.C h) Polynomial.X

private theorem slope_eval (h z : ℝ) : (slopePoly z).eval h = boundarySlope h z := by
  simp [slopePoly, boundarySlope, secant, evaluate, derivativeCoefficients, weighted, nltPqL]

private theorem base_eval (h : ℝ) : basePoly.eval h = face h (1 / 30) := by
  simp [basePoly, face, evaluate, nltPqL]

private theorem gap_eval (h j : ℝ) : (gapPoly h).eval j = face h j := by
  simp [gapPoly, face, evaluate, nltPqL]

private theorem gap_deriv_eval (h j : ℝ) : (gapPoly h).derivative.eval j = gapDerivative h j := by
  simp [gapPoly, face, gapDerivative, derivativeCoefficients, weighted, nltPqL, evaluate,
    Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring

/-- A concave derivative that starts nonnegative permits an interior maximum,
but no interior minimum below both endpoint values. -/
private theorem endpoint_floor {p : Polynomial ℝ} {a b m x : ℝ}
    (hx0 : a ≤ x) (hx1 : x ≤ b)
    (h3 : ∀ s, a ≤ s → s ≤ b → p.derivative.derivative.derivative.eval s ≤ 0)
    (hda : 0 ≤ p.derivative.eval a) (ha : m ≤ p.eval a) (hb : m ≤ p.eval b) :
    m ≤ p.eval x := by
  have anti2 {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
      p.derivative.derivative.eval t ≤ p.derivative.derivative.eval s :=
    poly_anti (fun v => p.derivative.derivative.hasDerivAt v) h3 hs hst ht
  have stays {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
      (hneg : p.derivative.eval s < 0) : p.derivative.eval t ≤ 0 := by
    have sd : p.derivative.derivative.eval s < 0 := by
      by_contra hc
      have hp : 0 ≤ p.derivative.derivative.eval s := le_of_not_gt hc
      have hm := poly_mono (fun v => p.derivative.hasDerivAt v) (a := a) (b := s)
        (fun v hv0 hvs => hp.trans (anti2 hv0 hvs (hst.trans ht))) le_rfl hs le_rfl
      linarith only [hm, hda, hneg]
    have hm := poly_anti (fun v => p.derivative.hasDerivAt v) (a := s) (b := t)
      (fun v hsv hvt => (anti2 hs hsv (hvt.trans ht)).trans sd.le) le_rfl hst le_rfl
    exact hm.trans hneg.le
  by_cases hc : ∃ s, a ≤ s ∧ s ≤ x ∧ p.derivative.eval s < 0
  · obtain ⟨s, hs, hsx, hneg⟩ := hc
    have hm := poly_anti (fun v => p.hasDerivAt v) (a := x) (b := b)
      (fun v hxv hvb => stays hs (hsx.trans hxv) hvb hneg) le_rfl hx1 le_rfl
    exact hb.trans hm
  · push Not at hc
    have hm := poly_mono (fun v => p.hasDerivAt v) (a := a) (b := x)
      (fun v hav hvx => hc v hav hvx) le_rfl hx0 le_rfl
    exact ha.trans hm

private theorem slope_first_left {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    0 ≤ (slopePoly z).derivative.eval (1 / 28) := by
  have lo (n : ℕ) : 0 ≤ z ^ n := pow_nonneg hz0 n
  have hi (n : ℕ) : z ^ (n + 1) ≤ z := by
    have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0 hz1 n) hz0
    simpa only [one_pow, one_mul, pow_succ] using this
  conv in (slopePoly z) =>
    simp only [slopePoly, boundarySlope, secant, evaluate, derivativeCoefficients, weighted,
      nltPqL, List.tail_cons]
    norm_num
    ring_nf
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_neg,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X,
    mul_zero, add_zero]
  norm_num
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, hi 1, hi 2, hi 3, hi 4,
    hi 5, hi 6, hi 7, hi 8, hi 9, hz1]

private theorem slope_third_nonpos {h z : ℝ} (h0 : 1 / 28 ≤ h) (h1 : h ≤ 1 / 21)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (slopePoly z).derivative.derivative.derivative.eval h ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = (1 / 28) + u := ⟨h - (1 / 28), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have hu1 : u ≤ 1 / 84 := by linarith only [h1]
  have lo (i k : ℕ) : 0 ≤ u ^ i * z ^ k := mul_nonneg (pow_nonneg hu i) (pow_nonneg hz0 k)
  have hi (i k : ℕ) : u ^ i * z ^ k ≤ u ^ i := by
    have hp := pow_le_pow_left₀ hz0 hz1 k
    have := mul_le_mul_of_nonneg_left (by simpa only [one_pow] using hp) (pow_nonneg hu i)
    simpa only [mul_one] using this
  have hiPow (n : ℕ) : u ^ n ≤ (1 / 84 : ℝ) ^ n := pow_le_pow_left₀ hu hu1 n
  conv in (slopePoly z) =>
    simp only [slopePoly, boundarySlope, secant, evaluate, derivativeCoefficients, weighted,
      nltPqL, List.tail_cons]
    norm_num
    ring_nf
  simp only [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_neg,
    Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_C,
    Polynomial.derivative_X,
    zero_mul, mul_zero, zero_add, add_zero]
  norm_num
  ring_nf
  linarith only [hi 9 9, hi 9 8, hi 9 7, hi 9 6, hi 9 5, lo 9 4, lo 9 3, lo 9 2, lo 9 1, lo 9 0,
    lo 8 10, lo 8 9, hi 8 8, hi 8 7, hi 8 6, hi 8 5, lo 8 4, lo 8 3, lo 8 2, lo 8 1, lo 8 0, lo 7 10,
    lo 7 9, lo 7 8, hi 7 7, hi 7 6, hi 7 5, lo 7 4, lo 7 3, lo 7 2, lo 7 1, lo 7 0, lo 6 10, lo 6 9,
    lo 6 8, hi 6 7, hi 6 6, hi 6 5, lo 6 4, lo 6 3, lo 6 2, lo 6 1, lo 6 0, hi 5 10, lo 5 9, lo 5 8,
    lo 5 7, hi 5 6, hi 5 5, hi 5 4, lo 5 3, lo 5 2, lo 5 1, lo 5 0, hi 4 10, hi 4 9, lo 4 8, lo 4 7,
    lo 4 6, hi 4 5, hi 4 4, lo 4 3, lo 4 2, lo 4 1, lo 4 0, hi 3 10, hi 3 9, hi 3 8, hi 3 7, lo 3 6,
    lo 3 5, hi 3 4, lo 3 3, lo 3 2, lo 3 1, lo 3 0, hi 2 10, hi 2 9, hi 2 8, hi 2 7, lo 2 6, lo 2 5,
    lo 2 4, hi 2 3, lo 2 2, lo 2 1, lo 2 0, hi 1 10, hi 1 9, hi 1 8, hi 1 7, hi 1 6, lo 1 5, lo 1 4,
    lo 1 3, hi 1 2, lo 1 1, lo 1 0, hi 0 10, hi 0 9, hi 0 8, hi 0 7, hi 0 6, lo 0 5, lo 0 4, lo 0 3,
    hi 0 2, hi 0 1, hiPow 7, hiPow 8, hiPow 9]

private theorem slope_left_floor {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    70000 ≤ boundarySlope (1 / 28 : ℝ) z := by
  have lo (n : ℕ) : 0 ≤ z ^ n := pow_nonneg hz0 n
  have hi (n : ℕ) : z ^ (n + 1) ≤ z := by
    have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0 hz1 n) hz0
    simpa only [one_pow, one_mul, pow_succ] using this
  norm_num [boundarySlope, secant, evaluate, derivativeCoefficients, weighted, nltPqL, smul_eq_mul]
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, hi 1, hi 2, hi 3, hi 4,
    hi 5, hi 6, hi 7, hi 8, hi 9, hz1]

private theorem slope_right_floor {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    10000 ≤ boundarySlope (1 / 21 : ℝ) z := by
  have lo (n : ℕ) : 0 ≤ z ^ n := pow_nonneg hz0 n
  have hi (n : ℕ) : z ^ (n + 1) ≤ z := by
    have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hz0 hz1 n) hz0
    simpa only [one_pow, one_mul, pow_succ] using this
  have lower : 100000 + 252000 * z - 73000 * z ^ 2 - 224000 * z ^ 3
      - 61000 * z ^ 4 + 36000 * z ^ 5 ≤ boundarySlope (1 / 21 : ℝ) z := by
    norm_num [boundarySlope, secant, evaluate, derivativeCoefficients, weighted, nltPqL, smul_eq_mul]
    nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10]
  have tangent : 5 * (3 / 4 : ℝ) ^ 4 * z - 4 * (3 / 4 : ℝ) ^ 5 ≤ z ^ 5 := by
    have hs : 0 ≤ (z - 3 / 4) ^ 2 * (z ^ 3 + 3 / 2 * z ^ 2 + 27 / 16 * z + 27 / 16) := by positivity
    nlinarith only [hs]
  norm_num at tangent
  have charged : 100000 - 106000 * z + 36000 * z ^ 5 ≤ boundarySlope (1 / 21 : ℝ) z := by
    linear_combination lower + 73000 * (hi 1) + 224000 * (hi 2) + 61000 * (hi 3)
  nlinarith only [charged, tangent, hz1]

private theorem slope_nonneg {h z : ℝ} (h0 : 1 / 28 ≤ h) (h1 : h ≤ 1 / 21)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 ≤ boundarySlope h z := by
  have hf := endpoint_floor (p := slopePoly z) (m := 10000) h0 h1
    (fun v hv0 hv1 => slope_third_nonpos hv0 hv1 hz0 hz1)
    (slope_first_left hz0 hz1)
    (by rw [slope_eval]; linarith only [slope_left_floor hz0 hz1])
    (by rw [slope_eval]; exact slope_right_floor hz0 hz1)
  rw [slope_eval] at hf
  linarith only [hf]

private theorem outer_positive {h : ℝ} (h0 : 1 / 4 ≤ h) :
    1000 ≤ gapDerivative h (5 / 7 * h) := by
  obtain ⟨u, rfl⟩ : ∃ u, h = (1 / 4) + u := ⟨h - (1 / 4), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  norm_num [gapDerivative, derivativeCoefficients, weighted, nltPqL, evaluate]
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10, lo 11, lo 12, lo 13]

private theorem gap_positive {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 0 ≤ j) (hj1 : j ≤ 5 / 7 * h) : 0 ≤ (gapPoly h).derivative.eval j := by
  have hb : 0 < 5 / 7 * h := by linarith only [h0]
  let z := j / (5 / 7 * h)
  have hz0 : 0 ≤ z := div_nonneg hj0 hb.le
  have hz1 : z ≤ 1 := (div_le_one hb).mpr hj1
  have hs := slope_nonneg (h := h / 7) (by linarith only [h0]) (by linarith only [h1]) hz0 hz1
  have he := secant_identity (derivativeCoefficients (nltPqL h)) (5 / 7 * h) j
  have hz : 5 / 7 * h * z = j := by dsimp [z]; field_simp
  have hl : boundarySlope (h / 7) z = -secant (derivativeCoefficients (nltPqL h)) (5 / 7 * h) j := by
    have e7 : 7 * (h / 7) = h := by ring
    have e5 : 5 * (h / 7) = 5 / 7 * h := by ring
    simp only [boundarySlope, e7, e5, hz]
  rw [hl] at hs
  have hm := mul_nonneg (sub_nonneg.mpr hj1) hs
  have ho := outer_positive h0
  rw [gap_deriv_eval]
  unfold gapDerivative at *
  nlinarith only [he, hm, ho]

private theorem base_third_nonpos {h : ℝ} (h0 : 1 / 4 ≤ h) :
    basePoly.derivative.derivative.derivative.eval h ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, h = (1 / 4) + u := ⟨h - (1 / 4), by ring⟩
  have hu : 0 ≤ u := by linarith only [h0]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  norm_num [basePoly, face, evaluate, nltPqL, Polynomial.derivative_mul, Polynomial.derivative_pow]
  nlinarith only [lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7, lo 8, lo 9, lo 10]

private theorem base_floor {h : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3) :
    50 ≤ face h (1 / 30) := by
  have hf := endpoint_floor (p := basePoly) (m := 50) h0 h1
    (fun v hv0 _ => base_third_nonpos hv0)
    (by norm_num [basePoly, face, evaluate, nltPqL, Polynomial.derivative_mul, Polynomial.derivative_pow])
    (by norm_num [basePoly, face, evaluate, nltPqL])
    (by norm_num [basePoly, face, evaluate, nltPqL])
  simpa only [base_eval] using hf

private theorem face_positive {h j : ℝ} (h0 : 1 / 4 ≤ h) (h1 : h ≤ 1 / 3)
    (hj0 : 1 / 30 ≤ j) (hj1 : j ≤ 5 / 7 * h) : 0 < polyHorner (nltPqL h) j := by
  have hm := poly_mono (fun v => (gapPoly h).hasDerivAt v) (a := 1 / 30) (b := j)
    (fun v hv0 hv1 => gap_positive h0 h1 (by linarith only [hv0]) (hv1.trans hj1)) le_rfl hj0 le_rfl
  rw [gap_eval, gap_eval] at hm
  have hf := base_floor h0 h1
  have he : polyHorner (nltPqL h) j = face h j := by simp [polyHorner, face, nltPqL, evaluate]
  rw [he]
  linarith only [hf, hm]

end LowTDuration

/-- **The maximum-duration face**: for `1/4 ≤ h ≤ 1/3`,
`1/30 ≤ j ≤ 5h/7`, the circuit at `y = (h - j)/(1 + 2j)` is positive. -/
theorem nlt_face_qmax {h j : ℝ} (h1 : 1 / 4 ≤ h) (h2 : h ≤ 1 / 3) (j0 : 1 / 30 ≤ j)
    (j1 : j ≤ 5 / 7 * h) :
    0 < nltSt0 ((1 - h) / 2) (h + j) + nltSt1 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j))
      + nltSt2 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 2
      + nltSt3 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 3
      + nltSt4 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 4
      + nltSt5 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 5
      + nltSt6 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 6 := by
  have hP := LowTDuration.face_positive h1 h2 j0 j1
  have e := nlt_Pq_eq h j
  have hd1 : 0 < 1 + 2 * j := by linarith
  set P := polyHorner (nltPqL h) j
  have key : nltSt0 ((1 - h) / 2) (h + j) + nltSt1 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j))
      + nltSt2 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 2
      + nltSt3 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 3
      + nltSt4 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 4
      + nltSt5 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 5
      + nltSt6 ((1 - h) / 2) (h + j) * ((h - j) / (1 + 2 * j)) ^ 6 =
      (1 + h + j) ^ 2 * P / (6 * (1 + 2 * j) ^ 6) := by
    rw [← e]; field_simp
  rw [key]
  have : 0 < 1 + h + j := by linarith
  positivity

end SmoothedOctagon
