module

public meta import SmoothedOctagon.Tactic.Deriv

public import SmoothedOctagon.Exclusion.Forward.Scalars.Canon
public import Mathlib.Analysis.Convex.Deriv

/-!
# The tangent endpoints of the individual forward norm residual

The rational part is cubic in the normalized factor. The logarithmic terms have
positive third derivatives, and the lower second derivative is nonnegative, so
the value is convex in that factor. On the upper edge, a second convexity
argument reduces the sign to the two geometric corners. The other tangent
endpoint increases to the geometric factor boundary: its first derivative is
concave, with its upper edge controlled by three concave reciprocal kernels.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set


/-- The rational part of the smooth cancelled residual, retaining the row factors. -/
noncomputable def fs_normRat (U z h : ℝ) : ℝ :=
  let S := 1 + z
  let Z := z ^ 2 + U
  let K := 1 + U
  let d := 3 - U
  let y := z - 1
  let H := h - 1
  let phi := S / 2 - 2 / S + 2 / K - K / 8
  let f := (h - 1 / h) / 2
  (d * y * (d + 2 * y) + H * (d ^ 2 * (y ^ 2 + 4 * y + 2) +
    8 * d * y * z + 2 * y ^ 2 * (8 + 4 * y - y ^ 2))) / (8 * S * Z) +
    H ^ 2 * z * (d + 4 * y + y ^ 2) / (2 * h * Z) +
    K * (1 + S * H) / Z * phi - z * f -
    (U - z) * H * y * (y + 2 * z * H) / (4 * Z) -
    z * S * (U - z) * h / Z * f -
    K ^ 2 / (S * Z) * (S ^ 2 / K - 1 + H * (S ^ 3 / K - 1)) / 64

/-- Rational part of the value at the least admissible factor. -/
noncomputable def fs_normValueRat (a t : ℝ) : ℝ :=
  let b := 1 - a
  let z := (1 + a) / b
  fs_normRat (4 / (b ^ 2 * (1 + t)) - z ^ 2) z (1 + t)

private noncomputable def fsV_lead (a : ℝ) : ℝ := (1 + a) ^ 3 / (2 * (1 - a) ^ 2)

/-- Cubic reconstruction is used only to differentiate the rational part. -/
private theorem fsV_R_cubic {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    fs_normValueRat a t = fs_normValueRat a 0 + (fs_normValueRat a 1 - fs_normValueRat a 0 - fsV_lead a) * t +
      (fs_normValueRat a 2 - 2 * fs_normValueRat a 1 + fs_normValueRat a 0 - 6 * fsV_lead a) / 2 * t * (t - 1) +
      fsV_lead a * t ^ 3 := by
  have hb : 0 < 1 - a := by linarith
  have hl : 0 < 1 + t := by linarith
  have hc : 0 < 1 - a * (1 + t) := by nlinarith
  have hc2 : 0 < 1 - 2 * a := by linarith
  have hc3 : 0 < 1 - 3 * a := by linarith
  unfold fs_normValueRat fs_normRat fsV_lead
  dsimp only
  have he : 1 + (4 / ((1 - a) ^ 2 * (1 + t)) - ((1 + a) / (1 - a)) ^ 2) =
      4 * (1 - a * (1 + t)) / ((1 - a) ^ 2 * (1 + t)) := by field_simp; ring
  rw [he]
  have he2 : 1 + (4 / ((1 - a) ^ 2 * (1 + (1 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      2 * (1 - 2 * a) / (1 - a) ^ 2 := by field_simp; ring
  have he3 : 1 + (4 / ((1 - a) ^ 2 * (1 + (2 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      4 * (1 - 3 * a) / (3 * (1 - a) ^ 2) := by field_simp; ring
  have he1 : 1 + (4 / ((1 - a) ^ 2 * (1 + (0 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      4 / (1 - a) := by field_simp; ring
  rw [he2, he3, he1]
  field_simp
  ring_nf
  field_simp [show (1 - a * 2 : ℝ) ≠ 0 by linarith]
  ring

private noncomputable def fsV_quadLog (A B C l : ℝ) : ℝ :=
  (A * l ^ 2 + B * l + C) * Real.log l
private noncomputable def fsV_quadLog1 (A B C l : ℝ) : ℝ :=
  (2 * A * l + B) * Real.log l + A * l + B + C / l
private noncomputable def fsV_quadLog2 (A B C l : ℝ) : ℝ :=
  2 * A * Real.log l + 3 * A + B / l - C / l ^ 2

private theorem fsV_quadLog_deriv (A B C : ℝ) {l : ℝ} (hl : 0 < l) :
    HasDerivAt (fsV_quadLog A B C) (fsV_quadLog1 A B C l) l := by
  unfold fsV_quadLog fsV_quadLog1
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]
    field_simp
    ring

private theorem fsV_quadLog1_deriv (A B C : ℝ) {l : ℝ} (hl : 0 < l) :
    HasDerivAt (fsV_quadLog1 A B C) (fsV_quadLog2 A B C l) l := by
  unfold fsV_quadLog1 fsV_quadLog2
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]
    field_simp
    ring

private theorem fsV_quadLog2_deriv (A B C : ℝ) {l : ℝ} (hl : 0 < l) :
    HasDerivAt (fsV_quadLog2 A B C) (2 * A / l - B / l ^ 2 + 2 * C / l ^ 3) l := by
  unfold fsV_quadLog2
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]
    field_simp
    ring

private noncomputable def fsV_affineLog (A B C c d t : ℝ) : ℝ :=
  (A * t ^ 2 + B * t + C) * Real.log (c + d * t)
private noncomputable def fsV_affineLog1 (A B C c d t : ℝ) : ℝ :=
  (2 * A * t + B) * Real.log (c + d * t) + (A * t ^ 2 + B * t + C) * d / (c + d * t)
private noncomputable def fsV_affineLog2 (A B C c d t : ℝ) : ℝ :=
  2 * A * Real.log (c + d * t) + 2 * (2 * A * t + B) * d / (c + d * t) -
    (A * t ^ 2 + B * t + C) * d ^ 2 / (c + d * t) ^ 2

private theorem fsV_affineLog_deriv (A B C c d : ℝ) {t : ℝ} (hc : 0 < c + d * t) :
    HasDerivAt (fsV_affineLog A B C c d) (fsV_affineLog1 A B C c d t) t := by
  unfold fsV_affineLog fsV_affineLog1
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]
    field_simp

private theorem fsV_affineLog1_deriv (A B C c d : ℝ) {t : ℝ} (hc : 0 < c + d * t) :
    HasDerivAt (fsV_affineLog1 A B C c d) (fsV_affineLog2 A B C c d t) t := by
  unfold fsV_affineLog1 fsV_affineLog2
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]
    field_simp
    ring

private theorem fsV_affineLog2_deriv (A B C c d : ℝ) {t : ℝ} (hc : 0 < c + d * t) :
    HasDerivAt (fsV_affineLog2 A B C c d)
      (6 * A * d / (c + d * t) - 3 * (2 * A * t + B) * d ^ 2 / (c + d * t) ^ 2 +
        2 * (A * t ^ 2 + B * t + C) * d ^ 3 / (c + d * t) ^ 3) t := by
  unfold fsV_affineLog2
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]
    field_simp
    ring

private noncomputable def fsV_linear (a : ℝ) : ℝ := fs_normValueRat a 1 - fs_normValueRat a 0 - fsV_lead a
private noncomputable def fsV_quadratic (a : ℝ) : ℝ :=
  (fs_normValueRat a 2 - 2 * fs_normValueRat a 1 + fs_normValueRat a 0 - 6 * fsV_lead a) / 2
private noncomputable def fsV_cubic (a t : ℝ) : ℝ :=
  fs_normValueRat a 0 + fsV_linear a * t + fsV_quadratic a * t * (t - 1) + fsV_lead a * t ^ 3
private noncomputable def fsV_cubicFirst (a t : ℝ) : ℝ :=
  fsV_linear a + fsV_quadratic a * (2 * t - 1) + 3 * fsV_lead a * t ^ 2
private noncomputable def fsV_cubicSecond (a t : ℝ) : ℝ := 2 * fsV_quadratic a + 6 * fsV_lead a * t

private theorem fsV_Rmodel_deriv (a t : ℝ) : HasDerivAt (fsV_cubic a) (fsV_cubicFirst a t) t := by
  unfold fsV_cubic fsV_cubicFirst
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]
    ring
private theorem fsV_Rmodel1_deriv (a t : ℝ) : HasDerivAt (fsV_cubicFirst a) (fsV_cubicSecond a t) t := by
  unfold fsV_cubicFirst fsV_cubicSecond
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]
    ring
private theorem fsV_Rmodel2_deriv (a t : ℝ) : HasDerivAt (fsV_cubicSecond a) (6 * fsV_lead a) t := by
  unfold fsV_cubicSecond
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]

private noncomputable def fsV_valueModel (a t : ℝ) : ℝ :=
  fsV_cubic a t +
    fsV_quadLog (-(1 + 3 * a ^ 2) / (1 - a) ^ 2) (a * (a ^ 2 + 3) / (1 - a) ^ 2)
      (2 * (1 - a ^ 2) / (1 - a) ^ 2) (1 + t) +
    fsV_affineLog (-2 * a / (1 - a)) (2 - a) (1 - a) (1 - a) (-a) t
private noncomputable def fsV_valueFirst (a t : ℝ) : ℝ :=
  fsV_cubicFirst a t +
    fsV_quadLog1 (-(1 + 3 * a ^ 2) / (1 - a) ^ 2) (a * (a ^ 2 + 3) / (1 - a) ^ 2)
      (2 * (1 - a ^ 2) / (1 - a) ^ 2) (1 + t) +
    fsV_affineLog1 (-2 * a / (1 - a)) (2 - a) (1 - a) (1 - a) (-a) t
private noncomputable def fsV_valueSecond (a t : ℝ) : ℝ :=
  fsV_cubicSecond a t +
    fsV_quadLog2 (-(1 + 3 * a ^ 2) / (1 - a) ^ 2) (a * (a ^ 2 + 3) / (1 - a) ^ 2)
      (2 * (1 - a ^ 2) / (1 - a) ^ 2) (1 + t) +
    fsV_affineLog2 (-2 * a / (1 - a)) (2 - a) (1 - a) (1 - a) (-a) t

private theorem fsV_V_deriv {a t : ℝ} (hl : 0 < 1 + t) (hc : 0 < 1 - a + -a * t) :
    HasDerivAt (fsV_valueModel a) (fsV_valueFirst a t) t := by
  have h := (fsV_quadLog_deriv (-(1 + 3 * a ^ 2) / (1 - a) ^ 2)
    (a * (a ^ 2 + 3) / (1 - a) ^ 2) (2 * (1 - a ^ 2) / (1 - a) ^ 2) hl).comp t
    ((hasDerivAt_id t).const_add 1)
  have hd := ((fsV_Rmodel_deriv a t).add h).add
    (fsV_affineLog_deriv (-2 * a / (1 - a)) (2 - a) (1 - a) (1 - a) (-a) hc)
  convert! hd using 1; simp only [fsV_valueFirst, mul_one]

private theorem fsV_V1_deriv {a t : ℝ} (hl : 0 < 1 + t) (hc : 0 < 1 - a + -a * t) :
    HasDerivAt (fsV_valueFirst a) (fsV_valueSecond a t) t := by
  have h := (fsV_quadLog1_deriv (-(1 + 3 * a ^ 2) / (1 - a) ^ 2)
    (a * (a ^ 2 + 3) / (1 - a) ^ 2) (2 * (1 - a ^ 2) / (1 - a) ^ 2) hl).comp t
    ((hasDerivAt_id t).const_add 1)
  have hd := ((fsV_Rmodel1_deriv a t).add h).add
    (fsV_affineLog1_deriv (-2 * a / (1 - a)) (2 - a) (1 - a) (1 - a) (-a) hc)
  convert! hd using 1; simp only [fsV_valueSecond, mul_one]

private theorem fsV_V2_deriv {a t : ℝ} (hb : 0 < 1 - a) (hl : 0 < 1 + t)
    (hc : 0 < 1 - a * (1 + t)) :
    HasDerivAt (fsV_valueSecond a)
      (3 * (1 + a) ^ 3 / (1 - a) ^ 2 +
       (4 * (1 - a ^ 2) - 2 * (1 + 3 * a ^ 2) * (1 + t) ^ 2 - a * (a ^ 2 + 3) * (1 + t)) /
         ((1 - a) ^ 2 * (1 + t) ^ 3) +
       a ^ 2 * (a * ((1 - a) + 2 * t) + 6 * (1 - a * (1 + t))) /
         ((1 - a) * (1 - a * (1 + t)) ^ 2)) t := by
  have hc' : 0 < 1 - a + -a * t := by nlinarith only [hc]
  have h := (fsV_quadLog2_deriv (-(1 + 3 * a ^ 2) / (1 - a) ^ 2)
    (a * (a ^ 2 + 3) / (1 - a) ^ 2) (2 * (1 - a ^ 2) / (1 - a) ^ 2) hl).comp t
    ((hasDerivAt_id t).const_add 1)
  have hd := ((fsV_Rmodel2_deriv a t).add h).add
    (fsV_affineLog2_deriv (-2 * a / (1 - a)) (2 - a) (1 - a) (1 - a) (-a) hc')
  refine hd.congr_deriv ?_
  unfold fsV_lead
  simp only [mul_one]
  rw [show 1 - a + -a * t = 1 - a * (1 + t) by ring]
  field_simp
  ring

private theorem fsV_V3_pos {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    0 < 3 * (1 + a) ^ 3 / (1 - a) ^ 2 +
       (4 * (1 - a ^ 2) - 2 * (1 + 3 * a ^ 2) * (1 + t) ^ 2 - a * (a ^ 2 + 3) * (1 + t)) /
         ((1 - a) ^ 2 * (1 + t) ^ 3) +
       a ^ 2 * (a * ((1 - a) + 2 * t) + 6 * (1 - a * (1 + t))) /
         ((1 - a) * (1 - a * (1 + t)) ^ 2) := by
  have hb : 0 < 1 - a := by linarith
  have hl : 0 < 1 + t := by linarith
  have hc : 0 < 1 - a * (1 + t) := by nlinarith only [ha, ha1, ht, ht1]
  have ha2 : a ^ 2 ≤ (1 / 7 : ℝ) ^ 2 := by nlinarith only [ha, ha1]
  have hl2 : (1 + t) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 := by nlinarith only [ht, ht1]
  have hm1 := mul_le_mul
    (mul_le_mul ha1 (by linarith only [ha2] : a ^ 2 + 3 ≤ (1 / 7 : ℝ) ^ 2 + 3)
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1 / 7))
    (by linarith only [ht1] : 1 + t ≤ 5 / 4) (by linarith only [ht]) (by positivity)
  have hm2 := mul_le_mul (by linarith only [ha2] : 1 + 3 * a ^ 2 ≤ 1 + 3 * (1 / 7 : ℝ) ^ 2)
    hl2 (by positivity) (by norm_num : (0 : ℝ) ≤ 1 + 3 * (1 / 7 : ℝ) ^ 2)
  have hnum : 0 < 4 * (1 - a ^ 2) - 2 * (1 + 3 * a ^ 2) * (1 + t) ^ 2 - a * (a ^ 2 + 3) * (1 + t) := by
    nlinarith only [hm1, hm2, ha2]
  have hfirst : 0 < 3 * (1 + a) ^ 3 / (1 - a) ^ 2 := by positivity
  have hsecond : 0 < (4 * (1 - a ^ 2) - 2 * (1 + 3 * a ^ 2) * (1 + t) ^ 2 - a * (a ^ 2 + 3) * (1 + t)) /
      ((1 - a) ^ 2 * (1 + t) ^ 3) := div_pos hnum (by positivity)
  have hthird : 0 ≤ a ^ 2 * (a * ((1 - a) + 2 * t) + 6 * (1 - a * (1 + t))) /
      ((1 - a) * (1 - a * (1 + t)) ^ 2) := by positivity
  linarith only [hfirst, hsecond, hthird]

private theorem fsV_V2_bottom {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    fsV_valueSecond a 0 = a / (16 * (1 - a) ^ 2) *
      (2 + a - 33 * a ^ 2 + 64 * (1 - a) * (-Real.log (1 - a) - a)) := by
  have hb : 0 < 1 - a := by linarith
  have hc2 : 0 < 1 - 2 * a := by linarith
  have hc3 : 0 < 1 - 3 * a := by linarith
  have he2 : 1 + (4 / ((1 - a) ^ 2 * (1 + (1 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      2 * (1 - 2 * a) / (1 - a) ^ 2 := by field_simp; ring
  have he3 : 1 + (4 / ((1 - a) ^ 2 * (1 + (2 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      4 * (1 - 3 * a) / (3 * (1 - a) ^ 2) := by field_simp; ring
  have he1 : 1 + (4 / ((1 - a) ^ 2 * (1 + (0 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      4 / (1 - a) := by field_simp; ring
  unfold fsV_valueSecond fsV_cubicSecond fsV_quadratic fsV_lead fs_normValueRat fs_normRat fsV_quadLog2 fsV_affineLog2
  dsimp only
  rw [he2, he3, he1]
  norm_num
  field_simp
  ring_nf

private theorem fsV_V_bottom {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    fsV_valueModel a 0 = (1 - a) * Real.log (1 - a) + a * (31 - 16 * a) / 32 := by
  have hb : 0 < 1 - a := by linarith
  unfold fsV_valueModel fsV_cubic fsV_quadLog fsV_affineLog
  norm_num
  unfold fs_normValueRat fs_normRat
  dsimp only
  have he : 1 + (4 / ((1 - a) ^ 2 * (1 + (0 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      4 / (1 - a) := by field_simp; ring
  rw [he]
  field_simp
  ring

private theorem fsV_V2_bottom_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    0 ≤ fsV_valueSecond a 0 := by
  rw [fsV_V2_bottom ha ha1]
  have hb : 0 < 1 - a := by linarith
  have hlog := Real.log_le_sub_one_of_pos hb
  have ha2 : a ^ 2 ≤ (1 / 7 : ℝ) ^ 2 := by nlinarith only [ha, ha1]
  have hlog' : 0 ≤ -Real.log (1 - a) - a := by linarith only [hlog]
  have hbracket : 0 ≤ 2 + a - 33 * a ^ 2 + 64 * (1 - a) * (-Real.log (1 - a) - a) := by
    have h := mul_nonneg (by positivity : 0 ≤ 64 * (1 - a)) hlog'
    nlinarith only [h, ha, ha2]
  exact mul_nonneg (by positivity) hbracket

private theorem fsV_V_bottom_nonpos {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    fsV_valueModel a 0 ≤ 0 := by
  rw [fsV_V_bottom ha ha1]
  have hb : 0 < 1 - a := by linarith
  have hlog := fs_log_one_sub_le ha (by linarith : a < 1)
  have hlog2 : Real.log (1 - a) ≤ -a - a ^ 2 / 2 := by
    nlinarith only [hlog, pow_nonneg ha 3]
  have h := mul_le_mul_of_nonneg_left hlog2 hb.le
  have ha2 : a ^ 2 ≤ (1 / 7 : ℝ) ^ 2 := by nlinarith only [ha, ha1]
  have hprod := mul_nonneg ha (show 0 ≤ 1 - 16 * a ^ 2 by nlinarith only [ha2])
  nlinarith only [h, hprod]

private theorem fsV_V_convex {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    ConvexOn ℝ (Icc (0 : ℝ) (1 / 4)) (fsV_valueModel a) := by
  have hpos : ∀ t ∈ Icc (0 : ℝ) (1 / 4), 0 < 1 + t ∧ 0 < 1 - a * (1 + t) := by
    intro t ht
    exact ⟨by linarith [ht.1], by nlinarith [ht.1, ht.2]⟩
  have hsecond : ∀ t ∈ Icc (0 : ℝ) (1 / 4), 0 ≤ fsV_valueSecond a t := by
    intro t ht
    have h := ff_le_of_deriv (f := fsV_valueSecond a) ht.1 (fun s hs =>
      fsV_V2_deriv (by linarith) (by linarith [hs.1])
        (hpos s ⟨hs.1, hs.2.trans ht.2⟩).2) (fun s hs =>
          (fsV_V3_pos ha ha1 hs.1 (hs.2.trans ht.2)).le)
    linarith only [h, fsV_V2_bottom_nonneg ha ha1]
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun t ht => (fsV_V_deriv (hpos t ht).1 (by nlinarith only [(hpos t ht).2])).continuousAt.continuousWithinAt)
    (fun t ht => (fsV_V_deriv (hpos t (interior_subset ht)).1
      (by nlinarith only [(hpos t (interior_subset ht)).2])).hasDerivWithinAt)
    (fun t ht => (fsV_V1_deriv (hpos t (interior_subset ht)).1
      (by nlinarith only [(hpos t (interior_subset ht)).2])).hasDerivWithinAt)
    (fun t ht => hsecond t (interior_subset ht))

private theorem fsV_V_eq {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    fsV_valueModel a t = fs_normValueRat a t +
      (a * (a ^ 2 + 3) * (1 + t) + 2 * (1 - a ^ 2) - (1 + 3 * a ^ 2) * (1 + t) ^ 2) /
        (1 - a) ^ 2 * Real.log (1 + t) +
      ((1 - a) + 2 * t) * (1 - a * (1 + t)) / (1 - a) * Real.log (1 - a * (1 + t)) := by
  have hb : 0 < 1 - a := by linarith
  have hr : fsV_cubic a t = fs_normValueRat a t := (fsV_R_cubic ha ha1 ht ht1).symm
  unfold fsV_valueModel
  rw [hr]
  unfold fsV_quadLog fsV_affineLog
  rw [show 1 - a + -a * t = 1 - a * (1 + t) by ring]
  field_simp
  ring

private noncomputable def fsV_UR (S : ℝ) : ℝ :=
  fs_normRat (4 * S ^ 2 / 5 - (S - 1) ^ 2) (S - 1) (5 / 4)
private noncomputable def fsV_UB (S : ℝ) : ℝ :=
  65 * S ^ 2 / 1024 - 75 / (256 * S) - 5 / (2 * S ^ 2)
private noncomputable def fsV_UA : ℝ := fsV_UR 2 - fsV_UB 2
private noncomputable def fsV_UC : ℝ := fsV_UR 3 - fsV_UB 3 - fsV_UA
private noncomputable def fsV_URmodel (S : ℝ) : ℝ := fsV_UB S + fsV_UA + fsV_UC * (S - 2)

private theorem fsV_UR_eq {S : ℝ} (hS : 0 < S) (hD : 0 < 10 - S) :
    fsV_UR S = fsV_URmodel S := by
  unfold fsV_URmodel fsV_UC fsV_UA fsV_UR fsV_UB fs_normRat
  dsimp only
  rw [show 1 + (4 * S ^ 2 / 5 - (S - 1) ^ 2) = S * (10 - S) / 5 by ring]
  norm_num
  field_simp
  ring

private noncomputable def fsV_upperModel (S : ℝ) : ℝ :=
  fsV_URmodel S + (-5 * S ^ 2 / 16 + 47 * S / 16 - 47 / 16 - 5 / (2 * S)) * Real.log (5 / 4) +
    (-S + 6 + 40 / S) / 16 * Real.log ((10 - S) / (4 * S))
private noncomputable def fsV_upperFirst (S : ℝ) : ℝ :=
  65 * S / 512 + 75 / (256 * S ^ 2) + 5 / S ^ 3 + fsV_UC +
    (-5 * S / 8 + 47 / 16 + 5 / (2 * S ^ 2)) * Real.log (5 / 4) +
    (-1 - 40 / S ^ 2) / 16 * Real.log ((10 - S) / (4 * S)) -
    (-S + 6 + 40 / S) / 16 * (10 / (S * (10 - S)))
private noncomputable def fsV_upperSecond (S : ℝ) : ℝ :=
  65 / 512 - 75 / (128 * S ^ 3) - 15 / S ^ 4 - 5 / 8 * Real.log (5 / 4) -
    5 / S ^ 3 * Real.log (5 * S / (10 - S)) + 5 * (S + 60) / (4 * (10 - S) * S ^ 3)

private theorem fsV_U_deriv {S : ℝ} (hS : 0 < S) (hD : 0 < 10 - S) :
    HasDerivAt fsV_upperModel (fsV_upperFirst S) S := by
  unfold fsV_upperModel fsV_upperFirst fsV_URmodel fsV_UB
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]
    field_simp
    ring

private theorem fsV_U1_deriv {S : ℝ} (hS : 0 < S) (hD : 0 < 10 - S) :
    HasDerivAt fsV_upperFirst (fsV_upperSecond S) S := by
  have hlog : Real.log (5 * S / (10 - S)) =
      Real.log (5 / 4) - Real.log ((10 - S) / (4 * S)) := by
    rw [← Real.log_div (by norm_num) (by positivity)]
    congr 1
    field_simp
  unfold fsV_upperFirst fsV_upperSecond
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · rw [hlog]
    norm_num [npowRec]
    field_simp
    ring

private theorem fsV_V_upper_eq {S : ℝ} (hS : 2 ≤ S) (hS1 : S ≤ 7 / 3) :
    fsV_valueModel ((S - 2) / S) (1 / 4) = fsV_upperModel S := by
  have hS0 : 0 < S := by linarith
  have hD : 0 < 10 - S := by linarith
  have ha : 0 ≤ (S - 2) / S := by positivity
  have ha1 : (S - 2) / S ≤ 1 / 7 := by rw [div_le_iff₀ hS0]; linarith
  rw [fsV_V_eq ha ha1 (by norm_num) (by norm_num)]
  have hr : fs_normValueRat ((S - 2) / S) (1 / 4) = fsV_UR S := by
    unfold fs_normValueRat fsV_UR
    dsimp only
    have hb : 1 - (S - 2) / S = 2 / S := by field_simp; ring
    have hz : (1 + (S - 2) / S) / (1 - (S - 2) / S) = S - 1 := by rw [hb]; field_simp; ring
    rw [hz, hb]
    congr 1 <;> field_simp <;> ring
  rw [hr, fsV_UR_eq hS0 hD]
  unfold fsV_upperModel
  rw [show 1 - (S - 2) / S * (1 + 1 / 4) = (10 - S) / (4 * S) by field_simp; ring]
  field_simp
  ring_nf

private theorem fsV_U2_pos {S : ℝ} (hS : 2 ≤ S) (hS1 : S ≤ 7 / 3) : 0 < fsV_upperSecond S := by
  have hS0 : 0 < S := by linarith
  have hD : 0 < 10 - S := by linarith
  have hpow : S ^ 4 ≤ 16 + 52 * (S - 2) := by
    have hm := ff_le_of_deriv (f := fun r : ℝ => 16 + 52 * (r - 2) - r ^ 4)
      (f' := fun r => 52 - 4 * r ^ 3) hS
      (fun r _ => by
        apply HasDerivAt.congr_deriv
        · elementary_deriv
        · norm_num [npowRec]; ring) (fun r hr => ?_)
    · norm_num at hm
      linarith only [hm]
    · have hr0 : 0 ≤ r := by linarith [hr.1]
      have hr1 : r ≤ 7 / 3 := hr.2.trans hS1
      have h : r ^ 3 ≤ (7 / 3 : ℝ) ^ 3 := by gcongr
      nlinarith only [h]
  have hk : 0 ≤ (S - 2) * (19 - 43 * (S - 2)) / (8 * (10 - S)) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by linarith) (by linarith)
  have hb : 0 < 3 * (S - 1) / 8 + (S - 2) * (19 - 43 * (S - 2)) / (8 * (10 - S)) -
      15 * S / 128 - 3 * S ^ 4 / 512 := by
    nlinarith only [hpow, hk, hS1]
  have hlow : 0 < 65 / 512 - 75 / (128 * S ^ 3) - 15 / S ^ 4 - 5 / 32 -
      5 / S ^ 3 * (5 * S / (10 - S) - 1) + 5 * (S + 60) / (4 * (10 - S) * S ^ 3) := by
    have he : 65 / 512 - 75 / (128 * S ^ 3) - 15 / S ^ 4 - 5 / 32 -
        5 / S ^ 3 * (5 * S / (10 - S) - 1) + 5 * (S + 60) / (4 * (10 - S) * S ^ 3) =
        5 / S ^ 4 * (3 * (S - 1) / 8 + (S - 2) * (19 - 43 * (S - 2)) / (8 * (10 - S)) -
          15 * S / 128 - 3 * S ^ 4 / 512) := by field_simp; ring
    rw [he]
    exact mul_pos (by positivity) hb
  have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  have hq := Real.log_le_sub_one_of_pos (show 0 < 5 * S / (10 - S) by positivity)
  have hm1 := mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 5 / 8)
  have hm2 := mul_le_mul_of_nonneg_left hq (by positivity : (0 : ℝ) ≤ 5 / S ^ 3)
  unfold fsV_upperSecond
  nlinarith only [hlow, hm1, hm2]

private theorem fsV_U_convex : ConvexOn ℝ (Icc (2 : ℝ) (7 / 3)) fsV_upperModel := by
  have hpos : ∀ S ∈ Icc (2 : ℝ) (7 / 3), 0 < S ∧ 0 < 10 - S :=
    fun S h => ⟨by linarith [h.1], by linarith [h.2]⟩
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun S h => (fsV_U_deriv (hpos S h).1 (hpos S h).2).continuousAt.continuousWithinAt)
    (fun S h => (fsV_U_deriv (hpos S (interior_subset h)).1
      (hpos S (interior_subset h)).2).hasDerivWithinAt)
    (fun S h => (fsV_U1_deriv (hpos S (interior_subset h)).1
      (hpos S (interior_subset h)).2).hasDerivWithinAt)
    (fun S h => (fsV_U2_pos (interior_subset h).1 (interior_subset h).2).le)

private theorem fsV_V_corner_left : fsV_valueModel 0 (1 / 4) < 0 := by
  rw [fsV_V_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [fs_normValueRat, fs_normRat]
  linarith only [ff_log_five_fourths_lt]

private theorem fsV_V_corner_right : fsV_valueModel (1 / 7) (1 / 4) < 0 := by
  have hprod : Real.log (5 / 4) + Real.log (23 / 28) < 3 / 112 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    have h := Real.log_lt_sub_one_of_pos (x := 115 / 112) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have h := fs_log_one_sub_le (y := 5 / 28) (by norm_num) (by norm_num)
  norm_num at h
  have hxi : Real.log (23 / 28) ≤ -5 / 28 - (5 / 28) ^ 2 / 2 := by linarith only [h]
  rw [fsV_V_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [fs_normValueRat, fs_normRat]
  linarith only [hprod, hxi]

private theorem fsV_U_neg {S : ℝ} (hS : 2 ≤ S) (hS1 : S ≤ 7 / 3) : fsV_upperModel S < 0 := by
  have hleft : fsV_upperModel 2 < 0 := by
    have h := fsV_V_upper_eq (S := 2) (by norm_num) (by norm_num)
    norm_num at h
    rw [← h]
    exact fsV_V_corner_left
  have hright : fsV_upperModel (7 / 3) < 0 := by
    have h := fsV_V_upper_eq (S := 7 / 3) (by norm_num) (by norm_num)
    norm_num at h
    rw [← h]
    exact fsV_V_corner_right
  have hθ : 0 ≤ 3 * (S - 2) := by linarith
  have hθ1 : 0 ≤ 1 - 3 * (S - 2) := by linarith
  have hc := fsV_U_convex.2 (by norm_num : (2 : ℝ) ∈ Icc 2 (7 / 3))
    (by norm_num : (7 / 3 : ℝ) ∈ Icc 2 (7 / 3)) hθ1 hθ (by ring)
  simp only [smul_eq_mul] at hc
  rw [show (1 - 3 * (S - 2)) * 2 + 3 * (S - 2) * (7 / 3) = S by ring] at hc
  by_cases he : S = 2
  · rwa [he]
  · have hθpos : 0 < 3 * (S - 2) := by rcases lt_or_eq_of_le hS with h | h; linarith; exact (he h.symm).elim
    have hl := mul_nonpos_of_nonneg_of_nonpos hθ1 hleft.le
    have hr := mul_neg_of_pos_of_neg hθpos hright
    linarith only [hc, hl, hr]

private theorem fsV_V_neg {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 < t) (ht1 : t ≤ 1 / 4) : fsV_valueModel a t < 0 := by
  have hb : 0 < 1 - a := by linarith
  have hS : 2 ≤ 2 / (1 - a) := by rw [le_div_iff₀ hb]; linarith
  have hS1 : 2 / (1 - a) ≤ 7 / 3 := by rw [div_le_iff₀ hb]; linarith
  have hupper := fsV_V_upper_eq hS hS1
  rw [show (2 / (1 - a) - 2) / (2 / (1 - a)) = a by field_simp; ring] at hupper
  have hneg : fsV_valueModel a (1 / 4) < 0 := by rw [hupper]; exact fsV_U_neg hS hS1
  have hc := (fsV_V_convex ha ha1).2 (by norm_num : (0 : ℝ) ∈ Icc 0 (1 / 4))
    (by norm_num : (1 / 4 : ℝ) ∈ Icc 0 (1 / 4)) (show 0 ≤ 1 - 4 * t by linarith)
    (show 0 ≤ 4 * t by linarith) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add] at hc
  rw [show 4 * t * (1 / 4) = t by ring] at hc
  have hl := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 - 4 * t by linarith) (fsV_V_bottom_nonpos ha ha1)
  have hr := mul_neg_of_pos_of_neg (show 0 < 4 * t by linarith) hneg
  linarith only [hc, hl, hr]

/-- The individual norm residual at the least factor, with its singularity cancelled. -/
noncomputable def fs_normValue (a t : ℝ) : ℝ :=
  fs_normValueRat a t +
    (a * (a ^ 2 + 3) * (1 + t) + 2 * (1 - a ^ 2) - (1 + 3 * a ^ 2) * (1 + t) ^ 2) /
      (1 - a) ^ 2 * Real.log (1 + t) +
    ((1 - a) + 2 * t) * (1 - a * (1 + t)) / (1 - a) * Real.log (1 - a * (1 + t))

/-- Convexity and the two upper-edge corners make the least-factor value negative. -/
theorem fs_normValue_neg {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 < t) (ht1 : t ≤ 1 / 4) : fs_normValue a t < 0 := by
  have h := fsV_V_neg ha ha1 ht ht1
  rwa [fsV_V_eq ha ha1 ht.le ht1] at h

/-! ### The other endpoint of the affine tangent -/

/-- Rational part of the factor derivative after cancellation of the logarithmic terms. -/
noncomputable def fs_normSlopeRat (U z h : ℝ) : ℝ :=
  let S := 1 + z
  let Z := z ^ 2 + U
  let K := 1 + U
  let d := 3 - U
  let y := z - 1
  let phi := S / 2 - 2 / S + 2 / K - K / 8
  (d ^ 2 * (y ^ 2 + 4 * y + 2) + 8 * d * y * z +
    2 * y ^ 2 * (8 + 4 * y - y ^ 2)) / (8 * S * Z) +
    z * (d + 4 * y + y ^ 2) / (2 * Z) * (1 - 1 / h ^ 2) +
    K * S / Z * phi - z / 2 * (1 + 1 / h ^ 2) -
    (U - z) * y * (y + 4 * z * (h - 1)) / (4 * Z) -
    z * S * (U - z) * h / Z -
    K ^ 2 / (S * Z) * (S ^ 3 / K - 1) / 64 +
    (z + z * S * (U - z) * h / Z) / h

/-- The factor slope at the least admissible factor. -/
noncomputable def fs_normSlope (a t : ℝ) : ℝ :=
  let b := 1 - a
  let z := (1 + a) / b
  let U := 4 / (b ^ 2 * (1 + t)) - z ^ 2
  fs_normSlopeRat U z (1 + t) +
    (1 + z) * (z * (U - z) - (1 + U)) / (z ^ 2 + U) * Real.log (1 + t) +
    (1 + U) * (1 + z) / (z ^ 2 + U) * Real.log (1 - a * (1 + t))

/-- Distance from the least factor to the cost endpoint. -/
noncomputable def fs_normSpan (a t : ℝ) : ℝ :=
  2 * (1 - a ^ 2 - (4 + a ^ 2) * t) / (3 * (1 - a))

/-- The affine tangent evaluated at the cost endpoint. -/
noncomputable def fs_normTangent (a t : ℝ) : ℝ :=
  fs_normValue a t + fs_normSpan a t * fs_normSlope a t

private noncomputable def fsT_rat (a t : ℝ) : ℝ :=
  let b := 1 - a
  let z := (1 + a) / b
  let U := 4 / (b ^ 2 * (1 + t)) - z ^ 2
  fs_normValueRat a t + fs_normSpan a t * fs_normSlopeRat U z (1 + t)
private noncomputable def fsT_recip (a : ℝ) : ℝ := 5 * (1 - 16 * a ^ 2) / (48 * (1 - a) ^ 2)
private noncomputable def fsT_lead (a : ℝ) : ℝ :=
  -(1 + a) ^ 3 * (13 + 3 * a + 4 * a ^ 2) / (6 * (1 - a) ^ 3)
private noncomputable def fsT_slopeRat (a t : ℝ) : ℝ :=
  fs_normSlopeRat (4 / ((1 - a) ^ 2 * (1 + t)) - ((1 + a) / (1 - a)) ^ 2)
    ((1 + a) / (1 - a)) (1 + t)
private noncomputable def fsT_slopeRecip (a : ℝ) : ℝ := (1 - 16 * a ^ 2) / (32 * (1 - a))
private noncomputable def fsT_slopeLead (a : ℝ) : ℝ := (1 + a) ^ 3 / (1 - a) ^ 2
private noncomputable def fsT_slopeConst (a : ℝ) : ℝ := fsT_slopeRat a 0 - fsT_slopeRecip a
private noncomputable def fsT_slopeLinear (a : ℝ) : ℝ :=
  fsT_slopeRat a 1 - fsT_slopeLead a - fsT_slopeConst a - fsT_slopeRecip a / 2
private noncomputable def fsT_slopeModel (a t : ℝ) : ℝ :=
  fsT_slopeLead a * t ^ 2 + fsT_slopeLinear a * t + fsT_slopeConst a + fsT_slopeRecip a / (1 + t)

private theorem fsT_slope_eq {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : fsT_slopeRat a t = fsT_slopeModel a t := by
  have hb : 0 < 1 - a := by linarith
  have hl : 0 < 1 + t := by linarith
  have hc : 0 < 1 - a * (1 + t) := by nlinarith
  have hc2 : 0 < 1 - 2 * a := by linarith
  have he : 1 + (4 / ((1 - a) ^ 2 * (1 + t)) - ((1 + a) / (1 - a)) ^ 2) =
      4 * (1 - a * (1 + t)) / ((1 - a) ^ 2 * (1 + t)) := by field_simp; ring
  have he2 : 1 + (4 / ((1 - a) ^ 2 * (1 + (1 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      2 * (1 - 2 * a) / (1 - a) ^ 2 := by field_simp; ring
  have he1 : 1 + (4 / ((1 - a) ^ 2 * (1 + (0 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      4 / (1 - a) := by field_simp; ring
  unfold fsT_slopeModel fsT_slopeLinear fsT_slopeConst fsT_slopeRat
    fs_normSlopeRat fsT_slopeLead fsT_slopeRecip
  dsimp only
  rw [he, he2, he1]
  field_simp
  ring_nf
  field_simp [show (1 - a * 2 : ℝ) ≠ 0 by linarith]
  ring

private theorem fsT_rat_eq {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    fsT_rat a t = fsV_cubic a t + fs_normSpan a t * fsT_slopeModel a t := by
  change fs_normValueRat a t + fs_normSpan a t * fsT_slopeRat a t = _
  rw [fsV_R_cubic ha ha1 ht ht1, fsT_slope_eq ha ha1 ht ht1]
  rfl

private noncomputable def fsT_span0 (a : ℝ) : ℝ := 2 * (1 - a ^ 2) / (3 * (1 - a))
private noncomputable def fsT_span1 (a : ℝ) : ℝ := -2 * (4 + a ^ 2) / (3 * (1 - a))
private noncomputable def fsT_constant (a : ℝ) : ℝ :=
  fs_normValueRat a 0 + fsT_span0 a * fsT_slopeConst a + fsT_span1 a * fsT_slopeRecip a
private noncomputable def fsT_linear (a : ℝ) : ℝ :=
  fsV_linear a - fsV_quadratic a + fsT_span0 a * fsT_slopeLinear a + fsT_span1 a * fsT_slopeConst a
private noncomputable def fsT_quadratic (a : ℝ) : ℝ :=
  fsV_quadratic a + fsT_span0 a * fsT_slopeLead a + fsT_span1 a * fsT_slopeLinear a
private noncomputable def fsT_ratModel (a t : ℝ) : ℝ :=
  fsT_constant a + fsT_linear a * t + fsT_quadratic a * t ^ 2 +
    fsT_lead a * t ^ 3 + fsT_recip a / (1 + t)
private noncomputable def fsT_ratFirst (a t : ℝ) : ℝ :=
  fsT_linear a + 2 * fsT_quadratic a * t + 3 * fsT_lead a * t ^ 2 - fsT_recip a / (1 + t) ^ 2
private noncomputable def fsT_ratSecond (a t : ℝ) : ℝ :=
  2 * fsT_quadratic a + 6 * fsT_lead a * t + 2 * fsT_recip a / (1 + t) ^ 3

private theorem fsT_R_eq {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : fsT_rat a t = fsT_ratModel a t := by
  have hb : 0 < 1 - a := by linarith
  have hl : 0 < 1 + t := by linarith
  rw [fsT_rat_eq ha ha1 ht ht1]
  unfold fsV_cubic fsT_ratModel fsT_constant fsT_linear fsT_quadratic
    fs_normSpan fsT_slopeModel fsT_span0 fsT_span1 fsT_lead fsT_recip fsT_slopeLead fsT_slopeRecip fsV_lead
  field_simp
  ring

private noncomputable def fsT_k (a : ℝ) : ℝ := 2 * (5 + 3 * a + 2 * a ^ 2)
private noncomputable def fsT_p2 (a : ℝ) : ℝ := (1 + 3 * a ^ 2) * (5 + 3 * a + 2 * a ^ 2)
private noncomputable def fsT_p1 (a : ℝ) : ℝ :=
  10 * (1 + 3 * a ^ 2) + a * (8 * (4 + a ^ 2) - 3 * (1 - a) * (a ^ 2 + 3))
private noncomputable def fsT_p0 (a : ℝ) : ℝ := 6 * (1 - a) * (1 - a ^ 2) + 40 * a
private noncomputable def fsT_model (a t : ℝ) : ℝ :=
  fsT_ratModel a t +
    fsV_quadLog (fsT_p2 a / (3 * (1 - a) ^ 3)) (-fsT_p1 a / (3 * (1 - a) ^ 3))
      (fsT_p0 a / (3 * (1 - a) ^ 3)) (1 + t) +
    fsV_affineLog (a * fsT_k a / (3 * (1 - a) ^ 2))
      (-(fsT_k a + a * (7 + a)) / (3 * (1 - a))) ((7 + a) / 3) (1 - a) (-a) t
private noncomputable def fsT_first (a t : ℝ) : ℝ :=
  fsT_ratFirst a t +
    fsV_quadLog1 (fsT_p2 a / (3 * (1 - a) ^ 3)) (-fsT_p1 a / (3 * (1 - a) ^ 3))
      (fsT_p0 a / (3 * (1 - a) ^ 3)) (1 + t) +
    fsV_affineLog1 (a * fsT_k a / (3 * (1 - a) ^ 2))
      (-(fsT_k a + a * (7 + a)) / (3 * (1 - a))) ((7 + a) / 3) (1 - a) (-a) t
private noncomputable def fsT_second (a t : ℝ) : ℝ :=
  fsT_ratSecond a t +
    fsV_quadLog2 (fsT_p2 a / (3 * (1 - a) ^ 3)) (-fsT_p1 a / (3 * (1 - a) ^ 3))
      (fsT_p0 a / (3 * (1 - a) ^ 3)) (1 + t) +
    fsV_affineLog2 (a * fsT_k a / (3 * (1 - a) ^ 2))
      (-(fsT_k a + a * (7 + a)) / (3 * (1 - a))) ((7 + a) / 3) (1 - a) (-a) t

private theorem fsT_eq {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : fs_normTangent a t = fsT_model a t := by
  have hb : 0 < 1 - a := by linarith
  have hl : 0 < 1 + t := by linarith
  rw [fsT_model, ← fsT_R_eq ha ha1 ht ht1]
  unfold fs_normTangent fs_normValue fs_normSlope fsT_rat fs_normSpan
    fsV_quadLog fsV_affineLog fsT_p2 fsT_p1 fsT_p0 fsT_k
  dsimp only
  rw [show 1 - a + -a * t = 1 - a * (1 + t) by ring]
  field_simp
  ring

private theorem fsT_R_deriv {a t : ℝ} (hl : 0 < 1 + t) :
    HasDerivAt (fsT_ratModel a) (fsT_ratFirst a t) t := by
  unfold fsT_ratModel fsT_ratFirst
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]; field_simp; ring
private theorem fsT_R1_deriv {a t : ℝ} (hl : 0 < 1 + t) :
    HasDerivAt (fsT_ratFirst a) (fsT_ratSecond a t) t := by
  unfold fsT_ratFirst fsT_ratSecond
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]; field_simp; ring
private theorem fsT_R2_deriv {a t : ℝ} (hl : 0 < 1 + t) :
    HasDerivAt (fsT_ratSecond a) (6 * fsT_lead a - 6 * fsT_recip a / (1 + t) ^ 4) t := by
  unfold fsT_ratSecond
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem fsT_deriv {a t : ℝ} (hl : 0 < 1 + t) (hc : 0 < 1 - a + -a * t) :
    HasDerivAt (fsT_model a) (fsT_first a t) t := by
  have h := (fsV_quadLog_deriv (fsT_p2 a / (3 * (1 - a) ^ 3)) (-fsT_p1 a / (3 * (1 - a) ^ 3))
    (fsT_p0 a / (3 * (1 - a) ^ 3)) hl).comp t ((hasDerivAt_id t).const_add 1)
  have hd := ((fsT_R_deriv (a := a) hl).add h).add
    (fsV_affineLog_deriv (a * fsT_k a / (3 * (1 - a) ^ 2))
      (-(fsT_k a + a * (7 + a)) / (3 * (1 - a))) ((7 + a) / 3) (1 - a) (-a) hc)
  convert! hd using 1; simp only [fsT_first, mul_one]
private theorem fsT_1_deriv {a t : ℝ} (hl : 0 < 1 + t) (hc : 0 < 1 - a + -a * t) :
    HasDerivAt (fsT_first a) (fsT_second a t) t := by
  have h := (fsV_quadLog1_deriv (fsT_p2 a / (3 * (1 - a) ^ 3)) (-fsT_p1 a / (3 * (1 - a) ^ 3))
    (fsT_p0 a / (3 * (1 - a) ^ 3)) hl).comp t ((hasDerivAt_id t).const_add 1)
  have hd := ((fsT_R1_deriv (a := a) hl).add h).add
    (fsV_affineLog1_deriv (a * fsT_k a / (3 * (1 - a) ^ 2))
      (-(fsT_k a + a * (7 + a)) / (3 * (1 - a))) ((7 + a) / 3) (1 - a) (-a) hc)
  convert! hd using 1; simp only [fsT_second, mul_one]

private noncomputable def fsT_third (a t : ℝ) : ℝ :=
  -(1 + a) ^ 3 * (13 + 3 * a + 4 * a ^ 2) / (1 - a) ^ 3 -
    5 * (1 - 16 * a ^ 2) / (8 * (1 - a) ^ 2 * (1 + t) ^ 4) +
    (2 * fsT_p2 a / (1 + t) + fsT_p1 a / (1 + t) ^ 2 + 2 * fsT_p0 a / (1 + t) ^ 3) /
      (3 * (1 - a) ^ 3) +
    a ^ 2 * (a * ((1 - a) * (7 + a) - fsT_k a * t) - 3 * fsT_k a * (1 - a * (1 + t))) /
      (3 * (1 - a) ^ 2 * (1 - a * (1 + t)) ^ 2)
private theorem fsT_2_deriv {a t : ℝ} (hb : 0 < 1 - a) (hl : 0 < 1 + t)
    (hc : 0 < 1 - a * (1 + t)) : HasDerivAt (fsT_second a) (fsT_third a t) t := by
  have hc' : 0 < 1 - a + -a * t := by nlinarith only [hc]
  have h := (fsV_quadLog2_deriv (fsT_p2 a / (3 * (1 - a) ^ 3)) (-fsT_p1 a / (3 * (1 - a) ^ 3))
    (fsT_p0 a / (3 * (1 - a) ^ 3)) hl).comp t ((hasDerivAt_id t).const_add 1)
  have hd := ((fsT_R2_deriv (a := a) hl).add h).add
    (fsV_affineLog2_deriv (a * fsT_k a / (3 * (1 - a) ^ 2))
      (-(fsT_k a + a * (7 + a)) / (3 * (1 - a))) ((7 + a) / 3) (1 - a) (-a) hc')
  refine hd.congr_deriv ?_
  unfold fsT_third fsT_lead fsT_recip fsT_k
  simp only [mul_one]
  rw [show 1 - a + -a * t = 1 - a * (1 + t) by ring]
  field_simp
  ring

private theorem fsT_third_neg {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : fsT_third a t < 0 := by
  have hb : 0 < 1 - a := by linarith
  have ha2 : a ^ 2 ≤ (1 / 7 : ℝ) ^ 2 := by nlinarith only [ha, ha1]
  have hl : 1 ≤ 1 + t := by linarith
  have hl2 : 1 ≤ (1 + t) ^ 2 := by nlinarith only [ht]
  have hl3 : 1 ≤ (1 + t) ^ 3 := by nlinarith only [ht, sq_nonneg t, mul_nonneg ht (sq_nonneg t)]
  have hxi : 3 / 4 ≤ 1 - a * (1 + t) := by nlinarith only [ha, ha1, ht, ht1]
  have hk : 10 ≤ fsT_k a := by unfold fsT_k; nlinarith only [ha, sq_nonneg a]
  have hp2 : 0 ≤ fsT_p2 a := by unfold fsT_p2; positivity
  have hp0 : 0 ≤ fsT_p0 a := by
    unfold fsT_p0
    exact add_nonneg (mul_nonneg (by positivity) (by nlinarith only [ha2])) (by positivity)
  have hp1 : 0 ≤ fsT_p1 a := by
    have hm : 3 * (1 - a) * (a ^ 2 + 3) ≤ 3 * (a ^ 2 + 3) := by
      nlinarith only [mul_nonneg ha (show 0 ≤ a ^ 2 + 3 by positivity)]
    unfold fsT_p1
    exact add_nonneg (by positivity) (mul_nonneg ha (by nlinarith only [hm, sq_nonneg a]))
  have he : 13 * (1 + a) ^ 3 - (2 * fsT_p2 a + fsT_p1 a + 2 * fsT_p0 a) / 3 =
      (7 + 20 * a + a ^ 2 * (56 + 4 * a - 15 * a ^ 2)) / 3 := by
    unfold fsT_p2 fsT_p1 fsT_p0
    ring
  have habs : 0 < 13 * (1 + a) ^ 3 - (2 * fsT_p2 a + fsT_p1 a + 2 * fsT_p0 a) / 3 := by
    rw [he]
    have hbr : 0 ≤ 56 + 4 * a - 15 * a ^ 2 := by nlinarith only [ha, ha2]
    positivity
  have habs' : (2 * fsT_p2 a + fsT_p1 a + 2 * fsT_p0 a) / (3 * (1 - a) ^ 3) <
      13 * (1 + a) ^ 3 / (1 - a) ^ 3 := by
    have h := div_pos habs (pow_pos hb 3)
    have hid : (13 * (1 + a) ^ 3 - (2 * fsT_p2 a + fsT_p1 a + 2 * fsT_p0 a) / 3) / (1 - a) ^ 3 =
        13 * (1 + a) ^ 3 / (1 - a) ^ 3 -
          (2 * fsT_p2 a + fsT_p1 a + 2 * fsT_p0 a) / (3 * (1 - a) ^ 3) := by field_simp
    rw [hid] at h
    linarith only [h]
  have hp2' := div_le_self (show 0 ≤ 2 * fsT_p2 a by positivity) hl
  have hp1' := div_le_self hp1 hl2
  have hp0' := div_le_self (show 0 ≤ 2 * fsT_p0 a by positivity) hl3
  have hlogs := div_le_div_of_nonneg_right (add_le_add (add_le_add hp2' hp1') hp0')
    (show 0 ≤ 3 * (1 - a) ^ 3 by positivity)
  have hmain : 13 * (1 + a) ^ 3 / (1 - a) ^ 3 ≤
      (1 + a) ^ 3 * (13 + 3 * a + 4 * a ^ 2) / (1 - a) ^ 3 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hm := mul_nonneg (show 0 ≤ (1 + a) ^ 3 by positivity) (show 0 ≤ 3 * a + 4 * a ^ 2 by positivity)
    nlinarith only [hm]
  have hrec : 0 ≤ 5 * (1 - 16 * a ^ 2) / (8 * (1 - a) ^ 2 * (1 + t) ^ 4) := by
    exact div_nonneg (by nlinarith only [ha2]) (by positivity)
  have hu : (1 - a) * (7 + a) - fsT_k a * t ≤ 7 := by
    have hp := mul_nonneg (by linarith only [hk] : 0 ≤ fsT_k a) ht
    nlinarith only [ha, sq_nonneg a, hp]
  have hau : a * ((1 - a) * (7 + a) - fsT_k a * t) ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hu ha
    linarith only [hm, ha1]
  have hkxi : (10 : ℝ) * (3 / 4) ≤ fsT_k a * (1 - a * (1 + t)) :=
    mul_le_mul hk hxi (by norm_num) (by linarith only [hk])
  have hlast : a ^ 2 * (a * ((1 - a) * (7 + a) - fsT_k a * t) -
      3 * fsT_k a * (1 - a * (1 + t))) / (3 * (1 - a) ^ 2 * (1 - a * (1 + t)) ^ 2) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) (by linarith only [hau, hkxi])
  unfold fsT_third
  simp only [neg_mul, neg_div]
  linarith only [habs', hlogs, hmain, hrec, hlast]

private theorem fsT_first_concave {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    ConcaveOn ℝ (Icc (0 : ℝ) (1 / 4)) (fsT_first a) := by
  have hb : 0 < 1 - a := by linarith
  have hpos : ∀ t ∈ Icc (0 : ℝ) (1 / 4), 0 < 1 + t ∧ 0 < 1 - a * (1 + t) :=
    fun t h => ⟨by linarith [h.1], by nlinarith [h.1, h.2]⟩
  have hpos' : ∀ t ∈ Icc (0 : ℝ) (1 / 4), 0 < 1 - a + -a * t :=
    fun t h => by nlinarith only [(hpos t h).2]
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun t h => (fsT_1_deriv (hpos t h).1 (hpos' t h)).continuousAt.continuousWithinAt)
    (fun t h => (fsT_1_deriv (hpos t (interior_subset h)).1 (hpos' t (interior_subset h))).hasDerivWithinAt)
    (fun t h => (fsT_2_deriv hb (hpos t (interior_subset h)).1
      (hpos t (interior_subset h)).2).hasDerivWithinAt)
    (fun t h => (fsT_third_neg ha ha1 (interior_subset h).1 (interior_subset h).2).le)

private theorem fsT_first_bottom {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    fsT_first a 0 =
      a * (23 + 11 * a - 2 * a ^ 2 * (81 + 106 * a + 40 * a ^ 2)) / (96 * (1 - a) ^ 2) +
      (5 * a ^ 2 + 13 * a + 10) / (3 * (1 - a)) * (-Real.log (1 - a) - a - a ^ 2 / 2) := by
  have hb : 0 < 1 - a := by linarith
  have hc2 : 0 < 1 - 2 * a := by linarith
  have hc3 : 0 < 1 - 3 * a := by linarith
  have he2 : 1 + (4 / ((1 - a) ^ 2 * (1 + (1 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      2 * (1 - 2 * a) / (1 - a) ^ 2 := by field_simp; ring
  have he3 : 1 + (4 / ((1 - a) ^ 2 * (1 + (2 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      4 * (1 - 3 * a) / (3 * (1 - a) ^ 2) := by field_simp; ring
  have he1 : 1 + (4 / ((1 - a) ^ 2 * (1 + (0 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      4 / (1 - a) := by field_simp; ring
  unfold fsT_first fsT_ratFirst fsT_linear fsT_quadratic fsT_lead fsT_recip
    fsT_span0 fsT_span1 fsT_slopeLinear fsT_slopeConst fsT_slopeRecip fsT_slopeLead fsT_slopeRat
    fsV_linear fsV_quadratic fsV_lead fsV_quadLog1 fsV_affineLog1 fsT_p2 fsT_p1 fsT_p0 fsT_k
  norm_num
  unfold fs_normValueRat fs_normRat fs_normSlopeRat
  dsimp only
  rw [he2, he3, he1]
  field_simp
  ring_nf
  field_simp [show (4 - a * 8 : ℝ) ≠ 0 by linarith, show (1 - a * 2 : ℝ) ≠ 0 by linarith]
  ring

private theorem fsT_bottom_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) : 0 ≤ fsT_first a 0 := by
  have hb : 0 < 1 - a := by linarith
  have ha2 : a ^ 2 ≤ (1 / 7 : ℝ) ^ 2 := by nlinarith only [ha, ha1]
  have hinner : 81 + 106 * a + 40 * a ^ 2 < 100 := by nlinarith only [ha1, ha2]
  have hm := mul_le_mul_of_nonneg_left hinner.le (show 0 ≤ 2 * a ^ 2 by positivity)
  have hbr : 0 ≤ 23 + 11 * a - 2 * a ^ 2 * (81 + 106 * a + 40 * a ^ 2) := by
    nlinarith only [hm, ha, ha2]
  have hlog := fs_log_one_sub_le ha (show a < 1 by linarith)
  have hrem : 0 ≤ -Real.log (1 - a) - a - a ^ 2 / 2 := by
    have hcube : 0 ≤ a ^ 3 / 3 := by positivity
    linarith only [hlog, hcube]
  rw [fsT_first_bottom ha ha1]
  positivity

private noncomputable def fsT_upperBound (a : ℝ) : ℝ :=
  fsT_ratFirst a (1 / 4) +
    (5 * fsT_p2 a / 2 - fsT_p1 a) / (3 * (1 - a) ^ 3) * Real.log (5 / 4) +
    (5 * fsT_p2 a / 4 - fsT_p1 a + 4 * fsT_p0 a / 5) / (3 * (1 - a) ^ 3) -
    (5 * a / 4) * (a * fsT_k a / (6 * (1 - a) ^ 2) - (fsT_k a + a * (7 + a)) / (3 * (1 - a))) -
    a * ((1 - a) * (7 + a) - fsT_k a / 4) / (3 * (1 - a) ^ 2)

private theorem fsT_upper_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    fsT_upperBound a ≤ fsT_first a (1 / 4) := by
  have hb : 0 < 1 - a := by linarith
  have hxi : 0 < 1 - 5 * a / 4 := by linarith
  have ha2 : a ^ 2 ≤ (1 / 7 : ℝ) ^ 2 := by nlinarith only [ha, ha1]
  have ha3 : a ^ 3 ≤ (1 / 7 : ℝ) ^ 3 := by gcongr
  have hc : (7 * a ^ 3 + 11 * a ^ 2 + 2 * a - 10) / (3 * (1 - a) ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith only [ha1, ha2, ha3]) (by positivity)
  have hl := Real.log_le_sub_one_of_pos hxi
  have hm := mul_nonneg_of_nonpos_of_nonpos hc
    (show Real.log (1 - 5 * a / 4) + 5 * a / 4 ≤ 0 by linarith only [hl])
  have he : fsT_first a (1 / 4) = fsT_upperBound a +
      (7 * a ^ 3 + 11 * a ^ 2 + 2 * a - 10) / (3 * (1 - a) ^ 2) *
        (Real.log (1 - 5 * a / 4) + 5 * a / 4) := by
    unfold fsT_first fsT_upperBound fsV_quadLog1 fsV_affineLog1 fsT_k
    rw [show 1 - a + -a * (1 / 4) = 1 - 5 * a / 4 by ring]
    norm_num
    field_simp
    ring_nf
    field_simp [show (4 - a * 5 : ℝ) ≠ 0 by linarith]
    ring
  linarith only [he, hm]

private noncomputable def fsT_C2 : ℝ := 92 / 3 * Real.log (5 / 4) - 173 / 48
private noncomputable def fsT_C3 : ℝ := 133 / 48 - 20 / 3 * Real.log (5 / 4)
private noncomputable def fsT_D0 : ℝ := 28 / 3 * Real.log (5 / 4) - 113 / 320
private noncomputable def fsT_kernel (b : ℝ) : ℝ :=
  -113 * b ^ 2 / 96 + fsT_C2 * (3 / b - 1 / b ^ 2) +
    fsT_C3 * (6 / b - 1 / b ^ 3) - fsT_D0 / b
private noncomputable def fsT_G (b : ℝ) : ℝ := fsT_upperBound (1 - b)
private noncomputable def fsT_Gmodel (b : ℝ) : ℝ :=
  fsT_kernel b + (fsT_G 1 - fsT_kernel 1) +
    (b - 1) * (fsT_G 2 - fsT_kernel 2 - (fsT_G 1 - fsT_kernel 1))
private noncomputable def fsT_Gfirst (b : ℝ) : ℝ :=
  -113 * b / 48 + fsT_C2 * (-3 / b ^ 2 + 2 / b ^ 3) +
    fsT_C3 * (-6 / b ^ 2 + 3 / b ^ 4) + fsT_D0 / b ^ 2 +
    (fsT_G 2 - fsT_kernel 2 - (fsT_G 1 - fsT_kernel 1))
private noncomputable def fsT_Gsecond (b : ℝ) : ℝ :=
  -113 / 48 - 6 * fsT_C2 * (1 - b) / b ^ 4 -
    12 * fsT_C3 * (1 - b ^ 2) / b ^ 5 - 2 * fsT_D0 / b ^ 3

private theorem fsT_G_deriv {b : ℝ} (hb : 0 < b) :
    HasDerivAt fsT_Gmodel (fsT_Gfirst b) b := by
  unfold fsT_Gmodel fsT_Gfirst fsT_kernel
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]; field_simp; ring
private theorem fsT_G1_deriv {b : ℝ} (hb : 0 < b) :
    HasDerivAt fsT_Gfirst (fsT_Gsecond b) b := by
  unfold fsT_Gfirst fsT_Gsecond
  apply HasDerivAt.congr_deriv
  · elementary_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem fsT_log_lower : (1 : ℝ) / 5 < Real.log (5 / 4) := by
  have h := ff_log_gt_midpoint (v := 5 / 4) (by norm_num)
  norm_num at h
  linarith only [h]

private theorem fsT_G2_neg {b : ℝ} (hb : 6 / 7 ≤ b) (hb1 : b ≤ 1) : fsT_Gsecond b < 0 := by
  have hb0 : 0 < b := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 / 4 by norm_num)
  have hc2 : 0 ≤ fsT_C2 := by unfold fsT_C2; linarith only [fsT_log_lower]
  have hc3 : 0 ≤ fsT_C3 := by unfold fsT_C3; linarith only [hlog]
  have hd0 : 0 ≤ fsT_D0 := by unfold fsT_D0; linarith only [fsT_log_lower]
  have hk2 : 0 ≤ 6 * fsT_C2 * (1 - b) / b ^ 4 := by positivity
  have hk3 : 0 ≤ 12 * fsT_C3 * (1 - b ^ 2) / b ^ 5 := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (by positivity) (by nlinarith only [hb1, hb0.le])
  have hkd : 0 ≤ 2 * fsT_D0 / b ^ 3 := by positivity
  unfold fsT_Gsecond
  linarith only [hk2, hk3, hkd]

private theorem fsT_G_concave : ConcaveOn ℝ (Icc (6 / 7 : ℝ) 1) fsT_Gmodel := by
  have hpos : ∀ b ∈ Icc (6 / 7 : ℝ) 1, 0 < b := fun b h => by linarith [h.1]
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun b h => (fsT_G_deriv (hpos b h)).continuousAt.continuousWithinAt)
    (fun b h => (fsT_G_deriv (hpos b (interior_subset h))).hasDerivWithinAt)
    (fun b h => (fsT_G1_deriv (hpos b (interior_subset h))).hasDerivWithinAt)
    (fun b h => (fsT_G2_neg (interior_subset h).1 (interior_subset h).2).le)

private theorem fsT_G_one : fsT_G 1 = 5 / 6 * Real.log (5 / 4) - 49 / 480 := by
  norm_num [fsT_G, fsT_upperBound, fsT_ratFirst, fsT_linear, fsT_quadratic, fsT_span0, fsT_span1,
    fsT_slopeLinear, fsT_slopeConst, fsT_slopeLead, fsT_slopeRecip, fsT_slopeRat,
    fsV_linear, fsV_quadratic, fsV_lead, fsT_lead, fsT_recip, fsT_p2, fsT_p1, fsT_p0, fsT_k,
    fs_normValueRat, fs_normRat, fs_normSlopeRat]
  ring
private theorem fsT_G_two : fsT_G 2 = 2 / 3 * Real.log (5 / 4) - 41 / 96 := by
  norm_num [fsT_G, fsT_upperBound, fsT_ratFirst, fsT_linear, fsT_quadratic, fsT_span0, fsT_span1,
    fsT_slopeLinear, fsT_slopeConst, fsT_slopeLead, fsT_slopeRecip, fsT_slopeRat,
    fsV_linear, fsV_quadratic, fsV_lead, fsT_lead, fsT_recip, fsT_p2, fsT_p1, fsT_p0, fsT_k,
    fs_normValueRat, fs_normRat, fs_normSlopeRat]
  ring

private noncomputable def fsT_upperRat (a : ℝ) : ℝ :=
  fsT_ratFirst a (1 / 4) +
    (5 * fsT_p2 a / 4 - fsT_p1 a + 4 * fsT_p0 a / 5) / (3 * (1 - a) ^ 3) -
    (5 * a / 4) * (a * fsT_k a / (6 * (1 - a) ^ 2) - (fsT_k a + a * (7 + a)) / (3 * (1 - a))) -
    a * ((1 - a) * (7 + a) - fsT_k a / 4) / (3 * (1 - a) ^ 2)
private noncomputable def fsT_GR (b : ℝ) : ℝ :=
  -113 * b ^ 2 / 96 - 173 / 48 * (3 / b - 1 / b ^ 2) +
    133 / 48 * (6 / b - 1 / b ^ 3) + 113 / (320 * b) + 1261 * b / 192 - 1499 / 120

private noncomputable def fsT_extraFirst (a : ℝ) : ℝ :=
  fsT_span0 a * fsT_slopeLinear a + fsT_span1 a * fsT_slopeConst a +
    (fsT_span0 a * fsT_slopeLead a + fsT_span1 a * fsT_slopeLinear a) / 2 +
    3 * (fsT_lead a - fsV_lead a) / 16 - 16 * fsT_recip a / 25
private theorem fsT_ratFirst_upper (a : ℝ) :
    fsT_ratFirst a (1 / 4) = fsV_cubicFirst a (1 / 4) + fsT_extraFirst a := by
  unfold fsT_ratFirst fsV_cubicFirst fsT_extraFirst fsT_linear fsT_quadratic
  ring

-- Exact derivative evaluations; signs are proved later by the reciprocal kernels.
private theorem fsT_V1_upper {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    fsV_cubicFirst a (1 / 4) = -(1 - a) ^ 2 / 2 - 65 * (1 - a) / 64 + 79 / 16 -
      347 / (64 * (1 - a)) + 73 / (32 * (1 - a) ^ 2) := by
  have hb : 0 < 1 - a := by linarith
  have hc2 : 0 < 1 - 2 * a := by linarith
  have hc3 : 0 < 1 - 3 * a := by linarith
  have he2 : 1 + (4 / ((1 - a) ^ 2 * (1 + (1 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      2 * (1 - 2 * a) / (1 - a) ^ 2 := by field_simp; ring
  have he3 : 1 + (4 / ((1 - a) ^ 2 * (1 + (2 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      4 * (1 - 3 * a) / (3 * (1 - a) ^ 2) := by field_simp; ring
  have he1 : 1 + (4 / ((1 - a) ^ 2 * (1 + (0 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      4 / (1 - a) := by field_simp; ring
  unfold fsV_cubicFirst fsV_linear fsV_quadratic fsV_lead fs_normValueRat fs_normRat
  dsimp only
  rw [he2, he3, he1]
  field_simp
  ring_nf
  field_simp [show (4 - a * 8 : ℝ) ≠ 0 by linarith, show (1 - a * 2 : ℝ) ≠ 0 by linarith]
  ring

private theorem fsT_extra_upper {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    fsT_extraFirst a = 215 * (1 - a) ^ 2 / 96 - 19 * (1 - a) / 2 + 1587 / 80 -
      1469 / (80 * (1 - a)) + 815 / (96 * (1 - a) ^ 2) - 55 / (16 * (1 - a) ^ 3) := by
  have hb : 0 < 1 - a := by linarith
  have hc2 : 0 < 1 - 2 * a := by linarith
  have he2 : 1 + (4 / ((1 - a) ^ 2 * (1 + (1 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      2 * (1 - 2 * a) / (1 - a) ^ 2 := by field_simp; ring
  have he1 : 1 + (4 / ((1 - a) ^ 2 * (1 + (0 : ℝ))) - ((1 + a) / (1 - a)) ^ 2) =
      4 / (1 - a) := by field_simp; ring
  unfold fsT_extraFirst fsT_span0 fsT_span1 fsT_slopeLinear fsT_slopeConst fsT_slopeLead
    fsT_slopeRecip fsT_lead fsV_lead fsT_recip fsT_slopeRat fs_normSlopeRat
  dsimp only
  rw [he2, he1]
  field_simp
  ring_nf

private theorem fsT_GR_eq {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    fsT_upperRat a = fsT_GR (1 - a) := by
  have hb : 0 < 1 - a := by linarith
  unfold fsT_upperRat
  rw [fsT_ratFirst_upper, fsT_V1_upper ha ha1, fsT_extra_upper ha ha1]
  unfold fsT_GR fsT_p2 fsT_p1 fsT_p0 fsT_k
  field_simp
  ring

private theorem fsT_G_eq {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7) :
    fsT_upperBound a = fsT_Gmodel (1 - a) := by
  have hb : 0 < 1 - a := by linarith
  have hsplit : fsT_upperBound a = fsT_upperRat a +
      (5 * fsT_p2 a / 2 - fsT_p1 a) / (3 * (1 - a) ^ 3) * Real.log (5 / 4) := by
    unfold fsT_upperBound fsT_upperRat
    ring
  rw [hsplit, fsT_GR_eq ha ha1]
  unfold fsT_Gmodel
  rw [fsT_G_one, fsT_G_two]
  unfold fsT_GR fsT_kernel fsT_C2 fsT_C3 fsT_D0 fsT_p2 fsT_p1
  field_simp
  ring

private theorem fsT_G_left : 0 < fsT_Gmodel (6 / 7) := by
  have he : fsT_Gmodel (6 / 7) = fsT_G (6 / 7) := by
    have h := fsT_G_eq (a := 1 / 7) (by norm_num) (by norm_num)
    norm_num [fsT_G] at h ⊢
    exact h.symm
  rw [he]
  norm_num [fsT_G, fsT_upperBound, fsT_ratFirst, fsT_linear, fsT_quadratic, fsT_span0, fsT_span1,
    fsT_slopeLinear, fsT_slopeConst, fsT_slopeLead, fsT_slopeRecip, fsT_slopeRat,
    fsV_linear, fsV_quadratic, fsV_lead, fsT_lead, fsT_recip, fsT_p2, fsT_p1, fsT_p0, fsT_k,
    fs_normValueRat, fs_normRat, fs_normSlopeRat]
  linarith only [fsT_log_lower]

private theorem fsT_G_right : 0 < fsT_Gmodel 1 := by
  have he : fsT_Gmodel 1 = fsT_G 1 := by simp [fsT_Gmodel]
  rw [he, fsT_G_one]
  linarith only [fsT_log_lower]

private theorem fsT_G_pos {b : ℝ} (hb : 6 / 7 ≤ b) (hb1 : b ≤ 1) : 0 < fsT_Gmodel b := by
  have hθ : 0 ≤ 7 * (b - 6 / 7) := by linarith
  have hθ1 : 0 ≤ 1 - 7 * (b - 6 / 7) := by linarith
  have hc := fsT_G_concave.2 (by norm_num : (6 / 7 : ℝ) ∈ Icc (6 / 7) 1)
    (by norm_num : (1 : ℝ) ∈ Icc (6 / 7) 1) hθ1 hθ (by ring)
  simp only [smul_eq_mul] at hc
  rw [show (1 - 7 * (b - 6 / 7)) * (6 / 7) + 7 * (b - 6 / 7) * 1 = b by ring] at hc
  by_cases he : b = 6 / 7
  · rw [he]; exact fsT_G_left
  · have hθpos : 0 < 7 * (b - 6 / 7) := by rcases lt_or_eq_of_le hb with h | h; linarith; exact (he h.symm).elim
    have hl := mul_nonneg hθ1 fsT_G_left.le
    have hr := mul_pos hθpos fsT_G_right
    linarith only [hc, hl, hr]

private theorem fsT_first_nonneg {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : 0 ≤ fsT_first a t := by
  have hupper : 0 < fsT_first a (1 / 4) := by
    have hpos := fsT_G_pos (b := 1 - a) (by linarith) (by linarith)
    rw [← fsT_G_eq ha ha1] at hpos
    exact hpos.trans_le (fsT_upper_le ha ha1)
  have hc := (fsT_first_concave ha ha1).2 (by norm_num : (0 : ℝ) ∈ Icc 0 (1 / 4))
    (by norm_num : (1 / 4 : ℝ) ∈ Icc 0 (1 / 4)) (show 0 ≤ 1 - 4 * t by linarith)
    (show 0 ≤ 4 * t by linarith) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add] at hc
  rw [show 4 * t * (1 / 4) = t by ring] at hc
  exact (add_nonneg (mul_nonneg (by linarith) (fsT_bottom_nonneg ha ha1))
    (mul_nonneg (by linarith) hupper.le)).trans hc

/-- The other tangent endpoint is negative on the geometric factor interval. -/
theorem fs_normTangent_neg {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 < t) (htstar : t ≤ (1 - a ^ 2) / (4 + a ^ 2)) : fs_normTangent a t < 0 := by
  have hb : 0 < 1 - a := by linarith
  have ha2 : a ^ 2 ≤ (1 / 7 : ℝ) ^ 2 := by nlinarith only [ha, ha1]
  have hden : 0 < 4 + a ^ 2 := by positivity
  have hstar : 0 < (1 - a ^ 2) / (4 + a ^ 2) := div_pos (by nlinarith only [ha2]) hden
  have hstar1 : (1 - a ^ 2) / (4 + a ^ 2) ≤ 1 / 4 := by
    rw [div_le_iff₀ hden]; nlinarith only [sq_nonneg a]
  have ht1 := htstar.trans hstar1
  have hm := ff_le_of_deriv (f := fsT_model a) (f' := fsT_first a) htstar
    (fun s hs => fsT_deriv (by linarith [hs.1]) (by nlinarith [hs.1, hs.2]))
    (fun s hs => fsT_first_nonneg ha ha1 (ht.le.trans hs.1) (hs.2.trans hstar1))
  rw [← fsT_eq ha ha1 ht.le ht1, ← fsT_eq ha ha1 hstar.le hstar1] at hm
  have he : fs_normSpan a ((1 - a ^ 2) / (4 + a ^ 2)) = 0 := by
    unfold fs_normSpan; field_simp; ring
  have hv := fs_normValue_neg ha ha1 hstar hstar1
  have hend : fs_normTangent a ((1 - a ^ 2) / (4 + a ^ 2)) < 0 := by
    simpa only [fs_normTangent, he, zero_mul, add_zero] using hv
  exact hm.trans_lt hend

end SmoothedOctagon
