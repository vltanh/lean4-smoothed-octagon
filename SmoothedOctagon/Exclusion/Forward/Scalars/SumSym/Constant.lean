module

public import SmoothedOctagon.Exclusion.Forward.Scalars.Canon

/-!
# The constant coefficient of the forward sum residual

At fixed normalized factor the third shape derivative is negative. The initial
slope and curvature are nonpositive by the reciprocal logarithm remainder, so
the coefficient decreases from its zero value at the symmetric shape.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

local syntax "analytic_deriv" : tactic
macro_rules
| `(tactic| analytic_deriv) => `(tactic|
  first
  | assumption
  | exact hasDerivAt_id' _
  | exact hasDerivAt_const _ _
  | apply HasDerivAt.add <;> analytic_deriv
  | apply HasDerivAt.sub <;> analytic_deriv
  | apply HasDerivAt.pow <;> analytic_deriv
  | apply HasDerivAt.mul <;> analytic_deriv
  | apply HasDerivAt.div <;> first | analytic_deriv | positivity | assumption
  | apply HasDerivAt.neg <;> analytic_deriv
  | apply HasDerivAt.log <;> first | analytic_deriv | positivity | assumption)

/-- The value of the continuously extended sum residual at factor one, with logarithms as atoms. -/
noncomputable def fs_SA0 (a t LI Lc : ℝ) : ℝ :=
  (1 - a * (1 + t)) * Lc +
    a * (1 - a * (1 + t)) * (a * (1 + t) + 3 * t + 1) / ((1 - a) * t) * LI +
    a * (a + t + a * t) / (2 * (1 - a)) * ((1 + a) ^ 2 * (1 + t) - 4)

private theorem fsA_log_lower {t : ℝ} (ht : 0 ≤ t) : t - t ^ 2 / 2 ≤ Real.log (1 + t) := by
  have h := ff_le_of_deriv (f := fun s : ℝ => Real.log (1 + s) - s + s ^ 2 / 2)
    (f' := fun s => s ^ 2 / (1 + s)) ht (fun s hs => ?_) (fun s hs => ?_)
  · norm_num at h
    linarith only [h]
  · have hs0 : 0 < 1 + s := by linarith [hs.1]
    apply HasDerivAt.congr_deriv
    · analytic_deriv
    · norm_num [npowRec]; field_simp; ring
  · have hs0 : 0 < 1 + s := by linarith [hs.1]
    positivity

private theorem fsA_log_upper {t : ℝ} (ht : 0 ≤ t) :
    Real.log (1 + t) ≤ t - t ^ 2 / (2 * (1 + t)) := by
  have h := ff_le_of_deriv (f := fun s : ℝ => s - s ^ 2 / (2 * (1 + s)) - Real.log (1 + s))
    (f' := fun s => s ^ 2 / (2 * (1 + s) ^ 2)) ht (fun s hs => ?_) (fun s hs => ?_)
  · norm_num at h
    linarith only [h]
  · have hs0 : 0 < 1 + s := by linarith [hs.1]
    apply HasDerivAt.congr_deriv
    · analytic_deriv
    · norm_num [npowRec]; field_simp; ring
  · have hs0 : 0 < 1 + s := by linarith [hs.1]
    positivity

private noncomputable def fsA_remainder (t : ℝ) : ℝ :=
  2 * (1 + 2 * t) * (t - Real.log (1 + t))
private noncomputable def fsA_slope (t : ℝ) : ℝ :=
  (t ^ 3 - 5 * t ^ 2 + (6 * t + 2) * Real.log (1 + t) - 2 * t) / (2 * t)
private noncomputable def fsA_curvature (t : ℝ) : ℝ :=
  (5 * t ^ 3 - t ^ 2 - 2 * t + (2 - 6 * t ^ 2) * Real.log (1 + t)) / t

-- The reciprocal term carries the logarithm remainder; the remaining rational part is cubic.
private noncomputable def fsA_model (t a : ℝ) : ℝ :=
  (1 - a * (1 + t)) * Real.log (1 - a * (1 + t)) - fsA_remainder t +
    (fsA_slope t + (1 + t) - fsA_remainder t) * a +
    (fsA_curvature t - (1 + t) ^ 2 - 2 * fsA_remainder t) / 2 * a ^ 2 -
    (1 + t) ^ 2 / 2 * a ^ 3 + fsA_remainder t / (1 - a)
private noncomputable def fsA_first (t a : ℝ) : ℝ :=
  -(1 + t) * Real.log (1 - a * (1 + t)) + fsA_slope t - fsA_remainder t +
    (fsA_curvature t - (1 + t) ^ 2 - 2 * fsA_remainder t) * a -
    3 * (1 + t) ^ 2 / 2 * a ^ 2 + fsA_remainder t / (1 - a) ^ 2
private noncomputable def fsA_second (t a : ℝ) : ℝ :=
  (1 + t) ^ 2 / (1 - a * (1 + t)) + fsA_curvature t - (1 + t) ^ 2 -
    2 * fsA_remainder t - 3 * (1 + t) ^ 2 * a + 2 * fsA_remainder t / (1 - a) ^ 3
private noncomputable def fsA_third (t a : ℝ) : ℝ :=
  (1 + t) ^ 3 / (1 - a * (1 + t)) ^ 2 - 3 * (1 + t) ^ 2 +
    6 * fsA_remainder t / (1 - a) ^ 4

private theorem fsA_model_eq {a t : ℝ} (hb : 0 < 1 - a) (ht : 0 < t) :
    fs_SA0 a t (Real.log (1 + t)) (Real.log (1 - a * (1 + t))) = fsA_model t a := by
  unfold fs_SA0 fsA_model fsA_slope fsA_curvature fsA_remainder
  field_simp
  ring
private theorem fsA_deriv {a t : ℝ} (hb : 0 < 1 - a) (hc : 0 < 1 - a * (1 + t)) :
    HasDerivAt (fsA_model t) (fsA_first t a) a := by
  unfold fsA_model fsA_first
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring
private theorem fsA_1_deriv {a t : ℝ} (hb : 0 < 1 - a) (hc : 0 < 1 - a * (1 + t)) :
    HasDerivAt (fsA_first t) (fsA_second t a) a := by
  unfold fsA_first fsA_second
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring
private theorem fsA_2_deriv {a t : ℝ} (hb : 0 < 1 - a) (hc : 0 < 1 - a * (1 + t)) :
    HasDerivAt (fsA_second t) (fsA_third t a) a := by
  unfold fsA_second fsA_third
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem fsA_third_neg {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 < t) (ht1 : t ≤ 1 / 4) : fsA_third t a < 0 := by
  have hb : 0 < 1 - a := by linarith
  have hh : 0 < 1 + t := by linarith
  have hbeta : 23 / 28 ≤ 1 - a * (1 + t) := by nlinarith only [ha, ha1, ht.le, ht1]
  have hbeta0 : 0 < 1 - a * (1 + t) := by linarith
  have hbeta2 : (23 / 28 : ℝ) ^ 2 ≤ (1 - a * (1 + t)) ^ 2 := by gcongr
  have hgap : 1 + t < 2 * (1 - a * (1 + t)) ^ 2 := by nlinarith only [ht1, hbeta2]
  have hfirst : (1 + t) ^ 3 / (1 - a * (1 + t)) ^ 2 < 2 * (1 + t) ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have hm := mul_lt_mul_of_pos_left hgap (sq_pos_of_pos hh)
    nlinarith only [hm]
  have hb4 : (6 / 7 : ℝ) ^ 4 ≤ (1 - a) ^ 4 := by gcongr; linarith
  have hratio : t ≤ (1 + t) / 5 := by linarith only [ht1]
  have hratio2 : t ^ 2 ≤ ((1 + t) / 5) ^ 2 := by gcongr
  have hK : fsA_remainder t ≤ (1 + 2 * t) * t ^ 2 := by
    have hl := fsA_log_lower ht.le
    have hm := mul_le_mul_of_nonneg_left (show t - Real.log (1 + t) ≤ t ^ 2 / 2 by linarith only [hl])
      (show 0 ≤ 2 * (1 + 2 * t) by positivity)
    unfold fsA_remainder
    nlinarith only [hm]
  have hm := mul_le_mul_of_nonneg_right (show 1 + 2 * t ≤ 3 / 2 by linarith only [ht1]) (sq_nonneg t)
  have hK' : 6 * fsA_remainder t ≤ 9 / 25 * (1 + t) ^ 2 := by nlinarith only [hK, hm, hratio2]
  have hthird : 6 * fsA_remainder t / (1 - a) ^ 4 < (1 + t) ^ 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have hg : (9 / 25 : ℝ) < (1 - a) ^ 4 := by nlinarith only [hb4]
    have hg' := mul_lt_mul_of_pos_right hg (sq_pos_of_pos hh)
    nlinarith only [hK', hg']
  unfold fsA_third
  linarith only [hfirst, hthird]

private theorem fsA_slope_neg {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 4) : fsA_slope t < 0 := by
  have hh : 0 < 1 + t := by linarith
  have hl := mul_le_mul_of_nonneg_left (fsA_log_upper ht.le) (show 0 ≤ 6 * t + 2 by positivity)
  have he : (t ^ 3 - 5 * t ^ 2 + (6 * t + 2) * (t - t ^ 2 / (2 * (1 + t))) - 2 * t) / (2 * t) =
      t ^ 2 * (t - 1) / (2 * (1 + t)) := by field_simp; ring
  unfold fsA_slope
  have hbnd := div_le_div_of_nonneg_right (show t ^ 3 - 5 * t ^ 2 + (6 * t + 2) * Real.log (1 + t) - 2 * t ≤
      t ^ 3 - 5 * t ^ 2 + (6 * t + 2) * (t - t ^ 2 / (2 * (1 + t))) - 2 * t by linarith only [hl])
    (show 0 ≤ 2 * t by positivity)
  rw [he] at hbnd
  exact hbnd.trans_lt (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (sq_pos_of_pos ht)
    (by linarith only [ht1])) (by positivity))

private theorem fsA_curvature_nonpos {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 4) : fsA_curvature t ≤ 0 := by
  have hh : 0 < 1 + t := by linarith
  have ht2 : t ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith only [ht.le, ht1]
  have hl := mul_le_mul_of_nonneg_left (fsA_log_upper ht.le) (show 0 ≤ 2 - 6 * t ^ 2 by nlinarith only [ht2])
  have he : (5 * t ^ 3 - t ^ 2 - 2 * t + (2 - 6 * t ^ 2) * (t - t ^ 2 / (2 * (1 + t)))) / t =
      2 * t * (t ^ 2 - t - 1) / (1 + t) := by field_simp; ring
  unfold fsA_curvature
  have hbnd := div_le_div_of_nonneg_right (show 5 * t ^ 3 - t ^ 2 - 2 * t + (2 - 6 * t ^ 2) * Real.log (1 + t) ≤
      5 * t ^ 3 - t ^ 2 - 2 * t + (2 - 6 * t ^ 2) * (t - t ^ 2 / (2 * (1 + t))) by linarith only [hl]) ht.le
  rw [he] at hbnd
  exact hbnd.trans (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (by nlinarith only [ht2, ht.le])) (by positivity))

private theorem fsA_model_le_tangent {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1 / 7)
    (ht : 0 < t) (ht1 : t ≤ 1 / 4) : fsA_model t a ≤ a * fsA_slope t := by
  have hb : ∀ x ∈ Icc (0 : ℝ) a, 0 < 1 - x := fun x hx => by linarith [hx.2]
  have hc : ∀ x ∈ Icc (0 : ℝ) a, 0 < 1 - x * (1 + t) := fun x hx => by nlinarith [hx.1, hx.2]
  have hsecond (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) : fsA_second t x ≤ 0 := by
    have hm := ff_le_of_deriv (f := fun s => -fsA_second t s) hx.1
      (fun s hs => (fsA_2_deriv (hb s ⟨hs.1, hs.2.trans hx.2⟩) (hc s ⟨hs.1, hs.2.trans hx.2⟩)).neg)
      (fun s hs => by have h := fsA_third_neg hs.1 (hs.2.trans (hx.2.trans ha1)) ht ht1; linarith only [h])
    change -fsA_second t 0 ≤ -fsA_second t x at hm
    rw [show fsA_second t 0 = fsA_curvature t by norm_num [fsA_second]] at hm
    linarith only [hm, fsA_curvature_nonpos ht ht1]
  have hfirst (x : ℝ) (hx : x ∈ Icc (0 : ℝ) a) : fsA_first t x ≤ fsA_slope t := by
    have hm := ff_le_of_deriv (f := fun s => -fsA_first t s) hx.1
      (fun s hs => (fsA_1_deriv (hb s ⟨hs.1, hs.2.trans hx.2⟩) (hc s ⟨hs.1, hs.2.trans hx.2⟩)).neg)
      (fun s hs => by have h := hsecond s ⟨hs.1, hs.2.trans hx.2⟩; linarith only [h])
    change -fsA_first t 0 ≤ -fsA_first t x at hm
    rw [show fsA_first t 0 = fsA_slope t by norm_num [fsA_first]] at hm
    linarith only [hm]
  have hm := ff_le_of_deriv (f := fun s => s * fsA_slope t - fsA_model t s)
    (f' := fun s => fsA_slope t - fsA_first t s) ha
    (fun s hs => (((hasDerivAt_id' s).mul_const (fsA_slope t)).sub
      (fsA_deriv (hb s hs) (hc s hs))).congr_deriv (by ring))
    (fun s hs => by have h := hfirst s hs; linarith only [h])
  rw [show fsA_model t 0 = 0 by norm_num [fsA_model]] at hm
  simp only [zero_mul, sub_self] at hm
  linarith only [hm]

/-- The constant coefficient decreases from its zero value at the symmetric shape. -/
theorem fs_SA0_bound {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 7) (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    fs_SA0 a t (Real.log (1 + t)) (Real.log (1 - a * (1 + t))) ≤ 0 := by
  rw [fsA_model_eq (by linarith : 0 < 1 - a) ht0]
  exact (fsA_model_le_tangent ha0 ha1 ht0 ht1).trans
    (mul_nonpos_of_nonneg_of_nonpos ha0 (fsA_slope_neg ht0 ht1).le)

/-- The constant coefficient is strictly negative away from the symmetric shape. -/
theorem fs_SA0_neg {a t : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1 / 7) (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    fs_SA0 a t (Real.log (1 + t)) (Real.log (1 - a * (1 + t))) < 0 := by
  rw [fsA_model_eq (by linarith : 0 < 1 - a) ht0]
  exact (fsA_model_le_tangent ha0.le ha1 ht0 ht1).trans_lt (mul_neg_of_pos_of_neg ha0 (fsA_slope_neg ht0 ht1))

end SmoothedOctagon
