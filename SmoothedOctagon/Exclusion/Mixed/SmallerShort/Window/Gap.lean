module
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.LogSecant
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Mean
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Endpoint gaps of the reciprocal kernel

The endpoint gaps are first moments of a positive derivative weight. Comparing
positive weights gives the two endpoint bounds; a linear tilt retains the
variance gain in the lower bound.
-/

@[expose] public section
namespace SmoothedOctagon
open Real Set MeasureTheory
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

private noncomputable def ssGap_h (p q t : ℝ) : ℝ :=
  (1 - p - (q - p) * t) / (1 + p + (q - p) * t) ^ 3
private noncomputable def ssGap_massPrimitive (p q t : ℝ) : ℝ :=
  -ss_gB 1 (p + (q - p) * t) / (q - p)
private noncomputable def ssGap_firstPrimitive (p q t : ℝ) : ℝ :=
  (ss_FB 1 (p + (q - p) * t) - (q - p) * t * ss_gB 1 (p + (q - p) * t)) / (q - p) ^ 2

private theorem ssGap_continuous {p q : ℝ} (hp : 0 ≤ p) (hd : 0 < q - p) :
    ContinuousOn (ssGap_h p q) (Icc (0 : ℝ) 1) := by
  unfold ssGap_h
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro t ht
    have ht0 := ht.1
    positivity

private theorem ssGap_mass_deriv {p q t : ℝ} (hp : 0 ≤ p) (hd : 0 < q - p) (ht : 0 ≤ t) :
    HasDerivAt (ssGap_massPrimitive p q) (ssGap_h p q t) t := by
  have hD : 0 < 1 + p + (q - p) * t := by positivity
  unfold ssGap_massPrimitive ssGap_h ss_gB
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem ssGap_first_deriv {p q t : ℝ} (hp : 0 ≤ p) (hd : 0 < q - p) (ht : 0 ≤ t) :
    HasDerivAt (ssGap_firstPrimitive p q) (t * ssGap_h p q t) t := by
  have hD : 0 < p + (q - p) * t + 1 := by positivity
  unfold ssGap_firstPrimitive ssGap_h ss_gB ss_FB
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem ssGap_mass {p q : ℝ} (hp : 0 ≤ p) (hpq : p < q) :
    (∫ t in (0 : ℝ)..1, ssGap_h p q t) = (ss_gB 1 p - ss_gB 1 q) / (q - p) := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun t ht => by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ssGap_mass_deriv hp hd ht.1)
    ((ssGap_continuous hp hd).intervalIntegrable_of_Icc (by norm_num))
  rw [hFT]
  simp only [ssGap_massPrimitive, mul_one, mul_zero, add_zero, show p + (q - p) = q by ring]
  ring

private theorem ssGap_first {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    (∫ t in (0 : ℝ)..1, t * ssGap_h p q t) = (m2Sec p 1 q - ss_gB 1 q) / (q - p) := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hq : 0 < q := hp.trans hpq
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := ssGap_firstPrimitive p q) (f' := fun t : ℝ => t * ssGap_h p q t) (a := 0) (b := 1)
    (fun t ht => by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ssGap_first_deriv hp.le hd ht.1)
    ((continuousOn_id.mul (ssGap_continuous hp.le hd)).intervalIntegrable_of_Icc (by norm_num))
  rw [hFT]
  simp only [ssGap_firstPrimitive, mul_one, mul_zero, add_zero, show p + (q - p) = q by ring, zero_mul, sub_zero]
  have hsec := ss_sec_mul hp (by norm_num : (0 : ℝ) < 1) hq
  rw [show ss_FB 1 q = (q - p) * m2Sec p 1 q + ss_FB 1 p by linarith only [hsec]]
  field_simp
  ring

private theorem ssGap_left {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    (∫ t in (0 : ℝ)..1, (1 - t) * ssGap_h p q t) = (ss_gB 1 p - m2Sec p 1 q) / (q - p) := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hc := ssGap_continuous hp.le hd
  have he : (fun t => (1 - t) * ssGap_h p q t) = (fun t => ssGap_h p q t - t * ssGap_h p q t) := by funext t; ring
  rw [he, intervalIntegral.integral_sub (f := ssGap_h p q) (g := fun t => t * ssGap_h p q t)
    (hc.intervalIntegrable_of_Icc (by norm_num))
    ((continuousOn_id.mul hc).intervalIntegrable_of_Icc (by norm_num)), ssGap_mass hp.le hpq, ssGap_first hp hpq]
  ring

private theorem ssGap_base_mass : (∫ t in (0 : ℝ)..1, ssGap_h 0 1 t) = 1 / 4 := by
  rw [ssGap_mass (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1)]
  norm_num [ss_gB]

private theorem ssGap_base_first : (∫ t in (0 : ℝ)..1, t * ssGap_h 0 1 t) = 3 / 4 - Real.log 2 := by
  have hc := ssGap_continuous (p := 0) (q := 1) (by norm_num) (by norm_num)
  have hFT := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := ssGap_firstPrimitive 0 1) (f' := fun t : ℝ => t * ssGap_h 0 1 t) (a := 0) (b := 1)
    (fun t ht => by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ssGap_first_deriv (by norm_num) (by norm_num) ht.1)
    ((continuousOn_id.mul hc).intervalIntegrable_of_Icc (by norm_num))
  rw [hFT]
  norm_num [ssGap_firstPrimitive, ss_gB, ss_FB]
  ring

private theorem ssGap_base_left : (∫ t in (0 : ℝ)..1, (1 - t) * ssGap_h 0 1 t) = Real.log 2 - 1 / 2 := by
  have hc := ssGap_continuous (p := 0) (q := 1) (by norm_num) (by norm_num)
  have he : (fun t => (1 - t) * ssGap_h 0 1 t) = (fun t => ssGap_h 0 1 t - t * ssGap_h 0 1 t) := by funext t; ring
  rw [he, intervalIntegral.integral_sub (f := ssGap_h 0 1) (g := fun t => t * ssGap_h 0 1 t)
    (hc.intervalIntegrable_of_Icc (by norm_num))
    ((continuousOn_id.mul hc).intervalIntegrable_of_Icc (by norm_num)), ssGap_base_mass, ssGap_base_first]
  ring

private theorem ssGap_base_moments_pos : 0 < 3 / 4 - Real.log 2 ∧ 0 < Real.log 2 - 1 / 2 := by
  have hc := ssGap_continuous (p := 0) (q := 1) (by norm_num) (by norm_num)
  have hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ssGap_h 0 1 t := by
    intro t ht
    have ht0 := ht.1
    unfold ssGap_h
    norm_num only [sub_zero, one_mul, add_zero, zero_add]
    exact div_nonneg (by linarith only [ht.2]) (by positivity)
  constructor
  · rw [← ssGap_base_first]
    apply intervalIntegral.integral_pos (f := fun t : ℝ => t * ssGap_h 0 1 t) (by norm_num) (continuousOn_id.mul hc)
    · intro t ht
      exact mul_nonneg ht.1.le (hpos t ⟨ht.1.le, ht.2⟩)
    · exact ⟨1 / 2, by norm_num, by norm_num [ssGap_h]⟩
  · rw [← ssGap_base_left]
    apply intervalIntegral.integral_pos (f := fun t : ℝ => (1 - t) * ssGap_h 0 1 t) (by norm_num) ((continuousOn_const.sub continuousOn_id).mul hc)
    · intro t ht
      exact mul_nonneg (by linarith only [ht.2]) (hpos t ⟨ht.1.le, ht.2⟩)
    · exact ⟨1 / 2, by norm_num, by norm_num [ssGap_h]⟩

private theorem ssGap_base_centered :
    (∫ t in (0 : ℝ)..1, (t - (3 - 4 * Real.log 2)) * ssGap_h 0 1 t) = 0 := by
  have hc := ssGap_continuous (p := 0) (q := 1) (by norm_num) (by norm_num)
  have he : (fun t => (t - (3 - 4 * Real.log 2)) * ssGap_h 0 1 t) =
      (fun t => t * ssGap_h 0 1 t - (3 - 4 * Real.log 2) * ssGap_h 0 1 t) := by funext t; ring
  rw [he, intervalIntegral.integral_sub (f := fun t => t * ssGap_h 0 1 t)
    (g := fun t => (3 - 4 * Real.log 2) * ssGap_h 0 1 t)
    ((continuousOn_id.mul hc).intervalIntegrable_of_Icc (by norm_num))
    ((continuousOn_const.mul hc).intervalIntegrable_of_Icc (by norm_num)),
    intervalIntegral.integral_const_mul, ssGap_base_first, ssGap_base_mass]
  ring

private noncomputable def ssGap_ratioModel (p q t : ℝ) : ℝ :=
  (1 - p - (q - p) * t) / (1 - t) * ((1 + t) / (1 + p + (q - p) * t)) ^ 3
private noncomputable def ssGap_ratioDerivative (p q t : ℝ) : ℝ :=
  (1 - q) / (1 - t) ^ 2 * ((1 + t) / (1 + p + (q - p) * t)) ^ 3 +
    (1 - p - (q - p) * t) / (1 - t) * 3 * ((1 + t) / (1 + p + (q - p) * t)) ^ 2 *
      (1 + 2 * p - q) / (1 + p + (q - p) * t) ^ 2

private theorem ssGap_ratio_eq {p q t : ℝ} (hp : 0 < p) (hpq : p < q) (ht : 0 ≤ t) (ht1 : t < 1) :
    ssGap_h p q t / ssGap_h 0 1 t = ssGap_ratioModel p q t := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hD : 0 < 1 + p + (q - p) * t := by positivity
  have h1 : 0 < 1 - t := by linarith
  have ht' : 0 < 1 + t := by positivity
  unfold ssGap_h ssGap_ratioModel
  norm_num
  field_simp

private theorem ssGap_ratio_deriv {p q t : ℝ} (hp : 0 < p) (hpq : p < q) (ht : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt (ssGap_ratioModel p q) (ssGap_ratioDerivative p q t) t := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hD : 0 < 1 + p + (q - p) * t := by positivity
  have h1 : 0 < 1 - t := by linarith
  unfold ssGap_ratioModel ssGap_ratioDerivative
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem ssGap_ratio_derivative_pos {p q t : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1)
    (ht : 0 ≤ t) (ht1 : t < 1) : 0 < ssGap_ratioDerivative p q t := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hD : 0 < 1 + p + (q - p) * t := by positivity
  have h1 : 0 < 1 - t := by linarith
  have hq1 : 0 ≤ 1 - q := by linarith
  have hnum : 0 < 1 - p - (q - p) * t := by
    have hm := mul_pos hd h1
    nlinarith only [hm, hq]
  have hB : 0 < 1 + 2 * p - q := by linarith only [hp, hq]
  unfold ssGap_ratioDerivative
  positivity

private theorem ssGap_ratio_strictMono {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    StrictMonoOn (fun t => ssGap_h p q t / ssGap_h 0 1 t) (Ico (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hm := ss_lt_of_deriv (f := ssGap_ratioModel p q) (f' := ssGap_ratioDerivative p q) hst
    (fun x hx => ssGap_ratio_deriv hp hpq (hs.1.trans hx.1) (hx.2.trans_lt ht.2))
    (fun x hx => ssGap_ratio_derivative_pos hp hpq hq (by linarith [hs.1, hx.1]) (hx.2.trans ht.2))
  dsimp only
  rw [ssGap_ratio_eq hp hpq hs.1 hs.2, ssGap_ratio_eq hp hpq ht.1 ht.2]
  exact hm

/-- The sharp upper ratio of the endpoint gaps of the reciprocal kernel. -/
theorem ss_gap_ratio_upper {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (ss_gB 1 p - m2Sec p 1 q) / (m2Sec p 1 q - ss_gB 1 q) <
      (Real.log 2 - 1 / 2) / (3 / 4 - Real.log 2) := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  obtain ⟨hbase1, hbase0⟩ := ssGap_base_moments_pos
  have hc0 : 0 < 3 - 4 * Real.log 2 := by linarith only [hbase1]
  have hc1 : 3 - 4 * Real.log 2 < 1 := by linarith only [hbase0]
  have hv : ∀ t ∈ Ico (0 : ℝ) 1, 0 < ssGap_h 0 1 t := by
    intro t ht
    have ht0 := ht.1
    have ht1 : 0 < 1 - t := by linarith only [ht.2]
    unfold ssGap_h
    norm_num only [sub_zero, one_mul, add_zero, zero_add]
    positivity
  have hv1 : ssGap_h 0 1 1 = 0 := by norm_num [ssGap_h]
  have hw1 : 0 ≤ ssGap_h p q 1 := by
    have he : ssGap_h p q 1 = (1 - q) / (1 + q) ^ 3 := by unfold ssGap_h; ring
    rw [he]
    exact div_nonneg (by linarith only [hq]) (by have hq0 : 0 < q := hp.trans hpq; positivity)
  have hm := ss_weighted_moment_of_strictMono (ssGap_continuous hp.le hd)
    (ssGap_continuous (p := 0) (q := 1) (by norm_num) (by norm_num)) hc0 hc1 hv hv1 hw1
    ssGap_base_centered (ssGap_ratio_strictMono hp hpq hq)
  rw [ssGap_mass hp.le hpq, ssGap_first hp hpq] at hm
  rw [show (3 - 4 * Real.log 2) * ((ss_gB 1 p - ss_gB 1 q) / (q - p)) =
      ((3 - 4 * Real.log 2) * (ss_gB 1 p - ss_gB 1 q)) / (q - p) by ring] at hm
  have hm' := (div_lt_div_iff_of_pos_right hd).mp hm
  have hright : 0 < m2Sec p 1 q - ss_gB 1 q := sub_pos.mpr (ss_sec_gt_right hp hpq hq)
  rw [div_lt_div_iff₀ hright hbase1]
  nlinarith only [hm']

/-- Both endpoint gaps in the limiting full interval are positive. -/
theorem ss_gap_limit_pos : 0 < Real.log 2 - 1 / 2 ∧ 0 < 3 / 4 - Real.log 2 := by
  obtain ⟨hright, hleft⟩ := ssGap_base_moments_pos
  exact ⟨hleft, hright⟩

/-- Mass of the tilted linear weight `(1-p-(q-p)t)(1-e t)` on the unit interval. -/
noncomputable def ss_gapTiltMass (p q e : ℝ) : ℝ :=
  (1 - p) - (q - p) / 2 - e * ((1 - p) / 2 - (q - p) / 3)
/-- First moment of the tilted linear weight on the unit interval. -/
noncomputable def ss_gapTiltFirst (p q e : ℝ) : ℝ :=
  (1 - p) / 2 - (q - p) / 3 - e * ((1 - p) / 3 - (q - p) / 4)
/-- The endpoint-gap ratio of the tilted linear comparison weight. -/
noncomputable def ss_gapTiltRatio (p q e : ℝ) : ℝ :=
  (ss_gapTiltMass p q e - ss_gapTiltFirst p q e) / ss_gapTiltFirst p q e

private noncomputable def ssGap_tiltV (p q e t : ℝ) : ℝ :=
  (1 - p - (q - p) * t) * (1 - e * t)
private noncomputable def ssGap_tiltFactor (p q e t : ℝ) : ℝ :=
  1 / ((1 + p + (q - p) * t) ^ 3 * (1 - e * t))
private noncomputable def ssGap_tiltFactorDerivative (p q e t : ℝ) : ℝ :=
  (e * (1 + p + 4 * (q - p) * t) - 3 * (q - p)) /
    ((1 + p + (q - p) * t) ^ 4 * (1 - e * t) ^ 2)
private noncomputable def ssGap_tiltPrimitive (p q e t : ℝ) : ℝ :=
  (1 - p) * t - ((q - p) + e * (1 - p)) * t ^ 2 / 2 + e * (q - p) * t ^ 3 / 3
private noncomputable def ssGap_tiltFirstPrimitive (p q e t : ℝ) : ℝ :=
  (1 - p) * t ^ 2 / 2 - ((q - p) + e * (1 - p)) * t ^ 3 / 3 + e * (q - p) * t ^ 4 / 4

private theorem ssGap_tilt_range {p q e : ℝ} (hp : 0 < p) (hpq : p < q)
    (he : e ≤ 3 * (q - p) / (1 + p + 4 * (q - p))) : e < 3 / 4 := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hD : 0 < 1 + p + 4 * (q - p) := by positivity
  apply lt_of_le_of_lt he
  rw [div_lt_iff₀ hD]
  linarith only [hp]

private theorem ssGap_tilt_den_pos {e t : ℝ} (he : 0 ≤ e) (he1 : e < 3 / 4)
    (ht : t ≤ 1) : 0 < 1 - e * t := by
  have hm := mul_le_mul_of_nonneg_left ht he
  linarith only [hm, he1]

private theorem ssGap_tilt_nonneg {p q e t : ℝ} (hpq : p < q) (hq : q ≤ 1)
    (he : 0 ≤ e) (he1 : e < 3 / 4) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ ssGap_tiltV p q e t := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hn : 0 ≤ 1 - p - (q - p) * t := by
    have hm := mul_nonneg hd.le (show 0 ≤ 1 - t by linarith only [ht.2])
    nlinarith only [hm, hq]
  exact mul_nonneg hn (ssGap_tilt_den_pos he he1 ht.2).le

private theorem ssGap_tilt_pos {p q e t : ℝ} (hpq : p < q) (hq : q ≤ 1)
    (he : 0 ≤ e) (he1 : e < 3 / 4) (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < ssGap_tiltV p q e t := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hn : 0 < 1 - p - (q - p) * t := by
    have hm := mul_pos hd (show 0 < 1 - t by linarith only [ht.2])
    nlinarith only [hm, hq]
  exact mul_pos hn (ssGap_tilt_den_pos he he1 ht.2.le)

private theorem ssGap_tilt_cont (p q e : ℝ) : ContinuousOn (ssGap_tiltV p q e) (Icc (0 : ℝ) 1) := by
  unfold ssGap_tiltV
  fun_prop

private theorem ssGap_tilt_deriv (p q e t : ℝ) :
    HasDerivAt (ssGap_tiltPrimitive p q e) (ssGap_tiltV p q e t) t := by
  unfold ssGap_tiltPrimitive ssGap_tiltV
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; ring

private theorem ssGap_tilt_first_deriv (p q e t : ℝ) :
    HasDerivAt (ssGap_tiltFirstPrimitive p q e) (t * ssGap_tiltV p q e t) t := by
  unfold ssGap_tiltFirstPrimitive ssGap_tiltV
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; ring

private theorem ssGap_tilt_mass (p q e : ℝ) :
    (∫ t in (0 : ℝ)..1, ssGap_tiltV p q e t) = ss_gapTiltMass p q e := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := ssGap_tiltPrimitive p q e) (f' := ssGap_tiltV p q e) (a := 0) (b := 1)
    (fun t _ => ssGap_tilt_deriv p q e t)
    ((ssGap_tilt_cont p q e).intervalIntegrable_of_Icc (by norm_num))
  rw [h]
  norm_num [ssGap_tiltPrimitive, ss_gapTiltMass]; ring

private theorem ssGap_tilt_first (p q e : ℝ) :
    (∫ t in (0 : ℝ)..1, t * ssGap_tiltV p q e t) = ss_gapTiltFirst p q e := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := ssGap_tiltFirstPrimitive p q e) (f' := fun t : ℝ => t * ssGap_tiltV p q e t) (a := 0) (b := 1)
    (fun t _ => ssGap_tilt_first_deriv p q e t)
    ((continuousOn_id.mul (ssGap_tilt_cont p q e)).intervalIntegrable_of_Icc (by norm_num))
  rw [h]
  norm_num [ssGap_tiltFirstPrimitive, ss_gapTiltFirst]; ring

private theorem ssGap_tilt_left (p q e : ℝ) :
    (∫ t in (0 : ℝ)..1, (1 - t) * ssGap_tiltV p q e t) = ss_gapTiltMass p q e - ss_gapTiltFirst p q e := by
  have hc := ssGap_tilt_cont p q e
  have he : (fun t => (1 - t) * ssGap_tiltV p q e t) =
      (fun t => ssGap_tiltV p q e t - t * ssGap_tiltV p q e t) := by funext t; ring
  rw [he, intervalIntegral.integral_sub (f := ssGap_tiltV p q e) (g := fun t : ℝ => t * ssGap_tiltV p q e t)
    (hc.intervalIntegrable_of_Icc (by norm_num)) ((continuousOn_id.mul hc).intervalIntegrable_of_Icc (by norm_num)),
    ssGap_tilt_mass, ssGap_tilt_first]

private theorem ssGap_tilt_moments_pos {p q e : ℝ} (hpq : p < q) (hq : q ≤ 1)
    (he : 0 ≤ e) (he1 : e < 3 / 4) :
    0 < ss_gapTiltMass p q e ∧ 0 < ss_gapTiltFirst p q e ∧
      0 < ss_gapTiltMass p q e - ss_gapTiltFirst p q e := by
  have hc := ssGap_tilt_cont p q e
  have hhalf := ssGap_tilt_pos hpq hq he he1 (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  have hn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ssGap_tiltV p q e t :=
    fun t ht => ssGap_tilt_nonneg hpq hq he he1 ht
  refine ⟨?_, ?_, ?_⟩
  · rw [← ssGap_tilt_mass]
    exact intervalIntegral.integral_pos (by norm_num) hc (fun t ht => hn t ⟨ht.1.le, ht.2⟩)
      ⟨1 / 2, by norm_num, hhalf⟩
  · rw [← ssGap_tilt_first]
    apply intervalIntegral.integral_pos (f := fun t : ℝ => t * ssGap_tiltV p q e t)
      (by norm_num) (continuousOn_id.mul hc)
    · intro t ht
      exact mul_nonneg ht.1.le (hn t ⟨ht.1.le, ht.2⟩)
    · exact ⟨1 / 2, by norm_num, mul_pos (by norm_num) hhalf⟩
  · rw [← ssGap_tilt_left]
    apply intervalIntegral.integral_pos (f := fun t : ℝ => (1 - t) * ssGap_tiltV p q e t)
      (by norm_num) ((continuousOn_const.sub continuousOn_id).mul hc)
    · intro t ht
      exact mul_nonneg (by linarith only [ht.2]) (hn t ⟨ht.1.le, ht.2⟩)
    · exact ⟨1 / 2, by norm_num, mul_pos (by norm_num) hhalf⟩

private theorem ssGap_tilt_factor_deriv {p q e t : ℝ} (hp : 0 < p) (hpq : p < q)
    (he : 0 ≤ e) (he1 : e < 3 / 4) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (ssGap_tiltFactor p q e) (ssGap_tiltFactorDerivative p q e t) t := by
  have ht0 := ht.1
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hD : 0 < 1 + p + (q - p) * t := by positivity
  have hE := ssGap_tilt_den_pos he he1 ht.2
  unfold ssGap_tiltFactor ssGap_tiltFactorDerivative
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem ssGap_tilt_factor_derivative_neg {p q e t : ℝ} (hp : 0 < p) (hpq : p < q)
    (he : 0 ≤ e) (hemax : e ≤ 3 * (q - p) / (1 + p + 4 * (q - p))) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ssGap_tiltFactorDerivative p q e t < 0 := by
  have ht0 := ht.1.le
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hD : 0 < 1 + p + (q - p) * t := by positivity
  have hE := ssGap_tilt_den_pos he (ssGap_tilt_range hp hpq hemax) ht.2.le
  have hbig : 0 < 1 + p + 4 * (q - p) := by positivity
  have heD := (le_div_iff₀ hbig).mp hemax
  have hnum : e * (1 + p + 4 * (q - p) * t) - 3 * (q - p) < 0 := by
    by_cases he0 : e = 0
    · rw [he0]; nlinarith only [hd]
    · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm he0)
      have hm := mul_pos (mul_pos hepos hd) (show 0 < 1 - t by linarith only [ht.2])
      nlinarith only [heD, hm]
  unfold ssGap_tiltFactorDerivative
  exact div_neg_of_neg_of_pos hnum (by positivity)

private theorem ssGap_tilt_factor_strictAnti {p q e : ℝ} (hp : 0 < p) (hpq : p < q)
    (he : 0 ≤ e) (hemax : e ≤ 3 * (q - p) / (1 + p + 4 * (q - p))) :
    StrictAntiOn (ssGap_tiltFactor p q e) (Icc (0 : ℝ) 1) := by
  have he1 := ssGap_tilt_range hp hpq hemax
  intro s hs t ht hst
  have h := ss_lt_of_deriv (f := fun u => -ssGap_tiltFactor p q e u)
    (f' := fun u => -ssGap_tiltFactorDerivative p q e u) hst
    (fun u hu => (ssGap_tilt_factor_deriv hp hpq he he1 ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩).neg)
    (fun u hu => neg_pos.mpr (ssGap_tilt_factor_derivative_neg hp hpq he hemax
      ⟨by linarith [hs.1, hu.1], by linarith [ht.2, hu.2]⟩))
  linarith only [h]

private theorem ssGap_tilt_factorization {p q e t : ℝ} (hp : 0 < p) (hpq : p < q)
    (he : 0 ≤ e) (he1 : e < 3 / 4) (ht : t ∈ Icc (0 : ℝ) 1) :
    ssGap_h p q t = ssGap_tiltV p q e t * ssGap_tiltFactor p q e t := by
  have ht0 := ht.1
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hD : 0 < 1 + p + (q - p) * t := by positivity
  have hE := ssGap_tilt_den_pos he he1 ht.2
  have hE' : 0 < 1 - t * e := by nlinarith only [hE]
  unfold ssGap_h ssGap_tiltV ssGap_tiltFactor
  field_simp [hE.ne', hE'.ne']

/-- Tilting the linear derivative weight gives a strict lower comparison of endpoint gaps. -/
theorem ss_gap_ratio_tilted {p q e : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1)
    (he : 0 ≤ e) (hemax : e ≤ 3 * (q - p) / (1 + p + 4 * (q - p))) :
    ss_gapTiltRatio p q e < (ss_gB 1 p - m2Sec p 1 q) / (m2Sec p 1 q - ss_gB 1 q) := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  have he1 := ssGap_tilt_range hp hpq hemax
  obtain ⟨hM0, hM1, hML⟩ := ssGap_tilt_moments_pos hpq hq he he1
  let c := ss_gapTiltFirst p q e / ss_gapTiltMass p q e
  have hc0 : 0 < c := div_pos hM1 hM0
  have hc1 : c < 1 := (div_lt_one hM0).mpr (by linarith only [hML])
  have hcenter : (∫ t in (0 : ℝ)..1, (t - c) * ssGap_tiltV p q e t) = 0 := by
    have hcont := ssGap_tilt_cont p q e
    have hfun : (fun t => (t - c) * ssGap_tiltV p q e t) =
        (fun t => t * ssGap_tiltV p q e t - c * ssGap_tiltV p q e t) := by funext t; ring
    rw [hfun, intervalIntegral.integral_sub (f := fun t : ℝ => t * ssGap_tiltV p q e t)
      (g := fun t : ℝ => c * ssGap_tiltV p q e t)
      ((continuousOn_id.mul hcont).intervalIntegrable_of_Icc (by norm_num))
      ((continuousOn_const.mul hcont).intervalIntegrable_of_Icc (by norm_num)),
      intervalIntegral.integral_const_mul, ssGap_tilt_first, ssGap_tilt_mass]
    dsimp [c]
    field_simp
    ring
  have hm := ss_weighted_moment_of_strictAnti_factor
    (ssGap_continuous hp.le hd) (ssGap_tilt_cont p q e) hc0 hc1
    (fun t ht => ssGap_tilt_nonneg hpq hq he he1 ht)
    (fun t ht => ssGap_tilt_pos hpq hq he he1 ht)
    (fun t ht => ssGap_tilt_factorization hp hpq he he1 ht)
    (ssGap_tilt_factor_strictAnti hp hpq he hemax) hcenter
  rw [ssGap_first hp hpq, ssGap_mass hp.le hpq] at hm
  rw [show c * ((ss_gB 1 p - ss_gB 1 q) / (q - p)) =
      (c * (ss_gB 1 p - ss_gB 1 q)) / (q - p) by ring] at hm
  have hm' := (div_lt_div_iff_of_pos_right hd).mp hm
  dsimp [c] at hm'
  rw [show ss_gapTiltFirst p q e / ss_gapTiltMass p q e * (ss_gB 1 p - ss_gB 1 q) =
      (ss_gapTiltFirst p q e * (ss_gB 1 p - ss_gB 1 q)) / ss_gapTiltMass p q e by ring] at hm'
  have hcross := (lt_div_iff₀ hM0).mp hm'
  have hright : 0 < m2Sec p 1 q - ss_gB 1 q := sub_pos.mpr (ss_sec_gt_right hp hpq hq)
  unfold ss_gapTiltRatio
  rw [div_lt_div_iff₀ hM1 hright]
  nlinarith only [hcross]

private theorem ssGap_half_tilt_admissible {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (q - p) / 2 ≤ 3 * (q - p) / (1 + p + 4 * (q - p)) := by
  have hd : 0 < q - p := sub_pos.mpr hpq
  have hD : 0 < 1 + p + 4 * (q - p) := by positivity
  rw [le_div_iff₀ hD]
  have hbound : 0 ≤ 6 - (1 + p + 4 * (q - p)) := by linarith only [hp, hq]
  have hm := mul_nonneg hd.le hbound
  nlinarith only [hm]

private theorem ssGap_half_tilt_gain {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (3 - 2 * p - q) / (3 - p - 2 * q) + (q - p) / 6 < ss_gapTiltRatio p q ((q - p) / 2) := by
  let b := 1 - p
  let d := q - p
  let e := d / 2
  let A0 := b - d / 2
  let A1 := b / 2 - d / 3
  let A2 := b / 3 - d / 4
  let V := A0 * A2 - A1 ^ 2
  have hd : 0 < d := sub_pos.mpr hpq
  have hbd : d ≤ b := by dsimp [b, d]; linarith only [hq]
  have he : 0 < e := by dsimp [e]; positivity
  have hA1 : 0 < A1 := by dsimp [A1]; nlinarith only [hbd, hd]
  have hA2 : 0 < A2 := by dsimp [A2]; nlinarith only [hbd, hd]
  have hemax : e ≤ 3 * (q - p) / (1 + p + 4 * (q - p)) := ssGap_half_tilt_admissible hp hpq hq
  have he1 := ssGap_tilt_range hp hpq hemax
  obtain ⟨hM0, hM1, hML⟩ := ssGap_tilt_moments_pos hpq hq he.le he1
  have hMA : ss_gapTiltMass p q e = A0 - e * A1 := by dsimp [ss_gapTiltMass, A0, A1, b, d]
  have hME : ss_gapTiltFirst p q e = A1 - e * A2 := by dsimp [ss_gapTiltFirst, A1, A2, b, d]
  have hF : 0 < A1 - e * A2 := by rw [← hME]; exact hM1
  have hvariance : V - A1 ^ 2 / 3 = d * (6 * b - 5 * d) / 216 := by
    dsimp [V, A0, A1, A2]
    ring
  have hvar : A1 ^ 2 / 3 < V := by
    have hpositive : 0 < d * (6 * b - 5 * d) / 216 := by
      have hb6 : 0 < 6 * b - 5 * d := by nlinarith only [hbd, hd]
      positivity
    linarith only [hvariance, hpositive]
  have hfirst : ss_gapTiltFirst p q e < A1 := by
    rw [hME]
    have hproduct := mul_pos he hA2
    linarith only [hproduct]
  have hpair := mul_lt_mul_of_pos_left hfirst hA1
  have hscaled := mul_lt_mul_of_pos_left hpair (show 0 < e / 3 by positivity)
  have hvarscaled := mul_lt_mul_of_pos_left hvar he
  have hquot : e / 3 < e * V / (A1 * ss_gapTiltFirst p q e) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith only [hscaled, hvarscaled]
  have hgain : ss_gapTiltRatio p q e - (A0 - A1) / A1 =
      e * V / (A1 * ss_gapTiltFirst p q e) := by
    unfold ss_gapTiltRatio
    rw [hMA, hME]
    dsimp only [V]
    field_simp
    ring
  have hden : 0 < 3 - p - 2 * q := by linarith only [hpq, hq]
  have hbase : (A0 - A1) / A1 = (3 - 2 * p - q) / (3 - p - 2 * q) := by
    dsimp [A0, A1, b, d]
    field_simp
    ring
  have hefrac : e / 3 = (q - p) / 6 := by dsimp [e, d]; ring
  rw [← hbase]
  change (A0 - A1) / A1 + (q - p) / 6 < ss_gapTiltRatio p q e
  linarith only [hgain, hquot, hefrac]

/-- The refined lower endpoint-gap ratio from the variance of the linear weight. -/
theorem ss_gap_ratio_lower {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    (3 - 2 * p - q) / (3 - p - 2 * q) + (q - p) / 6 <
      (ss_gB 1 p - m2Sec p 1 q) / (m2Sec p 1 q - ss_gB 1 q) := by
  have htilt := ss_gap_ratio_tilted hp hpq hq (show 0 ≤ (q - p) / 2 by linarith only [hpq])
    (ssGap_half_tilt_admissible hp hpq hq)
  exact lt_trans (ssGap_half_tilt_gain hp hpq hq) htilt

/-- Both sharp endpoint-gap comparisons, including the strict variance improvement. -/
theorem ss_gap_ratio_bounds {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    ((3 - 2 * p - q) / (3 - p - 2 * q) + (q - p) / 6 <
      (ss_gB 1 p - m2Sec p 1 q) / (m2Sec p 1 q - ss_gB 1 q)) ∧
    ((ss_gB 1 p - m2Sec p 1 q) / (m2Sec p 1 q - ss_gB 1 q) <
      (Real.log 2 - 1 / 2) / (3 / 4 - Real.log 2)) :=
  ⟨ss_gap_ratio_lower hp hpq hq, ss_gap_ratio_upper hp hpq hq⟩

private theorem ssGap_scale_den {b r t : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (_hr : 0 ≤ r) (hr1 : r < 1) (ht : t ∈ Icc (0:ℝ) 1) :
    0 < 2-b*(1-(1-r)*t) := by
  have hv : 1-(1-r)*t ≤ 1 := by nlinarith only [hr1,ht.1]
  have hh := mul_le_mul_of_nonneg_left hv hb.le
  linarith only [hh,hb1]

private noncomputable def ssGap_scaleFactor (b1 b2 r t : ℝ) : ℝ :=
  b2/b1 * ((2-b1*(1-(1-r)*t))/(2-b2*(1-(1-r)*t)))^3
private noncomputable def ssGap_scaleFactorD (b1 b2 r t : ℝ) : ℝ :=
  -(6*b2/b1)*(b2-b1)*(1-r)*(2-b1*(1-(1-r)*t))^2 /
    (2-b2*(1-(1-r)*t))^4

private theorem ssGap_scaleFactor_deriv {b1 b2 r t : ℝ} (hb1 : 0 < b1)
    (hb12 : b1 < b2) (hb2 : b2 < 1) (hr : 0 ≤ r) (hr1 : r < 1)
    (ht : t ∈ Icc (0:ℝ) 1) : HasDerivAt (ssGap_scaleFactor b1 b2 r) (ssGap_scaleFactorD b1 b2 r t) t := by
  have hd := ssGap_scale_den (hb1.trans hb12) hb2 hr hr1 ht
  unfold ssGap_scaleFactor ssGap_scaleFactorD
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem ssGap_scaleFactor_anti {b1 b2 r : ℝ} (hb1 : 0 < b1)
    (hb12 : b1 < b2) (hb2 : b2 < 1) (hr : 0 ≤ r) (hr1 : r < 1) :
    StrictAntiOn (ssGap_scaleFactor b1 b2 r) (Icc (0:ℝ) 1) := by
  intro s hs t ht hst
  have h := ss_lt_of_deriv (f := fun u => -ssGap_scaleFactor b1 b2 r u)
    (f' := fun u => -ssGap_scaleFactorD b1 b2 r u) hst
    (fun u hu => (ssGap_scaleFactor_deriv hb1 hb12 hb2 hr hr1 ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩).neg)
    (fun u hu => by
      have huI : u ∈ Icc (0:ℝ) 1 := ⟨hs.1.trans hu.1.le,hu.2.le.trans ht.2⟩
      have hD1 := ssGap_scale_den hb1 (hb12.trans hb2) hr hr1 huI
      have hD2 := ssGap_scale_den (hb1.trans hb12) hb2 hr hr1 huI
      have hb2p : 0 < b2 := hb1.trans hb12
      have h12 : 0 < b2-b1 := sub_pos.mpr hb12
      have hrp : 0 < 1-r := by linarith
      unfold ssGap_scaleFactorD
      have : 0 < (6*b2/b1)*(b2-b1)*(1-r)*(2-b1*(1-(1-r)*u))^2 /
          (2-b2*(1-(1-r)*u))^4 := by positivity
      convert this using 1; ring)
  linarith only [h]

/-- Increasing the scale of an interval with fixed deficit ratio increases its endpoint-gap ratio. -/
theorem ss_gap_ratio_scale_mono {b1 b2 r : ℝ} (hb1 : 0 < b1)
    (hb12 : b1 ≤ b2) (hb2 : b2 < 1) (hr : 0 ≤ r) (hr1 : r < 1) :
    (ss_gB 1 (1-b1)-m2Sec (1-b1) 1 (1-b1*r)) /
        (m2Sec (1-b1) 1 (1-b1*r)-ss_gB 1 (1-b1*r)) ≤
    (ss_gB 1 (1-b2)-m2Sec (1-b2) 1 (1-b2*r)) /
        (m2Sec (1-b2) 1 (1-b2*r)-ss_gB 1 (1-b2*r)) := by
  rcases hb12.eq_or_lt with he | hb12
  · subst b2; exact le_rfl
  have hb2p : 0 < b2 := hb1.trans hb12
  have h1 : 0 < 1-b1 := by linarith only [hb12,hb2]
  have h2 : 0 < 1-b2 := by linarith only [hb2]
  have hpq1 : 1-b1 < 1-b1*r := by nlinarith only [hb1,hr1]
  have hpq2 : 1-b2 < 1-b2*r := by nlinarith only [hb2p,hr1]
  have hq1 : 1-b1*r ≤ 1 := by nlinarith only [hb1,hr]
  have hq2 : 1-b2*r ≤ 1 := by nlinarith only [hb2p,hr]
  have hη1 : 0 < m2Sec (1-b1) 1 (1-b1*r)-ss_gB 1 (1-b1*r) :=
    sub_pos.mpr (ss_sec_gt_right h1 hpq1 hq1)
  have hξ1 : 0 < ss_gB 1 (1-b1)-m2Sec (1-b1) 1 (1-b1*r) :=
    sub_pos.mpr (ss_sec_lt_left h1 hpq1 hq1)
  have hη2 : 0 < m2Sec (1-b2) 1 (1-b2*r)-ss_gB 1 (1-b2*r) :=
    sub_pos.mpr (ss_sec_gt_right h2 hpq2 hq2)
  have htotal : 0 < ss_gB 1 (1-b1)-ss_gB 1 (1-b1*r) := by linarith only [hη1,hξ1]
  let c := (m2Sec (1-b1) 1 (1-b1*r)-ss_gB 1 (1-b1*r)) /
      (ss_gB 1 (1-b1)-ss_gB 1 (1-b1*r))
  have hc0 : 0 < c := div_pos hη1 htotal
  have hc1 : c < 1 := by dsimp [c]; rw [div_lt_one htotal]; linarith only [hξ1]
  have hcA := ssGap_continuous h1.le (sub_pos.mpr hpq1)
  have hcB := ssGap_continuous h2.le (sub_pos.mpr hpq2)
  have hcenter : (∫ t in (0:ℝ)..1, (t-c)*ssGap_h (1-b1) (1-b1*r) t) = 0 := by
    have he : (fun t => (t-c)*ssGap_h (1-b1) (1-b1*r) t) =
        (fun t => t*ssGap_h (1-b1) (1-b1*r) t-c*ssGap_h (1-b1) (1-b1*r) t) := by funext t; ring
    rw [he,intervalIntegral.integral_sub (f := fun t : ℝ => t*ssGap_h (1-b1) (1-b1*r) t)
      (g := fun t : ℝ => c*ssGap_h (1-b1) (1-b1*r) t)
      ((continuousOn_id.mul hcA).intervalIntegrable_of_Icc (by norm_num))
      ((continuousOn_const.mul hcA).intervalIntegrable_of_Icc (by norm_num)),
      intervalIntegral.integral_const_mul,ssGap_first h1 hpq1,ssGap_mass h1.le hpq1]
    dsimp [c]
    field_simp [htotal.ne']
    ring
  have hfac : ∀ t ∈ Icc (0:ℝ) 1, ssGap_h (1-b2) (1-b2*r) t =
      ssGap_h (1-b1) (1-b1*r) t * ssGap_scaleFactor b1 b2 r t := by
    intro t ht
    have hD1 := ssGap_scale_den hb1 (hb12.trans hb2) hr hr1 ht
    have hD2 := ssGap_scale_den hb2p hb2 hr hr1 ht
    have he1 : 1+(1-b1)+((1-b1*r)-(1-b1))*t = 2-b1*(1-(1-r)*t) := by ring
    have he2 : 1+(1-b2)+((1-b2*r)-(1-b2))*t = 2-b2*(1-(1-r)*t) := by ring
    unfold ssGap_h ssGap_scaleFactor
    rw [he1,he2]
    field_simp (disch := first | positivity | nlinarith)
    ring
  have hvn : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ ssGap_h (1-b1) (1-b1*r) t := by
    intro t ht
    have hd := ssGap_scale_den hb1 (hb12.trans hb2) hr hr1 ht
    have hv : 0 ≤ 1-(1-r)*t := by
      have hm := mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 1-r by linarith)
      linarith only [hm,hr]
    have he : ssGap_h (1-b1) (1-b1*r) t = b1*(1-(1-r)*t)/(2-b1*(1-(1-r)*t))^3 := by
      unfold ssGap_h; congr 1 <;> ring
    rw [he]; positivity
  have hvp : ∀ t ∈ Ioo (0:ℝ) 1, 0 < ssGap_h (1-b1) (1-b1*r) t := by
    intro t ht
    have hd := ssGap_scale_den hb1 (hb12.trans hb2) hr hr1 ⟨ht.1.le,ht.2.le⟩
    have hv : 0 < 1-(1-r)*t := by
      have hm := mul_le_mul_of_nonneg_left ht.2.le (show 0 ≤ 1-r by linarith)
      have hm2 := mul_nonneg hr ht.1.le
      nlinarith only [ht.2,hm2]
    have he : ssGap_h (1-b1) (1-b1*r) t = b1*(1-(1-r)*t)/(2-b1*(1-(1-r)*t))^3 := by
      unfold ssGap_h; congr 1 <;> ring
    rw [he]; positivity
  have hm := ss_weighted_moment_of_strictAnti_factor hcB hcA hc0 hc1 hvn hvp hfac
    (ssGap_scaleFactor_anti hb1 hb12 hb2 hr hr1) hcenter
  rw [ssGap_first h2 hpq2,ssGap_mass h2.le hpq2] at hm
  have hd2 : 0 < (1-b2*r)-(1-b2) := sub_pos.mpr hpq2
  rw [show c*((ss_gB 1 (1-b2)-ss_gB 1 (1-b2*r))/((1-b2*r)-(1-b2))) =
      (c*(ss_gB 1 (1-b2)-ss_gB 1 (1-b2*r)))/((1-b2*r)-(1-b2)) by ring] at hm
  have hm' := (div_lt_div_iff_of_pos_right hd2).mp hm
  dsimp [c] at hm'
  have hcross : (m2Sec (1-b2) 1 (1-b2*r)-ss_gB 1 (1-b2*r)) *
      (ss_gB 1 (1-b1)-ss_gB 1 (1-b1*r)) <
      (m2Sec (1-b1) 1 (1-b1*r)-ss_gB 1 (1-b1*r)) *
      (ss_gB 1 (1-b2)-ss_gB 1 (1-b2*r)) := by
    have hh := (lt_div_iff₀ htotal).mp (show
      m2Sec (1-b2) 1 (1-b2*r)-ss_gB 1 (1-b2*r) <
      ((m2Sec (1-b1) 1 (1-b1*r)-ss_gB 1 (1-b1*r))*
        (ss_gB 1 (1-b2)-ss_gB 1 (1-b2*r)))/
        (ss_gB 1 (1-b1)-ss_gB 1 (1-b1*r)) by
          convert hm' using 1; ring)
    exact hh
  rw [div_le_div_iff₀ hη1 hη2]
  linarith only [hcross]
end SmoothedOctagon
