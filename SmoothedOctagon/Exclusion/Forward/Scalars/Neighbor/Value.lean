module

public import SmoothedOctagon.Exclusion.Forward.Scalars.Canon
public import Mathlib.Analysis.Convex.Deriv

/-!
# The value of the symmetric forward neighbour residual

The reciprocal logarithm remainder gives a rational majorant. Its positive
moment weights control the shape derivative; convexity on the remaining edge
reduces the sign to its two corners.
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

/-- Rational part of the symmetric neighbour row at its least factor. -/
noncomputable def fs_neighborR (a t : ℝ) : ℝ :=
  let b := 1 - a
  let p := 1 + a
  let l := 1 + t
  p ^ 3 * (1 + 2 * a - a ^ 2) / (2 * b ^ 2) * l ^ 3 -
    a * p * (13 + 4 * a - a ^ 2) / (2 * b ^ 2) * l ^ 2 -
    (a ^ 4 - 4 * a ^ 3 - 14 * a ^ 2 - 8 * a + 9) / (2 * b ^ 2) * l + 4 * p / b
/-- Coefficient of the least-factor logarithm. -/
noncomputable def fs_neighborCL (a t : ℝ) : ℝ :=
  -(1 + 2 * a + 6 * a ^ 2 - a ^ 4) / (1 - a) ^ 2 * (1 + t) ^ 2 +
    (a ^ 4 - a ^ 2 + 6 * a + 2) / (1 - a) ^ 2 * (1 + t) +
    (2 - a) * (1 + a) ^ 2 / (1 - a) + a * (1 + a) / t
/-- Coefficient of the centred-factor logarithm. -/
noncomputable def fs_neighborCM (a t : ℝ) : ℝ :=
  ((1 - a) + 2 * t) * (1 - a * (1 + t)) / (1 - a)
/-- Symmetric neighbour residual at the least factor. -/
noncomputable def fs_neighborValue (a t : ℝ) : ℝ :=
  fs_neighborR a t + fs_neighborCL a t * Real.log (1 + t) +
    fs_neighborCM a t * Real.log (1 - a * (1 + t))

private noncomputable def fsN_S (t : ℝ) : ℝ := t / 6 * (1 + 8 / (2 + t) + 1 / (1 + t))
private noncomputable def fsN_P (y : ℝ) : ℝ := -y - y ^ 2 / 2 - y ^ 3 / 3
private noncomputable def fsN_A (a : ℝ) : ℝ := 1 + 2 * a + 6 * a ^ 2 - a ^ 4
private noncomputable def fsN_B (a : ℝ) : ℝ := a ^ 4 - a ^ 2 + 6 * a + 2
private noncomputable def fsN_baseCL (a t : ℝ) : ℝ :=
  (-fsN_A a * (1 + t) ^ 2 + fsN_B a * (1 + t)) / (1 - a) ^ 2 +
    (2 - a) * (1 + a) ^ 2 / (1 - a)
-- The removable t=0 singularity is cancelled in this definition.
private noncomputable def fsN_majorant (a t : ℝ) : ℝ :=
  fs_neighborR a t + fsN_baseCL a t * fsN_S t +
    a * (1 + a) / 6 * (1 + 8 / (2 + t) + 1 / (1 + t)) +
    fs_neighborCM a t * fsN_P (a * (1 + t))

private theorem fsN_simpson_upper {t : ℝ} (ht : 0 ≤ t) : Real.log (1 + t) ≤ fsN_S t := by
  have h := ff_le_of_deriv (f := fun s => fsN_S s - Real.log (1 + s))
    (f' := fun s => s ^ 4 / (6 * (1 + s) ^ 2 * (2 + s) ^ 2)) ht (fun s hs => ?_) (fun s hs => ?_)
  · norm_num [fsN_S] at h
    unfold fsN_S
    simpa only [one_div] using h
  · have hs0 : 0 < 1 + s := by linarith [hs.1]
    have hs2 : 0 < 2 + s := by linarith [hs.1]
    unfold fsN_S
    apply HasDerivAt.congr_deriv
    · analytic_deriv
    · norm_num [npowRec]; field_simp; ring
  · positivity

private theorem fsN_value_le {a t : ℝ} (ha : 1 / 7 ≤ a) (ha1 : a ≤ 1 / 4)
    (ht : 0 < t) (ht1 : t ≤ 1 / 4) : fs_neighborValue a t ≤ fsN_majorant a t := by
  have ha0 : 0 ≤ a := by linarith
  have hb : 0 < 1 - a := by linarith
  have hl : 0 < 1 + t := by linarith
  have ha2 : a ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith only [ha0, ha1]
  have ha4 : a ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := by gcongr
  have hA : 0 ≤ fsN_A a := by unfold fsN_A; nlinarith only [ha0, ha4, sq_nonneg a]
  have hBA : 0 ≤ fsN_B a - 5 / 4 * fsN_A a := by
    unfold fsN_B fsN_A
    nlinarith only [ha0, ha2, sq_nonneg (a ^ 2)]
  have hBAl : 0 ≤ fsN_B a - fsN_A a * (1 + t) := by
    have hm := mul_le_mul_of_nonneg_left (show 1 + t ≤ 5 / 4 by linarith) hA
    nlinarith only [hBA, hm]
  have htwo : 0 ≤ 2 - a := by linarith
  have hbase : 0 ≤ fsN_baseCL a t := by
    have he : fsN_baseCL a t = (1 + t) * (fsN_B a - fsN_A a * (1 + t)) / (1 - a) ^ 2 +
        (2 - a) * (1 + a) ^ 2 / (1 - a) := by unfold fsN_baseCL; ring
    rw [he]
    positivity
  have hCL : 0 ≤ fs_neighborCL a t := by
    have he : fs_neighborCL a t = fsN_baseCL a t + a * (1 + a) / t := by
      unfold fs_neighborCL fsN_baseCL fsN_A fsN_B
      ring
    rw [he]
    positivity
  have hy0 : 0 ≤ a * (1 + t) := by positivity
  have hy1 : a * (1 + t) < 1 := by nlinarith only [ha0, ha1, ht.le, ht1]
  have hCM : 0 ≤ fs_neighborCM a t := by unfold fs_neighborCM; positivity
  have hlI := mul_le_mul_of_nonneg_left (fsN_simpson_upper ht.le) hCL
  have hlc := mul_le_mul_of_nonneg_left (fs_log_one_sub_le hy0 hy1) hCM
  have he : fsN_majorant a t = fs_neighborR a t + fs_neighborCL a t * fsN_S t +
      fs_neighborCM a t * fsN_P (a * (1 + t)) := by
    unfold fsN_majorant fs_neighborCL fsN_baseCL fsN_A fsN_B fsN_S
    field_simp
    ring
  rw [he]
  unfold fs_neighborValue fsN_P
  linarith only [hlI, hlc]

private noncomputable def fsN_Q (t : ℝ) : ℝ := (1 + t) ^ 3 * (2 * t ^ 2 + 2 * t + 1)
private noncomputable def fsN_N1 (t : ℝ) : ℝ :=
  t ^ 2 * (4 * (1 + t) ^ 4 + 10 * (1 + t) ^ 3 + 19 * (1 + t) ^ 2 + 12 * (1 + t) + 1)
private noncomputable def fsN_N2 (t : ℝ) : ℝ :=
  t * (1 + t) * (4 * (1 + t) ^ 4 + 6 * (1 + t) ^ 3 + 10 * (1 + t) ^ 2 + (1 + t) - 3)
private noncomputable def fsN_R2 (t : ℝ) : ℝ := 4 * t ^ 3 * (5 * t + 6) / (3 * (t + 2))
private noncomputable def fsN_R1 (t : ℝ) : ℝ :=
  t ^ 2 * (16 + 24 * t + 11 * t ^ 2 + t ^ 3 * (18 + 15 * t + 2 * t ^ 2)) / (3 * (1 + t) * (t + 2))

private noncomputable def fsN_shapeModel (t a : ℝ) : ℝ :=
  fsN_majorant 0 t - fsN_R2 t - fsN_R1 t +
    (1 + t) ^ 4 / 3 * a ^ 4 - fsN_Q t / 3 * a ^ 3 -
    fsN_N2 t / (6 * (t + 2)) * a ^ 2 - fsN_N1 t / (6 * (t + 2)) * a +
    fsN_R2 t / (1 - a) ^ 2 + fsN_R1 t / (1 - a)
private noncomputable def fsN_shapeDeriv (t a : ℝ) : ℝ :=
  4 / 3 * (1 + t) ^ 4 * a ^ 3 - fsN_Q t * a ^ 2 -
    fsN_N2 t * a / (3 * (t + 2)) - fsN_N1 t / (6 * (t + 2)) +
    2 * fsN_R2 t / (1 - a) ^ 3 + fsN_R1 t / (1 - a) ^ 2

private theorem fsN_shape_eq {a t : ℝ} (hb : 0 < 1 - a) (ht : 0 ≤ t) :
    fsN_majorant a t = fsN_shapeModel t a := by
  have hl : 0 < 1 + t := by linarith
  have h2 : 0 < t + 2 := by linarith
  unfold fsN_shapeModel fsN_majorant fs_neighborR fs_neighborCM fsN_baseCL fsN_S fsN_P
    fsN_A fsN_B fsN_Q fsN_N1 fsN_N2 fsN_R2 fsN_R1
  dsimp only
  norm_num
  field_simp
  ring

private theorem fsN_shape_deriv {a t : ℝ} (hb : 0 < 1 - a) :
    HasDerivAt (fsN_shapeModel t) (fsN_shapeDeriv t a) a := by
  unfold fsN_shapeModel fsN_shapeDeriv
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem fsN_reciprocal_weights {a : ℝ} (ha : 1 / 7 ≤ a) (ha1 : a ≤ 1 / 4) :
    2 / (a * (1 - a) ^ 3) ≤ 23 ∧ 1 / (a * (1 - a) ^ 2) ≤ 10 := by
  have ha0 : 0 < a := by linarith
  have hb : 0 < 1 - a := by linarith
  have h3 := ff_le_of_deriv (f := fun x : ℝ => x * (1 - x) ^ 3)
    (f' := fun x => (1 - x) ^ 2 * (1 - 4 * x)) ha (fun x hx => ?_) (fun x hx => ?_)
  · have h2 := ff_le_of_deriv (f := fun x : ℝ => x * (1 - x) ^ 2)
      (f' := fun x => (1 - x) * (1 - 3 * x)) ha (fun x hx => ?_) (fun x hx => ?_)
    · constructor
      · rw [div_le_iff₀ (by positivity)]
        norm_num at h3
        nlinarith only [h3]
      · rw [div_le_iff₀ (by positivity)]
        norm_num at h2
        nlinarith only [h2]
    · apply HasDerivAt.congr_deriv
      · analytic_deriv
      · norm_num [npowRec]; ring
    · exact mul_nonneg (by linarith [hx.2]) (by linarith [hx.2])
  · apply HasDerivAt.congr_deriv
    · analytic_deriv
    · norm_num [npowRec]; ring
  · exact mul_nonneg (sq_nonneg _) (by linarith [hx.2])

private theorem fsN_moment_bounds {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    (2 / 3 + 11 / 3 * t + 9 * t ^ 2 ≤ fsN_Q t - (1 + t) ^ 4 / 3) ∧
    (46 * t ^ 2 + 96 * t ^ 3 + 73 * t ^ 4 ≤ fsN_N1 t) ∧
    (18 * t + 73 * t ^ 2 + 107 * t ^ 3 + 74 * t ^ 4 ≤ fsN_N2 t) ∧
    (fsN_R2 t ≤ 13 * t ^ 3 / 3) ∧ (fsN_R1 t ≤ 11 * t ^ 2 / 4) := by
  have hl : 0 < 1 + t := by linarith
  have h2 : 0 < t + 2 := by linarith
  have hq : fsN_Q t - (1 + t) ^ 4 / 3 - (2 / 3 + 11 / 3 * t + 9 * t ^ 2) =
      t ^ 3 * (35 + 23 * t + 6 * t ^ 2) / 3 := by unfold fsN_Q; ring
  have hn1 : fsN_N1 t - (46 * t ^ 2 + 96 * t ^ 3 + 73 * t ^ 4) = t ^ 5 * (26 + 4 * t) := by
    unfold fsN_N1; ring
  have hn2 : fsN_N2 t - (18 * t + 73 * t ^ 2 + 107 * t ^ 3 + 74 * t ^ 4) = t ^ 5 * (26 + 4 * t) := by
    unfold fsN_N2; ring
  have hr2 : fsN_R2 t ≤ 13 * t ^ 3 / 3 := by
    unfold fsN_R2
    rw [div_le_iff₀ (by positivity)]
    have hm := mul_nonneg (show 0 ≤ 2 - 7 * t by linarith only [ht1]) (show 0 ≤ t ^ 3 by positivity)
    nlinarith only [hm]
  have hr1 : fsN_R1 t ≤ 11 * t ^ 2 / 4 := by
    have ht2 : t ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith only [ht, ht1]
    have hp : 18 + 15 * t + 2 * t ^ 2 ≤ 22 := by nlinarith only [ht1, ht2]
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ t ^ 3 by positivity)
    have ht3 : t ^ 3 ≤ t ^ 2 / 4 := by nlinarith only [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 / 4 - t by linarith)]
    have ht2' : t ^ 2 ≤ t / 4 := by nlinarith only [mul_nonneg ht (show 0 ≤ 1 / 4 - t by linarith)]
    have hb : 16 + 24 * t + 11 * t ^ 2 + t ^ 3 * (18 + 15 * t + 2 * t ^ 2) ≤
        33 / 4 * (1 + t) * (t + 2) := by nlinarith only [hm, ht3, ht2', ht1]
    unfold fsN_R1
    rw [div_le_iff₀ (by positivity)]
    have hm' := mul_le_mul_of_nonneg_left hb (sq_nonneg t)
    nlinarith only [hm']
  refine ⟨?_, ?_, ?_, hr2, hr1⟩
  · have h : 0 ≤ t ^ 3 * (35 + 23 * t + 6 * t ^ 2) / 3 := by positivity
    linarith only [hq, h]
  · have h : 0 ≤ t ^ 5 * (26 + 4 * t) := by positivity
    linarith only [hn1, h]
  · have h : 0 ≤ t ^ 5 * (26 + 4 * t) := by positivity
    linarith only [hn2, h]

private theorem fsN_shape_neg {a t : ℝ} (ha : 1 / 7 ≤ a) (ha1 : a ≤ 1 / 4)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : fsN_shapeDeriv t a < 0 := by
  have ha0 : 0 < a := by linarith
  have hb : 0 < 1 - a := by linarith
  have h2 : 0 < t + 2 := by linarith
  obtain ⟨hQ, hN1, hN2, hR2, hR1⟩ := fsN_moment_bounds ht ht1
  have hQ0 : 0 ≤ fsN_Q t - (1 + t) ^ 4 / 3 := by
    have h : 0 ≤ 11 / 3 * t + 9 * t ^ 2 := by positivity
    linarith only [hQ, h]
  have hN10 : 0 ≤ fsN_N1 t := by
    have h : 0 ≤ 46 * t ^ 2 + 96 * t ^ 3 + 73 * t ^ 4 := by positivity
    linarith only [hN1, h]
  have hN20 : 0 ≤ fsN_N2 t := by
    have h : 0 ≤ 18 * t + 73 * t ^ 2 + 107 * t ^ 3 + 74 * t ^ 4 := by positivity
    linarith only [hN2, h]
  have hR10 : 0 ≤ fsN_R1 t := by unfold fsN_R1; positivity
  have hR20 : 0 ≤ fsN_R2 t := by unfold fsN_R2; positivity
  obtain ⟨hrec3, hrec2⟩ := fsN_reciprocal_weights ha ha1
  have hr3 := mul_le_mul_of_nonneg_right hrec3 hR20
  have hr2 := mul_le_mul_of_nonneg_right hrec2 hR10
  have hfirst : 4 / 3 * (1 + t) ^ 4 * a ^ 2 - fsN_Q t * a ≤
      -(fsN_Q t - (1 + t) ^ 4 / 3) / 7 := by
    have hsq : 4 * a ^ 2 ≤ a := by nlinarith only [mul_nonneg ha0.le (show 0 ≤ 1 / 4 - a by linarith)]
    have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (1 + t) ^ 4 / 3 by positivity)
    have hm' := mul_le_mul_of_nonneg_left ha hQ0
    nlinarith only [hm, hm']
  have hN1frac : 2 * fsN_N1 t / (3 * (t + 2)) ≤ fsN_N1 t / (6 * (t + 2) * a) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hm := mul_nonneg (mul_nonneg hN10 (show 0 ≤ 1 - 4 * a by linarith)) h2.le
    nlinarith only [hm]
  have he : fsN_shapeDeriv t a / a =
      (4 / 3 * (1 + t) ^ 4 * a ^ 2 - fsN_Q t * a) - fsN_N2 t / (3 * (t + 2)) -
        fsN_N1 t / (6 * (t + 2) * a) + 2 / (a * (1 - a) ^ 3) * fsN_R2 t +
        1 / (a * (1 - a) ^ 2) * fsN_R1 t := by
    unfold fsN_shapeDeriv
    field_simp
  have hquot : fsN_shapeDeriv t a / a ≤
      -(fsN_Q t - (1 + t) ^ 4 / 3) / 7 -
        (fsN_N2 t + 2 * fsN_N1 t) / (3 * (t + 2)) + 23 * fsN_R2 t + 10 * fsN_R1 t := by
    rw [he]
    have hc : (fsN_N2 t + 2 * fsN_N1 t) / (3 * (t + 2)) =
        fsN_N2 t / (3 * (t + 2)) + 2 * fsN_N1 t / (3 * (t + 2)) := by ring
    rw [hc]
    linarith only [hfirst, hN1frac, hr3, hr2]
  have hrec : 4 / 27 ≤ 1 / (3 * (t + 2)) := by rw [le_div_iff₀ (by positivity)]; linarith only [ht1]
  have hsum0 : 0 ≤ 18 * t + 165 * t ^ 2 + 299 * t ^ 3 + 220 * t ^ 4 := by positivity
  have hsum : 18 * t + 165 * t ^ 2 + 299 * t ^ 3 + 220 * t ^ 4 ≤ fsN_N2 t + 2 * fsN_N1 t := by
    linarith only [hN1, hN2]
  have hneg := mul_le_mul hsum hrec (by norm_num : (0 : ℝ) ≤ 4 / 27)
    (show 0 ≤ fsN_N2 t + 2 * fsN_N1 t by positivity)
  have hneg' : 4 / 27 * (18 * t + 165 * t ^ 2 + 299 * t ^ 3 + 220 * t ^ 4) ≤
      (fsN_N2 t + 2 * fsN_N1 t) / (3 * (t + 2)) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hneg
  have hcoarse : fsN_shapeDeriv t a / a ≤
      -2 / 21 - 67 / 21 * t + 2 * t ^ 2 + 56 * t ^ 3 - 32 * t ^ 4 := by
    nlinarith only [hquot, hQ, hneg', hR2, hR1, sq_nonneg t, show 0 ≤ t ^ 3 by positivity, show 0 ≤ t ^ 4 by positivity]
  have habs : 2 * t ^ 2 + 56 * t ^ 3 - 32 * t ^ 4 ≤ 14 * t ^ 2 := by
    have h : 0 ≤ 4 * t ^ 2 * (1 - 4 * t) * (3 - 2 * t) := by
      exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    nlinarith only [h]
  have ht2 : t ^ 2 ≤ t / 4 := by nlinarith only [mul_nonneg ht (show 0 ≤ 1 / 4 - t by linarith)]
  have hnegq : fsN_shapeDeriv t a / a < 0 := by nlinarith only [hcoarse, habs, ht2, ht1]
  have h := (div_lt_iff₀ ha0).mp hnegq
  simpa only [zero_mul] using h

private theorem fsN_majorant_le_edge {a t : ℝ} (ha : 1 / 7 ≤ a) (ha1 : a ≤ 1 / 4)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : fsN_majorant a t ≤ fsN_majorant (1 / 7) t := by
  have hm := ff_le_of_deriv (f := fun x => -fsN_shapeModel t x) ha
    (fun x hx => (fsN_shape_deriv (by linarith [hx.2] : 0 < 1 - x)).neg)
    (fun x hx => by have h := fsN_shape_neg hx.1 (hx.2.trans ha1) ht ht1; linarith only [h])
  rw [← fsN_shape_eq (by norm_num : (0 : ℝ) < 1 - 1 / 7) ht,
    ← fsN_shape_eq (by linarith : 0 < 1 - a) ht] at hm
  linarith only [hm]


-- The high-degree coefficients and residues of the Simpson kernel.
private noncomputable def fsN_p5 : ℝ :=
  let a : ℝ := 1 / 7
  2 * a ^ 4 / (3 * (1 - a))
private noncomputable def fsN_p4 : ℝ :=
  let a : ℝ := 1 / 7
  a ^ 3 * (-a ^ 2 + 9 * a + 1) / (3 * (1 - a))
private noncomputable def fsN_p3 : ℝ :=
  let a : ℝ := 1 / 7
  5 / 6 + (a ^ 4 * (22 - 42 * a + 8 * a ^ 2) + 13 * a ^ 3 +
    19 * a ^ 2 + 23 * a - 3) / (6 * (1 - a) ^ 2)
private noncomputable def fsN_C2 : ℝ :=
  let a : ℝ := 1 / 7
  4 * (1 + a) * (-a ^ 3 + 2 * a ^ 2 + 13 * a + 2) / (3 * (1 - a) ^ 2)
private noncomputable def fsN_C1 : ℝ :=
  let a : ℝ := 1 / 7
  (-(1 + a) / (3 * (1 - a)))
private noncomputable def fsN_edgeHigh (t : ℝ) : ℝ := fsN_p5 * t ^ 5 + fsN_p4 * t ^ 4 + fsN_p3 * t ^ 3
private noncomputable def fsN_edgePoles (t : ℝ) : ℝ := fsN_C2 / (t + 2) + fsN_C1 / (t + 1)
private noncomputable def fsN_edgeLow (t : ℝ) : ℝ := fsN_majorant (1 / 7) t - fsN_edgeHigh t - fsN_edgePoles t
private noncomputable def fsN_edgeLinear : ℝ := fsN_edgeLow 1 - fsN_edgeLow 0
private noncomputable def fsN_edgeQuadratic : ℝ := (fsN_edgeLow 2 - 2 * fsN_edgeLow 1 + fsN_edgeLow 0) / 2
private noncomputable def fsN_edgeModel (t : ℝ) : ℝ :=
  fsN_edgeLow 0 + fsN_edgeLinear * t + fsN_edgeQuadratic * t * (t - 1) + fsN_edgeHigh t + fsN_edgePoles t
private noncomputable def fsN_edgeFirst (t : ℝ) : ℝ :=
  fsN_edgeLinear + fsN_edgeQuadratic * (2 * t - 1) +
    5 * fsN_p5 * t ^ 4 + 4 * fsN_p4 * t ^ 3 + 3 * fsN_p3 * t ^ 2 -
    fsN_C2 / (t + 2) ^ 2 - fsN_C1 / (t + 1) ^ 2
private noncomputable def fsN_edgeSecond (t : ℝ) : ℝ :=
  2 * fsN_edgeQuadratic + 20 * fsN_p5 * t ^ 3 + 12 * fsN_p4 * t ^ 2 + 6 * fsN_p3 * t +
    2 * fsN_C2 / (t + 2) ^ 3 + 2 * fsN_C1 / (t + 1) ^ 3
private noncomputable def fsN_edgeThird (t : ℝ) : ℝ :=
  60 * fsN_p5 * t ^ 2 + 24 * fsN_p4 * t + 6 * fsN_p3 -
    6 * fsN_C2 / (t + 2) ^ 4 - 6 * fsN_C1 / (t + 1) ^ 4

private theorem fsN_edge_eq {t : ℝ} (ht : 0 ≤ t) :
    fsN_majorant (1 / 7) t = fsN_edgeModel t := by
  have h1 : 0 < t + 1 := by linarith
  have h2 : 0 < t + 2 := by linarith
  unfold fsN_edgeModel fsN_edgeLinear fsN_edgeQuadratic fsN_edgeLow fsN_edgeHigh
    fsN_edgePoles fsN_p5 fsN_p4 fsN_p3 fsN_C2 fsN_C1 fsN_majorant
    fs_neighborR fs_neighborCM fsN_baseCL fsN_S fsN_P fsN_A fsN_B
  norm_num
  field_simp
  ring

private theorem fsN_edge_deriv {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt fsN_edgeModel (fsN_edgeFirst t) t := by
  have h1 : 0 < t + 1 := by linarith
  have h2 : 0 < t + 2 := by linarith
  unfold fsN_edgeModel fsN_edgeHigh fsN_edgePoles fsN_edgeFirst
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem fsN_edge_first_deriv {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt fsN_edgeFirst (fsN_edgeSecond t) t := by
  have h1 : 0 < t + 1 := by linarith
  have h2 : 0 < t + 2 := by linarith
  unfold fsN_edgeFirst fsN_edgeSecond
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem fsN_edge_second_deriv {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt fsN_edgeSecond (fsN_edgeThird t) t := by
  have h1 : 0 < t + 1 := by linarith
  have h2 : 0 < t + 2 := by linarith
  unfold fsN_edgeSecond fsN_edgeThird
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem fsN_edge_third_lower {t : ℝ} (ht : 0 ≤ t) :
    31 / 16 + 8 / (3 * (1 + t) ^ 4) < fsN_edgeThird t := by
  have h1 : 0 < 1 + t := by linarith
  have h2 : 0 < t + 2 := by linarith
  have hp5 : 0 < fsN_p5 := by norm_num [fsN_p5]
  have hp4 : 0 < fsN_p4 := by norm_num [fsN_p4]
  have hp3 : 5 / 6 < fsN_p3 := by norm_num [fsN_p3]
  have hc2 : 6 * fsN_C2 < 49 := by norm_num [fsN_C2]
  have hc1 : -6 * fsN_C1 = 8 / 3 := by norm_num [fsN_C1]
  have hpow : (2 : ℝ) ^ 4 ≤ (t + 2) ^ 4 := by gcongr; linarith
  have hfrac : 6 * fsN_C2 / (t + 2) ^ 4 < 49 / 16 := by
    apply lt_of_lt_of_le (div_lt_div_of_pos_right hc2 (by positivity))
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 49) (by norm_num : (0 : ℝ) < 2 ^ 4) hpow
    norm_num at h
    exact h
  have ht5 : 0 ≤ 60 * fsN_p5 * t ^ 2 := by positivity
  have ht4 : 0 ≤ 24 * fsN_p4 * t := by positivity
  have hrec : 6 * fsN_C1 / (t + 1) ^ 4 = -(8 / (3 * (1 + t) ^ 4)) := by
    have hc : 6 * fsN_C1 = -(8 / 3) := by linarith only [hc1]
    rw [hc]
    field_simp
    ring
  unfold fsN_edgeThird
  linarith only [hfrac, hp3, ht5, ht4, hrec]

private noncomputable def fsN_curvatureGrowth : ℝ := 31 / 16 + 8 / 3 * (8 / 9) ^ 4

private theorem fsN_edge_second_eighth : 0 < fsN_edgeSecond (1 / 8) := by
  have hinit : -4 / 9 < fsN_edgeSecond 0 := by
    norm_num [fsN_edgeSecond, fsN_edgeQuadratic, fsN_edgeLow, fsN_majorant,
      fs_neighborR, fs_neighborCM, fsN_baseCL, fsN_S, fsN_P, fsN_A, fsN_B,
      fsN_edgeHigh, fsN_edgePoles, fsN_p5, fsN_p4, fsN_p3, fsN_C2, fsN_C1]
  have hm := ff_le_of_deriv (f := fun t => fsN_edgeSecond t - fsN_curvatureGrowth * t)
    (f' := fun t => fsN_edgeThird t - fsN_curvatureGrowth)
    (show (0 : ℝ) ≤ 1 / 8 by norm_num) (fun t ht => ?_) (fun t ht => ?_)
  · have hpos : 0 < -4 / 9 + fsN_curvatureGrowth / 8 := by norm_num [fsN_curvatureGrowth]
    norm_num only [mul_zero, sub_zero] at hm
    linarith only [hinit, hm, hpos]
  · apply HasDerivAt.congr_deriv
    · apply HasDerivAt.sub
      · exact fsN_edge_second_deriv ht.1
      · analytic_deriv
    · ring
  · have h1 : 0 < 1 + t := by linarith [ht.1]
    have hp : (1 + t) ^ 4 ≤ (9 / 8 : ℝ) ^ 4 := by gcongr; linarith [ht.1, ht.2]
    have hrec : 8 / (3 * (9 / 8 : ℝ) ^ 4) ≤ 8 / (3 * (1 + t) ^ 4) := by
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by gcongr)
    have h := fsN_edge_third_lower ht.1
    unfold fsN_curvatureGrowth
    norm_num at hrec
    linarith only [h, hrec]

private theorem fsN_edge_second_pos {t : ℝ} (ht : 1 / 8 ≤ t) : 0 < fsN_edgeSecond t := by
  have hm := ff_le_of_deriv (f := fsN_edgeSecond) ht
    (fun s hs => fsN_edge_second_deriv (by linarith [hs.1]))
    (fun s hs => by
      have h := fsN_edge_third_lower (by linarith [hs.1] : 0 ≤ s)
      have hr : 0 ≤ 8 / (3 * (1 + s) ^ 4) := by positivity
      linarith only [h, hr])
  exact lt_of_lt_of_le fsN_edge_second_eighth hm

private theorem fsN_edge_convex : ConvexOn ℝ (Icc (1 / 8 : ℝ) (1 / 4)) fsN_edgeModel := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun t ht => (fsN_edge_deriv (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => (fsN_edge_deriv (by linarith [(interior_subset ht).1])).hasDerivWithinAt)
    (fun t ht => (fsN_edge_first_deriv (by linarith [(interior_subset ht).1])).hasDerivWithinAt)
    (fun t ht => (fsN_edge_second_pos (interior_subset ht).1).le)

private theorem fsN_edge_neg {t : ℝ} (ht : 1 / 8 ≤ t) (ht1 : t ≤ 1 / 4) : fsN_edgeModel t < 0 := by
  have hleft : fsN_edgeModel (1 / 8) < 0 := by
    rw [← fsN_edge_eq (by norm_num)]
    norm_num [fsN_majorant, fs_neighborR, fs_neighborCM, fsN_baseCL, fsN_S, fsN_P, fsN_A, fsN_B]
  have hright : fsN_edgeModel (1 / 4) < 0 := by
    rw [← fsN_edge_eq (by norm_num)]
    norm_num [fsN_majorant, fs_neighborR, fs_neighborCM, fsN_baseCL, fsN_S, fsN_P, fsN_A, fsN_B]
  have hθ : 0 ≤ 8 * t - 1 := by linarith
  have hθ1 : 0 ≤ 1 - (8 * t - 1) := by linarith
  have hc := fsN_edge_convex.2 (by norm_num : (1 / 8 : ℝ) ∈ Icc (1 / 8) (1 / 4))
    (by norm_num : (1 / 4 : ℝ) ∈ Icc (1 / 8) (1 / 4)) hθ1 hθ (by ring)
  simp only [smul_eq_mul] at hc
  rw [show (1 - (8 * t - 1)) * (1 / 8) + (8 * t - 1) * (1 / 4) = t by ring] at hc
  by_cases he : t = 1 / 8
  · rwa [he]
  · have hθpos : 0 < 8 * t - 1 := by rcases lt_or_eq_of_le ht with h | h; linarith; exact (he h.symm).elim
    have hl := mul_nonpos_of_nonneg_of_nonpos hθ1 hleft.le
    have hr := mul_neg_of_pos_of_neg hθpos hright
    linarith only [hc, hl, hr]

/-- The symmetric neighbour value is negative on the rectangle containing its physical face. -/
theorem fs_neighborValue_neg {a t : ℝ} (ha : 1 / 7 ≤ a) (ha1 : a ≤ 1 / 4)
    (ht : 1 / 8 ≤ t) (ht1 : t ≤ 1 / 4) : fs_neighborValue a t < 0 := by
  have ht0 : 0 < t := by linarith
  have hle := fsN_value_le ha ha1 ht0 ht1
  have hm := fsN_majorant_le_edge ha ha1 ht0.le ht1
  rw [fsN_edge_eq ht0.le] at hm
  exact lt_of_le_of_lt (hle.trans hm) (fsN_edge_neg ht ht1)

end SmoothedOctagon
