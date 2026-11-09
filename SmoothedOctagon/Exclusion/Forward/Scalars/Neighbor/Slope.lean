module

public import SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Value
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Convex.Jensen

/-!
# The partial slope of the symmetric forward neighbour residual

Reciprocal moments give a maximum principle for the shape derivative.
The remaining edge is convex after its two reciprocal poles are separated.
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


/-- Rational part of the partial factor slope, before moving the least factor. -/
noncomputable def fs_neighborSlopeR (a t : ℝ) : ℝ :=
  let b := 1 - a
  let p := 1 + a
  let l := 1 + t
  p * (-a ^ 4 + 5 * a ^ 2 + 6 * a + 2) / (2 * b ^ 2) * l ^ 2 -
    (-a ^ 4 + 9 * a ^ 2 + 10 * a + 2) / b ^ 2 * l -
    (a ^ 3 - 5 * a ^ 2 - 13 * a + 1) / (2 * b ^ 2) + p / (2 * l)
noncomputable def fs_neighborSlopeCL (a t : ℝ) : ℝ :=
  -(1 + 2 * a + 6 * a ^ 2 - a ^ 4) / (1 - a) ^ 2 * t +
    (2 * a ^ 4 - 2 * a ^ 3 - 9 * a ^ 2 + 4 * a + 1) / (1 - a) ^ 2 +
    (1 + a) * (1 + 2 * a - a ^ 2) / ((1 - a) * t)
/-- Partial derivative in the original exterior factor, at its least value. -/
noncomputable def fs_neighborSlope (a t : ℝ) : ℝ :=
  fs_neighborSlopeR a t + fs_neighborSlopeCL a t * Real.log (1 + t) +
    2 * (1 - a * (1 + t)) / (1 - a) * Real.log (1 - a * (1 + t))

private noncomputable def fsNd_S (t : ℝ) : ℝ := t / 6 * (1 + 8 / (2 + t) + 1 / (1 + t))
private noncomputable def fsNd_P (y : ℝ) : ℝ := -y - y ^ 2 / 2 - y ^ 3 / 3
private noncomputable def fsNd_A (a : ℝ) : ℝ := 1 + 2 * a + 6 * a ^ 2 - a ^ 4
private noncomputable def fsNd_PD (a : ℝ) : ℝ := 2 * a ^ 4 - 2 * a ^ 3 - 9 * a ^ 2 + 4 * a + 1
private noncomputable def fsNd_KD (a : ℝ) : ℝ := (1 + a) * (1 + 2 * a - a ^ 2) / (1 - a)
-- Cancel the removable singularity before using the extension at t=0.
private noncomputable def fsNd_majorant (a t : ℝ) : ℝ :=
  fs_neighborSlopeR a t + (-fsNd_A a * t + fsNd_PD a) / (1 - a) ^ 2 * fsNd_S t +
    fsNd_KD a / 6 * (1 + 8 / (2 + t) + 1 / (1 + t)) +
    2 * (1 - a * (1 + t)) / (1 - a) * fsNd_P (a * (1 + t))

private theorem fsNd_simpson_upper {t : ℝ} (ht : 0 ≤ t) : Real.log (1 + t) ≤ fsNd_S t := by
  have h := ff_le_of_deriv (f := fun s => fsNd_S s - Real.log (1 + s))
    (f' := fun s => s ^ 4 / (6 * (1 + s) ^ 2 * (2 + s) ^ 2)) ht (fun s hs => ?_) (fun s hs => ?_)
  · norm_num [fsNd_S] at h
    unfold fsNd_S
    simpa only [one_div] using h
  · have hs0 : 0 < 1 + s := by linarith [hs.1]
    have hs2 : 0 < 2 + s := by linarith [hs.1]
    unfold fsNd_S
    apply HasDerivAt.congr_deriv
    · analytic_deriv
    · norm_num [npowRec]; field_simp; ring
  · positivity

private theorem fsNd_slope_le {a t : ℝ} (ha : 1 / 7 ≤ a) (ha1 : a ≤ 1 / 4)
    (ht : 0 < t) (ht1 : t ≤ 1 / 4) : fs_neighborSlope a t ≤ fsNd_majorant a t := by
  have ha0 : 0 ≤ a := by linarith
  have hb : 0 < 1 - a := by linarith
  have ha2 : a ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith only [ha0, ha1]
  have ha3 : a ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := by gcongr
  have ha4 : a ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := by gcongr
  have hA : 0 ≤ fsNd_A a := by unfold fsNd_A; nlinarith only [ha0, ha4, sq_nonneg a]
  have hPD : 0 ≤ fsNd_PD a - fsNd_A a / 4 := by
    unfold fsNd_PD fsNd_A
    nlinarith only [ha0, ha2, ha3, sq_nonneg (a ^ 2)]
  have hbase : 0 ≤ -fsNd_A a * t + fsNd_PD a := by
    have hm := mul_le_mul_of_nonneg_left ht1 hA
    linarith only [hPD, hm]
  have hKD : 0 ≤ fsNd_KD a := by
    have hk : 0 ≤ 1 + 2 * a - a ^ 2 := by nlinarith only [ha0, ha2]
    unfold fsNd_KD
    positivity
  have hCL : 0 ≤ fs_neighborSlopeCL a t := by
    have he : fs_neighborSlopeCL a t = (-fsNd_A a * t + fsNd_PD a) / (1 - a) ^ 2 + fsNd_KD a / t := by
      unfold fs_neighborSlopeCL fsNd_A fsNd_PD fsNd_KD
      field_simp
    rw [he]
    positivity
  have hy0 : 0 ≤ a * (1 + t) := by positivity
  have hy1 : a * (1 + t) < 1 := by nlinarith only [ha0, ha1, ht.le, ht1]
  have hCM : 0 ≤ 2 * (1 - a * (1 + t)) / (1 - a) := by positivity
  have hL := mul_le_mul_of_nonneg_left (fsNd_simpson_upper ht.le) hCL
  have hM := mul_le_mul_of_nonneg_left (fs_log_one_sub_le hy0 hy1) hCM
  have he : fsNd_majorant a t = fs_neighborSlopeR a t + fs_neighborSlopeCL a t * fsNd_S t +
      2 * (1 - a * (1 + t)) / (1 - a) * fsNd_P (a * (1 + t)) := by
    unfold fsNd_majorant fs_neighborSlopeCL fsNd_S fsNd_A fsNd_PD fsNd_KD
    field_simp
    ring
  rw [he]
  unfold fs_neighborSlope fsNd_P
  linarith only [hL, hM]

private noncomputable def fsNd_P3 (t : ℝ) : ℝ := (1 + t) ^ 2 * (4 * (1 + t) ^ 2 + 3) / 6
private noncomputable def fsNd_P2 (t : ℝ) : ℝ :=
  (1 + t) * (4 * (1 + t) ^ 4 + 6 * (1 + t) ^ 3 + 10 * (1 + t) ^ 2 - 7 * (1 + t) - 7) / (6 * (t + 2))
private noncomputable def fsNd_P1 (t : ℝ) : ℝ :=
  t * (4 * (1 + t) ^ 5 + 10 * (1 + t) ^ 4 + 16 * (1 + t) ^ 3 - 8 * (1 + t) ^ 2 + (1 + t) + 3) /
    (6 * (1 + t) * (t + 2))
private noncomputable def fsNd_R2 (t : ℝ) : ℝ :=
  2 * t ^ 2 * (16 * t ^ 2 + 35 * t + 18) / (3 * (1 + t) * (t + 2))
private noncomputable def fsNd_R1 (t : ℝ) : ℝ :=
  t * (10 - 25 * t - 49 * t ^ 2 + 15 * t ^ 4 + 2 * t ^ 5) / (3 * (1 + t) * (t + 2))
private noncomputable def fsNd_shapeModel (t a : ℝ) : ℝ :=
  fsNd_majorant 0 t - fsNd_R2 t - fsNd_R1 t - fsNd_P3 t * a ^ 3 - fsNd_P2 t * a ^ 2 -
    fsNd_P1 t * a + fsNd_R2 t / (1 - a) ^ 2 + fsNd_R1 t / (1 - a)
private noncomputable def fsNd_shapeFirst (t a : ℝ) : ℝ :=
  -3 * fsNd_P3 t * a ^ 2 - 2 * fsNd_P2 t * a - fsNd_P1 t +
    2 * fsNd_R2 t / (1 - a) ^ 3 + fsNd_R1 t / (1 - a) ^ 2
private noncomputable def fsNd_shapeSecond (t a : ℝ) : ℝ :=
  -6 * fsNd_P3 t * a - 2 * fsNd_P2 t + 6 * fsNd_R2 t / (1 - a) ^ 4 + 2 * fsNd_R1 t / (1 - a) ^ 3
private noncomputable def fsNd_shapeThird (t a : ℝ) : ℝ :=
  -6 * fsNd_P3 t + 24 * fsNd_R2 t / (1 - a) ^ 5 + 6 * fsNd_R1 t / (1 - a) ^ 4
private noncomputable def fsNd_shapeFourth (t a : ℝ) : ℝ :=
  120 * fsNd_R2 t / (1 - a) ^ 6 + 24 * fsNd_R1 t / (1 - a) ^ 5

private theorem fsNd_shape_eq {a t : ℝ} (hb : 0 < 1 - a) (ht : 0 ≤ t) :
    fsNd_majorant a t = fsNd_shapeModel t a := by
  have hl : 0 < 1 + t := by linarith
  have h2 : 0 < t + 2 := by linarith
  unfold fsNd_shapeModel fsNd_majorant fs_neighborSlopeR fsNd_S fsNd_P fsNd_A fsNd_PD fsNd_KD
    fsNd_P3 fsNd_P2 fsNd_P1 fsNd_R2 fsNd_R1
  dsimp only
  norm_num
  field_simp
  ring

private theorem fsNd_shape_deriv {a t : ℝ} (hb : 0 < 1 - a) :
    HasDerivAt (fsNd_shapeModel t) (fsNd_shapeFirst t a) a := by
  unfold fsNd_shapeModel fsNd_shapeFirst
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring
private theorem fsNd_shape_first_deriv {a t : ℝ} (hb : 0 < 1 - a) :
    HasDerivAt (fsNd_shapeFirst t) (fsNd_shapeSecond t a) a := by
  unfold fsNd_shapeFirst fsNd_shapeSecond
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring
private theorem fsNd_shape_second_deriv {a t : ℝ} (hb : 0 < 1 - a) :
    HasDerivAt (fsNd_shapeSecond t) (fsNd_shapeThird t a) a := by
  unfold fsNd_shapeSecond fsNd_shapeThird
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring
private theorem fsNd_shape_third_deriv {a t : ℝ} (hb : 0 < 1 - a) :
    HasDerivAt (fsNd_shapeThird t) (fsNd_shapeFourth t a) a := by
  unfold fsNd_shapeThird fsNd_shapeFourth
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private noncomputable def fsNd_L3 (t : ℝ) : ℝ := 7 / 6 + 11 / 3 * t + 9 / 2 * t ^ 2
private noncomputable def fsNd_L2 (t : ℝ) : ℝ := 2 / 27 * (6 + 53 * t + 99 * t ^ 2)
private noncomputable def fsNd_L1 (t : ℝ) : ℝ := 8 / 135 * (26 * t + 93 * t ^ 2)
private noncomputable def fsNd_U2 (t : ℝ) : ℝ := 20 / 3 * t ^ 2
private noncomputable def fsNd_U1 (t : ℝ) : ℝ := 5 / 3 * t - 6 * t ^ 2

private theorem fsNd_moment_bounds {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    fsNd_L3 t ≤ fsNd_P3 t ∧ fsNd_L2 t ≤ fsNd_P2 t ∧ fsNd_L1 t ≤ fsNd_P1 t ∧
    fsNd_R2 t ≤ fsNd_U2 t ∧ fsNd_R1 t ≤ fsNd_U1 t := by
  have hl : 0 < 1 + t := by linarith
  have h2 : 0 < t + 2 := by linarith
  have ht2 : t ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith only [ht, ht1]
  have ht3 : t ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := by gcongr
  have ht4 : t ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := by gcongr
  have h3 : fsNd_P3 t - fsNd_L3 t = 8 / 3 * t ^ 3 + 2 / 3 * t ^ 4 := by unfold fsNd_P3 fsNd_L3; ring
  have hn2 : (1 + t) * (4 * (1 + t) ^ 4 + 6 * (1 + t) ^ 3 + 10 * (1 + t) ^ 2 - 7 * (1 + t) - 7) =
      6 + 53 * t + 99 * t ^ 2 + t ^ 3 * (74 + 26 * t + 4 * t ^ 2) := by ring
  have hn1 : t * (4 * (1 + t) ^ 5 + 10 * (1 + t) ^ 4 + 16 * (1 + t) ^ 3 - 8 * (1 + t) ^ 2 + (1 + t) + 3) =
      26 * t + 93 * t ^ 2 + t ^ 3 * (140 + 96 * t + 30 * t ^ 2 + 4 * t ^ 3) := by ring
  have hL2 : fsNd_L2 t ≤ fsNd_P2 t := by
    unfold fsNd_P2 fsNd_L2
    rw [le_div_iff₀ (by positivity), hn2]
    have hm := mul_nonneg (show 0 ≤ 1 / 4 - t by linarith) (show 0 ≤ 6 + 53 * t + 99 * t ^ 2 by positivity)
    have hr : 0 ≤ t ^ 3 * (74 + 26 * t + 4 * t ^ 2) := by positivity
    nlinarith only [hm, hr]
  have hL1 : fsNd_L1 t ≤ fsNd_P1 t := by
    unfold fsNd_P1 fsNd_L1
    rw [le_div_iff₀ (by positivity), hn1]
    have hd : (1 + t) * (t + 2) ≤ 45 / 16 := by nlinarith only [ht1, ht2]
    have hm := mul_le_mul_of_nonneg_right hd (show 0 ≤ 26 * t + 93 * t ^ 2 by positivity)
    have hr : 0 ≤ t ^ 3 * (140 + 96 * t + 30 * t ^ 2 + 4 * t ^ 3) := by positivity
    nlinarith only [hm, hr]
  have hU2 : fsNd_R2 t ≤ fsNd_U2 t := by
    unfold fsNd_R2 fsNd_U2
    rw [div_le_iff₀ (by positivity)]
    have hm := mul_nonneg (sq_nonneg t) (show 0 ≤ 4 - 10 * t - 12 * t ^ 2 by nlinarith only [ht1, ht2])
    nlinarith only [hm]
  have hU1 : fsNd_R1 t ≤ fsNd_U1 t := by
    unfold fsNd_R1 fsNd_U1
    rw [div_le_iff₀ (by positivity)]
    have hm := mul_nonneg (sq_nonneg t) (show 0 ≤ 4 - 18 * t ^ 2 - 15 * t ^ 3 - 2 * t ^ 4 by nlinarith only [ht2, ht3, ht4])
    nlinarith only [hm]
  refine ⟨?_, hL2, hL1, hU2, hU1⟩
  have hp : 0 ≤ 8 / 3 * t ^ 3 + 2 / 3 * t ^ 4 := by positivity
  linarith only [h3, hp]

private theorem fsNd_residues_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    0 ≤ fsNd_R2 t ∧ 0 ≤ fsNd_R1 t := by
  have ht2 : t ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith only [ht, ht1]
  have h : 0 ≤ 10 - 25 * t - 49 * t ^ 2 := by nlinarith only [ht1, ht2]
  unfold fsNd_R2 fsNd_R1
  constructor <;> positivity


private noncomputable def fsNd_boundFirst (a t : ℝ) : ℝ :=
  -3 * a ^ 2 * fsNd_L3 t - 2 * a * fsNd_L2 t - fsNd_L1 t +
    2 * fsNd_U2 t / (1 - a) ^ 3 + fsNd_U1 t / (1 - a) ^ 2
private noncomputable def fsNd_boundFirstC (a : ℝ) : ℝ :=
  -3 * a ^ 2 * (9 / 2) - 2 * a * (2 / 27 * 99) - 8 / 135 * 93 +
    2 * (20 / 3) / (1 - a) ^ 3 - 6 / (1 - a) ^ 2
private noncomputable def fsNd_boundSecond (t : ℝ) : ℝ :=
  -6 / 7 * fsNd_L3 t - 2 * fsNd_L2 t + 6 * (7 / 6) ^ 4 * fsNd_U2 t + 2 * (7 / 6) ^ 3 * fsNd_U1 t
private noncomputable def fsNd_boundSecondC : ℝ :=
  -6 / 7 * (9 / 2) - 2 * (2 / 27 * 99) + 6 * (7 / 6) ^ 4 * (20 / 3) - 2 * (7 / 6) ^ 3 * 6

-- Convexity of a quadratic, written as its chord minus a positive remainder.
private theorem fsNd_quadratic_neg {q : ℝ → ℝ} {c t : ℝ}
    (hc : 0 ≤ c) (h0 : q 0 < 0) (h1 : q (1 / 4) < 0)
    (he : q t = (1 - 4 * t) * q 0 + 4 * t * q (1 / 4) - c * t * (1 / 4 - t))
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : q t < 0 := by
  have hr : 0 ≤ c * t * (1 / 4 - t) := by positivity
  by_cases ht0 : t = 0
  · simpa only [ht0] using h0
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hleft := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1 - 4 * t by linarith) h0.le
    have hright := mul_neg_of_pos_of_neg (show 0 < 4 * t by positivity) h1
    linarith only [he, hr, hleft, hright]

private theorem fsNd_boundFirst_neg {a t : ℝ} (ha : a = 1 / 7 ∨ a = 1 / 4)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : fsNd_boundFirst a t < 0 := by
  have he : fsNd_boundFirst a t =
      (1 - 4 * t) * fsNd_boundFirst a 0 + 4 * t * fsNd_boundFirst a (1 / 4) -
        fsNd_boundFirstC a * t * (1 / 4 - t) := by
    unfold fsNd_boundFirst fsNd_boundFirstC fsNd_L3 fsNd_L2 fsNd_L1 fsNd_U2 fsNd_U1
    ring
  refine fsNd_quadratic_neg ?_ ?_ ?_ he ht ht1
  all_goals rcases ha with rfl | rfl <;>
    norm_num [fsNd_boundFirstC, fsNd_boundFirst, fsNd_L3, fsNd_L2, fsNd_L1, fsNd_U2, fsNd_U1]

private theorem fsNd_boundSecond_neg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : fsNd_boundSecond t < 0 := by
  refine fsNd_quadratic_neg (q := fsNd_boundSecond) (c := fsNd_boundSecondC) ?_ ?_ ?_ ?_ ht ht1
  · norm_num [fsNd_boundSecondC]
  · norm_num [fsNd_boundSecond, fsNd_L3, fsNd_L2, fsNd_U2, fsNd_U1]
  · norm_num [fsNd_boundSecond, fsNd_L3, fsNd_L2, fsNd_U2, fsNd_U1]
  · unfold fsNd_boundSecond fsNd_boundSecondC fsNd_L3 fsNd_L2 fsNd_U2 fsNd_U1
    ring

private theorem fsNd_first_le {a t : ℝ} (ha : 0 ≤ a) (hb : 0 < 1 - a)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : fsNd_shapeFirst t a ≤ fsNd_boundFirst a t := by
  obtain ⟨h3, h2, h1, hR2, hR1⟩ := fsNd_moment_bounds ht ht1
  have h3' := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 3 * a ^ 2 by positivity)
  have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * a by positivity)
  have hR2' : 2 * fsNd_R2 t / (1 - a) ^ 3 ≤ 2 * fsNd_U2 t / (1 - a) ^ 3 := by gcongr
  have hR1' : fsNd_R1 t / (1 - a) ^ 2 ≤ fsNd_U1 t / (1 - a) ^ 2 := by gcongr
  unfold fsNd_shapeFirst fsNd_boundFirst
  nlinarith only [h3', h2', h1, hR2', hR1']

private theorem fsNd_second_left_neg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    fsNd_shapeSecond t (1 / 7) < 0 := by
  obtain ⟨h3, h2, h1, hR2, hR1⟩ := fsNd_moment_bounds ht ht1
  have h := fsNd_boundSecond_neg ht ht1
  norm_num [fsNd_shapeSecond, fsNd_boundSecond] at h ⊢
  linarith only [h3, h2, hR2, hR1, h]

private theorem fsNd_second_convex {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) :
    ConvexOn ℝ (Icc (1 / 7 : ℝ) (1 / 4)) (fsNd_shapeSecond t) := by
  have hball : ∀ a ∈ Icc (1 / 7 : ℝ) (1 / 4), 0 < 1 - a := fun a ha => by linarith [ha.2]
  obtain ⟨hR2, hR1⟩ := fsNd_residues_nonneg ht ht1
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun a ha => (fsNd_shape_second_deriv (hball a ha)).continuousAt.continuousWithinAt)
    (fun a ha => (fsNd_shape_second_deriv (hball a (interior_subset ha))).hasDerivWithinAt)
    (fun a ha => (fsNd_shape_third_deriv (hball a (interior_subset ha))).hasDerivWithinAt)
    (fun a ha => by
      have hb := hball a (interior_subset ha)
      unfold fsNd_shapeFourth
      positivity)

private theorem fsNd_shape_first_neg {a t : ℝ} (ha : 1 / 7 ≤ a) (ha1 : a ≤ 1 / 4)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : fsNd_shapeFirst t a < 0 := by
  have hleft : fsNd_shapeFirst t (1 / 7) < 0 := lt_of_le_of_lt
    (fsNd_first_le (by norm_num) (by norm_num) ht ht1)
    (fsNd_boundFirst_neg (Or.inl rfl) ht ht1)
  have hright : fsNd_shapeFirst t (1 / 4) < 0 := lt_of_le_of_lt
    (fsNd_first_le (by norm_num) (by norm_num) ht ht1)
    (fsNd_boundFirst_neg (Or.inr rfl) ht ht1)
  have hinit := fsNd_second_left_neg ht ht1
  have hc := fsNd_second_convex ht ht1
  by_cases hga : fsNd_shapeSecond t a ≤ 0
  · have hm := ff_le_of_deriv (f := fun x => -fsNd_shapeFirst t x) ha
      (fun x hx => (fsNd_shape_first_deriv (by linarith [hx.2])).neg)
      (fun x hx => by
        have h := hc.le_max_of_mem_Icc (by norm_num) ⟨ha, ha1⟩ hx
        have hmax := max_le hinit.le hga
        linarith only [h, hmax])
    linarith only [hm, hleft]
  · have hga' : 0 < fsNd_shapeSecond t a := lt_of_not_ge hga
    have ha' : 1 / 7 < a := by
      rcases lt_or_eq_of_le ha with h | h
      · exact h
      · subst a; exact (not_lt_of_ge hinit.le hga').elim
    have hm := ff_le_of_deriv (f := fsNd_shapeFirst t) ha1
      (fun x hx => fsNd_shape_first_deriv (by linarith [hx.2]))
      (fun x hx => by
        rcases eq_or_lt_of_le hx.1 with he | he
        · simpa only [← he] using hga'.le
        · have hsec := hc.slope_mono_adjacent (by norm_num) ⟨ha.trans hx.1, hx.2⟩ ha' he
          have hsec0 : 0 < (fsNd_shapeSecond t a - fsNd_shapeSecond t (1 / 7)) / (a - 1 / 7) := by
            exact div_pos (by linarith only [hinit, hga']) (by linarith only [ha'])
          have hdiff := (le_div_iff₀ (sub_pos.mpr he)).mp (hsec0.le.trans hsec)
          linarith only [hdiff, hga'])
    exact lt_of_le_of_lt hm hright

private theorem fsNd_majorant_le_edge {a t : ℝ} (ha : 1 / 7 ≤ a) (ha1 : a ≤ 1 / 4)
    (ht : 0 ≤ t) (ht1 : t ≤ 1 / 4) : fsNd_majorant a t ≤ fsNd_majorant (1 / 7) t := by
  have hm := ff_le_of_deriv (f := fun x => -fsNd_shapeModel t x) ha
    (fun x hx => (fsNd_shape_deriv (by linarith [hx.2] : 0 < 1 - x)).neg)
    (fun x hx => by have h := fsNd_shape_first_neg hx.1 (hx.2.trans ha1) ht ht1; linarith only [h])
  rw [← fsNd_shape_eq (by norm_num : (0 : ℝ) < 1 - 1 / 7) ht,
    ← fsNd_shape_eq (by linarith : 0 < 1 - a) ht] at hm
  linarith only [hm]


-- The edge poles come directly from the Simpson kernel in the original row.
private noncomputable def fsNd_Ae : ℝ :=
  let a : ℝ := 1 / 7
  8 / 3 * ((2 * fsNd_A a + fsNd_PD a) / (1 - a) ^ 2 - fsNd_KD a / 2)
private noncomputable def fsNd_Be : ℝ :=
  let a : ℝ := 1 / 7
  1 + a - (fsNd_A a + fsNd_PD a) / (3 * (1 - a) ^ 2) + fsNd_KD a / 3
private noncomputable def fsNd_edgeHigh (t : ℝ) : ℝ := t ^ 4 / (9 * 7 ^ 3) + 5 * t ^ 3 / (6 * 7 ^ 3)
private noncomputable def fsNd_edgePoles (t : ℝ) : ℝ := -fsNd_Ae / (t + 2) + fsNd_Be / (2 * (t + 1))
private noncomputable def fsNd_edgeLow (t : ℝ) : ℝ := fsNd_majorant (1 / 7) t - fsNd_edgeHigh t - fsNd_edgePoles t
private noncomputable def fsNd_edgeLinear : ℝ := fsNd_edgeLow 1 - fsNd_edgeLow 0
private noncomputable def fsNd_edgeQuadratic : ℝ := (fsNd_edgeLow 2 - 2 * fsNd_edgeLow 1 + fsNd_edgeLow 0) / 2
private noncomputable def fsNd_edgeModel (t : ℝ) : ℝ :=
  fsNd_edgeLow 0 + fsNd_edgeLinear * t + fsNd_edgeQuadratic * t * (t - 1) + fsNd_edgeHigh t + fsNd_edgePoles t
private noncomputable def fsNd_edgeFirst (t : ℝ) : ℝ :=
  fsNd_edgeLinear + fsNd_edgeQuadratic * (2 * t - 1) +
    4 * t ^ 3 / (9 * 7 ^ 3) + 5 * t ^ 2 / (2 * 7 ^ 3) +
    fsNd_Ae / (t + 2) ^ 2 - fsNd_Be / (2 * (t + 1) ^ 2)
private noncomputable def fsNd_edgeSecond (t : ℝ) : ℝ :=
  2 * fsNd_edgeQuadratic + 4 * t ^ 2 / (3 * 7 ^ 3) + 5 * t / 7 ^ 3 -
    2 * fsNd_Ae / (t + 2) ^ 3 + fsNd_Be / (t + 1) ^ 3

private theorem fsNd_edge_eq {t : ℝ} (ht : 0 ≤ t) :
    fsNd_majorant (1 / 7) t = fsNd_edgeModel t := by
  have h1 : 0 < t + 1 := by linarith
  have h2 : 0 < t + 2 := by linarith
  unfold fsNd_edgeModel fsNd_edgeLinear fsNd_edgeQuadratic fsNd_edgeLow fsNd_edgeHigh fsNd_edgePoles
    fsNd_Ae fsNd_Be fsNd_majorant fs_neighborSlopeR fsNd_S fsNd_P fsNd_A fsNd_PD fsNd_KD
  norm_num
  field_simp
  ring

private theorem fsNd_edge_deriv {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt fsNd_edgeModel (fsNd_edgeFirst t) t := by
  have h1 : 0 < t + 1 := by linarith
  have h2 : 0 < t + 2 := by linarith
  unfold fsNd_edgeModel fsNd_edgeHigh fsNd_edgePoles fsNd_edgeFirst
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem fsNd_edge_first_deriv {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt fsNd_edgeFirst (fsNd_edgeSecond t) t := by
  have h1 : 0 < t + 1 := by linarith
  have h2 : 0 < t + 2 := by linarith
  unfold fsNd_edgeFirst fsNd_edgeSecond
  apply HasDerivAt.congr_deriv
  · analytic_deriv
  · norm_num [npowRec]; field_simp; ring

private theorem fsNd_edge_second_pos {t : ℝ} (ht : 0 ≤ t) : 0 < fsNd_edgeSecond t := by
  have h1 : 0 < t + 1 := by linarith
  have h2 : 0 < t + 2 := by linarith
  have hpoly : 4 < 2 * fsNd_edgeQuadratic := by
    norm_num [fsNd_edgeQuadratic, fsNd_edgeLow, fsNd_majorant, fs_neighborSlopeR,
      fsNd_S, fsNd_P, fsNd_A, fsNd_PD, fsNd_KD, fsNd_edgeHigh, fsNd_edgePoles, fsNd_Ae, fsNd_Be]
  have hAe : fsNd_Ae < 13 := by norm_num [fsNd_Ae, fsNd_A, fsNd_PD, fsNd_KD]
  have hBe : 0 < fsNd_Be := by norm_num [fsNd_Be, fsNd_A, fsNd_PD, fsNd_KD]
  have hpow : (2 : ℝ) ^ 3 ≤ (t + 2) ^ 3 := by gcongr; linarith
  have hrec : 2 * fsNd_Ae / (t + 2) ^ 3 < 26 / 8 := by
    apply lt_of_lt_of_le (div_lt_div_of_pos_right (show 2 * fsNd_Ae < 26 by linarith only [hAe]) (by positivity))
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 26) (by norm_num : (0 : ℝ) < 2 ^ 3) hpow
    norm_num at h ⊢
    exact h
  have hpositive : 0 < fsNd_Be / (t + 1) ^ 3 := by positivity
  have hp2 : 0 ≤ 4 * t ^ 2 / (3 * (7 : ℝ) ^ 3) := by positivity
  have hp1 : 0 ≤ 5 * t / (7 : ℝ) ^ 3 := by positivity
  unfold fsNd_edgeSecond
  linarith only [hpoly, hrec, hpositive, hp2, hp1]

private theorem fsNd_edge_convex : ConvexOn ℝ (Icc (1 / 8 : ℝ) (48 / 197)) fsNd_edgeModel := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun t ht => (fsNd_edge_deriv (by linarith [ht.1])).continuousAt.continuousWithinAt)
    (fun t ht => (fsNd_edge_deriv (by linarith [(interior_subset ht).1])).hasDerivWithinAt)
    (fun t ht => (fsNd_edge_first_deriv (by linarith [(interior_subset ht).1])).hasDerivWithinAt)
    (fun t ht => (fsNd_edge_second_pos (by linarith [(interior_subset ht).1])).le)

private theorem fsNd_edge_neg {t : ℝ} (ht : 1 / 8 ≤ t) (ht1 : t ≤ 48 / 197) : fsNd_edgeModel t < 0 := by
  have hleft : fsNd_edgeModel (1 / 8) < 0 := by
    rw [← fsNd_edge_eq (by norm_num)]
    norm_num [fsNd_majorant, fs_neighborSlopeR, fsNd_S, fsNd_P, fsNd_A, fsNd_PD, fsNd_KD]
  have hright : fsNd_edgeModel (48 / 197) < 0 := by
    rw [← fsNd_edge_eq (by norm_num)]
    norm_num [fsNd_majorant, fs_neighborSlopeR, fsNd_S, fsNd_P, fsNd_A, fsNd_PD, fsNd_KD]
  have hθ : 0 ≤ (t - 1 / 8) / (48 / 197 - 1 / 8) := by positivity
  have hθ1 : 0 ≤ 1 - (t - 1 / 8) / (48 / 197 - 1 / 8) := by
    norm_num
    linarith only [ht1]
  have hc := fsNd_edge_convex.2 (by norm_num : (1 / 8 : ℝ) ∈ Icc (1 / 8) (48 / 197))
    (by norm_num : (48 / 197 : ℝ) ∈ Icc (1 / 8) (48 / 197)) hθ1 hθ (by ring)
  simp only [smul_eq_mul] at hc
  rw [show (1 - (t - 1 / 8) / (48 / 197 - 1 / 8)) * (1 / 8) +
      (t - 1 / 8) / (48 / 197 - 1 / 8) * (48 / 197) = t by ring] at hc
  by_cases he : t = 1 / 8
  · rwa [he]
  · have hθpos : 0 < (t - 1 / 8) / (48 / 197 - 1 / 8) := by
      have htp : 1 / 8 < t := lt_of_le_of_ne ht (Ne.symm he)
      positivity
    have hl := mul_nonpos_of_nonneg_of_nonpos hθ1 hleft.le
    have hr := mul_neg_of_pos_of_neg hθpos hright
    linarith only [hc, hl, hr]

/-- The partial factor slope is negative on the intrinsic symmetric neighbour range. -/
theorem fs_neighborSlope_neg {a t : ℝ} (ha : 1 / 7 ≤ a) (ha1 : a ≤ 1 / 4)
    (ht : 1 / 8 ≤ t) (ht1 : t ≤ 48 / 197) : fs_neighborSlope a t < 0 := by
  have ht0 : 0 < t := by linarith
  have htq : t ≤ 1 / 4 := by linarith
  have hle := fsNd_slope_le ha ha1 ht0 htq
  have hm := fsNd_majorant_le_edge ha ha1 ht0.le htq
  rw [fsNd_edge_eq ht0.le] at hm
  exact lt_of_le_of_lt (hle.trans hm) (fsNd_edge_neg ht ht1)

end SmoothedOctagon
