module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Period.OctagonCost.LogMoment
public import SmoothedOctagon.Period.OctagonCost.PiMoment
public import Mathlib.Tactic.LinearCombination

/-!
# Exact octagon cost comparisons

Positive reciprocal and inverse-sine moments bound the octagon cost by exact
radical expressions. Two signed squarings give the cost-to-π ratio and the
central-score comparison; these bounds supply the competitive Casimir caps.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

private noncomputable def octM : ℝ := 1+1/12+21/640+65/3584
private noncomputable def octN : ℝ := 1/24+3/160+75/7168
private noncomputable def octP : ℝ := 3*(octM+octN)
private noncomputable def octR : ℝ := 3*(octM+3*octN)
noncomputable def octagonCostMoment : ℝ :=
  2*sqrt 3*(8-4*sqrt 2-octagonLogMoment)/(2*sqrt 2-1)

private theorem octagonPiMoment_eq : octagonPiMoment = octP*sqrt 6-octR*sqrt 2 := by
  have h2 : (sqrt (2:ℝ))^2 = 2 := sq_sqrt (by norm_num)
  have h3 : (sqrt (3:ℝ))^2 = 3 := sq_sqrt (by norm_num)
  have h6 : sqrt (6:ℝ) = sqrt 2*sqrt 3 := by
    rw [show (6:ℝ) = 2*3 by norm_num,sqrt_mul (by norm_num)]
  have hs : ((sqrt 6-sqrt 2)/4)^2 = (2-sqrt 3)/4 := by
    rw [h6]
    linear_combination ((sqrt 3-1)^2/16)*h2+(1/8)*h3
  have hs4 : ((sqrt 6-sqrt 2)/4)^4 = (((sqrt 6-sqrt 2)/4)^2)^2 := by ring
  have hs6 : ((sqrt 6-sqrt 2)/4)^6 = (((sqrt 6-sqrt 2)/4)^2)^3 := by ring
  have hp3 : (sqrt (3:ℝ))^3 = 3*sqrt 3 := by
    calc
      (sqrt (3:ℝ))^3 = (sqrt (3:ℝ))^2*sqrt 3 := by ring
      _ = 3*sqrt 3 := by rw [h3]
  have hb : 1+((sqrt 6-sqrt 2)/4)^2/6+3*((sqrt 6-sqrt 2)/4)^4/40+
      5*((sqrt 6-sqrt 2)/4)^6/112 = octM-octN*sqrt 3 := by
    rw [hs4,hs6,hs]
    dsimp [octM,octN]
    ring_nf
    rw [h3,hp3]
    ring
  change 12*((sqrt 6-sqrt 2)/4)*(1+((sqrt 6-sqrt 2)/4)^2/6+
    3*((sqrt 6-sqrt 2)/4)^4/40+5*((sqrt 6-sqrt 2)/4)^6/112) = _
  rw [hb,h6]
  unfold octP octR
  linear_combination (-3*sqrt 2*octN)*h3

/-- Two signed squarings compare the exact radical expressions. -/
private theorem oct_radical_gap {A B C : ℝ}
    (hB : 0 < B) (hAB : 0 < A+B) (hC : 0 < C)
    (hR : 0 < 18*C^2-3*A^2-6*B^2)
    (hT : 0 < 6*A*B+8*C^2)
    (hTR : (18*C^2-3*A^2-6*B^2)^2 < 2*(6*A*B+8*C^2)^2) :
    C*(4-sqrt 2) < (A+B*sqrt 2)*sqrt 3 := by
  have h2 : (sqrt (2:ℝ))^2 = 2 := sq_sqrt (by norm_num)
  have h3 : (sqrt (3:ℝ))^2 = 3 := sq_sqrt (by norm_num)
  have hr1 : (1:ℝ) < sqrt 2 := by rw [lt_sqrt (by norm_num)]; norm_num
  have hr2 : sqrt (2:ℝ) < 2 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have hs3 : 0 < sqrt (3:ℝ) := by positivity
  have hA : 0 < A+B*sqrt 2 := by
    have := mul_pos hB (sub_pos.mpr hr1)
    nlinarith only [hAB,this]
  have hTroot : 18*C^2-3*A^2-6*B^2 < (6*A*B+8*C^2)*sqrt 2 := by
    apply (sq_lt_sq₀ hR.le (mul_pos hT (by positivity)).le).mp
    have he : ((6*A*B+8*C^2)*sqrt 2)^2 = 2*(6*A*B+8*C^2)^2 := by
      rw [mul_pow,h2]
      ring
    rwa [he]
  have hleft : 0 ≤ C*(4-sqrt 2) := mul_nonneg hC.le (by linarith only [hr2])
  have hright : 0 ≤ (A+B*sqrt 2)*sqrt 3 := mul_nonneg hA.le hs3.le
  apply (sq_lt_sq₀ hleft hright).mp
  have he : ((A+B*sqrt 2)*sqrt 3)^2-(C*(4-sqrt 2))^2 =
      (6*A*B+8*C^2)*sqrt 2-(18*C^2-3*A^2-6*B^2) := by
    rw [mul_pow,mul_pow,h3]
    linear_combination (3*B^2-C^2)*h2
  linarith only [he,hTroot]

private theorem oct_cost_moment_lt {q b : ℝ}
    (hB : 0 < 8-q*octP+2*b)
    (hAB : 0 < (4*q*octP-16+2*octagonLogMoment-b)+(8-q*octP+2*b))
    (hC : 0 < q*octR)
    (hR : 0 < 18*(q*octR)^2-3*(4*q*octP-16+2*octagonLogMoment-b)^2-6*(8-q*octP+2*b)^2)
    (hT : 0 < 6*(4*q*octP-16+2*octagonLogMoment-b)*(8-q*octP+2*b)+8*(q*octR)^2)
    (hTR : (18*(q*octR)^2-3*(4*q*octP-16+2*octagonLogMoment-b)^2-6*(8-q*octP+2*b)^2)^2 <
      2*(6*(4*q*octP-16+2*octagonLogMoment-b)*(8-q*octP+2*b)+8*(q*octR)^2)^2) :
    octagonCostMoment < q*octagonPiMoment+b*sqrt 3 := by
  have hgap := oct_radical_gap hB hAB hC hR hT hTR
  have h2 : (sqrt (2:ℝ))^2 = 2 := sq_sqrt (by norm_num)
  have hr : (1:ℝ) < sqrt 2 := by rw [lt_sqrt (by norm_num)]; norm_num
  have hD : 0 < 2*sqrt (2:ℝ)-1 := by linarith only [hr]
  have h6 : sqrt (6:ℝ) = sqrt 2*sqrt 3 := by
    rw [show (6:ℝ) = 2*3 by norm_num,sqrt_mul (by norm_num)]
  have hid : (q*octagonPiMoment+b*sqrt 3-octagonCostMoment)*(2*sqrt 2-1) =
      ((4*q*octP-16+2*octagonLogMoment-b)+(8-q*octP+2*b)*sqrt 2)*sqrt 3-
      (q*octR)*(4-sqrt 2) := by
    rw [octagonPiMoment_eq,h6]
    unfold octagonCostMoment
    rw [sub_mul,div_mul_cancel₀ _ hD.ne']
    linear_combination (2*q*octP*sqrt 3-2*q*octR)*h2
  have hpos : 0 < (q*octagonPiMoment+b*sqrt 3-octagonCostMoment)*(2*sqrt 2-1) := by
    rw [hid]
    linarith only [hgap]
  have := (mul_pos_iff_of_pos_right hD).mp hpos
  linarith only [this]

theorem octagonCostMoment_lt_ratio : octagonCostMoment < (203/204)*octagonPiMoment := by
  have h := oct_cost_moment_lt (q := (203/204:ℝ)) (b := 0)
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])
  simpa only [zero_mul,add_zero] using h

theorem octagonCostMoment_lt_score :
    octagonCostMoment < (161/162)*octagonPiMoment+(9/4000)*sqrt 3 := by
  exact oct_cost_moment_lt
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])
    (by norm_num [octP,octR,octM,octN,octagonLogMoment])


/-- The retained positive log moments bound the original octagon cost. -/
theorem octagonCost_lt_moment : octagonCost < octagonCostMoment := by
  have hlog := octagonLogMoment_lt_log_two
  have hs3 : 0 < sqrt (3:ℝ) := by positivity
  have hr : (1:ℝ) < sqrt 2 := by rw [lt_sqrt (by norm_num)]; norm_num
  have hD : 0 < 2*sqrt (2:ℝ)-1 := by linarith only [hr]
  have h12 : sqrt (12:ℝ) = 2*sqrt 3 := by
    rw [show (12:ℝ) = 2^2*3 by norm_num,sqrt_mul (by norm_num),sqrt_sq (by norm_num)]
  have h32 : sqrt (32:ℝ) = 4*sqrt 2 := by
    rw [show (32:ℝ) = 4^2*2 by norm_num,sqrt_mul (by norm_num),sqrt_sq (by norm_num)]
  have h8 : sqrt (8:ℝ) = 2*sqrt 2 := by
    rw [show (8:ℝ) = 2^2*2 by norm_num,sqrt_mul (by norm_num),sqrt_sq (by norm_num)]
  have hN : 8-4*sqrt 2-log 2 < 8-4*sqrt 2-octagonLogMoment := by linarith only [hlog]
  have hm := mul_lt_mul_of_pos_left hN (show 0 < 2*sqrt (3:ℝ) by positivity)
  have hd := div_lt_div_of_pos_right hm hD
  rw [octagonCost,octagonDensity,h12,h32,h8]
  unfold octagonCostMoment at hd ⊢
  convert hd using 1; ring

theorem octagonCost_lt_pi_mul : octagonCost < (203/204)*π := by
  have hp := mul_lt_mul_of_pos_left octagonPiMoment_lt (show (0:ℝ) < 203/204 by norm_num)
  exact octagonCost_lt_moment.trans (octagonCostMoment_lt_ratio.trans hp)

theorem octagonCost_ratio_lt : octagonCost/π < 203/204 :=
  (div_lt_iff₀ Real.pi_pos).mpr octagonCost_lt_pi_mul

theorem octagonCost_lt_score : octagonCost < (161/162)*π+(9/4000)*sqrt 3 := by
  have hp := mul_lt_mul_of_pos_left octagonPiMoment_lt (show (0:ℝ) < 161/162 by norm_num)
  exact octagonCost_lt_moment.trans (octagonCostMoment_lt_score.trans (by linarith only [hp]))

/-- The exact moment bound supplies the current cover's cost ceiling. -/
theorem octagonCost_lt_cover : octagonCost < 2501/800 := by
  apply octagonCost_lt_moment.trans
  have h2 : (sqrt (2:ℝ))^2 = 2 := sq_sqrt (by norm_num)
  have h3 : (sqrt (3:ℝ))^2 = 3 := sq_sqrt (by norm_num)
  have hr : (1:ℝ) < sqrt 2 := by rw [lt_sqrt (by norm_num)]; norm_num
  have hr2 : sqrt (2:ℝ) < 3/2 := by rw [sqrt_lt' (by norm_num)]; norm_num
  have hD : 0 < 2*sqrt (2:ℝ)-1 := by linarith only [hr]
  have hN : 0 < 8-4*sqrt 2-octagonLogMoment := by
    have hL : octagonLogMoment < 1 := by norm_num [octagonLogMoment]
    linarith only [hL,hr2]
  let a : ℝ := 2501/800
  let T : ℝ := 96*(8-octagonLogMoment)-4*a^2
  let R : ℝ := 12*((8-octagonLogMoment)^2+32)-9*a^2
  have hT : 0 < T := by norm_num [T,a,octagonLogMoment]
  have hR : 0 < R := by norm_num [R,a,octagonLogMoment]
  have hTR : R^2 < 2*T^2 := by norm_num [T,R,a,octagonLogMoment]
  have hroot : R < T*sqrt 2 := by
    apply (sq_lt_sq₀ hR.le (mul_pos hT (by positivity)).le).mp
    rw [mul_pow,h2]
    simpa only [mul_comm] using hTR
  have hid : (a*(2*sqrt 2-1))^2-(2*sqrt 3*(8-4*sqrt 2-octagonLogMoment))^2 =
      T*sqrt 2-R := by
    dsimp [T,R]
    rw [show (2*sqrt 3*(8-4*sqrt 2-octagonLogMoment))^2 =
      4*(sqrt (3:ℝ))^2*(8-4*sqrt 2-octagonLogMoment)^2 by ring,h3]
    linear_combination (4*a^2-192)*h2
  have hsq : (2*sqrt 3*(8-4*sqrt 2-octagonLogMoment))^2 < (a*(2*sqrt 2-1))^2 := by
    linarith only [hid,hroot]
  have hm := (sq_lt_sq₀ (show 0 ≤ 2*sqrt 3*(8-4*sqrt 2-octagonLogMoment) by positivity)
    (show 0 ≤ a*(2*sqrt 2-1) by dsimp [a]; positivity)).mp hsq
  unfold octagonCostMoment
  rw [div_lt_iff₀ hD]
  exact hm

/-- The spectral cost inequality gives the cap used by forward and mixed periods. -/
theorem octagon_spectral_cap {x c : ℝ} (hx : 0 < x)
    (h : π/3*(sqrt x+3/2) ≤ c) (hc : c ≤ octagonCost) : x/12 < 9193/50000 := by
  have hi := h.trans_lt (hc.trans_lt octagonCost_lt_pi_mul)
  have hk : sqrt x < 101/68 := by
    apply (mul_lt_mul_iff_right₀ Real.pi_pos).mp
    nlinarith only [hi]
  have hs : (sqrt x)^2 < (101/68:ℝ)^2 :=
    (sq_lt_sq₀ (sqrt_nonneg _) (by norm_num)).mpr hk
  rw [sq_sqrt hx.le] at hs
  nlinarith only [hs]


/-- The spectral moment ratio is below the exact golden-unit threshold. -/
theorem octagon_moment_ratio_lt_golden :
    (203/204:ℝ) < 8*sqrt 5/(9+4*sqrt 5) := by
  have hs2 : (sqrt (5:ℝ))^2 = 5 := sq_sqrt (by norm_num)
  have hs : (2:ℝ) < sqrt 5 := (lt_sqrt (by norm_num)).mpr (by norm_num)
  let l := sqrt (5:ℝ)-2
  have hl0 : 0 < l := by dsimp [l]; linarith only [hs]
  have hd : 0 < sqrt (5:ℝ)+2 := by positivity
  have hlinv : l = 1/(sqrt 5+2) := by
    rw [eq_div_iff hd.ne']
    dsimp [l]
    nlinarith only [hs2]
  have hl1 : l < 1/4 := by
    rw [hlinv,div_lt_iff₀ hd]
    linarith only [hs]
  have hlq : l^2 = 1-4*l := by dsimp [l]; nlinarith only [hs2]
  have hl4 : l^4 = 17-72*l := by
    calc
      l^4 = (l^2)^2 := by ring
      _ = (1-4*l)^2 := by rw [hlq]
      _ = 17-72*l := by nlinarith only [hlq]
  have hrad : sqrt (5:ℝ) = l+2 := by dsimp [l]; ring
  have heq : 8*sqrt 5/(9+4*sqrt 5) = 1-l^4 := by
    rw [div_eq_iff (show 9+4*sqrt (5:ℝ) ≠ 0 by positivity),hl4,hrad]
    nlinarith only [hlq]
  have hpow : l^4 < (1/4:ℝ)^4 := pow_lt_pow_left₀ hl1 hl0.le (by norm_num)
  rw [heq]
  nlinarith only [hpow]

/-- The retained inverse-sine moments themselves exceed the current cover's pi constant. -/
theorem octagonPiMoment_gt_cover : (6283/2000:ℝ) < octagonPiMoment := by
  let q : ℝ := 6283/2000
  let A : ℝ := 6*octP^2+2*octR^2-q^2
  let B : ℝ := 4*octP*octR
  have hA : 0 < A := by norm_num [A,q,octP,octR,octM,octN]
  have hB : 0 < B := by norm_num [B,octP,octR,octM,octN]
  have hsq : 3*B^2 < A^2 := by norm_num [A,B,q,octP,octR,octM,octN]
  have h3 : (sqrt (3:ℝ))^2 = 3 := sq_sqrt (by norm_num)
  have hroot : B*sqrt 3 < A := by
    apply (sq_lt_sq₀ (mul_nonneg hB.le (sqrt_nonneg _)) hA.le).mp
    rw [mul_pow,h3]
    nlinarith only [hsq]
  have h2 : (sqrt (2:ℝ))^2 = 2 := sq_sqrt (by norm_num)
  have h6 : sqrt (6:ℝ) = sqrt 2*sqrt 3 := by
    rw [← sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hP2 : octagonPiMoment^2 = 6*octP^2+2*octR^2-4*octP*octR*sqrt 3 := by
    rw [octagonPiMoment_eq]
    rw [show (octP*sqrt 6-octR*sqrt 2)^2 = (sqrt (2:ℝ))^2*(octP*sqrt 3-octR)^2 by rw [h6]; ring,h2]
    linear_combination (2*octP^2)*h3
  have hgap : q^2 < octagonPiMoment^2 := by
    dsimp [A,B] at hroot
    rw [hP2]
    linarith only [hroot]
  have hP : 0 < octagonPiMoment := by
    have hs := octagonPiEndpoint_pos
    unfold octagonPiMoment
    positivity
  exact (sq_lt_sq₀ (show 0 ≤ q by dsimp [q]; positivity) hP.le).mp hgap

/-- Compatibility with the existing fixed cover parameter follows from the exact moment. -/
theorem octagon_pi_gt_cover : (6283/2000:ℝ) < Real.pi :=
  octagonPiMoment_gt_cover.trans octagonPiMoment_lt

end SmoothedOctagon
