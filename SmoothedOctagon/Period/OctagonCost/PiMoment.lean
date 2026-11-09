module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


/-!
# Pi moment

The four inverse-sine moments below π, proved by a positive square remainder.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real MeasureTheory

/-- The exact endpoint sin(Real.pi/12), written in the radical form used by the paper. -/
noncomputable def octagonPiEndpoint : ℝ := (sqrt 6-sqrt 2)/4
/-- The four positive inverse-sine moments retained in the Real.pi comparison. -/
noncomputable def octagonPiMoment : ℝ :=
  12*octagonPiEndpoint*(1+octagonPiEndpoint^2/6+3*octagonPiEndpoint^4/40+
    5*octagonPiEndpoint^6/112)
noncomputable def octagonAsinKernelPolynomial (t : ℝ) : ℝ :=
  1+t^2/2+3*t^4/8+5*t^6/16
noncomputable def octagonAsinPrimitivePolynomial (t : ℝ) : ℝ :=
  t+t^3/6+3*t^5/40+5*t^7/112

/-- Exact trigonometric normalization; no numerical enclosure of Real.pi or a radical. -/
theorem octagonPiEndpoint_eq_sin : octagonPiEndpoint = sin (Real.pi/12) := by
  have hm : sqrt (2:ℝ)*sqrt 3 = sqrt 6 := by
    rw [← sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [show Real.pi/12 = Real.pi/4-Real.pi/6 by ring,sin_sub,sin_pi_div_four,cos_pi_div_six,
    cos_pi_div_four,sin_pi_div_six]
  unfold octagonPiEndpoint
  nlinarith only [hm]

theorem octagonPiEndpoint_pos : 0 < octagonPiEndpoint := by
  rw [octagonPiEndpoint_eq_sin]
  exact sin_pos_of_pos_of_lt_pi (by positivity) (by linarith only [pi_pos])
theorem octagonPiEndpoint_lt_one : octagonPiEndpoint < 1 := by
  rw [octagonPiEndpoint_eq_sin,← sin_pi_div_two]
  exact sin_lt_sin_of_lt_of_le_pi_div_two (by linarith only [pi_pos]) le_rfl
    (by linarith only [pi_pos])
theorem arcsin_octagonPiEndpoint : arcsin octagonPiEndpoint = Real.pi/12 := by
  rw [octagonPiEndpoint_eq_sin,arcsin_sin]
  · linarith only [pi_pos]
  · linarith only [pi_pos]

/-- The positive square remainder of the cubic inverse-root polynomial in t². -/
theorem octagonAsin_square_remainder (t : ℝ) :
    1-(1-t^2)*(octagonAsinKernelPolynomial t)^2 =
      t^8*(140+56*t^2+35*t^4+25*t^6)/256 := by
  unfold octagonAsinKernelPolynomial
  ring

/-- The polynomial lies STRICTLY below the reciprocal square root away from zero. -/
theorem octagonAsinPolynomial_lt {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    octagonAsinKernelPolynomial t < 1/sqrt (1-t^2) := by
  have hq : 0 < 1-t^2 := by nlinarith only [ht,ht1]
  have hs : 0 < sqrt (1-t^2) := sqrt_pos.2 hq
  have hs2 : (sqrt (1-t^2))^2 = 1-t^2 := sq_sqrt hq.le
  have hp : 0 < octagonAsinKernelPolynomial t := by unfold octagonAsinKernelPolynomial; positivity
  have hrem : 0 < t^8*(140+56*t^2+35*t^4+25*t^6)/256 := by positivity
  have hid := octagonAsin_square_remainder t
  have hprod : (sqrt (1-t^2)*octagonAsinKernelPolynomial t)^2 < 1 := by
    rw [mul_pow,hs2]
    linarith only [hid,hrem]
  have hless : sqrt (1-t^2)*octagonAsinKernelPolynomial t < 1 :=
    (sq_lt_one_iff₀ (by positivity)).mp hprod
  rw [lt_div_iff₀ hs]
  nlinarith only [hless]

theorem octagonAsinPolynomial_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    octagonAsinKernelPolynomial t ≤ 1/sqrt (1-t^2) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · norm_num [octagonAsinKernelPolynomial]
  · exact (octagonAsinPolynomial_lt ht ht1).le

private lemma octagon_inv_sqrt_cont {s : ℝ} (_hs : 0 ≤ s) (hs1 : s < 1) :
    ContinuousOn (fun t : ℝ => 1/sqrt (1-t^2)) (Icc 0 s) := by
  refine continuousOn_const.div ((continuousOn_const.sub (continuousOn_id.pow 2)).sqrt) ?_
  intro t ht
  have ht1 : t < 1 := lt_of_le_of_lt ht.2 hs1
  exact (sqrt_pos.2 (by nlinarith only [ht.1,ht1] : 0 < 1-t^2)).ne'
private lemma octagon_poly_cont : Continuous octagonAsinKernelPolynomial := by
  unfold octagonAsinKernelPolynomial
  fun_prop

/-- The actual inverse-sine reciprocal integral on a closed nonsingular interval. -/
theorem octagon_arcsin_integral {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    (∫ t in (0:ℝ)..s, 1/sqrt (1-t^2)) = arcsin s := by
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => Real.hasDerivAt_arcsin (by
      have ht0 := (uIcc_of_le hs ▸ ht).1
      linarith only [ht0]) (by
      have ht1 := (uIcc_of_le hs ▸ ht).2
      linarith only [ht1,hs1]))
    ((octagon_inv_sqrt_cont hs hs1).intervalIntegrable_of_Icc hs)
  simpa using hI

private lemma octagon_poly_primitive_deriv (t : ℝ) :
    HasDerivAt octagonAsinPrimitivePolynomial (octagonAsinKernelPolynomial t) t := by
  have h := (((hasDerivAt_id' t).add ((hasDerivAt_pow 3 t).div_const 6)).add
    (((hasDerivAt_pow 5 t).const_mul 3).div_const 40)).add
    (((hasDerivAt_pow 7 t).const_mul 5).div_const 112)
  convert h using 1
  · rfl
  · unfold octagonAsinKernelPolynomial
    norm_num
    ring

theorem octagonAsinPolynomial_integral (s : ℝ) :
    (∫ t in (0:ℝ)..s, octagonAsinKernelPolynomial t) =
      s*(1+s^2/6+3*s^4/40+5*s^6/112) := by
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => octagon_poly_primitive_deriv t) (octagon_poly_cont.intervalIntegrable (0:ℝ) s)
  rw [hI]
  unfold octagonAsinPrimitivePolynomial
  ring

/-- Strict inverse-sine moment comparison, from a positive continuous remainder. -/
theorem octagonAsinMoment_lt {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    s*(1+s^2/6+3*s^4/40+5*s^6/112) < arcsin s := by
  have hI := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hs
    octagon_poly_cont.continuousOn (octagon_inv_sqrt_cont hs.le hs1)
    (fun t ht => octagonAsinPolynomial_le ht.1.le (ht.2.trans_lt hs1))
    ⟨s,⟨hs.le,le_rfl⟩,octagonAsinPolynomial_lt hs hs1⟩
  rw [octagonAsinPolynomial_integral,octagon_arcsin_integral hs.le hs1] at hI
  exact hI

/-- The exact normalized inverse-sine integral is Real.pi. -/
theorem octagonPi_integral_eq :
    12*(∫ t in (0:ℝ)..octagonPiEndpoint, 1/sqrt (1-t^2)) = Real.pi := by
  rw [octagon_arcsin_integral octagonPiEndpoint_pos.le octagonPiEndpoint_lt_one,
    arcsin_octagonPiEndpoint]
  ring

/-- The radical-defined four-moment lower bound is strictly below Real.pi. -/
theorem octagonPiMoment_lt : octagonPiMoment < Real.pi := by
  have h := octagonAsinMoment_lt octagonPiEndpoint_pos octagonPiEndpoint_lt_one
  rw [arcsin_octagonPiEndpoint] at h
  unfold octagonPiMoment
  linarith only [h]

end SmoothedOctagon
