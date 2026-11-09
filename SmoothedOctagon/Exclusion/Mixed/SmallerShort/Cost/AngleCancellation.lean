module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# S6 additional angle

The positive arctangent remainder cancels the exact square-root rationalization.
The resulting strict estimate includes zero anisotropy.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The exact antiderivative of the nonnegative arctangent remainder. -/
theorem s6_atan_remainder_integral (t : ℝ) :
    (∫ s in (0:ℝ)..t, 2*s^2/(1+s^2)) = 2*t-2*arctan t := by
  have hc : Continuous (fun s : ℝ => 2*s^2/(1+s^2)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro s; positivity
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => 2*s-2*arctan s)
      (2*s^2/(1+s^2)) s := by
    intro s
    have h := ((hasDerivAt_id' s).const_mul 2).sub
      ((Real.hasDerivAt_arctan s).const_mul 2)
    convert h using 1
    have hp : (1:ℝ)+s^2 ≠ 0 := by positivity
    field_simp
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) (hc.intervalIntegrable 0 t)
  simpa using hi

/-- On the unit interval the original positive integral removes at least the
full cubic term needed by the exact rationalization. -/
theorem s6_two_atan_le_cubic {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    2*arctan t ≤ 2*t-t^3/3 := by
  have hc : Continuous (fun s : ℝ => 2*s^2/(1+s^2)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro s; positivity
  have hp : Continuous (fun s : ℝ => s^2) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) ht (hp.intervalIntegrable 0 t)
    (hc.intervalIntegrable 0 t) (fun s hs => ?_)
  · have hpoly : (∫ s in (0:ℝ)..t, s^2) = t^3/3 := by
      have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => s^3/3) (s^2) s := by
        intro s
        convert (hasDerivAt_pow 3 s).div_const 3 using 1; ring
      simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hd s) (hp.intervalIntegrable 0 t)
    rw [hpoly,s6_atan_remainder_integral] at hi
    linarith only [hi]
  · have hs1 : s ≤ 1 := hs.2.trans ht1
    have hsq : s^2 ≤ 1 := by nlinarith only [hs.1,hs1]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < 1+s^2)]
    nlinarith only [mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hsq)]

/-- Exact decomposition of the two-root quotient.  Only the two defining
root-square identities enter this rationalization. -/
theorem s6_angle_rationalization {H K nu W D : ℝ}
    (hH : 0 < H) (hK : 0 < K) (hW : 0 ≤ W) (hD : 0 ≤ D)
    (hWsq : W^2 = H^2+nu^2) (hDsq : D^2 = K^2-nu^2) :
    2*(W+H)/(K+D) = 2*H/K+2*nu^2/((K+D)*(W+H))+
      2*H*nu^2/(K*(K+D)^2) := by
  have hw : W+H ≠ 0 := by positivity
  have hd : K+D ≠ 0 := by positivity
  have hwid : W-H = nu^2/(W+H) := by
    rw [eq_div_iff hw]
    nlinarith only [hWsq]
  have hdid : K-D = nu^2/(K+D) := by
    rw [eq_div_iff hd]
    nlinarith only [hDsq]
  calc
    2*(W+H)/(K+D) = 2*H/K+2*(W-H)/(K+D)+2*H*(K-D)/(K*(K+D)) := by
      field_simp
      ring
    _ = _ := by rw [hwid,hdid]; field_simp

/-- Domains of the two positive square roots and of the half-angle quotient. -/
theorem s6_additional_angle_domains {nu K H : ℝ} (hnu : 0 ≤ nu)
    (hK : nu+4 < K) (hH : 0 < H) (hH1 : H < 1/5) (hvar : 6*nu^2 < H^2) :
    4 < sqrt (K^2-nu^2) ∧ 0 < K ∧
      H ≤ sqrt (H^2+nu^2) ∧ sqrt (H^2+nu^2) < 2*H ∧
      sqrt (K^2-nu^2) ≤ K ∧
      0 < (sqrt (H^2+nu^2)+H)/(K+sqrt (K^2-nu^2)) ∧
      H/K ≤ (sqrt (H^2+nu^2)+H)/(K+sqrt (K^2-nu^2)) ∧
      (sqrt (H^2+nu^2)+H)/(K+sqrt (K^2-nu^2)) < 1 := by
  have hK0 : 0 < K := by linarith only [hnu,hK]
  have hbase : 0 < K^2-nu^2 := by
    have hp := mul_pos (show 0 < K-nu by linarith only [hK])
      (show 0 < K+nu by linarith only [hK0,hnu])
    nlinarith only [hp]
  have hDsq : (sqrt (K^2-nu^2))^2 = K^2-nu^2 := sq_sqrt hbase.le
  have hWsq : (sqrt (H^2+nu^2))^2 = H^2+nu^2 := sq_sqrt (by positivity)
  have hD0 := sqrt_nonneg (K^2-nu^2)
  have hW0 := sqrt_nonneg (H^2+nu^2)
  have hD4 : 4 < sqrt (K^2-nu^2) := by
    have hp := mul_pos (show 0 < K-nu-4 by linarith only [hK])
      (show 0 < K+nu+4 by linarith only [hK0,hnu])
    nlinarith only [hp,hDsq,hD0,hnu]
  have hWH : H ≤ sqrt (H^2+nu^2) := by nlinarith only [hWsq,hW0,hH,sq_nonneg nu]
  have hW2 : sqrt (H^2+nu^2) < 2*H := by nlinarith only [hWsq,hW0,hH,hvar,sq_nonneg nu]
  have hDK : sqrt (K^2-nu^2) ≤ K := by nlinarith only [hDsq,hD0,hK0,sq_nonneg nu]
  have hden : 0 < K+sqrt (K^2-nu^2) := by positivity
  have ht0 : 0 < (sqrt (H^2+nu^2)+H)/(K+sqrt (K^2-nu^2)) := by positivity
  have htH : H/K ≤ (sqrt (H^2+nu^2)+H)/(K+sqrt (K^2-nu^2)) := by
    rw [div_le_div_iff₀ hK0 hden]
    have hp := mul_le_mul hWH hDK hD0 hW0
    nlinarith only [hp]
  have ht1 : (sqrt (H^2+nu^2)+H)/(K+sqrt (K^2-nu^2)) < 1 := by
    rw [div_lt_one hden]
    linarith only [hW2,hH1,hD4,hK0]
  exact ⟨hD4,hK0,hWH,hW2,hDK,ht0,htH,ht1⟩

/-- The positive arctangent integral cancels the last exact rationalization
term. The statement includes nu=0, without division by nu. -/
theorem s6_additional_angle_cancellation {nu K H : ℝ} (hnu : 0 ≤ nu)
    (hK : nu+4 < K) (hH : 0 < H) (hH1 : H < 1/5) (hvar : 6*nu^2 < H^2) :
    2*arctan ((sqrt (H^2+nu^2)+H)/(K+sqrt (K^2-nu^2))) <
      2*H/K+2*nu^2/((K+sqrt (K^2-nu^2))*(sqrt (H^2+nu^2)+H)) := by
  obtain ⟨hD4,hK0,hWH,hW2,hDK,ht0,htH,ht1⟩ :=
    s6_additional_angle_domains hnu hK hH hH1 hvar
  let W := sqrt (H^2+nu^2)
  let D := sqrt (K^2-nu^2)
  let t := (W+H)/(K+D)
  have hD0 : 0 ≤ D := sqrt_nonneg _
  have hW0 : 0 ≤ W := sqrt_nonneg _
  have hbase : 0 ≤ K^2-nu^2 := by nlinarith only [hK,hnu]
  have hWsq : W^2 = H^2+nu^2 := sq_sqrt (by positivity)
  have hDsq : D^2 = K^2-nu^2 := sq_sqrt hbase
  have hdecomp := s6_angle_rationalization hH hK0 hW0 hD0 hWsq hDsq
  have hlast : 2*H*nu^2/(K*(K+D)^2) < H^3/(3*K^3) := by
    have hd : 0 < K*(K+D)^2 := by positivity
    have hk : 0 < 3*K^3 := by positivity
    rw [div_lt_div_iff₀ hd hk]
    have hsmall := mul_lt_mul_of_pos_right hvar (sq_pos_of_pos hK0)
    have hmore : 0 ≤ H^2*(D*(2*K+D)) := by positivity
    have hid : H^2*(K+D)^2-6*nu^2*K^2 =
        (H^2-6*nu^2)*K^2+H^2*(D*(2*K+D)) := by ring
    have hc : 0 < H^2*(K+D)^2-6*nu^2*K^2 := by nlinarith only [hsmall,hmore,hid]
    have hp := mul_pos (mul_pos hH hK0) hc
    nlinarith only [hp]
  have hcube : (H/K)^3 ≤ t^3 := pow_le_pow_left₀ (by positivity) htH 3
  have hcube' : H^3/(3*K^3) ≤ t^3/3 := by
    have heq : H^3/(3*K^3) = (H/K)^3/3 := by field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right hcube (by norm_num)
  have hlastt := hlast.trans_le hcube'
  have hatan : 2*arctan t ≤ 2*t-t^3/3 := s6_two_atan_le_cubic ht0.le ht1.le
  change 2*arctan t < 2*H/K+2*nu^2/((K+D)*(W+H))
  have hdecomp' : 2*t = 2*H/K+2*nu^2/((K+D)*(W+H))+
      2*H*nu^2/(K*(K+D)^2) := by
    calc
      2*t = 2*(W+H)/(K+D) := by dsimp only [t]; ring
      _ = _ := hdecomp
  linarith only [hatan,hlastt,hdecomp']

/-- The same exact cancellation gives the simple reciprocal anisotropy loss. -/
theorem s6_additional_angle_lt {nu K H : ℝ} (hnu : 0 ≤ nu)
    (hK : nu+4 < K) (hH : 0 < H) (hH1 : H < 1/5) (hvar : 6*nu^2 < H^2) :
    2*arctan ((sqrt (H^2+nu^2)+H)/(K+sqrt (K^2-nu^2))) <
      2*H/K+nu^2/(8*H) := by
  have ha := s6_additional_angle_cancellation hnu hK hH hH1 hvar
  obtain ⟨hD4,hK0,hWH,-,-,-,-,-⟩ := s6_additional_angle_domains hnu hK hH hH1 hvar
  have hden : 0 < (K+sqrt (K^2-nu^2))*(sqrt (H^2+nu^2)+H) := by positivity
  have hprod : 16*H ≤ (K+sqrt (K^2-nu^2))*(sqrt (H^2+nu^2)+H) := by
    have h8 : 8 ≤ K+sqrt (K^2-nu^2) := by linarith only [hK,hnu,hD4]
    have h2 : 2*H ≤ sqrt (H^2+nu^2)+H := by linarith only [hWH]
    have hp := mul_le_mul h8 h2 (by positivity : (0:ℝ) ≤ 2*H) (by linarith : (0:ℝ) ≤ K+sqrt (K^2-nu^2))
    nlinarith only [hp]
  have hrem : 2*nu^2/((K+sqrt (K^2-nu^2))*(sqrt (H^2+nu^2)+H)) ≤ nu^2/(8*H) := by
    rw [div_le_div_iff₀ hden (by positivity)]
    have hp := mul_le_mul_of_nonneg_left hprod (sq_nonneg nu)
    nlinarith only [hp]
  exact ha.trans_le (by linarith only [hrem])

/-- The strict symmetric endpoint follows from the same theorem. -/
theorem s6_additional_angle_zero {K H : ℝ} (hK : 4 < K)
    (hH : 0 < H) (hH1 : H < 1/5) : 2*arctan (H/K) < 2*H/K := by
  have ha := s6_additional_angle_lt (nu := 0) (by norm_num) (by simpa using hK) hH hH1
    (by nlinarith only [sq_pos_of_pos hH])
  have hK0 : 0 < K := by linarith only [hK]
  have heq : (H+H)/(K+K) = H/K := by field_simp
  simpa [Real.sqrt_sq_eq_abs,abs_of_pos hH,abs_of_pos hK0,heq] using ha

end SmoothedOctagon
