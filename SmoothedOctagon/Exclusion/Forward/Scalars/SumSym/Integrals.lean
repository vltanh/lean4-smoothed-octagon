module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Reciprocal means for the forward sum comparison

Positive integral remainders bound the paired logarithms. Their exact identity
gives the fixed tangent at `τ = 1/5`, including zero shape parameters.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real MeasureTheory

/-- Normalized reciprocal mean, including its genuine value at k = 0. -/
noncomputable def fwdSumEll (k : ℝ) : ℝ := ∫ v in (0:ℝ)..1, 1/(1-k*v)
/-- Paired reciprocal moment, defined without dividing by either shape parameter. -/
noncomputable def fwdSumJ (a k : ℝ) : ℝ :=
  ∫ v in (0:ℝ)..1, v/((1-k*v)*(1-(a+k)*v))

private theorem fs_den_pos {k v : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hv : v ∈ Icc (0:ℝ) 1) : 0 < 1-k*v := by
  have : k*v ≤ k := mul_le_of_le_one_right hk0 hv.2
  linarith

private theorem fs_recip_cont {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1) :
    ContinuousOn (fun v : ℝ => 1/(1-k*v)) (Icc 0 1) := by
  exact continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
    (fun v hv => ne_of_gt (fs_den_pos hk0 hk1 hv))

private theorem fs_pair_cont {a k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) (hc : a+k < 1) :
    ContinuousOn (fun v : ℝ => v/((1-k*v)*(1-(a+k)*v))) (Icc 0 1) := by
  apply continuousOn_id.div
    ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).mul
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id)))
  intro v hv
  exact mul_ne_zero (ne_of_gt (fs_den_pos hk (by linarith) hv))
    (ne_of_gt (fs_den_pos (by linarith) hc hv))

/-- The upper geometric remainder is an explicitly nonnegative product. -/
theorem fwdSumEll_remainder {k v : ℝ} (hk : 0 ≤ k) (hk1 : k < 1)
    (hv : v ∈ Icc (0:ℝ) 1) :
    1+k*v+k^2/(1-k)*v^2-1/(1-k*v) =
      k^3*v^2*(1-v)/((1-k)*(1-k*v)) := by
  have hd := fs_den_pos hk hk1 hv
  field_simp [ne_of_gt hd, ne_of_gt (sub_pos.mpr hk1)]
  ring

/-- The paired lower remainder retains the first two positive moments. -/
theorem fwdSumJ_remainder {a k v : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k)
    (hc : a+k < 1) (hv : v ∈ Icc (0:ℝ) 1) :
    v/((1-k*v)*(1-(a+k)*v))-(v+(a+2*k)*v^2) =
      v^3*(k^2*(1-(a+k)*v)+(a+k)^2*(1-k*v)+k*(a+k))/
        ((1-k*v)*(1-(a+k)*v)) := by
  have hd := fs_den_pos hk (by linarith) hv
  have he := fs_den_pos (by linarith) hc hv
  have hp : (1-k*v)*(1-(a+k)*v) ≠ 0 := mul_ne_zero (ne_of_gt hd) (ne_of_gt he)
  apply (eq_div_iff hp).mpr
  rw [sub_mul,div_mul_cancel₀ _ hp]
  ring

/-- Sharp geometric truncation used by the fixed sum tangent. -/
theorem fwdSumEll_le {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) :
    fwdSumEll k ≤ 1+k/2+k^2/(3*(1-k)) := by
  let p : ℝ → ℝ := fun v => 1+k*v+k^2/(1-k)*v^2
  have hp : Continuous p := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    ((fs_recip_cont hk hk1).intervalIntegrable_of_Icc (by norm_num))
    (hp.intervalIntegrable 0 1) (fun v hv => ?_)
  · have hpoly : (∫ v in (0:ℝ)..1, p v) = 1+k/2+k^2/(3*(1-k)) := by
      have hpderiv (v : ℝ) : HasDerivAt
          (fun w : ℝ => w+k/2*w^2+k^2/(3*(1-k))*w^3) (p v) v := by
        convert ((hasDerivAt_id v).add
          (((hasDerivAt_pow 2 v).const_mul (k/2)))).add
            ((hasDerivAt_pow 3 v).const_mul (k^2/(3*(1-k)))) using 1
        · rfl
        · dsimp [p]; field_simp [ne_of_gt (sub_pos.mpr hk1)]
      simpa using
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hpderiv v)
          (hp.intervalIntegrable 0 1)
    exact le_trans hi (le_of_eq hpoly)
  · have hrem := fwdSumEll_remainder hk hk1 hv
    have hpos : 0 ≤ k^3*v^2*(1-v)/((1-k)*(1-k*v)) := by
      apply div_nonneg
      · exact mul_nonneg (mul_nonneg (pow_nonneg hk _) (sq_nonneg v)) (sub_nonneg.mpr hv.2)
      · exact mul_nonneg (sub_nonneg.mpr hk1.le) (fs_den_pos hk hk1 hv).le
    dsimp [p]
    linarith only [hrem,hpos]

/-- The paired moment lies above its constant and linear reciprocal terms. -/
theorem fwdSumJ_ge {a k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) (hc : a+k < 1) :
    1/2+(a+2*k)/3 ≤ fwdSumJ a k := by
  let p : ℝ → ℝ := fun v => v+(a+2*k)*v^2
  have hp : Continuous p := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (hp.intervalIntegrable 0 1)
    ((fs_pair_cont ha hk hc).intervalIntegrable_of_Icc (by norm_num)) (fun v hv => ?_)
  · have hpoly : (∫ v in (0:ℝ)..1, p v) = 1/2+(a+2*k)/3 := by
      have hpderiv (v : ℝ) : HasDerivAt
          (fun w : ℝ => w^2/2+(a+2*k)/3*w^3) (p v) v := by
        convert (((hasDerivAt_pow 2 v).div_const 2).add
          ((hasDerivAt_pow 3 v).const_mul ((a+2*k)/3))) using 1
        dsimp [p]; ring
      simpa using
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hpderiv v)
          (hp.intervalIntegrable 0 1)
    exact hpoly ▸ hi
  · have hrem := fwdSumJ_remainder ha hk hc hv
    have hd := fs_den_pos hk (by linarith) hv
    have he := fs_den_pos (by linarith) hc hv
    have hpos : 0 ≤ v^3*(k^2*(1-(a+k)*v)+(a+k)^2*(1-k*v)+k*(a+k))/
        ((1-k*v)*(1-(a+k)*v)) := by
      apply div_nonneg
      · exact mul_nonneg (pow_nonneg hv.1 _) (add_nonneg
          (add_nonneg (mul_nonneg (sq_nonneg k) he.le)
            (mul_nonneg (sq_nonneg (a+k)) hd.le)) (mul_nonneg hk (by linarith)))
      · exact mul_nonneg hd.le he.le
    dsimp [p]
    linarith only [hrem,hpos]

/-- Weighted logarithm identity remains valid at k=0. -/
theorem fwdSumEll_log {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) :
    k*fwdSumEll k = -log (1-k) := by
  have hc := fs_recip_cont hk hk1
  have hderiv (v : ℝ) (hv : v ∈ uIcc (0:ℝ) 1) :
      HasDerivAt (fun w : ℝ => -log (1-k*w)) (k*(1/(1-k*v))) v := by
    have hd := fs_den_pos hk hk1 (by simpa using hv)
    convert ((((hasDerivAt_id v).const_mul k).const_sub 1).log
      (ne_of_gt hd)).neg using 1
    · rfl
    · simp only [id_eq]; ring
  have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuousOn_const.mul hc).intervalIntegrable_of_Icc (by norm_num))
  rw [intervalIntegral.integral_const_mul] at hid
  simpa only [fwdSumEll,mul_one,mul_zero,sub_zero,log_one,neg_zero] using hid

/-- Exact paired resolvent identity, with no division by a. -/
theorem fwdSumEll_pair {a k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) (hc : a+k < 1) :
    fwdSumEll (a+k)-fwdSumEll k = a*fwdSumJ a k := by
  have hkc := fs_recip_cont hk (by linarith : k < 1)
  have hcc := fs_recip_cont (by linarith : 0 ≤ a+k) hc
  have hjc := fs_pair_cont ha hk hc
  unfold fwdSumEll fwdSumJ
  rw [← intervalIntegral.integral_sub
    (hcc.intervalIntegrable_of_Icc (by norm_num))
    (hkc.intervalIntegrable_of_Icc (by norm_num)),
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  have hd := fs_den_pos hk (by linarith) (by simpa using hv)
  have he := fs_den_pos (by linarith) hc (by simpa using hv)
  field_simp [ne_of_gt hd,ne_of_gt he]
  ring

/-- Exact two-logarithm pairing, including a=0 and k=0. -/
theorem fwdSum_log_ratio {a k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) (hc : a+k < 1) :
    log ((1-(a+k))/(1-k)) = -a*fwdSumEll k-a*(a+k)*fwdSumJ a k := by
  rw [log_div (ne_of_gt (sub_pos.mpr hc)) (ne_of_gt (by linarith : 0 < 1-k))]
  have he := fwdSumEll_log hk (by linarith : k < 1)
  have hf := fwdSumEll_log (by linarith : 0 ≤ a+k) hc
  have hp := fwdSumEll_pair ha hk hc
  calc
    log (1-(a+k))-log (1-k) = -(a+k)*fwdSumEll (a+k)+k*fwdSumEll k := by
      linarith only [he,hf]
    _ = _ := by rw [sub_eq_iff_eq_add.mp hp]; ring

theorem fwdSumEll_zero : fwdSumEll 0 = 1 := by
  simp [fwdSumEll]
theorem fwdSumJ_zero : fwdSumJ 0 0 = 1/2 := by
  simp [fwdSumJ]

/-- The physical logarithm log(1+t), parametrized by k=t/(1+t). -/
theorem fwdSum_log_one_add {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) :
    log (1+k/(1-k)) = k*fwdSumEll k := by
  have hr : 0 < 1-k := sub_pos.mpr hk1
  rw [show 1+k/(1-k) = (1-k)⁻¹ by field_simp; ring, log_inv]
  exact (fwdSumEll_log hk hk1).symm

/-- The physical second logarithm log(1-a(1+t)) has the same paired representation. -/
theorem fwdSum_log_one_sub {a k : ℝ} (ha : 0 ≤ a) (hk : 0 ≤ k) (hc : a+k < 1) :
    log (1-a*(1+k/(1-k))) = -a*fwdSumEll k-a*(a+k)*fwdSumJ a k := by
  have hr : 0 < 1-k := by linarith
  rw [show 1-a*(1+k/(1-k)) = (1-(a+k))/(1-k) by field_simp; ring]
  exact fwdSum_log_ratio ha hk hc

/-- The rational reciprocal envelope before fixing its supporting tangent. -/
noncomputable def fwdSumPsi (A0 A1 D z τ : ℝ) : ℝ :=
  A0*(1/τ-1)+A1+z*(D*τ/2-τ^2/(3*(2-τ)))
/-- The supporting tangent at τ=1/5. -/
noncomputable def fwdSumFixedTangent (A0 A1 D z τ : ℝ) : ℝ :=
  A1+(9-25*τ)*A0+z*((D/2-19/243)*τ+2/243)

/-- Exact supporting-tangent remainder: both summands have their natural signs. -/
theorem fwdSum_fixedTangent_remainder {τ : ℝ} (hτ : 0 < τ) (hτ2 : τ < 2)
    (A0 A1 D z : ℝ) :
    fwdSumFixedTangent A0 A1 D z τ-fwdSumPsi A0 A1 D z τ =
      (5*τ-1)^2*(-A0/τ+4*z/(243*(2-τ))) := by
  unfold fwdSumFixedTangent fwdSumPsi
  field_simp [ne_of_gt hτ,ne_of_gt (sub_pos.mpr hτ2)]
  ring

theorem fwdSumPsi_le_fixedTangent {A0 A1 D z τ : ℝ}
    (hA0 : A0 ≤ 0) (hz : 0 ≤ z) (hτ : 0 < τ) (hτ2 : τ < 2) :
    fwdSumPsi A0 A1 D z τ ≤ fwdSumFixedTangent A0 A1 D z τ := by
  have hh := fwdSum_fixedTangent_remainder hτ hτ2 A0 A1 D z
  have hp : 0 ≤ (5*τ-1)^2*(-A0/τ+4*z/(243*(2-τ))) := by
    apply mul_nonneg (sq_nonneg _)
    exact add_nonneg (div_nonneg (neg_nonneg.mpr hA0) hτ.le)
      (div_nonneg (mul_nonneg (by norm_num) hz) (by positivity))
  linarith only [hh,hp]

/-- The actual paired logarithmic part of the fixed tangent. -/
noncomputable def fwdSumPairedLog (a k m : ℝ) : ℝ :=
  (a+k)/((1-a)*(1-k))*
    (((1-a)*(a+k)+2*a*(1+m*(1-a-k)))*fwdSumEll k-
      a*(1-a-k)*(m*(1-a)+2)*fwdSumJ a k)
/-- Its rational upper bound, with the reciprocal means replaced in opposite directions. -/
noncomputable def fwdSumPairedLogUpper (a k m : ℝ) : ℝ :=
  (a+k)/((1-a)*(1-k))*
    (((1-a)*(a+k)+2*a*(1+m*(1-a-k)))*(1+k/2+k^2/(3*(1-k)))-
      a*(1-a-k)*(m*(1-a)+2)*(1/2+(a+2*k)/3))

/-- All signs hold on the enlarged closed shape rectangle and the whole tangent interval. -/
theorem fwdSumPairedLog_le {a k m : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 ≤ k) (hk1 : k ≤ 1/5) (hm : -1 ≤ m) :
    fwdSumPairedLog a k m ≤ fwdSumPairedLogUpper a k m := by
  have hb : 0 < 1-a := by linarith
  have hr : 0 < 1-k := by linarith
  have hc : 0 ≤ a+k := by linarith
  have hcb : 0 < 1-a-k := by linarith
  have hmcb : a+k ≤ 1+m*(1-a-k) := by
    have hp := mul_nonneg (show 0 ≤ 1+m by linarith) hcb.le
    nlinarith only [hp]
  have hmb : 0 < m*(1-a)+2 := by
    have hp := mul_nonneg (show 0 ≤ 1+m by linarith) hb.le
    nlinarith only [ha,hp]
  have hu : 0 ≤ (1-a)*(a+k)+2*a*(1+m*(1-a-k)) :=
    add_nonneg (mul_nonneg hb.le hc)
      (mul_nonneg (mul_nonneg (by norm_num) ha) (le_trans hc hmcb))
  have hv : 0 ≤ a*(1-a-k)*(m*(1-a)+2) :=
    mul_nonneg (mul_nonneg ha hcb.le) hmb.le
  unfold fwdSumPairedLog fwdSumPairedLogUpper
  apply mul_le_mul_of_nonneg_left _ (div_nonneg hc (mul_nonneg hb.le hr.le))
  exact sub_le_sub
    (mul_le_mul_of_nonneg_left (fwdSumEll_le hk (by linarith)) hu)
    (mul_le_mul_of_nonneg_left (fwdSumJ_ge ha hk (by linarith)) hv)

/-- In the physical tangent interval m=9−25τ automatically has the required sign. -/
theorem fwdSumPairedLog_le_tangent {a k τ : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1/7) (hk : 0 ≤ k) (hk1 : k ≤ 1/5)
    (hτ : τ ≤ 2/5) :
    fwdSumPairedLog a k (9-25*τ) ≤ fwdSumPairedLogUpper a k (9-25*τ) :=
  fwdSumPairedLog_le ha ha1 hk hk1 (by linarith)


end SmoothedOctagon
