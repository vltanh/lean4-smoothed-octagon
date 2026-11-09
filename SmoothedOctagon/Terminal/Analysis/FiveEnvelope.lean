module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.LinearCombination

/-!
# The five-piece logarithmic envelope

With `h(t) = -2t log t/(1 - t) - log(1 + t)` on `(0, 1)`:

* `ra_fiveH`: the function `h`.
* `ra_fiveH_deriv_div_integral`: the normalized derivative is an integral of a positive kernel.
* `ra_fiveH_strictConcaveOn`: `x ↦ h(√x)` is strictly concave on `(0, 1)`.
* `ra_fiveH_concaveOn`: its concavity corollary.
* `ra_fiveH_circle_eq_iff`: equality in the circle bound holds exactly when `a = b`.
* `ra_fiveH_circle_le`: `h(a) + h(b) ≤ 2 h(√2/2)` for `a, b > 0`, `a² + b² = 1` (two-point Jensen).
* `ra_five_envelope`: for `0 < t < 1`, with
  `F(t) = ((1+t)/(1-t))² log((1+t²)/(2t)) + t⁻² log((1+t²)/(1-t²)) + log(2t/(1-t²))`,
  `F(t) + 2 log(1 - t) ≤ (3 + 2√2) log 2 + 2 log(2 - √2)`, through the identity
  `F(t) + 2 log(1 - t) = log 2 + h(α) + h(β)`, `α = 2t/(1 + t²)`, `β = (1 - t²)/(1 + t²)`, and
  `α² + β² = 1`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real MeasureTheory

/-- `h(t) = -2t log t/(1 - t) - log(1 + t)`. -/
noncomputable def ra_fiveH (t : ℝ) : ℝ := -2 * t * Real.log t / (1 - t) - Real.log (1 + t)

/-- Kernel of the logarithmic remainder. -/
noncomputable def fiveRemKernel (t s : ℝ) := s/(1-s+s*t)
/-- Positive kernel for the normalized derivative of `ra_fiveH`. -/
noncomputable def fiveHKernel (t s : ℝ) :=
  s/(1+t)*((1-s+s/t)/(1-s+s*t))
/-- The first derivative of `ra_fiveH` on `(0, 1)`. -/
noncomputable def fiveHD (t : ℝ) := 2*(t-1-log t)/(1-t)^2-1/(1+t)

private lemma five_den_pos {t s : ℝ} (ht : 0 < t) (hs : s ∈ Icc 0 1) :
    0 < 1-s+s*t := by
  rcases eq_or_lt_of_le hs.1 with rfl | hsp
  · norm_num
  · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr hs.2) (mul_pos hsp ht)
private lemma five_rem_cont {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fiveRemKernel t) (Icc 0 1) := by
  apply continuousOn_id.div
    ((continuousOn_const.sub continuousOn_id).add (continuousOn_id.mul continuousOn_const))
  intro s hs
  exact (five_den_pos ht hs).ne'
private lemma five_hkernel_cont {t : ℝ} (ht : 0 < t) :
    ContinuousOn (fiveHKernel t) (Icc 0 1) := by
  have hn : ContinuousOn (fun s : ℝ => 1-s+s/t) (Icc 0 1) :=
    (continuousOn_const.sub continuousOn_id).add (continuousOn_id.div_const t)
  exact (continuousOn_id.div_const (1+t)).mul
    (hn.div ((continuousOn_const.sub continuousOn_id).add
      (continuousOn_id.mul continuousOn_const)) (fun s hs => (five_den_pos ht hs).ne'))

/-- Logarithmic remainder identity for `t > 0`, including `t = 1`. -/
theorem ra_five_log_remainder_integral {t : ℝ} (ht : 0 < t) :
    t-1-log t = (1-t)^2*(∫ s in (0:ℝ)..1, fiveRemKernel t s) := by
  by_cases ht1 : t = 1
  · subst t; simp
  let P := fun s : ℝ => ((t-1)*s-log (1-s+s*t))/(1-t)^2
  have hP : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt P (fiveRemKernel t s) s := by
    intro s hs
    have hd := five_den_pos ht hs
    have hD := ((hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id' s)).add
      ((hasDerivAt_id' s).mul_const t)
    have h := (((hasDerivAt_id' s).const_mul (t-1)).sub (hD.log hd.ne')).div_const ((1-t)^2)
    refine h.congr_deriv ?_
    unfold fiveRemKernel
    change ((t-1)*1-(0-1+1*t)/(1-s+s*t))/(1-t)^2 = s/(1-s+s*t)
    field_simp [hd.ne',sub_ne_zero.mpr (Ne.symm ht1)]
    ring_nf
    field_simp [show 1+t*s-s ≠ 0 by nlinarith only [hd]]
    ring
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hP s (by simpa using hs))
    ((five_rem_cont ht).intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1))
  dsimp [P] at hI
  norm_num at hI
  have hm : (1-t)^2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm ht1))
  rw [eq_div_iff hm] at hI
  linarith only [hI]

/-- First derivative of the five-piece function. -/
theorem ra_fiveH_hasDerivAt {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt ra_fiveH (fiveHD t) t := by
  have h := ((((hasDerivAt_id' t).const_mul (-2)).mul (Real.hasDerivAt_log ht.ne')).div
    ((hasDerivAt_id' t).const_sub 1) (by linarith : (1:ℝ)-t ≠ 0)).sub
    (((hasDerivAt_id' t).const_add 1).log (by linarith : (1:ℝ)+t ≠ 0))
  convert h using 1
  · rfl
  · unfold fiveHD
    dsimp only [Pi.mul_apply]
    field_simp
    ring

/-- Integral representation of the normalized derivative. -/
theorem ra_fiveHD_div_integral {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    fiveHD t/t = 2*(∫ s in (0:ℝ)..1, fiveHKernel t s) := by
  have hr := ra_five_log_remainder_integral ht
  have heq : ∀ s ∈ Icc (0:ℝ) 1, fiveHKernel t s = (1/t)*fiveRemKernel t s-(1/(t*(1+t)))*s := by
    intro s hs
    have hd := five_den_pos ht hs
    unfold fiveHKernel fiveRemKernel
    field_simp [ht.ne',hd.ne',show 1+t ≠ 0 by positivity]
    ring
  have hInt : (∫ s in (0:ℝ)..1, fiveHKernel t s) =
      ∫ s in (0:ℝ)..1, (1/t)*fiveRemKernel t s-(1/(t*(1+t)))*s :=
    intervalIntegral.integral_congr (fun s hs => heq s (by simpa using hs))
  have hc1 := (five_rem_cont ht).const_mul (1/t)
  have hc2 : ContinuousOn (fun s : ℝ => (1/(t*(1+t)))*s) (Icc 0 1) :=
    continuousOn_const.mul continuousOn_id
  rw [hInt,intervalIntegral.integral_sub
    (hc1.intervalIntegrable_of_Icc (by norm_num)) (hc2.intervalIntegrable_of_Icc (by norm_num)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,integral_id]
  have hI : (∫ s in (0:ℝ)..1, fiveRemKernel t s) = (t-1-log t)/(1-t)^2 := by
    rw [eq_div_iff (pow_ne_zero 2 (by linarith only [ht1]))]
    linarith only [hr]
  rw [hI]
  unfold fiveHD
  have hmt : 1-t ≠ 0 := by linarith only [ht1]
  field_simp [ht.ne',hmt,show 1+t ≠ 0 by positivity]
  ring


private lemma five_kernel_strictAnti {a b s : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a < b) (hs : s ∈ Ioc (0:ℝ) 1) : fiveHKernel b s < fiveHKernel a s := by
  have hna : 0 < 1-s+s/a := add_pos_of_nonneg_of_pos (sub_nonneg.mpr hs.2) (div_pos hs.1 ha)
  have hnb : 0 < 1-s+s/b := add_pos_of_nonneg_of_pos (sub_nonneg.mpr hs.2) (div_pos hs.1 hb)
  have hda := five_den_pos ha ⟨hs.1.le,hs.2⟩
  have hdb := five_den_pos hb ⟨hs.1.le,hs.2⟩
  have hnlt : 1-s+s/b < 1-s+s/a := by
    have hr : s/b < s/a := by
      rw [div_lt_div_iff₀ hb ha]
      nlinarith only [mul_pos hs.1 (sub_pos.mpr hab)]
    linarith only [hr]
  have hdlt : (1+a)*(1-s+s*a) < (1+b)*(1-s+s*b) := by
    have hbump := mul_pos hs.1 (sub_pos.mpr hab)
    exact mul_lt_mul (by linarith only [hab]) (by nlinarith only [hbump]) hda (by positivity)
  have hdiv : (1-s+s/b)/((1+b)*(1-s+s*b)) <
      (1-s+s/a)/((1+a)*(1-s+s*a)) := by
    exact lt_trans (div_lt_div_of_pos_right hnlt (by positivity))
      (div_lt_div_of_pos_left hna (by positivity) hdlt)
  have hmul := mul_lt_mul_of_pos_left hdiv hs.1
  convert hmul using 1 <;> unfold fiveHKernel <;>
    field_simp [ha.ne',hb.ne',hda.ne',hdb.ne',
      show 1+a ≠ 0 by positivity,show 1+b ≠ 0 by positivity]

/-- The normalized derivative is strictly decreasing by its positive integral kernel. -/
theorem ra_fiveHD_div_strictAntiOn : StrictAntiOn (fun t => fiveHD t/t) (Ioo 0 1) := by
  intro a ha b hb hab
  have hI : (∫ s in (0:ℝ)..1, fiveHKernel b s) < ∫ s in (0:ℝ)..1, fiveHKernel a s := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt (by norm_num)
      (five_hkernel_cont hb.1) (five_hkernel_cont ha.1)
    · intro s hs
      exact (five_kernel_strictAnti ha.1 hb.1 hab hs).le
    · exact ⟨1,by norm_num,five_kernel_strictAnti ha.1 hb.1 hab (by norm_num)⟩
  change fiveHD b/b < fiveHD a/a
  rw [ra_fiveHD_div_integral ha.1 ha.2,ra_fiveHD_div_integral hb.1 hb.2]
  linarith only [hI]

/-- Integral representation of `h'(t)/t`. -/
theorem ra_fiveH_deriv_div_integral {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    deriv ra_fiveH t/t = 2*(∫ s in (0:ℝ)..1, fiveHKernel t s) := by
  rw [(ra_fiveH_hasDerivAt ht ht1).deriv]
  exact ra_fiveHD_div_integral ht ht1

/-- The normalized derivative decreases strictly by the positive kernel. -/
theorem ra_fiveH_deriv_div_strictAntiOn :
    StrictAntiOn (fun t => deriv ra_fiveH t/t) (Ioo 0 1) := by
  intro a ha b hb hab
  change deriv ra_fiveH b/b < deriv ra_fiveH a/a
  rw [(ra_fiveH_hasDerivAt ha.1 ha.2).deriv,
    (ra_fiveH_hasDerivAt hb.1 hb.2).deriv]
  exact ra_fiveHD_div_strictAntiOn ha hb hab

/-- Chain rule for `ra_fiveH` composed with the square root. -/
theorem ra_fiveH_sqrt_hasDerivAt {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => ra_fiveH (sqrt x)) ((fiveHD (sqrt x)/sqrt x)/2) x := by
  have hs : 0 < sqrt x := sqrt_pos.2 hx
  have hs1 : sqrt x < 1 := by rw [sqrt_lt' one_pos]; linarith only [hx1]
  have h := (ra_fiveH_hasDerivAt hs hs1).comp x (Real.hasDerivAt_sqrt hx.ne')
  convert h using 1
  · rfl
  · field_simp

/-- The derivative of `h(√x)` decreases strictly on `(0, 1)`. -/
theorem ra_fiveH_sqrt_deriv_strictAntiOn :
    StrictAntiOn (deriv (fun x => ra_fiveH (sqrt x))) (Ioo 0 1) := by
  intro x hx y hy hxy
  rw [(ra_fiveH_sqrt_hasDerivAt hx.1 hx.2).deriv,(ra_fiveH_sqrt_hasDerivAt hy.1 hy.2).deriv]
  have hsx : sqrt x ∈ Ioo (0:ℝ) 1 :=
    ⟨sqrt_pos.2 hx.1,by rw [sqrt_lt' one_pos]; linarith only [hx.2]⟩
  have hsy : sqrt y ∈ Ioo (0:ℝ) 1 :=
    ⟨sqrt_pos.2 hy.1,by rw [sqrt_lt' one_pos]; linarith only [hy.2]⟩
  have h := ra_fiveHD_div_strictAntiOn hsx hsy (sqrt_lt_sqrt hx.1.le hxy)
  linarith only [h]

/-- Strict concavity of `h(√x)` from its integral derivative. -/
theorem ra_fiveH_strictConcaveOn :
    StrictConcaveOn ℝ (Ioo 0 1) (fun x => ra_fiveH (sqrt x)) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioo 0 1)
  · exact fun x hx => (ra_fiveH_sqrt_hasDerivAt hx.1 hx.2).continuousAt.continuousWithinAt
  · rw [interior_Ioo]
    exact ra_fiveH_sqrt_deriv_strictAntiOn

/-- Concavity follows from strict concavity. -/
theorem ra_fiveH_concaveOn :
    ConcaveOn ℝ (Ioo 0 1) (fun x => ra_fiveH (sqrt x)) :=
  ra_fiveH_strictConcaveOn.concaveOn

/-- Strict two-point inequality for distinct positive coordinates on the unit circle. -/
theorem ra_fiveH_circle_lt {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a^2+b^2 = 1) (hne : a ≠ b) :
    ra_fiveH a+ra_fiveH b < 2*ra_fiveH (sqrt 2/2) := by
  have ha2 : a^2 ∈ Ioo (0:ℝ) 1 := ⟨by positivity,by nlinarith only [hab,sq_pos_of_pos hb]⟩
  have hb2 : b^2 ∈ Ioo (0:ℝ) 1 := ⟨by positivity,by nlinarith only [hab,sq_pos_of_pos ha]⟩
  have hne2 : a^2 ≠ b^2 := fun h => hne ((sq_eq_sq₀ ha.le hb.le).mp h)
  have h := ra_fiveH_strictConcaveOn.2 ha2 hb2 hne2
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1/2:ℝ)+1/2 = 1)
  simp only [smul_eq_mul,sqrt_sq ha.le,sqrt_sq hb.le] at h
  have hmid : 1/2*a^2+1/2*b^2 = (sqrt 2/2)^2 := by
    rw [div_pow,sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    linarith only [hab]
  rw [hmid,sqrt_sq (by positivity)] at h
  linarith only [h]

private lemma five_circle_equal {a b : ℝ} (ha : 0 < a) (_hb : 0 < b)
    (hab : a^2+b^2 = 1) (he : a = b) : a = sqrt 2/2 := by
  apply (sq_eq_sq₀ ha.le (by positivity : (0:ℝ) ≤ sqrt 2/2)).mp
  rw [div_pow,sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [← he] at hab
  linarith only [hab]

/-- Two-point Jensen inequality on the positive unit circle. -/
theorem ra_fiveH_circle_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a^2+b^2 = 1) : ra_fiveH a+ra_fiveH b ≤ 2*ra_fiveH (sqrt 2/2) := by
  by_cases he : a = b
  · have hc := five_circle_equal ha hb hab he
    rw [← he,hc]
    linarith
  · exact (ra_fiveH_circle_lt ha hb hab he).le

/-- Equality holds precisely at the equal positive coordinates. -/
theorem ra_fiveH_circle_eq_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a^2+b^2 = 1) :
    ra_fiveH a+ra_fiveH b = 2*ra_fiveH (sqrt 2/2) ↔ a = b := by
  constructor
  · intro he
    by_contra hne
    exact (ne_of_lt (ra_fiveH_circle_lt ha hb hab hne)) he
  · intro he
    have hc := five_circle_equal ha hb hab he
    rw [← he,hc]
    ring

/-- The maximal value: `log 2 + 2 h(√2/2) = (3 + 2√2) log 2 + 2 log(2 - √2)`. -/
private lemma fiveH_max_value :
    Real.log 2 + 2 * ra_fiveH (√2 / 2) = (3 + 2 * √2) * Real.log 2 + 2 * Real.log (2 - √2) := by
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < √2 := by positivity
  have hslt : √2 < 2 := by nlinarith
  have hlog : Real.log (√2 / 2) = -(Real.log 2 / 2) := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]
    ring
  have hplus : Real.log (1 + √2 / 2) = Real.log (2 + √2) - Real.log 2 := by
    rw [show 1 + √2 / 2 = (2 + √2) / 2 by ring, Real.log_div (by positivity) (by norm_num)]
  have hminus : Real.log (2 - √2) = Real.log 2 - Real.log (2 + √2) := by
    rw [show 2 - √2 = 2 / (2 + √2) by
      field_simp
      linear_combination -hs2, Real.log_div (by norm_num) (by positivity)]
  have hq : -2 * (√2 / 2) * -(Real.log 2 / 2) / (1 - √2 / 2) = (1 + √2) * Real.log 2 := by
    rw [div_eq_iff (by linarith)]
    linear_combination (Real.log 2 / 2) * hs2
  rw [ra_fiveH, hlog, hplus, hminus, hq]
  ring

/-- `F(t) + 2 log(1 - t) = log 2 + h(α) + h(β)`, `α = 2t/(1 + t²)`, `β = (1 - t²)/(1 + t²)`. -/
private lemma five_identity {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ((1 + t) / (1 - t)) ^ 2 * Real.log ((1 + t ^ 2) / (2 * t)) +
        Real.log ((1 + t ^ 2) / (1 - t ^ 2)) / t ^ 2 + Real.log (2 * t / (1 - t ^ 2)) +
        2 * Real.log (1 - t) =
      Real.log 2 + ra_fiveH (2 * t / (1 + t ^ 2)) + ra_fiveH ((1 - t ^ 2) / (1 + t ^ 2)) := by
  have hm : 0 < 1 - t := by linarith
  have hp : 0 < 1 + t := by linarith
  have hq : 0 < 1 + t ^ 2 := by positivity
  have hmp : 1 - t ^ 2 = (1 - t) * (1 + t) := by ring
  have hm2 : 0 < 1 - t ^ 2 := by rw [hmp]; positivity
  have l1 : Real.log ((1 + t ^ 2) / (2 * t)) =
      Real.log (1 + t ^ 2) - (Real.log 2 + Real.log t) := by
    rw [Real.log_div hq.ne' (by positivity), Real.log_mul (by norm_num) ht0.ne']
  have l2 : Real.log ((1 + t ^ 2) / (1 - t ^ 2)) =
      Real.log (1 + t ^ 2) - (Real.log (1 - t) + Real.log (1 + t)) := by
    rw [Real.log_div hq.ne' hm2.ne', hmp, Real.log_mul hm.ne' hp.ne']
  have l3 : Real.log (2 * t / (1 - t ^ 2)) =
      Real.log 2 + Real.log t - (Real.log (1 - t) + Real.log (1 + t)) := by
    rw [Real.log_div (by positivity) hm2.ne', hmp, Real.log_mul hm.ne' hp.ne',
      Real.log_mul (by norm_num) ht0.ne']
  have l4 : Real.log (2 * t / (1 + t ^ 2)) = Real.log 2 + Real.log t - Real.log (1 + t ^ 2) := by
    rw [Real.log_div (by positivity) hq.ne', Real.log_mul (by norm_num) ht0.ne']
  have l5 : Real.log (1 + 2 * t / (1 + t ^ 2)) = 2 * Real.log (1 + t) - Real.log (1 + t ^ 2) := by
    rw [show 1 + 2 * t / (1 + t ^ 2) = (1 + t) ^ 2 / (1 + t ^ 2) by field_simp; ring,
      Real.log_div (by positivity) hq.ne', Real.log_pow]
    push_cast
    ring
  have l6 : Real.log ((1 - t ^ 2) / (1 + t ^ 2)) =
      Real.log (1 - t) + Real.log (1 + t) - Real.log (1 + t ^ 2) := by
    rw [Real.log_div hm2.ne' hq.ne', hmp, Real.log_mul hm.ne' hp.ne']
  have l7 : Real.log (1 + (1 - t ^ 2) / (1 + t ^ 2)) = Real.log 2 - Real.log (1 + t ^ 2) := by
    rw [show 1 + (1 - t ^ 2) / (1 + t ^ 2) = 2 / (1 + t ^ 2) by field_simp; ring,
      Real.log_div (by norm_num) hq.ne']
  have d1 : 1 - 2 * t / (1 + t ^ 2) = (1 - t) ^ 2 / (1 + t ^ 2) := by field_simp; ring
  have d2 : 1 - (1 - t ^ 2) / (1 + t ^ 2) = 2 * t ^ 2 / (1 + t ^ 2) := by field_simp; ring
  rw [ra_fiveH, ra_fiveH, l1, l2, l3, l4, l5, l6, l7, d1, d2]
  field_simp
  ring

/-- **The five-piece envelope**: for `0 < t < 1`,
`F(t) + 2 log(1 - t) ≤ (3 + 2√2) log 2 + 2 log(2 - √2)`. By `five_identity` the left side is
`log 2 + h(α) + h(β)` with `α² + β² = 1`, and two-point Jensen bounds it by `log 2 + 2 h(√2/2)`. -/
theorem ra_five_envelope {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ((1 + t) / (1 - t)) ^ 2 * Real.log ((1 + t ^ 2) / (2 * t)) +
        Real.log ((1 + t ^ 2) / (1 - t ^ 2)) / t ^ 2 + Real.log (2 * t / (1 - t ^ 2)) +
        2 * Real.log (1 - t) ≤
      (3 + 2 * √2) * Real.log 2 + 2 * Real.log (2 - √2) := by
  rw [five_identity ht0 ht1, ← fiveH_max_value]
  have hq : 0 < 1 + t ^ 2 := by positivity
  have hm2 : 0 < 1 - t ^ 2 := by nlinarith
  have hcirc : (2 * t / (1 + t ^ 2)) ^ 2 + ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 = 1 := by
    field_simp
    ring
  have := ra_fiveH_circle_le (by positivity) (by positivity) hcirc
  linarith

end SmoothedOctagon
