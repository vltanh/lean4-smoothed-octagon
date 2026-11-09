module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!
# Ordering weighted means on an interval

Centering at the base mean turns comparison of positive weights into the sign
of a single continuous integral. The ratio comparison excludes a vanishing
right endpoint and checks that endpoint after multiplication.
-/

@[expose] public section
namespace SmoothedOctagon
open Set MeasureTheory

/-- Compare a positive weight with another weight by centering at the latter's mean. -/
theorem ss_weighted_moment_lt {w v : ℝ → ℝ} {c k : ℝ}
    (hw : ContinuousOn w (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (hc : (∫ t in (0 : ℝ)..1, (t - c) * v t) = 0)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (t - c) * (w t - k * v t))
    (hp : ∃ t ∈ Icc (0 : ℝ) 1, 0 < (t - c) * (w t - k * v t)) :
    c * (∫ t in (0 : ℝ)..1, w t) < ∫ t in (0 : ℝ)..1, t * w t := by
  have hcv : ContinuousOn (fun t => (t - c) * v t) (Icc 0 1) :=
    (continuousOn_id.sub continuousOn_const).mul hv
  have hcw : ContinuousOn (fun t => (t - c) * w t) (Icc 0 1) :=
    (continuousOn_id.sub continuousOn_const).mul hw
  have hcc : ContinuousOn (fun t => (t - c) * (w t - k * v t)) (Icc 0 1) :=
    (continuousOn_id.sub continuousOn_const).mul (hw.sub (continuousOn_const.mul hv))
  have hpositive := intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1) hcc
    (fun t ht => hn t ⟨ht.1.le, ht.2⟩) hp
  have he : (fun t => (t - c) * (w t - k * v t)) =
      (fun t => (t - c) * w t - k * ((t - c) * v t)) := by funext t; ring
  rw [he, intervalIntegral.integral_sub (f := fun t : ℝ => (t - c) * w t)
    (g := fun t : ℝ => k * ((t - c) * v t)) (hcw.intervalIntegrable_of_Icc (by norm_num))
    ((continuousOn_const.mul hcv).intervalIntegrable_of_Icc (by norm_num)),
    intervalIntegral.integral_const_mul, hc, mul_zero, sub_zero] at hpositive
  have he' : (fun t => (t - c) * w t) = (fun t => t * w t - c * w t) := by funext t; ring
  rw [he', intervalIntegral.integral_sub (f := fun t : ℝ => t * w t) (g := fun t : ℝ => c * w t)
    ((continuousOn_id.mul hw).intervalIntegrable_of_Icc (by norm_num))
    ((continuousOn_const.mul hw).intervalIntegrable_of_Icc (by norm_num)),
    intervalIntegral.integral_const_mul] at hpositive
  linarith only [hpositive]

private theorem ssWeighted_cross_pos {w v : ℝ → ℝ} {c t : ℝ}
    (hc : c ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1)
    (hvt : 0 < v t)
    (hm : StrictMonoOn (fun s => w s / v s) (Ico (0 : ℝ) 1)) (hne : t ≠ c) :
    0 < (t - c) * (w t - w c / v c * v t) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hratio := hm ht hc h
    have hdiff : w t - w c / v c * v t < 0 := by
      have h' := (div_lt_iff₀ hvt).mp hratio
      linarith only [h']
    exact mul_pos_of_neg_of_neg (sub_neg.mpr h) hdiff
  · have hratio := hm hc ht h
    have hdiff : 0 < w t - w c / v c * v t := by
      have h' := (lt_div_iff₀ hvt).mp hratio
      linarith only [h']
    exact mul_pos (sub_pos.mpr h) hdiff

/-- An increasing weight ratio raises the mean; the right endpoint may have zero base weight. -/
theorem ss_weighted_moment_of_strictMono {w v : ℝ → ℝ} {c : ℝ}
    (hw : ContinuousOn w (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (hc0 : 0 < c) (hc1 : c < 1)
    (hvc : ∀ t ∈ Ico (0 : ℝ) 1, 0 < v t) (hv1 : v 1 = 0) (hw1 : 0 ≤ w 1)
    (hc : (∫ t in (0 : ℝ)..1, (t - c) * v t) = 0)
    (hm : StrictMonoOn (fun t => w t / v t) (Ico (0 : ℝ) 1)) :
    c * (∫ t in (0 : ℝ)..1, w t) < ∫ t in (0 : ℝ)..1, t * w t := by
  have hcI : c ∈ Ico (0 : ℝ) 1 := ⟨hc0.le, hc1⟩
  refine ss_weighted_moment_lt (k := w c / v c) hw hv hc ?_ ?_
  · intro t ht
    rcases eq_or_lt_of_le ht.2 with he | he
    · subst t
      simpa only [hv1, mul_zero, sub_zero] using mul_nonneg (sub_nonneg.mpr hc1.le) hw1
    · by_cases htc : t = c
      · subst t; simp only [sub_self, zero_mul, le_refl]
      · exact (ssWeighted_cross_pos hcI ⟨ht.1, he⟩ (hvc t ⟨ht.1, he⟩) hm htc).le
  · have htI : (c + 1) / 2 ∈ Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    refine ⟨(c + 1) / 2, ⟨htI.1, htI.2.le⟩, ?_⟩
    exact ssWeighted_cross_pos hcI htI (hvc _ htI) hm (by linarith)

/-- A decreasing factor gives a negative centered first moment. -/
theorem ss_weighted_moment_of_strictAnti_factor {w v r : ℝ → ℝ} {c : ℝ}
    (hw : ContinuousOn w (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (hc0 : 0 < c) (hc1 : c < 1)
    (hvn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ v t) (hvp : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < v t)
    (hfac : ∀ t ∈ Icc (0 : ℝ) 1, w t = v t * r t)
    (hm : StrictAntiOn r (Icc (0 : ℝ) 1))
    (hc : (∫ t in (0 : ℝ)..1, (t - c) * v t) = 0) :
    (∫ t in (0 : ℝ)..1, t * w t) < c * (∫ t in (0 : ℝ)..1, w t) := by
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hc0.le, hc1.le⟩
  have he : ∀ t ∈ Icc (0 : ℝ) 1,
      (t - c) * (-w t - -r c * v t) = (c - t) * (r t - r c) * v t := by
    intro t ht
    rw [hfac t ht]
    ring
  have hcross : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ (t - c) * (-w t - -r c * v t) := by
    intro t ht
    rw [he t ht]
    rcases lt_trichotomy t c with h | h | h
    · have hdiff : 0 < r t - r c := sub_pos.mpr (hm ht hcI h)
      exact mul_nonneg (mul_nonneg (by linarith) hdiff.le) (hvn t ht)
    · rw [h]; simp only [sub_self, zero_mul, le_refl]
    · have hdiff : r t - r c < 0 := sub_neg.mpr (hm hcI ht h)
      exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) hdiff.le) (hvn t ht)
  have hstrict : ∃ t ∈ Icc (0 : ℝ) 1, 0 < (t - c) * (-w t - -r c * v t) := by
    let t := (c + 1) / 2
    have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have htc : c < t := by dsimp [t]; linarith
    refine ⟨t, htI, ?_⟩
    rw [he t htI]
    exact mul_pos (mul_pos_of_neg_of_neg (sub_neg.mpr htc) (sub_neg.mpr (hm hcI htI htc))) (hvp t ht)
  have h := ss_weighted_moment_lt (w := fun t => -w t) (k := -r c) hw.neg hv hc hcross hstrict
  simp only [mul_neg, intervalIntegral.integral_neg] at h
  linarith only [h]

end SmoothedOctagon
