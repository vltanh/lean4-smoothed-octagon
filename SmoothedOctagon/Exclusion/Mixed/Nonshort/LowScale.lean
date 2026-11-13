module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Core
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.Clearing

/-!
# The reverse successor in the low-scale region

The reciprocal-mean ceiling bounds `t` by a decreasing function of `x`.
The scale inequality then gives `t<3/8`. Above the order boundary,
shape monotonicity reduces the residual to the unit face or to
`k=2t+1/2`. Supporting lines prove the unit-face quartic positive;
monotone transport gives the other face.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Positivity of the relaxed quartic implies positivity of the exact residual. -/
theorem nsr_low_relax {t x k q v : ℝ} (ht : 0 < t) (ht1 : t < 1) (hx : 0 < x) (hk : 2 * t ≤ k)
    (hq : 1 < q) (hv : v = nsrSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v)
    (hP : 0 < 12 * (q + 1) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) *
      (nsrN t x k q (nsrVJensen t x) (nsrLp q)
        - (-nsrNv t x k q) * (nsrVJensen t x - nsrFl t x q))) :
    0 < nsrN t x k q v (Real.log q) := by
  have hpos : 0 < 12 * (q + 1) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) := by
    have : 0 < q + 1 := by linarith only [hq]
    positivity
  have hNv := nsrNv_nonpos ht.le hx.le hq.le hk
  refine nsr_N_pos_of_relax (vb := nsrVJensen t x) (Lb := nsrLp q) (Fl := nsrFl t x q)
    (m := -nsrNv t x k q) ?_ (nsr_log_lt_Lp hq).le hNv
    (nsrNL_nonpos ht.le hx.le (by linarith only [hq]) (by linarith only [hk, ht]))
    ((nsr_m2F_gt_Fl hq (by linarith only [ht, hx]) (by linarith only [hx])).le.trans hF)
    (by linarith only [hNv]) (pos_of_mul_pos_right hP hpos.le)
  rw [hv]
  exact (nsr_secN_lt_jensen hx ht1).le

/-- The feasible unit low-scale face lies above the order boundary. -/
theorem nsr_low_unit {t x q v : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 4) (hx0 : 1 / 2 ≤ x)
    (hxt : 1 ≤ 2 * t + x) (hq : 1 < q) (hv : v = nsrSecN t x)
    (hF : m2F ((t + x) / (1 + x)) q ≤ v) : 0 < nsrN t x 1 q v (Real.log q) := by
  have hx : 0 < x := by linarith only [hx0]
  have hg := (nsr_floor_gt_g hx hxt hq).le.trans hF
  have hT := nsr_t_lt_jensen_T (by linarith only [ht1]) hx hv hg
  have hx7 : x ≤ 7 / 3 := by
    by_contra h
    have hr := nsr_jensen_T_anti (a := 7 / 3) (by norm_num) (le_of_lt (lt_of_not_ge h)) hT.le
    norm_num at hr
    linarith only [ht, hr]
  refine nsr_low_relax ht (by linarith only [ht1]) hx (by linarith only [ht1]) hq hv hF ?_
  rw [LowScale.unit_eq hx (by linarith only [hq])]
  exact LowScale.unit_quartic_pos ht.le ht1 hx0 hx7 hT.le (by linarith only [hq])

/-- The increasing-shape low-scale face follows from the common quarter-scale boundary. -/
theorem nsr_low_kh {t x q v : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 3 / 8) (hx0 : 1 / 2 ≤ x)
    (hq : 1 < q) (hv : v = nsrSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nsrN t x (2 * t + 1 / 2) q v (Real.log q) := by
  have hx : 0 < x := by linarith only [hx0]
  have hg := (nsr_floor_gt_g hx (by linarith only [ht0, hx0]) hq).le.trans hF
  have hT := nsr_t_lt_jensen_T (by linarith only [ht1]) hx hv hg
  have hx1 : x ≤ 1 := by
    by_contra h
    have hr := nsr_jensen_T_anti (a := 1) (by norm_num) (le_of_lt (lt_of_not_ge h)) hT.le
    norm_num at hr
    linarith only [ht0, hr]
  refine nsr_low_relax (by linarith only [ht0]) (by linarith only [ht1]) hx (by norm_num) hq hv hF ?_
  rw [LowScale.high_eq hx (by linarith only [hq])]
  exact LowScale.high_quartic_pos ht0 ht1 hx0 hx1 hT.le (by linarith only [hq])

/-- The scalar low-scale exclusion on the necessary domain with `k≥17t²`. -/
theorem nsr_low_core {t x k q v : ℝ} (ht : 0 < t) (ht2 : t < 1 / 2) (hx : 0 < x) (hk1 : 1 ≤ k)
    (hk17 : 17 * t ^ 2 ≤ k) (hgap : k < 2 * t + 2 * x + x ^ 2) (hdur : x < 7 / 3 - 10 / 3 * t)
    (hq : 1 < q) (hqW : q < (1 + x) / (t + x)) (hv : v = nsrSecN t x) (hvU : v ≤ 1 - t + t ^ 2)
    (hg : 1 - (1 - t) * (t + x) / (1 + x) ^ 2 ≤ v) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nsrN t x k q v (Real.log q) := by
  have ht3 := nsr_low_t_three_eighths ht2 hx hk17 hgap hv hg
  by_cases hko : 2 * t + x ≤ k
  · exact nsr_reverse_core ht (by linarith only [ht3]) hx hk1 hko (by nlinarith only [hk17])
      hgap hdur hq hqW hv hvU hF
  have hko : k < 2 * t + x := lt_of_not_ge hko
  have hL : Real.log q < q - 1 := Real.log_lt_sub_one_of_pos (by linarith only [hq]) hq.ne'
  have mono : ∀ k', k' ≤ k → nsrN t x k' q v (Real.log q) ≤ nsrN t x k q v (Real.log q) :=
    fun k' hk' => nsrN_mono_k ht (by linarith only [ht2]) hx hq.le hvU hL hk'
  rcases le_total t (1 / 4) with h4 | h4
  · exact (nsr_low_unit ht h4 (by linarith only [hk1, hko, h4])
      (by linarith only [hk1, hko]) hq hv hF).trans_le (mono 1 hk1)
  · have hkh : 2 * t + 1 / 2 ≤ k := by nlinarith only [h4, hk17]
    have hxhalf : 1 / 2 ≤ x := by linarith only [hkh, hko]
    exact (nsr_low_kh h4 ht3.le hxhalf hq hv hF).trans_le (mono _ hkh)

end SmoothedOctagon
