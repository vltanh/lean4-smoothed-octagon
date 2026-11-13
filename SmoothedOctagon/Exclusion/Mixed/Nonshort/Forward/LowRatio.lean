module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio.Bounds
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Clearing
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio.UnitShape
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio.Shape

/-!
# The duration ratio of a forward successor exceeds one third

The combined residual is negative at the exact incoming norm. Raising
that norm to its effective ceiling and the logarithm to its rational
ceiling preserves negativity. Shape monotonicity then lowers the shape
to one, where the residual is positive.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The low-ratio scalar exclusion**: for `1/4 < t ≤ 1/3`, `1 ≤ k < 2t + x`, the swap bound and
the incoming floor, the combined residual `nsfComb 6 0` cannot be negative. -/
theorem nsf_lowRatio_core {t x k q v F : ℝ} (ht0 : 1 / 4 < t) (ht1 : t ≤ 1 / 3) (hk1 : 1 ≤ k)
    (hko : k < 2 * t + x) (hx1 : x < 1) (hq : 1 < q)
    (hqs : q * (4 * t + 2 * x - 1) < 1 + x) (hv : v = nsrSecN t x)
    (hF : m2F ((t + x) / (1 + x)) q ≤ v) (hcomb : nsfComb 6 0 t x k q v (Real.log q) F < 0) :
    False := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hj : 1 < 2 * t + x := by linarith
  have hq0 : 0 < q := by linarith
  have hqo : q * (2 * t + x) ≤ 1 + x := by nlinarith
  have hCv := nsf_LR_Cv ht0.le ht1 (by linarith) hx1.le hk1 hq.le hqo
  have hCL : nsfCL 6 t x k q ≤ 0 := by
    unfold nsfCL
    have hJ : (t + x * (x + 2)) * q ^ 2 ≤ 7 * (1 + x) ^ 2 := by
      have h1 : q * (2 * t + x) ≤ 1 + x := hqo
      have h2 : q ^ 2 * (2 * t + x) ^ 2 ≤ (1 + x) ^ 2 := by nlinarith [mul_le_mul h1 h1 (by positivity) (by linarith)]
      have h3 : t + x * (x + 2) ≤ 7 * (2 * t + x) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg q)]
    have := nsrNL_nonpos (t := t) (x := x) (k := k) (q := q) (by linarith) hx.le hq0.le (by linarith)
    have h7 : 0 ≤ 4 * q * ((6 + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) := by
      apply mul_nonneg (by positivity); linarith
    exact mul_nonpos_of_nonneg_of_nonpos h7 this
  -- the rational substitutions
  have hVG := nsf_secN_lt_VG hx (by linarith : t < 1)
  rw [← hv] at hVG
  have hFl := nsr_m2F_gt_Fl hq (by linarith : 0 < t + x) hW
  have hLp := nsr_log_lt_Lp hq
  have hvh : v < nsfVhat t x q := by
    unfold nsfVhat
    have : 0 ≤ 3 / 4 * (q + 2 * t + x - 1) * (nsfVG t x - nsrFl t x q) := by
      apply mul_nonneg (by linarith); linarith
    linarith
  have e1 := nsf_comb_sub_v 6 0 t x k q (nsfVhat t x q) v (nsrLp q) 0
  have e2 := nsf_comb_sub_L 6 0 t x k q v (nsrLp q) (Real.log q) 0
  have e3 := nsf_comb_sub_F 6 0 t x k q v (Real.log q) 0 F
  have m1 : (nsfVhat t x q - v) * nsfCv 6 0 t x k q < 0 := mul_neg_of_pos_of_neg (by linarith) hCv
  have m2 : (nsrLp q - Real.log q) * nsfCL 6 t x k q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hCL
  have hG : nsfComb 6 0 t x k q (nsfVhat t x q) (nsrLp q) 0 < 0 := by
    have : (0 - F) * (4 * q * (1 + x) ^ 2 * 0) = 0 := by ring
    linarith
  have hfloor : nsrFl t x q ≤ nsfVG t x := hFl.le.trans (hF.trans hVG.le)
  have hy : q - 1 ≤ 1 - 2 * t := by
    have hp := mul_nonneg (show 0 ≤ q - 1 by linarith only [hq])
      (show 0 ≤ 2 * t + x - 1 by linarith only [hj])
    nlinarith only [hp, hqo]
  have hA := nlr_unit_pos ht0.le ht1 hj.le hq.le hy
  change 0 < nsfComb 6 0 t x 1 q (nsfVhat t x q) (nsrLp q) 0 at hA
  have hm := nlr_shape_mono ht0.le ht1 (by linarith only [hj]) hx1.le hq hqo hfloor hk1 hko.le
  linarith only [hG, hA, hm]

/-- **The duration ratio exceeds one third**: an actual forward window has `t > 1/3`. -/
theorem nsf_low_ratio (W : M2Window) (hF : W.ForwardNext) : 1 / 3 < W.nt := by
  by_contra h
  push Not at h
  obtain ⟨-, -, hx, hk1, hq, -, hv, -, -, hFl, -⟩ := nsr_window_basic W
  exact nsf_lowRatio_core (nsf_window_quarter W) h hk1.le (nsf_window_order W)
    (nsf_window_x_lt_one W) hq (by
      have := nsf_window_swap W
      have hden : 0 < 4 * W.nt + 2 * W.nx - 1 := by
        have := nsf_window_order W; have := nsf_window_quarter W; linarith
      rwa [lt_div_iff₀ hden] at this) hv hFl
    (nsf_window_comb W hF (α := 6) (M := 0) (by norm_num) le_rfl)

end SmoothedOctagon
