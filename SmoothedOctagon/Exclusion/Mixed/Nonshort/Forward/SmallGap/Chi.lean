module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.ChiEndpoint

/-!
# Case M2, forward successor: the ratio `χ` on the small-gap domain

The residual increases with the shape, so it suffices to take unit shape.
Raise the incoming secant to `V₂`. The resulting residual is concave in
`q` on `[1, 8/7]` and positive at both ends of `[1, 4W/(7p)]`.
This excludes `χ = pq/W ≤ 4/7`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The forward ratio exceeds `4/7`**: `7pq > 4W` on the small-gap domain. -/
theorem nsf_chi_core {t x k q v : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 19 / 50) (hj0 : 0 ≤ 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk : 1 ≤ k) (hq : 1 < q) (hv : v = nsrSecN t x)
    (hvU : v ≤ 1 - t + t ^ 2) (hN : nsrN t x k q v (Real.log q) < 0) :
    4 * (1 + x) < 7 * (t + x) * q := by
  by_contra hc
  push Not at hc
  have hx : 0 < x := by linarith only [ht1, hj0]
  have hp : 0 < t + x := by linarith only [ht0, hx]
  have hW : 0 < 1 + x := by positivity
  have ht2 : t ≤ 2 / 5 := by linarith only [ht1]
  have hq0 : 0 < q := by linarith only [hq]
  have hL : Real.log q < q - 1 := Real.log_lt_sub_one_of_pos hq0 hq.ne'
  have hmono := nsrN_mono_k (k := 1) (k' := k) (by linarith only [ht0])
    (by linarith only [ht1]) hx hq.le hvU hL hk
  have hV2 : v < nsfV2 t x := by
    rw [hv]
    exact nsf_secN_lt_V2 hx (by linarith only [ht1])
  have hNv := nsrNv_nonpos (t := t) (x := x) (k := 1) (q := q)
    (by linarith only [ht0]) hx.le hq.le (by linarith only [ht1])
  have hraise := mul_nonneg_of_nonpos_of_nonpos (show v - nsfV2 t x ≤ 0 by linarith only [hV2]) hNv
  have hrelax := nsrN_sub_v t x 1 q v (nsfV2 t x) (Real.log q)
  let Q := 4 * (1 + x) / (7 * (t + x))
  have hQ : 1 < Q := by
    dsimp [Q]
    rw [lt_div_iff₀ (by positivity : 0 < 7 * (t + x))]
    nlinarith only [ht1, hj1]
  have hQcap : Q ≤ 8 / 7 := by
    dsimp [Q]
    rw [div_le_iff₀ (by positivity : 0 < 7 * (t + x))]
    nlinarith only [hj0]
  have hqQ : q ≤ Q := (le_div_iff₀ (by positivity : 0 < 7 * (t + x))).mpr (by nlinarith only [hc])
  have hleft : 0 < nsrN t x 1 1 (nsfV2 t x) (Real.log 1) := by
    simpa only [Real.log_one] using nsf_chi_left ht0 ht2 hj0 hj1
  have hright : 0 < nsrN t x 1 Q (nsfV2 t x) (Real.log Q) := by
    have hpos := nsf_chi_right ht0 ht1 hj0 hj1
    have hLp := nsr_log_lt_Lp hQ
    have hNL := nsrNL_nonpos (t := t) (x := x) (k := 1) (q := Q)
      (by linarith only [ht0]) hx.le (by linarith only [hQ]) (by norm_num)
    have hlog := mul_nonneg_of_nonpos_of_nonpos (show Real.log Q - nsrLp Q ≤ 0 by linarith only [hLp]) hNL
    have heq := nsrN_sub_L t x 1 Q (nsfV2 t x) (Real.log Q) (nsrLp Q)
    change 0 < nsrN t x 1 Q (nsfV2 t x) (nsrLp Q) at hpos
    linarith only [hpos, hlog, heq]
  have hconcave := nsf_chi_concave ht0 ht2 hj0 (nsf_chi_V2_ge ht2 hj0 hj1)
  have hmin := hconcave.min_le_of_mem_Icc (by norm_num : (1 : ℝ) ∈ Set.Icc 1 (8 / 7))
    (show Q ∈ Set.Icc 1 (8 / 7) from ⟨hQ.le, hQcap⟩) (show q ∈ Set.Icc 1 Q from ⟨hq.le, hqQ⟩)
  have hpos := (lt_min hleft hright).trans_le hmin
  linarith only [hpos, hraise, hrelax, hmono, hN]

end SmoothedOctagon
