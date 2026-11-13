module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowRatio.Bounds
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.HighRatio.Shape

/-!
# Shape monotonicity in the forward low-ratio region

The shape derivative decreases with the norm, logarithm, and shape.
At their upper endpoints it is a cubic in the event-factor gap.
Its only negative coefficient is absorbed by the preceding linear term,
since that gap is at most one half. Thus the unit shape is the worst case.
-/

@[expose] public section

namespace SmoothedOctagon

private def nlrD0 (t x : ℝ) : ℝ :=
  x * (1 - t) * (1 - 2 * t + (-2 * t ^ 2 + 14 * t - 1) * x
    + 24 * t * x ^ 2 + 12 * t * x ^ 3)

private def nlrD1 (t x : ℝ) : ℝ :=
  t - 2 * t ^ 2 + (16 - 27 * t + 8 * t ^ 2) * x
    + (51 - 68 * t + 10 * t ^ 2 + 4 * t ^ 3) * x ^ 2
    + (63 - 80 * t + 16 * t ^ 2) * x ^ 3 + (24 - 28 * t + 4 * t ^ 2) * x ^ 4

private def nlrD2 (t x : ℝ) : ℝ :=
  -6 * t ^ 2 + (-16 * t - 6 * t ^ 2) * x + (-5 - 27 * t + 2 * t ^ 3) * x ^ 2
    + (-7 - 19 * t + 8 * t ^ 2) * x ^ 3 + (-4 - 2 * t + 2 * t ^ 2) * x ^ 4

private def nlrD3 (t x : ℝ) : ℝ := x * (1 + x) * (t + x * (x + 2))

private theorem nlr_endpoint_eq (t x q : ℝ) :
    hrsK 6 t x (2 * t + x) q (1 - t + t ^ 2) (q - 1) =
      2 * t * q ^ 2 * (nlrD0 t x + nlrD1 t x * (q - 1)
        + nlrD2 t x * (q - 1) ^ 2 + nlrD3 t x * (q - 1) ^ 3) := by
  unfold hrsK hrsTk nsrA nsfE0 nlrD0 nlrD1 nlrD2 nlrD3
  ring

private theorem nlr_cubic_pos {t x y : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3)
    (hx : 1 / 3 ≤ x) (hy : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    0 < nlrD0 t x + nlrD1 t x * y + nlrD2 t x * y ^ 2 + nlrD3 t x * y ^ 3 := by
  have ht : 0 ≤ t := by linarith only [ht0]
  have hx0 : 0 < x := by linarith only [hx]
  have h2 : t ^ 2 ≤ 1 / 9 := by nlinarith only [ht, ht1]
  have h3 : t ^ 3 ≤ 1 / 27 := by
    have hp := pow_le_pow_left₀ ht ht1 3
    norm_num at hp
    exact hp
  have h0 : 0 < nlrD0 t x := by
    have hc : 0 ≤ -2 * t ^ 2 + 14 * t - 1 := by nlinarith only [ht0, h2]
    have hh : 0 < 1 - 2 * t := by linarith only [ht1]
    have hc1 : 0 < 1 - t := by linarith only [ht1]
    unfold nlrD0
    positivity
  have h2c : 0 ≥ nlrD2 t x := by
    have hc2 : 0 ≤ 5 + 27 * t - 2 * t ^ 3 := by nlinarith only [ht, h3]
    have hc3 : 0 ≤ 7 + 19 * t - 8 * t ^ 2 := by nlinarith only [ht, h2]
    have hc4 : 0 ≤ 4 + 2 * t - 2 * t ^ 2 := by nlinarith only [ht, h2]
    have hp : 0 ≤ 6 * t ^ 2 + (16 * t + 6 * t ^ 2) * x
        + (5 + 27 * t - 2 * t ^ 3) * x ^ 2 + (7 + 19 * t - 8 * t ^ 2) * x ^ 3
        + (4 + 2 * t - 2 * t ^ 2) * x ^ 4 := by positivity
    unfold nlrD2
    linarith only [hp]
  have h12 : 0 < 2 * nlrD1 t x + nlrD2 t x := by
    have hc0 : 0 ≤ 2 * t - 10 * t ^ 2 + 1 := by nlinarith only [ht0, h2]
    have hc1 : 0 ≤ 10 * t ^ 2 - 70 * t + 24 := by nlinarith only [ht1, sq_nonneg t]
    have hc2 : 0 ≤ 10 * t ^ 3 + 20 * t ^ 2 - 163 * t + 97 := by
      nlinarith only [ht1, pow_nonneg ht 3, sq_nonneg t]
    have hc3 : 0 ≤ 40 * t ^ 2 - 179 * t + 119 := by nlinarith only [ht1, sq_nonneg t]
    have hc4 : 0 ≤ 10 * t ^ 2 - 58 * t + 44 := by nlinarith only [ht1, sq_nonneg t]
    have hp : 0 ≤ (2 * t - 10 * t ^ 2 + 1) + (10 * t ^ 2 - 70 * t + 24) * x
        + (10 * t ^ 3 + 20 * t ^ 2 - 163 * t + 97) * x ^ 2
        + (40 * t ^ 2 - 179 * t + 119) * x ^ 3 + (10 * t ^ 2 - 58 * t + 44) * x ^ 4 := by
      positivity
    unfold nlrD1 nlrD2
    nlinarith only [hp, hx]
  have htail : 0 < nlrD1 t x + nlrD2 t x * y := by
    have hm := mul_le_mul_of_nonpos_left hy1 h2c
    linarith only [hm, h12]
  have hp := mul_nonneg htail.le hy
  have hlast : 0 ≤ nlrD3 t x * y ^ 3 := by unfold nlrD3; positivity
  nlinarith only [h0, hp, hlast]

private theorem nlr_Kv_neg {t x q : ℝ} (ht : 0 ≤ t) (hx : 0 < x) (hq : 1 ≤ q)
    (hJ : (t + x * (x + 2)) * q ^ 2 ≤ 10 / 3 * (1 + x) ^ 2)
    (hD0 : 0 ≤ q * (t + x * (x + 2)) - (t + x) * (1 + x))
    (hD : q * (t + x * (x + 2)) - (t + x) * (1 + x) ≤ 9 / 4 * x) :
    hrsKv 6 t x q < 0 := by
  let E := 7 * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2
  let D := q * (t + x * (x + 2)) - (t + x) * (1 + x)
  have hW : 1 ≤ (1 + x) ^ 2 := by nlinarith only [hx, sq_nonneg x]
  have hE : 11 / 3 ≤ E := by dsimp [E]; nlinarith only [hJ, hW]
  have hb : (1 - t) * (1 + x) - (x + 2) * q ≤ -1 := by
    have hm := mul_le_mul_of_nonneg_left hq (show 0 ≤ x + 2 by linarith only [hx])
    have hp := mul_nonneg ht (show 0 ≤ 1 + x by linarith only [hx])
    nlinarith only [hm, hp]
  have hA := mul_le_mul_of_nonneg_left hb (show 0 ≤ x * E by positivity)
  have hE' := mul_le_mul_of_nonneg_left hE hx.le
  have hq2 : 1 ≤ q ^ 2 := by nlinarith only [hq]
  have hY : (1 + x) ^ 2 - x * (x + 2) * q ^ 2 ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hq2 (show 0 ≤ x * (x + 2) by positivity)
    nlinarith only [hm]
  have hB := mul_le_mul_of_nonneg_left hY hD0
  have hn : x * E * ((1 - t) * (1 + x) - (x + 2) * q)
      + D * ((1 + x) ^ 2 - x * (x + 2) * q ^ 2) < 0 := by
    dsimp [D] at *
    nlinarith only [hA, hE', hB, hD, hx]
  have he : hrsKv 6 t x q = 4 * q ^ 2 *
      (x * E * ((1 - t) * (1 + x) - (x + 2) * q)
        + D * ((1 + x) ^ 2 - x * (x + 2) * q ^ 2)) := by
    dsimp [E, D, hrsKv]
    ring
  rw [he]
  exact mul_neg_of_pos_of_neg (by positivity) hn

/-- The effective low-ratio residual increases with shape up to the order face. -/
theorem nlr_shape_mono {t x a b q : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3)
    (hx0 : 1 - 2 * t ≤ x) (hx1 : x ≤ 1) (hq : 1 < q)
    (hqo : q * (2 * t + x) ≤ 1 + x) (hF : nsrFl t x q ≤ nsfVG t x)
    (hab : a ≤ b) (hb : b ≤ 2 * t + x) :
    nsfComb 6 0 t x a q (nsfVhat t x q) (nsrLp q) 0 ≤
      nsfComb 6 0 t x b q (nsfVhat t x q) (nsrLp q) 0 := by
  have ht : 0 ≤ t := by linarith only [ht0]
  have hx : 1 / 3 ≤ x := by linarith only [ht1, hx0]
  have hxpos : 0 < x := by linarith only [hx]
  have hq0 : 0 < q := by linarith only [hq]
  have ho : 1 ≤ 2 * t + x := by linarith only [hx0]
  have hJ := nsf_LR_J ht1 hx1 hxpos ho hq0.le hqo
  have hD := nsf_LR_WD ht0 ht1 hx0 hxpos hq0.le hqo
  have hD0 : 0 ≤ q * (t + x * (x + 2)) - (t + x) * (1 + x) := by
    have hp := mul_nonneg hxpos.le (show 0 ≤ 1 - t by linarith only [ht1])
    have hm := mul_le_mul_of_nonneg_right hq.le (show 0 ≤ t + x * (x + 2) by positivity)
    nlinarith only [hp, hm]
  have hy1 : q - 1 ≤ 1 / 2 := by
    have hp := mul_nonneg (show 0 ≤ q - 1 by linarith only [hq])
      (show 0 ≤ 2 * t + x - 1 by linarith only [hx0])
    nlinarith only [hp, hqo, ht0]
  have hC := nlr_cubic_pos ht0 ht1 hx (by linarith only [hq]) hy1
  have hEnd : 0 < hrsK 6 t x (2 * t + x) q (1 - t + t ^ 2) (q - 1) := by
    rw [nlr_endpoint_eq]
    exact mul_pos (by positivity) hC
  have hKv := nlr_Kv_neg ht hxpos hq.le hJ hD0 hD
  have hKL : hrsKL 6 t x q ≤ 0 := by
    have hE : 0 ≤ (6 + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2 := by
      norm_num
      nlinarith only [hJ, sq_nonneg (1 + x)]
    unfold hrsKL
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    have hp : 0 ≤ t * (t + x) * (1 + x) * q := by positivity
    linarith only [hp]
  have hKk : hrsKk t x q ≤ 0 := by
    unfold hrsKk
    apply mul_nonpos_of_nonneg_of_nonpos hD0
    have hp : 0 ≤ 2 * t * q ^ 4 := by positivity
    linarith only [hp]
  have hV := nsf_LR_norm_ceiling ht1 hx0 hx1 hq hqo hF
  have hdec := hrs_K_dec 6 t x ((b + a) / 2) (2 * t + x) q
    (nsfVhat t x q) (1 - t + t ^ 2) (nsrLp q) (q - 1)
  have hNv := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hV.le) hKv.le
  have hNL := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hrs_Lp_le hq.le)) hKL
  have hNk := mul_nonneg_of_nonpos_of_nonpos
    (show (b + a) / 2 - (2 * t + x) ≤ 0 by linarith only [hab, hb]) hKk
  have hK : 0 ≤ hrsK 6 t x ((b + a) / 2) q (nsfVhat t x q) (nsrLp q) := by
    linarith only [hdec, hEnd, hNv, hNL, hNk]
  have he := hrs_comb_sub_k 6 0 t x q (nsfVhat t x q) (nsrLp q) 0 b a
  have hp := mul_nonneg (sub_nonneg.mpr hab) hK
  linarith only [he, hp]

end SmoothedOctagon
