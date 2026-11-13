module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.ScaleStrip.Monotonicity

/-!
# The reverse scale strip

On `3/8 ≤ t ≤ 2/5`, the cleared residual on `k = 29t²/4` increases
with `t`. Its value at `3/8` is positive by shape monotonicity and
the unit-face inequality. This proves the whole strip without an
additional boundary estimate.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The cleared cubic on the scale face `k = 29t²/4`. -/
theorem nsrS_P_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    24 * (q + 1) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) *
      (nsrN t x (29 / 4 * t ^ 2) q (nsrVJensen t x) (nsrLp q) - (q - 1) * (nsrVJensen t x - nsrFl t x q)) =
      nsrSC0 t x + nsrSC1 t x * (q - 1) + nsrSC2 t x * (q - 1) ^ 2 + nsrSC3 t x * (q - 1) ^ 3 := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (x ^ 2 + 6 * x + 6) ≠ 0 := by positivity
  have h3 : (q + 1) ≠ 0 := by positivity
  unfold nsrN nsrVJensen nsrLp nsrFl nsrSC0 nsrSC1 nsrSC2 nsrSC3
  field_simp
  ring

/-- Coefficient monotonicity also gives monotonicity of the whole residual. -/
private theorem strip_poly_mono {x a b y : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4)
    (ha : 3 / 8 ≤ a) (hab : a ≤ b) (hb : b ≤ 2 / 5) (hy : 0 ≤ y) :
    nsrSC0 a x + nsrSC1 a x * y + nsrSC2 a x * y ^ 2 + nsrSC3 a x * y ^ 3 ≤
      nsrSC0 b x + nsrSC1 b x * y + nsrSC2 b x * y ^ 2 + nsrSC3 b x * y ^ 3 := by
  have h0 := nsrSC0_mono hx ha hab hb
  have h1 := mul_le_mul_of_nonneg_right (nsrSC1_mono hx ha hab hb) hy
  have h2 := mul_le_mul_of_nonneg_right (nsrSC2_mono hx hx1 ha hab hb) (sq_nonneg y)
  have h3 := mul_le_mul_of_nonneg_right (nsrSC3_mono hx hx1 ha hab hb) (pow_nonneg hy 3)
  linarith only [h0, h1, h2, h3]

/-- On the unit region, the reciprocal-mean ceiling lies below the incident ceiling. -/
private theorem strip_jensen_le_U {t x : ℝ} (ht : t ≤ 1) (hx : 0 < x)
    (hxt : x ≤ 1 - 2 * t) : nsrVJensen t x ≤ 1 - t + t ^ 2 := by
  have heq : 1 - t + t ^ 2 - nsrVJensen t x =
      (1 - t) * x * ((1 + x) * x * (x + 4)
        + (x ^ 2 + 6 * x + 6) * (1 - 2 * t - x)) /
        (2 * (1 + x) * (x ^ 2 + 6 * x + 6)) := by
    unfold nsrVJensen
    field_simp
    ring
  have hc : 0 ≤ 1 - t := sub_nonneg.mpr ht
  have hr : 0 ≤ 1 - 2 * t - x := by linarith only [hxt]
  have hp : 0 ≤ (1 - t) * x * ((1 + x) * x * (x + 4)
      + (x ^ 2 + 6 * x + 6) * (1 - 2 * t - x)) /
      (2 * (1 + x) * (x ^ 2 + 6 * x + 6)) := by positivity
  linarith only [heq, hp]

/-- The scale strip reduces to its lower edge and then to the unit face. -/
theorem nsr_strip {t x q v : ℝ} (ht0 : 3 / 8 ≤ t) (ht1 : t ≤ 2 / 5) (hx : 0 < x)
    (hx1 : x ≤ 1 / 4) (hgap : 29 / 4 * t ^ 2 < 2 * t + 2 * x + x ^ 2) (hq : 1 < q)
    (hv : v = nsrSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nsrN t x (29 / 4 * t ^ 2) q v (Real.log q) := by
  let t0 : ℝ := 3 / 8
  have ht : 0 < t := by linarith only [ht0]
  have hq0 : 0 < q := by linarith only [hq]
  have ht0p : 0 < t0 := by norm_num [t0]
  have ht0t : t0 ≤ t := ht0
  have hinc : 29 / 4 * t0 ^ 2 - 2 * t0 ≤ 29 / 4 * t ^ 2 - 2 * t := by
    have hp : 0 ≤ (t - t0) * (29 / 4 * (t + t0) - 2) := by
      apply mul_nonneg (sub_nonneg.mpr ht0t)
      dsimp [t0]
      linarith only [ht0]
    nlinarith only [hp]
  have hgap0 : 1 < 2 * t0 + 2 * x + x ^ 2 := by
    dsimp [t0] at hinc ⊢
    linarith only [hinc, hgap]
  have hxt0 : x ≤ 1 - 2 * t0 := by dsimp [t0]; linarith only [hx1]
  have hbase := nsrU_poly_pos ht0p (le_refl t0) hx hxt0 hgap0 hq.le
  have hvbU := strip_jensen_le_U (t := t0) (by norm_num [t0]) hx hxt0
  have hLp : nsrLp q < q - 1 := by
    have heq : q - 1 - nsrLp q = (q - 1) ^ 2 * (5 * q + 1) / (6 * q * (q + 1)) := by
      unfold nsrLp
      field_simp
      ring
    have hp : 0 < (q - 1) ^ 2 * (5 * q + 1) / (6 * q * (q + 1)) := by
      have : 0 < q - 1 := sub_pos.mpr hq
      positivity
    linarith only [heq, hp]
  have hshape := nsrN_mono_k (k := 1) (k' := 29 / 4 * t0 ^ 2)
    ht0p (by norm_num [t0]) hx hq.le hvbU hLp (by norm_num [t0])
  have hbase' : 0 < nsrN t0 x (29 / 4 * t0 ^ 2) q (nsrVJensen t0 x) (nsrLp q) -
      (q - 1) * (nsrVJensen t0 x - nsrFl t0 x q) := by linarith only [hbase, hshape]
  have hmul : 0 < 24 * (q + 1) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) := by positivity
  have hstart := mul_pos hmul hbase'
  rw [nsrS_P_eq hx hq0] at hstart
  have hmono := strip_poly_mono hx.le hx1 (by norm_num [t0]) ht0t ht1
    (show 0 ≤ q - 1 by linarith only [hq])
  have hpoly := hstart.trans_le hmono
  rw [← nsrS_P_eq hx hq0] at hpoly
  have hrelax := pos_of_mul_pos_right hpoly hmul.le
  refine nsr_N_pos_of_relax (vb := nsrVJensen t x) (Lb := nsrLp q) (Fl := nsrFl t x q) (m := q - 1)
    ?_ (nsr_log_lt_Lp hq).le (nsrNv_nonpos ht.le hx.le hq.le (by nlinarith only [ht0]))
    (nsrNL_nonpos ht.le hx.le hq0.le (by positivity))
    ((nsr_m2F_gt_Fl hq (by linarith only [ht, hx]) (by linarith only [hx])).le.trans hF)
    (by linarith only [hq]) hrelax
  rw [hv]
  exact (nsr_secN_lt_jensen hx (by linarith only [ht1])).le

end SmoothedOctagon
