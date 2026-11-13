module

public import SmoothedOctagon.Exclusion.Mixed.Residual
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Slope
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Remainder

/-!
# The unit face with the reciprocal-mean secant ceiling

The order gap satisfies `max 0 (1/4-x) ≤ r ≤ min (x(1+x)) (1-x)`.
Rescale the ratio increment by `q-1 = xz`. The cubic is positive by
its boundary value, its slope, and the quadratic remainder. These
quantities are controlled by monotonicity and concavity in the gap.
-/

@[expose] public section

namespace SmoothedOctagon.UnitShape

private theorem clearing {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    let r := 1 - 2 * t - x
    let z := (q - 1) / x
    let C := constant x r
    let S := cross x r
    let P := value x r
    let G := leading x r
    24 * (q + 1) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) *
      (nsrN t x 1 q (nsrVJensen t x) (nsrLp q) - (q - 1) * (nsrVJensen t x - nsrFl t x q)) =
      x ^ 2 * (C + (S - 2 * C + G) * z + (P + C - S - 2 * G) * z ^ 2 + G * z ^ 3) := by
  have hW : (1 + x) ≠ 0 := by positivity
  have hD : (x ^ 2 + 6 * x + 6) ≠ 0 := by positivity
  have hq1 : (q + 1) ≠ 0 := by positivity
  dsimp only
  unfold nsrN nsrVJensen nsrLp nsrFl constant cross value leading
    cross0 cross1 cross2 cross3 value0 value1 value2 value3 lead0 lead1 lead2 lead3
  field_simp
  ring

/-- The relaxed unit-face residual is positive up to the natural cutoff `3/8`. -/
theorem jensen_poly_pos {t x q : ℝ} (ht : 0 < t) (ht1 : t ≤ 3 / 8) (hx : 0 < x)
    (hxt : x ≤ 1 - 2 * t) (hgap : 1 < 2 * t + 2 * x + x ^ 2) (hq : 1 ≤ q) :
    0 < nsrN t x 1 q (nsrVJensen t x) (nsrLp q) - (q - 1) * (nsrVJensen t x - nsrFl t x q) := by
  let r := 1 - 2 * t - x
  have hx1 : x < 1 := by linarith only [hxt, ht]
  have hxlo : 1 / 10 ≤ x := by nlinarith only [ht1, hgap, hx, sq_nonneg (x - 1 / 10)]
  have hr : 0 ≤ r := by dsimp [r]; linarith only [hxt]
  have hr0 : 1 / 4 - x ≤ r := by dsimp [r]; linarith only [ht1]
  have hrx : r ≤ x * (1 + x) := by dsimp [r]; nlinarith only [hgap]
  have hr1 : r ≤ 1 - x := by dsimp [r]; linarith only [ht]
  obtain ⟨_, hS, hP⟩ := value_cross_bounds hx hx1.le hr hr0 hrx hr1
  have hK := slope_pos hxlo hr hr0 hrx hr1
  have hH := remainder_nonneg hxlo hr hr0 hrx hr1
  have hp := cubic_boundary_pos (constant_pos hx hr) (leading_pos hx hx1 hr hrx hr1)
    (show 0 ≤ (q - 1) / x by positivity)
    (A := cross x r - 2 * constant x r + leading x r)
    (B := value x r + constant x r - cross x r - 2 * leading x r)
    (by unfold slope at hK; linarith only [hK])
    (by unfold remainder at hH; linarith only [hH])
    (by linarith only [hS]) (by linarith only [hP])
  have hp' := mul_pos (sq_pos_of_pos hx) hp
  rw [← clearing hx (show 0 < q by linarith only [hq])] at hp'
  exact pos_of_mul_pos_right hp' (by positivity)

/-- The unit-face exclusion with the exact incoming secant. -/
theorem jensen_unit_shape {t x q v : ℝ} (ht : 0 < t) (ht1 : t ≤ 3 / 8) (hx : 0 < x)
    (hxt : x ≤ 1 - 2 * t) (hgap : 1 < 2 * t + 2 * x + x ^ 2) (hq : 1 < q)
    (hv : v = nsrSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nsrN t x 1 q v (Real.log q) := by
  refine nsr_N_pos_of_relax (vb := nsrVJensen t x) (Lb := nsrLp q)
    (Fl := nsrFl t x q) (m := q - 1) ?_ (nsr_log_lt_Lp hq).le
    (nsrNv_nonpos ht.le hx.le hq.le (by linarith only [ht1]))
    (nsrNL_nonpos ht.le hx.le (by linarith only [hq]) (by norm_num))
    ((nsr_m2F_gt_Fl hq (by linarith only [ht, hx]) (by linarith only [hx])).le.trans hF)
    (by linarith only [hq]) (jensen_poly_pos ht ht1 hx hxt hgap hq.le)
  rw [hv]
  exact (nsr_secN_lt_jensen hx (by linarith only [ht1])).le

end SmoothedOctagon.UnitShape
