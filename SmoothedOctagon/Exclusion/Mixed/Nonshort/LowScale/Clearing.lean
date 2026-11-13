module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.Feasibility
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.LowScale.High

/-!
# Clearing the low-scale residual

The common positive denominator is `12(q+1)(1+x)²(x²+6x+6)`.
Both faces use the reciprocal-mean ceiling and the full incoming floor.
-/

@[expose] public section

namespace SmoothedOctagon.LowScale

/-- The unit-face quartic is the cleared relaxed residual. -/
theorem unit_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    12 * (q + 1) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) *
      (nsrN t x 1 q (nsrVJensen t x) (nsrLp q)
        - (-nsrNv t x 1 q) * (nsrVJensen t x - nsrFl t x q)) =
      unit0 t x + unit1 t x * (q - 1) + unit2 t x * (q - 1) ^ 2
        + unit3 t x * (q - 1) ^ 3 + unit4 t x * (q - 1) ^ 4 := by
  have hW : (1 + x) ≠ 0 := by positivity
  have hD : (x ^ 2 + 6 * x + 6) ≠ 0 := by positivity
  have hq1 : (q + 1) ≠ 0 := by positivity
  unfold nsrN nsrNv nsrVJensen nsrLp nsrFl unit0 unit1 unit2 unit3 unit4 incoming0 incoming1
  field_simp
  ring

/-- The increasing-shape face has the same normalization. -/
theorem high_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    12 * (q + 1) * (1 + x) ^ 2 * (x ^ 2 + 6 * x + 6) *
      (nsrN t x (2 * t + 1 / 2) q (nsrVJensen t x) (nsrLp q)
        - (-nsrNv t x (2 * t + 1 / 2) q) * (nsrVJensen t x - nsrFl t x q)) =
      high0 t x + high1 t x * (q - 1) + high2 t x * (q - 1) ^ 2
        + high3 t x * (q - 1) ^ 3 + high4 t x * (q - 1) ^ 4 := by
  have hW : (1 + x) ≠ 0 := by positivity
  have hD : (x ^ 2 + 6 * x + 6) ≠ 0 := by positivity
  have hq1 : (q + 1) ≠ 0 := by positivity
  unfold nsrN nsrNv nsrVJensen nsrLp nsrFl high0 high1 high2 high3 high4 highIncoming0 highIncoming1
  field_simp
  ring

end SmoothedOctagon.LowScale
