module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Jensen

/-!
# The reverse unit face

Use the reciprocal-mean secant ceiling. Rescaling the ratio increment
turns the residual into a cubic. Square decompositions prove positivity
from its value and slope at one and a quadratic remainder; monotonicity
and concavity in the order gap control these quantities at the boundary.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The polynomial part of the unit-face exclusion. -/
theorem nsrU_poly_pos {t x q : ℝ} (ht : 0 < t) (ht1 : t ≤ 3 / 8) (hx : 0 < x)
    (hxt : x ≤ 1 - 2 * t) (hgap : 1 < 2 * t + 2 * x + x ^ 2) (hq : 1 ≤ q) :
    0 < nsrN t x 1 q (nsrVJensen t x) (nsrLp q) - (q - 1) * (nsrVJensen t x - nsrFl t x q) :=
  UnitShape.jensen_poly_pos ht ht1 hx hxt hgap hq

/-- The unit-face exclusion with the exact incoming secant and its control floor. -/
theorem nsr_unit_shape {t x q v : ℝ} (ht : 0 < t) (ht1 : t ≤ 3 / 8) (hx : 0 < x)
    (hxt : x ≤ 1 - 2 * t) (hgap : 1 < 2 * t + 2 * x + x ^ 2) (hq : 1 < q)
    (hv : v = nsrSecN t x) (hF : m2F ((t + x) / (1 + x)) q ≤ v) :
    0 < nsrN t x 1 q v (Real.log q) :=
  UnitShape.jensen_unit_shape ht ht1 hx hxt hgap hq hv hF

end SmoothedOctagon
