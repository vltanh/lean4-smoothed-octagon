# Generators of the Bernstein certificates for case F

Python scripts used to generate and check the exact Bernstein coefficients (positivity
certificates) in `SmoothedOctagon/Exclusion/Forward/Scalars/` and `Exclusion/Forward/`, for the
polynomial sign steps of the forward-period exclusion and its supports. Lean checks every
certificate itself (`ring`, `positivity`); the scripts are kept for reproducibility only.

The small-forward-minimum argument in `Scalars/SmallMin.lean` uses AM--GM,
positive products, and a completed square; it is written directly in Lean.

The exterior budget uses joint concavity, pairing of a reciprocal kernel, and an
endpoint chord in `Budget/Concavity.lean` and `Budget.lean`.

The individual norm endpoints in `Scalars/LargerNorm/Endpoints.lean` use successive
convexity arguments and two corner comparisons for the value. The other tangent
endpoint increases to the geometric boundary; its derivative is concave, with an
upper edge controlled by concave reciprocal functions.

The constant coefficient of the sum residual in `Scalars/SumSym/Constant.lean`
uses shape derivatives and the reciprocal logarithm remainder. The sum generators
retain the two tangent endpoint certificates.

The symmetric neighbour value and partial slope in `Scalars/Neighbor/` use
rational logarithm majorants, positive reciprocal moments, and convexity on the
remaining edge. The shape comparison for the slope uses a convex derivative
and its two endpoint values.
