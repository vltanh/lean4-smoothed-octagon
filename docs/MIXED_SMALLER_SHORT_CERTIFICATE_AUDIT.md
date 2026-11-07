# Independent audit of the smaller-short certificate

Date: 2026-11-07. Independent mathematical-interface and implementation
review. No Lean, Lake, typechecking or CI.

**Status:** the scalar reduction, interval engine and full caller have
passed independent source review. The engine regression checker has
also been independently compiled and replayed successfully. The first
full directed-interval cover is running; its completion remains pending.
This audit does not yet close the smaller-short branch or M2.

## 1. Mathematical scope

The reviewed reduction is
[MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md),
with the exact physical cost and endpoint identities in
[MIXED_GENERAL_SHORT_DEFECT_INTERFACE](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md).
The implemented independent coordinates are

\[
(r,\delta,\alpha,\rho,v,E)\in
[1/10,1/2]\times[0,2]\times[1,631/100]\times
[1/226,3/20]\times[3/4,1]\times[-23/16,9/20],
\]

with `x=(1-r)/r`, `beta=(1+delta)x`. Every closed boundary is retained.
The bounds `r>1/10`, `delta<2`, `alpha<631/100` and `E<=3rho`
have exact derivations in the reduction note. They do not arise from
the numerical optimizer.

The mathematical theorem needed is an exclusion of a larger set of
necessary conditions. In particular the second secant is relaxed to
`Sec(alpha,beta,x)<=u`, while u is the exact first secant. The rational
two-turn cost equals physical cost on the actual equal-secant locus;
there is no assertion that it is an off-locus physical competitor.

The opposite turn is removed with the proved strong pairing bound
using `log z<=z-1`. The previously proposed bound obtained merely by
dropping the logarithm was too weak and is not the bound implemented.
The lower pairing bound is exactly the central missing-control
polynomial. The rational outer-root chord applies off the central
zero-factor face because its derivation uses only the outer parameters
T,T_B,u,w,E_L and the incident norm interval.

The middle-switch and outer-entrance Hamiltonian slacks have been
independently checked by exact symbolic physical-matrix transport. Their
positive factors and orientation are recorded in the endpoint note.
The polar angle of the reflected incoming window equals that of the
original incoming window: time reversal and reflection each reverse
the polar increment, while the physical cost is unchanged. The
competitive whole-period angle, not a chosen auxiliary branch, supplies
`0<B<A` and the modulus filters `A+B>=4T_kappa`, `A>=2T_kappa`.

Thus the window retains the common actual primary multiplier and all
imported global normality, minimum, seam and geometric eligibility
assumptions. No local window is asserted to close by itself.

## 2. Engine review and independent replay

The reviewed engine is
[certified_mpfr_interval.hpp](../explorations/certified_mpfr_interval.hpp).
Its point numbers have 80-bit significands. Every proof-bound arithmetic
operation supplies an explicit MPFR direction; no round-to-nearest
point operation is later relabeled as an outward interval bound.

The review checked all multiplication sign cases, reciprocal intervals
on both sides of zero, squares crossing zero, exact negation, rational
and decimal input, unary derivatives, and the product and chain rules
for the full Hessian. All lower and upper endpoints use the required
directions.

The implementation's stack-owned significands follow the documented
[MPFR Custom Interface](https://www.mpfr.org/mpfr-current/mpfr.html#Custom-Interface):
they are initialized with the advertised size/alignment, remain at fixed
precision, and are neither resized nor passed to `mpfr_clear`. Copies
and moves copy the represented value into the destination object's own
storage. They do not copy a pointer to the source object's storage.
The MPFR [rounding contract](https://www.mpfr.org/mpfr-current/mpfr.html#Rounding)
is the arithmetic-library premise for directed transcendental bounds.

The analytic continuation of `log(h)/(h-1)` is enclosed by its convergent
even series in `(h-1)/(h+1)`. The positive geometric tail majorizes the
true series coefficient by coefficient; differentiating that majorant
therefore also bounds both omitted derivatives. The first derivative's
tail is enclosed symmetrically, so negative transformed arguments and
intervals crossing zero are covered. The second derivative's omitted
tail is nonnegative. The checker uses these bounds for the actual
analytic function and its derivatives, including at h=1.

The Taylor center is a chosen representable point inside the interval.
The code computes its actual, potentially asymmetric displacement
intervals. It does not assume that a rounded midpoint remains exactly
halfway between adjacent endpoints. Diagonal squares and off-diagonal
products have the correct coefficients, and the full-box Hessian
encloses every segment to which Taylor's theorem is applied.

An independent build and run of
[certified_mpfr_interval_check.cpp](../explorations/certified_mpfr_interval_check.cpp)
returned:

```
PASS 116914 independent checks; MPFR 4.2.2; precision 80 bits;
no range/domain flags
```

Those checks compare arithmetic endpoints with exact GMP rationals,
check analytic values against rational series bounds, test derivatives,
exercise object copy/move ownership, and include an adjacent-endpoint
Taylor case. They supplement the source review; they are not a sampled
proof of the M2 inequality.

## 3. Caller formulas and domain contractions

The reviewed full caller was named `m2_short_mpfrELP4.cpp` during the
replay. It is now published byte-identically as
[mixed_smaller_short_interval_certificate.cpp](../explorations/mixed_smaller_short_interval_certificate.cpp).

I checked both stable secant expressions, the central Casimir,
transported w and E_L, the reciprocal outer factor, rational root chord,
three stationary-slack expressions, the matrix inverse and two-factor
transfer, the rational physical cost, and both scalar endpoint traces
against the displayed hand identities. The upper pairing polynomial
has the stronger `+rho` term required by the `log z<=z-1` estimate.

Each contraction uses an actual necessary inequality. In particular,
the new lower bound on r rounds the square root down; the new upper
bound on alpha rounds its square root up. Bounds involving the smallest
possible x or delta use lower endpoints in increasing expressions.
The upper v contraction uses that `1-t+t^2` decreases for
`0<=t<=1/2`, with `t=rho/r`. Empty contracted boxes contain no actual
point of their original boxes.

The global secant value interval `[3/4,1]` is valid over every positive
endpoint rectangle, including reversed endpoint order. Intersecting
the value enclosure with this interval is therefore legitimate on the
whole box; it is not a feasible-subset restriction used improperly in
Taylor's theorem. The derivative enclosures remain those of the actual
secant function.

Before the centered angle quotient is evaluated, the code requires
`A+B` to have a positive lower bound on the entire box. Merely knowing
the actual angle/modulus inequality is not substituted for that test.
MPFR atan is evaluated with directed rounding, with the exact analytic
first and second derivatives.

The cost-defect expression uses the lower rational bound
`pi>=6283/2000` and the upper cost bound `A_oct<=2501/800`. Because
`kappa+3/2>0`, their directions make this a necessary inequality for
every actual competitive window.

## 4. Linear-program proposals and rigorous rejection

The native floating-point linear program is only a source of proposed
weights. Its feasibility result does not itself discard a box.
Each proposed weight is checked for finiteness and nonnegativity,
rounded to an integer between zero and `2^20`, and then converted to
that exact integer divided by `2^20`.

The only resulting rejection is a fresh directed-interval Taylor upper
bound, strictly below zero, for the nonnegative weighted sum of the
original necessary residuals. This is sound for any proposed weights
passing the stated nonnegativity test, independently of the quality or
correctness of the floating LP's suggested certificate.

The midpoint and full-box residual arrays are matched only through
their common prefix. A residual requiring an analytic denominator is
not used unless it was successfully enclosed on the full box.

## 5. Cover and failure behavior

Every bisection uses a represented point strictly between the interval
endpoints and retains both closed halves. Native floating arithmetic
only chooses a bisection coordinate or proposes weights; it cannot
establish a contradiction.

An analytic domain failure causes subdivision. A range or runtime
failure is fatal. The program retains sticky MPFR domain/range flags
and checks them before its success message. It does not clear an
arithmetic failure midway through a proof run. A remaining stack,
depth-limit box, or nonbisectable nonempty interval produces an
incomplete result and a nonzero exit status.

At the time of this source audit the full replay is pending. An
exclusion theorem may be concluded only after that unchanged source
finishes with an empty stack, zero unresolved boxes, no bad flags and
its explicit success exit. No duplicate full replay is claimed here.

## 6. Reviewed source identifiers

SHA-256:

- Full caller:
  `68ad563d1db8e0743eb6e2f94ef8d13a4f7fbf1f4e78c8f2dac9bcb0e350b36a`.
- Interval engine:
  `1607b4f02063722506a514598d23d9b032a4aebfd6e74753bc302a7a67e32e76`.
- Engine regression checker:
  `6639591181a4237726ba0c5ee254e794ca98ff615536db151c27d66c7cae486e`.

Any later source change requires reviewing the affected operations and
refreshing this record. The audit does not independently re-prove the
imported geometric correspondence or earlier whole-period normality
and minimum structure theorems.
