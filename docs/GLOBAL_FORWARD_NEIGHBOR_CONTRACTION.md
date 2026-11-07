# Forward neighbors lie below five quarters of the minimum

Date: 2026-11-07. Hand reduction with a finite exact rational interval
certificate. No Lean, Lake, typechecking, or CI.

## Statement and prerequisites

At a global active-margin minimum `a` of a competitive all-forward
period with `N>=7` pieces, let the neighboring margins be `b,c`. Then

\[
\boxed{1\le b/a<5/4,\qquad1\le c/a<5/4.}            \tag{1}
\]

The inputs are the actual same-covector three-arc stationarity system and
exterior missing-control floors of
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md),
the scale bound `11/5<U=4/a²<3`, and the scalar linear budget

\[
z+w<\frac53(U-1),\qquad z=b/a,\quad w=c/a          \tag{2}
\]

from [GLOBAL_FORWARD_LINEAR_BUDGET](GLOBAL_FORWARD_LINEAR_BUDGET.md).
The lemma uses no Casimir bound. It restricts the fixed continuous domain
for F; it does not prove F or a corresponding assertion for a mixed run.

## 1. One necessary scalar residual

Reflect the two scalar rows if needed so that `z<=w`, and put

\[
S=1+z,\quad T=1+w,\quad L=1+U,\quad
Z=z^2+U,\quad W=w^2+U,
\]
\[
q=ST/L,\qquad H=S^2/Z,\qquad I=T^2/W.
\]

The left exterior factor obeys `H<=h<=S/z`. The actual right exterior
factor is at least `I`; monotonicity of the exterior floor therefore
supplies the lower bound `F_{w/T}(I)` on the right multiplier coordinate.
Write

\[
\begin{aligned}
A&=1+z+w-S^{-1}-T^{-1}+L^{-1}-\log q,\\
B&=Zh/S+1-z^2S/(Zh)-z^2/S+z^3/Z-z\log h,\\
\alpha&=L(hS-z)/Z,\\
n&=S^2(U-z)(h-1)/Z,\\
m&=L^2\{q-1+(h-1)(Sq-1)\}/(SZ),\\
F_x(v)&=1+x^2v-xv\log(v)/(v-1).
\end{aligned}                                      \tag{3}
\]

The value at `v=1` is the continuous value `1-x+x²`. Positivity of the
first stationarity row and the two genuine exterior floors give the
necessary inequality

\[
\mathcal E=\alpha A-B-nF_{z/S}(h)-mF_{w/T}(I)\ge0.  \tag{4}
\]

This is equation (15) of the small-forward-minimum note, divided by `a`.
It retains the same actual multiplier and permits non-strict exterior
gaps.

## 2. An entirely rational upper bound

For `v>=1`, set `t=(v-1)/(v+1)` and

\[
L_-(v)=2t(1+t^2/3+t^4/5),\qquad
L_+(v)=2t\left(1+t^2/3+\frac{t^4}{5(1-t^2)}\right).
\]

The positive series for `2 atanh t` proves

\[
L_-(v)\le\log v\le L_+(v).
\]

Define the continuous rational lower floor

\[
\underline F_x(v)=1+x^2v
 -x(1+t)\left(1+t^2/3+\frac{t^4}{5(1-t^2)}\right).
\tag{5}
\]

It is at most `F_x(v)`, including `v=1`. Let `Abar` be `A` with
`log q` replaced by `L_-(q)` and `Bbar` be `B` with `log h`
replaced by `L_+(h)`. Then

\[
\mathcal E\le\overline{\mathcal E}
 :=\alpha\overline A-\overline B
   -n\underline F_{z/S}(h)-m\underline F_{w/T}(I).  \tag{6}
\]

The coefficient signs justify each replacement: `alpha>0`, `z>0`,
and `n,m>=0`. On the comparison domain below, the linear budget and ordering imply
`z<=5(U-1)/6<U` and `w<=(5U-8)/3<U`. Thus both strict-star
factors are positive. Also `q>=1`, `h>=1`, and `I>=1`, so
every logarithm argument is at least one. The expression on the right is a rational function of
four variables, with no transcendental evaluations remaining.

## 3. Exact exclusion of the closed comparison domain

If (1) fails, the ordered neighbors obey `w>=5/4`. By (2), both
neighbors are at most `7/3`. It is therefore enough to prove
`Ebar<0` on

\[
\begin{gathered}
11/5\le U\le3,\quad1\le z\le w\le7/3,\quad w\ge5/4,\\
z+w\le5(U-1)/3,\qquad S^2/Z\le h\le S/z.
\end{gathered}                                      \tag{7}
\]

A finite exact rational interval certificate proves this strict
inequality. Its source is
[global_forward_completion_neighbor_certificate.cpp](../explorations/global_forward_completion_neighbor_certificate.cpp).
The complete verification rules are:

1. Start with the rational rectangle
   `[11/5,3] × [1,7/3] × [5/4,7/3] × [1,2]`.
2. Apply the linear constraints and monotone exterior-factor bounds in
   (7), narrowing each interval outward. Empty intervals are discarded.
3. Evaluate (6), its gradient, and its Hessian by the sum, product,
   reciprocal, and square rules, using interval arithmetic throughout.
4. In addition to direct interval evaluation, bound the function by its
   second-order Taylor formula about the rational box midpoint. For a
   centered box of radii `r_i`, the diagonal quadratic coordinate lies in
   `[0,r_i²]`, and each off-diagonal product lies in
   `[-r_i r_j,r_i r_j]`. An upper endpoint strictly below zero discards
   the whole box.
5. Bisect a remaining interval at its exact midpoint and repeat. A
   denominator interval containing zero requires subdivision and never
   counts as an exclusion. An unprocessed box or a depth-limit box is a
   verification failure.

All bounds use GMP integer/rational arithmetic. Interval endpoints are
rounded **outward**, using exact integer floor and ceiling, to multiples
of `2^-80` after arithmetic operations; this bounds denominator growth
without introducing a floating-point sign. Bisection choices and all
comparisons are exact. Floating-point arithmetic is used only to print
elapsed wall time.

The deterministic replay completed with:

| Quantity | Exact replay result |
|---|---:|
| Processed tree nodes | 8183 |
| Empty-domain leaves | 6 |
| Negative Taylor-bound leaves | 4086 |
| Unprocessed boxes | 0 |
| Depth-limit boxes | 0 |
| Maximum depth | 20 |

Thus the closed domain (7) is completely covered by certified negative
or empty leaves. Equations (4) and (6) contradict one another there,
proving (1).

To replay with a C++17 compiler and GMP development headers:

```sh
g++ -O2 -std=c++17 explorations/global_forward_completion_neighbor_certificate.cpp -lgmpxx -lgmp -o /tmp/forward_neighbor_certificate
/tmp/forward_neighbor_certificate
```

The rational approximants, all initial endpoints, interval rules,
contraction formulas, and deterministic bisection rule are contained in
the source. The printed node count is a replay record, not a substitute
for checking the exact leaf inequalities. A fresh compile and replay of the repository
source reproduced all displayed counts in 112.85 seconds on the shared
worker (the earlier run took 91.48 seconds). These timings are descriptive
only; every sign and branch decision is rational.

## 4. Interface and arithmetic review

The dimensionless normalization was checked directly against equations
(4), (8), and (15) of the small-forward-minimum note: its original
`A,B` are `a` times the `A,B` of (3), its `(M11,M12)` are
`a(n,m)`, and its coefficient `alpha` is unchanged. Since
`(1+w)^2-(w^2+U)=1+2w-U>=0`, the max with one in the original
opposite floor is exactly `I`. Thus (4) follows from the actual
exterior switching inequalities, without choosing a new multiplier.

The contractions in step 2 preserve every feasible point. In particular,
`S^2/Z` increases with `z` and decreases with `U` on the relevant
range because its `z` derivative is `2S(U-z)/Z^2>0`. The lower
bound computed from the lower `z` endpoint and upper `U` endpoint
is therefore valid; the upper factor `S/z` decreases with `z`.
The budget-implied inequalities above ensure the necessary `z<U`.

The arithmetic implementation was checked for both positive and negative
intervals. Products use all four endpoint products; a nonzero reciprocal
uses `[1/upper,1/lower]`; squares include zero when the input interval
straddles zero. Exact GMP floor and ceiling enlarge every rounded bound.
The reciprocal Hessian is `2/x^3`, and the product and chain rules retain
both mixed terms. Taylor's formula uses the exact rational midpoint and
intervals for every diagonal and off-diagonal quadratic product.
Intersecting the Taylor enclosure with the direct enclosure preserves
inclusion. Domain errors cause subdivision, and the process returns
failure if any box is unprocessed or reaches the depth limit.

The linear-budget polynomial certificate was also replayed. These
checks concern the hand reduction and supplementary rational verifier;
no Lean kernel validation is asserted.
