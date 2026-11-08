# A smaller short-side bridge cannot occur at a global minimum

Date: 2026-11-07. Hand reduction and completed directed-interval
certificate, with an [independent internal audit](MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT.md).
No Lean, Lake, typechecking or CI.

## Theorem and exact scope

Consider a competitive finite normal mixed minimizing period in the
remaining M2 class. Let \(a\) be a globally smallest active margin,
which the established minimum theorem places at a reverse centre.
Choose the smaller of its two adjacent turn margins, including either
choice when they are equal.

**The forward run adjacent to that chosen turn cannot be short.**

Consequently the M2 contradiction argument can always be oriented so that
the smaller adjacent turn belongs to a forward run of length at least
two. The [nonshort continuation alternative](MIXED_SMALLER_TURN_CONTINUATION.md)
then applies.

**Completion follow-up:** the present theorem handles the smaller-short
branch. Both complementary nonshort successors are now excluded by the
[reverse boundary theorem](MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md)
and [forward endpoint theorem](MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION.md).
The [uniform whole-period theorem](MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md)
and [its independent audit](MIXED_GLOBAL_NONSHORT_PERIOD_AUDIT.md) combine
all three possibilities and close M2. This note's mathematical formulas,
scalar domain and completed certificate remain unchanged.

The proof uses the given period's normal covector, physical cost,
global minimum, actual exterior reverse switch, and complete-period
angle budget. It does not posit a closed local window, a replacement
trajectory, a new multiplier, or an endpoint-rank condition.

## 1. The actual bridge lies in a fixed six-variable domain

Orient the incoming short bridge as in
[MIXED_GENERAL_SHORT_DEFECT_INTERFACE](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md).
Its four consecutive active margins, divided by \(a\), are
\((\alpha,\beta,x,1)\); the other adjacent turn is \(y\ge x\).
Define

\[
\rho=\frac{a^2}{a^2+4},\qquad r=\frac1{1+x},\qquad
\delta=\frac\beta x-1,
\]

and retain the normalized opposite turn norm \(v\) and central pairing
\(E\). The first turn norm is the analytic secant
\(u=\operatorname{Sec}(1,x,\beta)\). On the actual bridge it also
equals \(\operatorname{Sec}(\alpha,\beta,x)\).

The [six-variable reduction](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md)
proves that every actual point is in the closed rectangle

\[
\boxed{
(r,\delta,\alpha,\rho,v,E)\in
[1/10,1/2]\times[0,2]\times[1,631/100]\times
[1/226,3/20]\times[3/4,1]\times[-23/16,9/20].}
\tag{1}
\]

The geometric compact domain gives \(a\ge2/15\), and the reverse-centre
scale theorem gives \(\rho<3/20\). Both strict and weak switch bounds,
the global minimum, and the Casimir bounds

\[
\frac{27}{256}<\Gamma:=\gamma^2
=\frac{4uv-E^2}{16(1-\rho)^2}<\frac{23}{125}
\tag{2}
\]

give the other bounds in (1). The reduction contains their exact
derivations, including \(\delta<2\), \(\alpha^2<675/17\), and
\(E\le3\rho\). No bound in (1) comes from numerical optimization.

The opposite turn can be removed by valid inequalities. In particular
the strong rational upper pairing condition is

\[
r(u+v-2)+2r^3-\rho r^2+\rho-r^2E\ge0.
\tag{3}
\]

Its proof uses \(\log z\le z-1\); merely dropping the logarithm gives
a weaker relaxation that does not suffice. The lower pairing condition
is exactly the central nonnegative stationary-control slack.

## 2. Every actual point satisfies the implemented residuals

The fixed caller retains the following necessary conditions, with the
exact formulas and positive clearing factors in the two interface notes.

| Group | Necessary data retained |
| --- | --- |
| Bridge order and two turn secants | Minimum-margin inequalities, strengthened turn order, \(u=\operatorname{Sec}(1,x,\beta)\), and the relaxed inequality \(\operatorname{Sec}(\alpha,\beta,x)\le u\) |
| Central reverse arc | Both incident norm ceilings, both Casimir bounds, the strong upper pairing bound (3), the lower pairing/slack polynomial, and \(E\le3\rho\) |
| Actual outer reverse switch | Transported norm and pairing, reverse-centre scale, incident norm bounds, and the rational convex-chord upper bound on the root maximum |
| Hamiltonian maximization | Nonnegative stationary-control slack at the initial switch, bridge midpoint and outer entrance |
| Complete-period geometry and cost | Actual polar-angle signs, both modulus filters, and the exact two-turn physical cost with its completion budget |

The second secant equality is deliberately relaxed to a one-sided
inequality. The rational cost expression remains the physical bridge
cost at every actual point, because actual points satisfy both equalities.
It need not be the cost of a trajectory at every point of the larger
comparison set. Excluding that larger set is sufficient.

For the endpoint angle, put \(\kappa=\sqrt{12\Gamma}\) and
\(T_\kappa=2\kappa(1-\rho)^2\). The exact trace expressions \(A,B\)
satisfy on the actual window

\[
A>0,\quad 0<B<A,\quad A\ge2T_\kappa,\quad A+B\ge4T_\kappa,
\]

\[
\Delta\theta=\frac\pi6+
\arctan\frac{3B-A}{\sqrt3(A+B)}.
\tag{4}
\]

The global spectral bound requires

\[
C_{\rm bridge}+(\kappa+3/2)(\pi/3-\Delta\theta)
\le A_{\rm oct}.
\tag{5}
\]

The caller weakens (5) with \(\pi>6283/2000\) and
\(A_{\rm oct}<2501/800\). It evaluates (4) on a whole interval box
only after verifying \(A+B>0\) on that whole box. Thus no feasible-set
sign is improperly substituted into a derivative calculation.

## 3. The scalar cover is rigorous and complete

The published caller is
[`mixed_smaller_short_interval_certificate.cpp`](../explorations/mixed_smaller_short_interval_certificate.cpp).
It uses the [documented directed MPFR engine](INTERVAL_ARITHMETIC_ENGINE.md)
at 80 significand bits. Every proof interval endpoint is rounded in the
required direction. Exact rational constants are supplied as integers
and denominators. The logarithmic divided difference is evaluated by a
convergent series with bounds for its actual value and first two
derivatives, including at coincident endpoints.

Necessary-condition contractions preserve every possible actual point.
Every remaining box is either excluded by a strictly negative upper
bound on a necessary residual, or bisected into two closed halves.
Residual bounds are natural interval bounds or Taylor enclosures using
the actual full-box Hessian and the actual displacement from the chosen
representable centre.

A native floating-point linear program may propose weights. It never
excludes a box. Each proposed weight is converted to an exact
nonnegative multiple of \(2^{-20}\), and a new directed Taylor upper
bound must prove the corresponding weighted residual sum strictly
negative. This is a valid contradiction for any such weights; the LP's
own correctness or accuracy is not a mathematical premise.

The independent review checked the domain reduction, every residual,
every contractor, the arithmetic engine, analytic domains, coverage and
failure behavior before the full run. The unchanged source then returned

```text
FINAL nodes 107977 stack 0 depth 37 unknown 0 domain_splits 0 sec 571.21
PASS: the full initial scalar box is excluded by directed interval bounds.
```

There are **53,989 excluded leaves**. The count identity
\(107977=2\cdot53989-1\) agrees with a complete binary tree from one
root. The program exited successfully with no bad MPFR flags. It reached
neither an unresolved box nor its depth limit. The full result, source
hashes, compiler/runtime and reproduction command are recorded in
[`mixed_smaller_short_interval_certificate_result.txt`](../explorations/mixed_smaller_short_interval_certificate_result.txt).

This is a computer-assisted directed-interval theorem, with the stated
MPFR/GMP/compiler trust boundary. It is not a floating-point optimizer's
verdict or a Lean kernel verification.

## 4. Return to the actual period

Suppose the chosen smaller turn belonged to a short forward run. The
same actual period would supply a point of (1) satisfying every residual
in Section 2. Section 3 excludes every such point. This contradiction
proves the theorem.

The closed domain includes equal minimum margins, equality in the
ordering of adjacent turns, weak third-control ties and all relevant
zero-duration limits. Divided differences keep their analytic limits.
The proof does not depend on the sign of an assumed bridge diagonal or
on a constrained endpoint rank. Reflection/time reversal and cyclic
continuation preserve the physical cost and actual twisted covector, so
windows crossing the chosen seam are covered as well.

The complementary smaller-nonshort branch is now excluded by the
[reverse boundary](MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION.md) and
[forward endpoint](MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION.md) theorems.
Together with the present result, they give the
[uniform M2 exclusion](MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md), with
its [whole-period audit](MIXED_GLOBAL_NONSHORT_PERIOD_AUDIT.md). The final
cost and affine equality consequence is recorded in
[GLOBAL_COST_EQUALITY_ASSEMBLY](GLOBAL_COST_EQUALITY_ASSEMBLY.md).
