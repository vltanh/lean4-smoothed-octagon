# Independent hand audit of the nonshort shape reductions

Date: 2026-11-07 UTC. Two independent internal mathematical readings.
The reviewed implications use the displayed identities and elementary
sign proofs, with no runtime exclusion premise.

## 1. Affine increasing residual numerator

[MIXED_NONSHORT_SHAPE_MONOTONICITY](MIXED_NONSHORT_SHAPE_MONOTONICITY.md)
is accepted. Normalizing by the unchanged positive pair sum gives the
stated secant, diagonal and outgoing envelope. Multiplication by
`t*B*q*W` clears positive denominators and cancels the quadratic shape
terms. The displayed coefficient of `k` is correct.

Its derivative with respect to `v` is negative because the remaining
bracket is `(q-1)(x+2)+1+tW>0`; its logarithm coefficient is also
negative. Inserting the incident norm ceiling and `log(q)<q-1` gives
exactly the displayed strictly positive factored lower bound. Thus
the strict increase in `k` is proved throughout the claimed domain.
The equivalence `a^2<=1/4` with `k>=17t^2` follows from the stated
normalization. Lowering `k` preserves the required residual sign, but
does not preserve arbitrary physical inequalities; the note explicitly
limits its conclusion accordingly.

## 2. Weighted secant concavity

[MIXED_NONSHORT_REVERSE_SHAPE_REDUCTION, Section 1](MIXED_NONSHORT_REVERSE_SHAPE_REDUCTION.md#1-a-strictly-concave-weighted-secant-deficit)
is accepted. Differentiating the rational integrand twice gives the
displayed kernel. It changes sign once, from positive to negative,
at `dr/(2d+3r)`. The exact integral over `[0,d]` has the stated second
derivative. The elementary logarithm bound follows by differentiating
its rational difference, whose derivative is strictly positive.

If the lower endpoint lies below the kernel's sign change, deleting
the initial interval removes a nonnegative contribution from a strictly
negative integral. If it lies above the sign change, all the retained
interior kernel is negative. This proves strict concavity for every
`0<=a<d` and `r>0`, including the endpoint `a=0`. The derivative limit
and resulting affine lower bound follow from the same integral formula.

## 3. Exact shape dependence and endpoint alternative

Eliminating the diagonal from the displayed central and forward
stationarity equations gives the stated coefficients of `B^2`, `B`
and 1. The denominator `D0` is positive because
`H-pW=(1-t)x>0` and `q>1`. Thus the solved outgoing norm is
`1-A/B-C/B^2` with shape-independent `A,C`.

Multiplying its reverse secant difference by `B^2` yields precisely
`(W/q)^2 J(r0)-AB-C`. Since `r0'=q/W`, its second shape derivative
is exactly `J''(r0)<0`.

The root ceiling gives a finite upper shape endpoint because the
residual numerator has positive slope. The third lower endpoint bound
retains the actual reverse log-concavity `r0>=sqrt(tp)>0`, so the
entire comparison interval stays inside the secant's domain. Concavity
then proves the necessary strict endpoint disjunction, including ties
among the lower bounds. At the upper endpoint, the root is its incident
upper envelope, as claimed.

## 4. Reflected reverse-only centre gap

The addendum to
[MIXED_NONSHORT_UPPER_ENVELOPE_GAP](MIXED_NONSHORT_UPPER_ENVELOPE_GAP.md)
is also accepted. Reflecting and reversing the actual two-switch run
from the next reverse centre exchanges the roles of its two turns.
The same transformed physical covector has the required outgoing
floor and genuine positive forward factor. The core upper-envelope
lemma needs no smaller-side ordering, so it gives `d^2+2dr>4` in
addition to `d^2+2cd>4`.

Only that centre inequality is transferred; the smaller-side duration
corollary is not silently applied at the other centre.

## Scope

The new shape endpoint signs have not been proved. An enlarged endpoint
domain may contain points that violate original shape-dependent
constraints. Such constraints may only be retained after proving their
direction of transfer, or by explicitly adding the appropriate shape
bound. The accepted conclusions are the dimension reductions and
necessary alternatives, not a replacement for the reverse or low-a
interval exclusion.
