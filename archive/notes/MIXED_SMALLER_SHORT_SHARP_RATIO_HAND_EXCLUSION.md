# The actual smaller-short ratio is less than thirteen sixths

Date: 2026-11-08 UTC. **Result: S2.** The two terminal scalar signs
now have complete explicit hand proofs. This actual-period assembly
is accepted in
[SHARP_RATIO_HAND_AUDIT](MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_AUDIT.md).
It does not assume S1, a short-gap bound, or a physical cost lower
bound at a changed scale.

## Theorem

Every actual eligible competitive normal smaller-short mixed bridge
retained by the common-covector
[six-variable reduction](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md)
satisfies

\[
\boxed{x<13/6.}
\]

Here “actual” retains the original common PMP covector, globally
minimal active reverse centre, chosen smaller adjacent turn on a
short forward run, genuine first events, positive durations and
whole-period competitive budget. This theorem changes none of that
scope and imposes no switch-count cutoff.

## Proof

Suppose instead that \(x\ge13/6\). The accepted
[large-ratio exclusion](MIXED_SMALLER_SHORT_LARGE_RATIO_HAND_EXCLUSION.md)
gives \(x<12/5\), and the accepted
[positive-diagonal theorem](MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING.md)
gives \(D>0\), \(E_L>0\). The original shape has

\[
1\le\alpha<x\le\beta\le\alpha x,
\qquad
\operatorname{Sec}(1,x,\beta)=\operatorname{Sec}(\alpha,\beta,x)=u,
\]

and the two proved order inequalities give

\[
x+\frac{8x(\alpha-1)}{9x+8}\le\beta
\le x+\frac{x(7x+1)(\alpha-1)}{4x^2+11x+1}.
\tag{1}
\]

At the original outer first root, \(2<\tau<T\), \(R_\tau=0\)
and \(w>3/4\). Consequently the combined actual test

\[
G_\tau=R_\tau+
 \left(2-\frac{7\tau}{4T}\right)(w-3/4)
\]

is strictly positive: its weight is between 1/4 and 2. The accepted
[variable-floor reduction](MIXED_SMALLER_SHORT_VARIABLE_FLOOR_REDUCTION.md)
and its [independent review](MIXED_SMALLER_SHORT_VARIABLE_FLOOR_AUDIT.md)
then force a strictly positive scalar upper-envelope value at one of
exactly

\[
q=q_c\le1/7,\qquad q=1/7\le q_c,
\qquad q_c=\frac{\alpha^2}{x(x+2)+\alpha^2},
\tag{2}
\]

with the same original shape and incoming norm and with
\(2\le\widehat\tau\le T\). The reduction excludes its zero-scale
endpoint explicitly and continues the \(\tau=2\) endpoint to one
of (2) by a proved strictly increasing scalar comparison. It does not
transport a physical cost, upper Casimir cap or separate outgoing norm
floor to a changed scale.

On the first face, \(q_c\le1/7\) is exactly
\(\alpha^2\le x(x+2)/6\). The
[central terminal theorem](MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_SIGN.md)
applies to (1) and this central-cap condition. Its proved incoming
ceiling may be inserted by the positive u coefficient in the
variable-floor reduction; the resulting combined scalar is strictly
negative for every \(2\le\widehat\tau\le T\). This contradicts
the positive value forced on the central face.

On the second face, \(1/7\le q_c\) is exactly
\(\alpha^2\ge x(x+2)/6\). The
[outer terminal theorem](MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_SIGN.md)
applies to (1) and this outer-cap condition. Its incoming ceiling is
chosen according to the exhaustive alternatives
\(\alpha\le3/2\) and \(\alpha\ge3/2\), then inserted by the
same positive u coefficient. Both duration tests in that theorem are
strictly negative, so every combined scalar on the required duration
interval is strictly negative. This contradicts positivity on the
outer face as well.

The cap equality \(q_c=1/7\) is included in both terminal theorems;
all duration endpoints and equality boundaries have strict signs.
Thus the exhaustive endpoint alternative (2) is impossible.
This contradicts \(x\ge13/6\) and proves the theorem.

## Scope of the new conclusion

The upper-ratio contraction is independent of a lower-ratio theorem.
It supplies S2 only. The actual lower-ratio, displacement, Casimir,
root-to-shear and physical completion-cost obligations retain their
own hypotheses and proofs. In particular, this result alone does
not close the whole smaller-short exclusion H-S or the final global
hand-only audit H-A. No Lean or kernel verification is asserted.
