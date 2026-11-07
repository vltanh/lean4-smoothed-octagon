# Independent review of the unit-shape hand exclusion

Date: 2026-11-07 UTC.

**Verdict: accepted.** The scalar theorem in
[MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION](MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION.md)
proves \(N(1)>0\) on its complete stated domain. It excludes the
reverse-next lower face \(k_{\min}=1\), including ties with the other
shape bounds. It also applies to the stated common-domain cases with
\(d\le c\). The reverse scale face remains a separate obligation.

This is an internal mathematical review. All polynomial identities and
all signs used by the argument are displayed in the proof. Arithmetic
and symbolic checks supplement those identities; no interval cover,
numerical minimizer or executable sign test is a premise.

## 1. Actual data and the lower-shape comparison

The review checked the normalization against
[MIXED_NONSHORT_SHAPE_MONOTONICITY](MIXED_NONSHORT_SHAPE_MONOTONICITY.md).
At \(k=1\), its diagonal, outgoing upper-envelope norm, residual and
positive multiplier are precisely the quantities in the new theorem.

For an actual reverse-next candidate,
\[
k\ge\max\{1,2t+x,29t^2/4\},\qquad
k<2t+2x+x^2.
\]
If the displayed maximum equals one, then
\(x\le1-2t\) and
\(t\le2/\sqrt{29}<13/35\); the last inequality is exactly
\(4900<4901\). Lowering the actual shape to one preserves its necessary
negative residual by the proved strict increase of \(N\) in \(k\).
The exact incoming secant and the incoming missing-control floor are
unchanged in this comparison. No outgoing floor or Casimir bound is
transported to an artificial boundary root.

The scalar theorem itself does not require a reverse successor.
Its broader application has exactly the stated additional domain
requirements, rather than an implicit extension to \(d>c\).

## 2. The logarithmic replacements and floor slack

The lower bound for \(\log(1+x)\) makes \(v<\bar v\). The upper
bound for \(\log q\) makes \(F_\ell<F_{p/W}(q)\le v\).
The coefficient of \(\log q\) in \(N\) is negative, and independent
collection gives
\[
N_v=-xq\{1+tx+tW(1-2t)
 +(q-1)[X+txX^2]\}<0.
\]
Both replacements therefore decrease \(N\).

The factor \(6(q+1)W^2X^3\) is positive. Since \(q-1>0\) and
\(\bar v-F_\ell>0\), positivity of the corrected polynomial \(P\)
does imply \(\bar N>0\), hence \(N>0\).
The floor slack is retained in the required direction.

Independent expansion from the rational formulas for \(N,\bar v,F_\ell\)
reproduces the cubic in \(q-1\). It also reproduces all four cubic
expansions in \(s=1-2t-x\), both four-entry Bernstein arrays, and the
four cap polynomial identities in the appendices. These are finite
explicit identities, not an unlisted coefficient-sign assertion.

## 3. The zero-q-increment coefficient is handled at the correct shape

The domain becomes
\[
\max(0,9/35-x)\le s\le\min(1-x,x+x^2),\qquad 3/25<x<1.
\]
The strict lower bound on \(x\) follows from the centre gap and
\(2(3/25)+(3/25)^2<9/35\). Every later weak enlargement is in the
safe direction.

The proof correctly avoids applying the shorter order-face
\(q=1\) formula at arbitrary shape. Instead it first proves
\(\bar v<U(t)\), and therefore
\[
\partial_k\bar N(1;k)
 =x\{(1-\bar v)(1+tW)-t(1-t^2)\}
 >t^2(1-t)x^2>0.
\]
It lowers \(k=1\) to \(2t+x\) only for this scalar comparison.
The order-face identity is then used at the shape where it is valid.

The resulting \(P_0\) has the four displayed quadratic lower bounds.
Since \(x<1\), its possible negative cubic is absorbed by the positive
quadratic coefficient, leaving the stated strictly positive expression.
This proves \(C_0>0\), including the tie \(2t+x=1\).

## 4. Every coefficient sign has a complete hand argument

The derivative bounds for \(J_1,J_2\) are positive throughout the
permitted \(s\) interval. Their lower endpoints are either the cap
\(t=13/35\) or \(s=0\); both are covered by the displayed signs.

For \(J_3\), the two endpoint bounds on
\(A_{32}+3A_{33}s\) establish concavity without assuming a sign for
\(A_{33}\). The coarse collections are valid: the positive tails minus
the negative cubic and quartic terms leave at most \(480x^2\) in
\(A_{32}\) and \(561x^2\) at the upper endpoint \(s=1-x\).
The smaller-\(x\) tail bound uses \(x\le1/4\) with its correct powers.
All possible lower and upper \(s\) endpoints then have strict positive
values. The two completed-square comparisons have positive
discriminant gaps.

For \(J_4\), the direct bound on \(3/25<x<1/8\) leaves a margin
greater than four. For \(x\ge1/8\), its quadratic derivative has
three positive Bernstein coefficients. The displayed initial
polynomials are increasing and positive at \(1/8\).
The remaining \(s=0\) polynomial is uniformly strongly convex:
\(f''>5000\) on \(x\ge9/35\), and the exact value and derivative at
\(3/10\) give \(f>5779/10000\) by completing a square.
This short convexity lemma was supplied by the interface reviewer and
separately checked by the proof author.

For \(J_*\), the two choices \(S=x+x^2\) and \(S=1-x\) cover the
whole domain. All four Bernstein coefficients have the displayed
positive lower bounds on each range. The \(s/S\) parameter is in
\([0,1]\), so the basis coefficients are nonnegative.

Finally, each cap polynomial takes its minimum at an endpoint:
ordinary concavity applies to \(Q_1,Q_2\), while
\((Q_i'/x)'<0\) permits only an interior maximum for \(Q_3,Q_4\).
All eight rational endpoint bounds were checked against the complete
displayed polynomials.

## 5. Six signs imply positivity for every q

The normalization by \(C_0>0\) converts the six inequalities into
the stated affine bounds on the three cubic coefficient ratios.
For a fixed \(z=(q-1)/x\ge0\), the lower cubic is affine in the
remaining ratio on each of its two intervals. Thus only
\(0,13/15,53/20\) need be considered.

The elementary positive bound for \(f_0\) covers \(z\le2\) and
\(z\ge2\). The two displayed square identities for \(f_1,f_2\)
are exact, and their residual constants are strictly positive.
Consequently \(P>0\) for every \(q>1\), with no upper bound on \(q\)
and no subdivision of its range.

Combining this with the actual-data implication proves the unit-shape
exclusion. This review is scoped to the unit face. The scale face is now closed by
the separate [complete reverse hand theorem](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md)
and [audit](MIXED_NONSHORT_REVERSE_HAND_AUDIT.md). The short-case and
forward-successor hand obligations remain open.
