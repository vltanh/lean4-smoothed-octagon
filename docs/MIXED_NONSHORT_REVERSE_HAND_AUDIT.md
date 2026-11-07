# Independent review of the nonshort reverse hand exclusion

Date: 2026-11-07 UTC.

**Verdict: accepted.** The argument in
[MIXED_NONSHORT_REVERSE_HAND_EXCLUSION](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md)
excludes every actual reverse successor in the smaller-nonshort
minimum window under its named hand prerequisites. It is uniform in the
surrounding period and needs no interval cover. The nonshort forward
successor, the smaller-short case, and final hand-only assembly remain
separate obligations.

The unit-shape argument has its own
[independent review](MIXED_NONSHORT_UNIT_SHAPE_HAND_AUDIT.md).
This note checks the strengthened use of the order face, the new scale
strip, and their exhaustive combination. It is an internal mathematical
review, not a kernel-checking or external peer-review claim.

## 1. Exact scope of the reused order face

The reviewer reread the entire
[order-face proof](MIXED_NONSHORT_REVERSE_ORDER_FACE_REDUCTION.md).
The inequality \(k_o\ge29t^2/4\) enters that proof only in the
preliminary deduction \(x>1/4\). After that deduction, its sign argument
uses precisely
\[
1/5<h<1,\qquad 0\le s<4/3,\qquad h+s=x>1/4.
\]
The new statement supplies \(x>1/4\) directly. Its duration bound
\(x<7/3-(10/3)t\) supplies \(s<4/3\), and also the weaker
\(x<5/2\) used at the other endpoint.

The incoming floor at the fixed normalized margins and the
\(k\)-independent star inequality \(1<q<W/p\) give
\(1<q\le W/k_o\) by the swapped-secant comparison.
On that entire interval the auxiliary outgoing margin lies between
\(t\) and \(c\), both at most \(p\). Thus the residual is concave in
\(q\), with its two already proved positive endpoint values.

The strengthened order-face lemma therefore follows from the existing
hand proof. It does not reuse the old scale hypothesis at an endpoint
where that hypothesis might fail.

## 2. The new polynomial and its derivative identities

The reviewer reconstructed the normalized residual from its exact
diagonal and outgoing-envelope formulas, keeping arbitrary \(k\).
The rational replacements for \(v\) and \(\log q\), and the subtraction
of the incoming-floor slack, produce exactly the polynomial \(P_k\)
defined in the proof.

Substitution \(k=29t^2/4\) gives a cubic in \(y=q-1\).
Independent coefficient collection reproduces every one of the
34 displayed cubic polynomials in the appendix for its four
\(t\)-derivatives. The table is complete; its sign argument uses the
displayed polynomials and elementary rational bounds, with no
executable coefficient-sign premise.

For every nonspecial table entry, the power-envelope rule applies
term by term because
\[
13/35\le t\le14/35.
\]
Positive terms are bounded below at \(13/35\), negative terms at
\(14/35\). Every resulting rational value is at least the stated
integer lower bound. The two constant entries attain their bounds;
all other required signs have positive rational margins.

For \(E_{00}\), the upper derivative estimate is
\[
1080-4752(13/35)+4176(2/5)^2=-2952/175<0.
\]
Thus this coefficient decreases, and its minimum is
\(5616/125>44\) at \(t=2/5\).
The exceptional treatment has the correct direction.

## 3. Strict coefficientwise increase on the whole strip

The four derivative bounds follow directly from the table.

- The first is at least \(44x^2>0\).
- The second is at least \(102x-2x^7-x^8\ge99x>0\).
- In the third, the negative coefficients sum to \(2301\), and every
  affected power is at least four. Since \(x<1/3\), their total
  magnitude is at most \(2301/81<48\).
- In the fourth, the negative coefficients sum to \(167\), and every
  affected power is at least six. Their total magnitude is at most
  \(167/729<64\).

Therefore every coefficient increases with \(t\) throughout the stated
rectangle. Since \(y=q-1\ge0\), this gives the claimed comparison of
the complete polynomial, not merely its value at a sampled \(q\).

## 4. No incoming floor is transferred to the bottom of the strip

The centre gap and monotonicity of \(29t^2/4-2t\) give
\[
2x+x^2>9/35+1/4900.
\]
Together with \(x\le9/35\), this places \((t_0,x)\), where
\(t_0=13/35\), inside the shape domain of the unit-shape polynomial
proof.

The logical distinction at this step is correct: the unit-shape proof
establishes \(P_1(t_0,x,y)>0\) from its six coefficient signs using
only the shape domain. Its incoming norm floor is used later, when
deducing \(N_1>0\) from \(P_1>0\). Consequently the new application
does not assume the actual floor at the changed value \(t_0\).

At that bottom value, \(\bar v<U(t_0)\) and
\[
1-\frac{L_+(q)}{q-1}
=\frac{(q-1)(5q+1)}{6q(q+1)}>0.
\]
These inequalities give strict increase of \(\bar N_k\), hence of
\(P_k\), in \(k\). The subtracted floor term and prefactor are
independent of \(k\). Since
\[
k_s(t_0)=4901/4900>1,
\]
the proof obtains strict positivity at the bottom of the scale strip
and then throughout the strip.

Only after this polynomial comparison returns to the original \(t\)
does the proof use
\(\bar v>v\ge F_{p/W}(q)>F_\ell\).
The coefficient of \(v\) is negative there because \(k_s>1>2t\);
the coefficient of \(\log q\) is negative as well.
Thus \(P_{k_s}>0\) implies \(N_{k_s}>0\) using the actual unchanged
incoming floor. No norm, trajectory, or Casimir premise has been moved
to the auxiliary \(t_0\).

## 5. Exhaustiveness and actual-period conclusion

The actual smaller-nonshort reverse-next window has all inequalities
listed in Section 4 of the proof. In particular its physical scale
bound, reverse order bound and centre gap give three genuine lower
shape comparisons. The residual is strictly increasing in \(k\) while
the exact incoming secant and its floor stay fixed.

The three cases are exhaustive:

1. \(t\le13/35\) and \(x\le1-2t\) are covered by the unit-shape theorem.
2. \(2t+x\ge1\) and \(x>1/4\) are covered by the strengthened order face.
3. Failure of both cases forces \(t>13/35\) and \(x\le9/35\), the
   new scale strip.

The overlaps and shared boundary values cause no gap: each relevant
sign is strict, and the comparison uses weak lower shape bounds.
Every case contradicts the original necessary \(N_k<0\).

The conclusion therefore retains the same actual primary multiplier,
genuine incoming switch, global-minimum normalization and twisted-period
interface of the preceding reductions. Neither endpoint rank nor a
lower bound on positive durations enters this new argument. No
outgoing norm floor or competitive Casimir is asserted for an artificial
boundary root. The entire reverse-successor branch is closed by the
linked hand inequalities.


## 6. Accepted common-order corollary

The final source adds a common-window consequence after its reverse
exclusion; Sections 1--4 and the derivative appendix are unchanged.
The reviewer accepts this addition as well.

Every scalar premise used in the three-case contradiction, except
\(k\ge2t+x\), already holds in the common smaller-nonshort window.
Thus a common point with \(N_k<0\) must satisfy \(k<2t+x\).
Since \(k\ge1\), this gives \(p=t+x>c=1-t\).

The first argument \(A_0=W/q-p\) in its incoming-floor secant is in
\((0,c)\): the two strict inequalities follow respectively from the
actual star bound and \(q>1\). Since \(t<c<p\), strict swapped-secant
order and the retained floor give
\[
\operatorname{Sec}(A_0,p,c)
\le\operatorname{Sec}(t,c,p)
<\operatorname{Sec}(t,p,c).
\]
Strict decrease in the starting point therefore forces \(A_0>t\),
or \(q<W/(p+t)\). This comparison uses no changed shape or outgoing
norm.

Finally \(B_k<(p+t)W\) follows exactly from \(k<2t+x\). Hence the
actual next active margin in normalized units satisfies
\[
r=qB_k/W-p<B_k/(p+t)-p<c.
\]
The original global-minimum assignment supplies the other endpoint
\(a\le r\). Returning to physical units gives
\[
a\le r<c\le b_*<d.
\]
All quantities here come from the same actual window, and the
argument makes no assumption about its successor sign.
This is a strengthened necessary order for the remaining forward
successor, not an exclusion of that successor.
