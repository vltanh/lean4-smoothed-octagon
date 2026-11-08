# A stronger order inequality for the exact short secants

Date: 2026-11-08 UTC. Hand lemma, accepted in the
[independent order and scale review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md).

This note strengthens the exact short-shape inequality used in the
negative-diagonal residual question. It uses the integral continuation
and the explicit logarithm bound in Sections 1--2 of
[MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL.md),
not the large polynomial certificate later in that note.
It does not assert a sign for the remaining root residual or cost.

## 1. Statement

Suppose
\[
1<x\le9,\qquad 1\le\alpha<x\le\beta\le\alpha x,
\qquad
u=\operatorname{Sec}(1,x,\beta)
 =\operatorname{Sec}(\alpha,\beta,x).
\]
Then
\[
\boxed{\alpha\ge\frac\beta x+
 \frac{4(x+1)}{7x+1}(\beta-x).}
\tag{1}
\]
For \(\beta>x\), the inequality is strict.
The upper bound \(x<9\) is already part of the actual smaller-short
compact domain; the closed endpoint is included here for the estimate.

Two useful weaker consequences are
\[
\alpha\ge\frac\beta x+\frac47(\beta-x),
\]
and, if \(x\le3\),
\[
\alpha\ge\frac\beta x+\frac8{11}(\beta-x).
\]
The coefficient \(4(x+1)/(7x+1)\) decreases with \(x\), is larger
than \(4/7\), and equals \(8/11\) at \(x=3\).

## 2. The exact branch and a rational secant-gap estimate

Fix \(x\), and continue \(\beta\) from \(x\) to its actual value
along the unique equal-secant branch \(\alpha(\beta)\).
This whole segment exists, starts at \(\alpha(x)=1\), and retains
\(1\le\alpha<x\le\beta\le\alpha x\), by the cited integral
continuation.
Put
\[
p=\alpha/\beta,\qquad q=x/\beta,
\qquad g(z)=1-\frac z{(1+z)^2},
\]
\[
\eta=u-g(q)>0,\qquad \xi=g(p)-u>0.
\]
The derivative formula is
\[
\alpha_\beta=p+\frac\eta\xi M,
\qquad M=q+\frac{x-\alpha}{\beta-1}
=\frac{(2q-p)x-q^2}{x-q}>0.
\tag{2}
\]
The explicit secant estimate cited above states
\[
\eta>\frac{(q-p)(6+p-5pq-q^2-q)}
 {6(1+p)(1+q)^2(p+q+2)}=: \eta_0.
\]
Since
\[
g(p)-g(q)=\frac{(q-p)(1-pq)}{(1+p)^2(1+q)^2},
\]
write
\[
N=(1+p)(6+p-5pq-q^2-q),\quad
W=6(p+q+2)(1-pq).
\]
Then \(0<N<W\) and
\[
\boxed{\frac\eta\xi>\frac{N}{W-N}.}
\tag{3}
\]
The positivity \(W-N>0\) also follows directly from
\(0<\eta_0<\eta<g(p)-g(q)\).
All inequalities remain strict for the nondegenerate interval \(p<q\).

## 3. An affine barrier for alpha

Set
\[
k=\frac{4(x+1)}{7x+1},\qquad
\underline\alpha(\beta)=\frac\beta x+k(\beta-x).
\]
At a contact with this barrier,
\[
p=\frac1x+k(1-q),\qquad
\underline\alpha_\beta=p+kq.
\tag{4}
\]
Only contacts with \(p\le q\) are relevant, because the actual
branch has \(\alpha<x\). Formula (4) therefore restricts a contact to
\[
q_{\min}\le q\le1,
\qquad
q_{\min}=\frac{4x^2+11x+1}{x(11x+5)}.
\tag{5}
\]
We prove
\[
\frac{N}{W-N}M\ge kq
\tag{6}
\]
on this whole possible-contact interval. Equations (2)--(3) then show
that the exact branch derivative is strictly larger than the barrier
slope at every contact.

Clear the positive denominator
\((7x+1)(W-N)(x-q)\) in (6). The resulting numerator is
\[
F=(7x+1)N\{(2q-p)x-q^2\}
       -4(x+1)q(x-q)(W-N).
\]
After substituting (4), the following explicit identity holds:
\[
\boxed{F=\frac{(1-q)(x+1)}{x^2(7x+1)^2}P(q,x).}
\tag{7}
\]
The quartic \(P\) is given completely by
\[
P(q,x)=-a(x)q^4+b(x)q^3-c(x)q^2+d(x)q-e(x),
\]
\[
\begin{aligned}
a(x)={}&860x^4+1096x^3+92x^2,\\
b(x)={}&1432x^5+2829x^4+3321x^3+583x^2+27x,\\
c(x)={}&3210x^5+12960x^4+5523x^3+787x^2+47x+1,\\
d(x)={}&8184x^5+9883x^4+8635x^3+1821x^2+145x+4,\\
e(x)={}&2024x^5+6498x^4+3181x^3+545x^2+39x+1.
\end{aligned}
\tag{8}
\]
These displayed polynomials are used through concavity and factored
endpoint values below, not through an unexplained coefficient-sign
check.

## 4. Concavity gives the quartic sign

For \(1<x\le9\),
\[
b-4a=x(x-1)(1432x^3+821x^2-242x-27)>0.
\tag{9}
\]
The last factor is positive for \(x\ge1\), for example by pairing
\(1432x^3-242x>0\) and \(821x^2-27>0\).
Consequently, for \(q\le1\),
\[
P_{qqq}=6b-24aq\ge6(b-4a)>0.
\]
Thus \(P_{qq}\) increases with \(q\), and its largest value on
\([q_{\min},1]\) is at 1. That value is
\[
P_{qq}(1,x)=2(1086x^5-9633x^4-2136x^3
                         +410x^2+34x-1)<0.
\tag{10}
\]
To see the strict sign directly, divide its parenthesis by \(x^3\).
The convex quadratic \(1086x^2-9633x\) is at most 1269 on
\([1,9]\), by its two endpoint values. Also
\(410/x+34/x^2-1/x^3\le444\). Hence the quotient is at most
\(1269-2136+444=-423<0\).
This proves strict concavity of \(P\) on the interval (5).

Its two endpoint values factor as follows:
\[
P(1,x)=2(x-1)^2(7x+1)(313x^2+38x+1)>0,
\tag{11}
\]
\[
P(q_{\min},x)=
\frac{18(x-1)^2(x+1)^2(7x+1)^2(11x+1)(15x+1)^2
                  (4x^2+11x+1)}
 {x^2(11x+5)^4}>0.
\tag{12}
\]
Concavity bounds \(P\) below by the chord between these positive
endpoint values. Thus \(P>0\) on (5), and (7) proves (6).

## 5. Complete the barrier argument

At \(\beta=x\), both the exact branch and the barrier have value 1.
At this starting contact and at every later possible contact,
(2)--(6) give
\[
\alpha_\beta>\underline\alpha_\beta.
\]
The branch is therefore strictly above the barrier immediately after
\(\beta=x\), and cannot have a first subsequent crossing from above.
If the barrier were to reach \(x\) before the actual endpoint, such
a crossing would be necessary because the exact branch remains below
\(x\); this is excluded by the same argument. This proves (1) on the
entire actual continuation segment.

No scale, root residual, determinant, or physical cost was changed in
this proof. The result is a restriction on the exact fixed short shape.
