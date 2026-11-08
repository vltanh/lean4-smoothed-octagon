# A conditional monotonicity of the forward Casimir

Date: 2026-11-08 UTC. Conditional hand lemma, accepted in the
[endpoint audit](HAND_ENDPOINT_REDUCTIONS_AUDIT.md), Section 19.

This note identifies one sufficient ratio bound that would remove the
separate lower-Casimir endpoint in the remaining nonshort forward case.
The additional bound \(\chi\ge4/7\) is an explicit hypothesis here;
it is not yet asserted for every actual window.

## 1. Fixed actual geometry and notation

Keep the common nonshort normalized data
\[
t=\frac a{a+c},\quad x=\frac{d-a}{a+c},\quad
k=\frac{a^2+4}{(a+c)^2},\qquad c=1-t,\quad p=t+x,\quad W=1+x.
\]
In formulas below c and p denote the normalized incoming and forward
centres. Put
\[
s=k-t^2,\quad B=s+p^2,\quad e=q/W,\quad Z=eB,\quad r=Z-p,
\quad \chi=pe.
\]
The common hand prerequisites give
\[
k\ge1,\quad a_{\rm normalized}=t\le r<c<p,\qquad
v=\operatorname{Sec}(t,c,p)>\frac34,
\]
and the original incoming missing-control floor
\[
v\ge F_{p/W}(q)
=1+\frac{p^2q}{W^2}-\frac{pq\log q}{W(q-1)}.
\tag{1}
\]
The actual star bound gives \(pr<s\), equivalently \(0<\chi<1\).

Assume in addition
\[
\frac13\le t<\frac25,\qquad \chi\ge\frac47.
\tag{2}
\]
The first-event stationarity equation, with geometry and v fixed, writes
the diagonal as an affine function of the outgoing norm w:
\[
L=\log q+\frac{Wv-c+p^2/W}{p},\qquad
H_d(w)=BL+\frac e p B^2(w-1)+\frac{p(1-\chi)}e.
\tag{3}
\]
Define the scalar squared Casimir on this line by
\[
\Gamma(w)=\frac{4B^2vw-H_d(w)^2}{16s^2}.
\tag{4}
\]

**Conditional theorem.** Under these hypotheses,
\[
\boxed{\Gamma'(w)\le-\frac{135B^2}{108416s^2}<0
       \qquad(w\ge3/4).}
\tag{5}
\]
All inequalities used here are on the original fixed geometry or on
the explicit stationarity line (3).

## 2. A geometric gap from the incoming turn floor

Write \(j=p-c=2t+x-1>0\). Then
\[
\boxed{j<1/4.}
\tag{6}
\]
To prove this, the usual two-atanh secant upper bound and the actual
turn derivative floor give
\[
t<T(x),\qquad
T(x)=\frac{12+10x-x^2-2x^3}{3(x+2)^3},\qquad T'(x)<0.
\]
If \(j\ge1/4\), then \(x\ge z:=5/4-2t\).
By (2), \(9/20<z\le7/12\).
The exact identity
\[
24(z+2)^3\left(\frac58-\frac z2-T(z)\right)
=24+4z-46z^2-41z^3-12z^4
\tag{7}
\]
has a strictly positive right side on that interval.
Indeed its derivative is
\(4-92z-123z^2-48z^3<0\), while its value at \(7/12\)
is \(83/72>0\).
Since \(t=5/8-z/2\), this gives \(T(x)\le T(z)<t\),
a contradiction.

It follows that \(p=c+j<5/4-t\). Consequently
\[
s-p^2\ge1-t^2-p^2
>1-t^2-(5/4-t)^2\ge\frac7{144}>0.
\tag{8}
\]
The last quadratic increases on \(1/3\le t\le2/5\), and its
value at \(1/3\) is \(7/144\).

Set \(A=Z/p=1+r/p\).
Using \(r\ge t\), (6), and \(r<c<p\), one obtains
\[
\boxed{\frac{15}{11}\le A<2,\qquad \frac A\chi
       =\frac{B}{p^2}>2.}
\tag{9}
\]
Here \(t/p>t/(5/4-t)\ge4/11\).
Weak endpoints in (9) suffice for the scalar comparison below.

## 3. Bound the derivative by a convex quadratic

Rearranging the original floor (1) gives
\[
\log q\ge(q-1)
 \left(\frac{W(1-v)}{pq}+\frac pW\right).
\]
Substitution in L yields the simple lower bound
\[
\boxed{L\ge1+\chi-\frac{1-v}{\chi}.}
\tag{10}
\]
This uses the actual incoming floor at the unchanged coordinates.

From (3), for every \(w\ge3/4\),
\[
\begin{aligned}
2v-\frac{eH_d(w)}p
&=2v-AL-A^2(w-1)-(1-\chi)\\
&\le2v-A\left(1+\chi-\frac{1-v}{\chi}\right)
       +\frac{A^2}{4}-1+\chi.
\end{aligned}
\]
The coefficient of v in the last expression is
\(2-A/\chi<0\) by (9). Thus \(v\ge3/4\) gives
\[
2v-\frac{eH_d(w)}p\le
f(A,\chi):=\frac{A^2}{4}
 -A\left(1+\chi-\frac1{4\chi}\right)+\frac12+\chi.
\tag{11}
\]
For \(A>1\),
\[
\partial_\chi f=1-A\left(1+\frac1{4\chi^2}\right)<0.
\]
By (2), \(f(A,\chi)\le f(A,4/7)\).
This last function is convex in A, so its maximum on
\([15/11,2]\) is at an endpoint. The exact endpoint values are
\[
f(15/11,4/7)=-\frac{135}{13552},\qquad
f(2,4/7)=-\frac{11}{56}.
\]
It follows that
\[
2v-\frac{eH_d(w)}p\le-\frac{135}{13552}<0.
\]
Differentiating (4) now gives (5).

## 4. Consequence for the actual outgoing-norm interval

The established
[forward boundary reduction](MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md)
shows that, on the stationarity line (3), the next norm is affine and
strictly decreasing in w under the actual star bound.
Let \(w_{3/4}\) be its unique value for which that next norm equals
\(3/4\). The original next forward switch has norm strictly greater than
\(3/4\), by [HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md),
Section 4, equation (13), using its actual positive turn and actual
missing-control floor. Hence its actual outgoing norm satisfies
\[
3/4<w_{\rm actual}<w_{3/4}.
\]
Equations (4)--(5) therefore imply directly
\[
\boxed{\Gamma_{\rm actual}>
       \Gamma(w_{3/4}).}
\tag{12}
\]
This comparison uses the same original first-event stationarity and
covector. It does not assign the competitive cap to the zero-duration
boundary root.

If the added ratio hypothesis in (2) is proved for every remaining
window, a hand lower bound
\(\Gamma(w_{3/4})>9193/50000\) would exclude that whole forward case.
A separate comparison of the solved lower endpoint, the incident-ceiling
shape endpoint, or a disconnected set of eligible shapes would then
be unnecessary for this route.

This note does not prove \(\chi\ge4/7\), does not prove the
upper-endpoint lower bound in the preceding paragraph, and does not
claim completion of the forward-successor exclusion.
