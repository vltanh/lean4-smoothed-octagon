# An upper order bound on the small short-shape domain

Date: 2026-11-08 UTC. Hand lemma, accepted in the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md),
Section 5. The bounds on x and delta in the statement are hypotheses
here; this note does not derive them from the outer reverse root.

## 1. Statement and exact continuation

Suppose
\[
1<x\le\frac{15}{7},\qquad
1\le\alpha<x\le\beta\le\alpha x,
\qquad
u=\operatorname{Sec}(1,x,\beta)
 =\operatorname{Sec}(\alpha,\beta,x),
\]
and put
\[
0\le\delta=\frac\beta x-1\le\frac1{19}.
\]
Then
\[
\boxed{\alpha\le1+3\delta.}
\tag{1}
\]
The inequality is strict when delta>0.

Use the complete equal-secant continuation and derivative formula
already stated in Section 2 of the
[strong lower-order theorem](MIXED_SMALLER_SHORT_STRONG_ORDER.md).
For fixed x, this continuation begins at beta=x,alpha=1 and retains
the short ordering up to the actual beta. With
\[
p=\frac\alpha\beta,\qquad q=\frac x\beta,\qquad
g(s)=1-\frac{s}{(1+s)^2},
\]
\[
\eta=u-g(q)>0,\qquad \xi=g(p)-u>0,
\]
the formula is
\[
\alpha_\beta=p+\frac\eta\xi M,
\qquad M=\frac{(2q-p)x-q^2}{x-q}>0.
\tag{2}
\]
Throughout this continuation, q>=19/20.

## 2. An upper bound for the secant-gap ratio

The second secant is the average of g over [p,q]. Its one-panel
Simpson upper estimate is
\[
u<\frac{g(p)+4g((p+q)/2)+g(q)}6.
\tag{3}
\]
This is an analytic inequality: the elementary Simpson remainder for
the average is minus \((q-p)^4g^{(4)}(\zeta)/2880\), for some
zeta in (p,q), and
\[
g^{(4)}(s)=\frac{24(4-s)}{(1+s)^6}>0
\qquad (0<p<s<q\le1).
\]
There is no numerical quadrature premise in (3).

Write m=(p+q)/2 and
\[
N=g(p)+4g(m)-5g(q),\qquad
Z=5g(p)-4g(m)-g(q).
\]
Both N and Z are positive, since g strictly decreases on [p,q].
The function \((u-g(q))/(g(p)-u)\) strictly increases with u, so
\[
\frac\eta\xi<\frac NZ.
\tag{4}
\]

## 3. The upper barrier and its rational derivative test

Consider
\[
\overline\alpha(\beta)=1+3(\beta/x-1).
\]
At a contact with this barrier,
\[
p=\frac{3-2q}{x},\qquad
\overline\alpha_\beta=\frac3x=p+\frac{2q}{x}.
\tag{5}
\]
Only contacts with p<q are relevant because the exact branch has
alpha<x. We prove
\[
\frac NZ M<\frac{2q}{x}
\tag{6}
\]
at every possible contact. Equations (2), (4) and (5) then give
\(\alpha_\beta<\overline\alpha_\beta\).

All denominators being positive, (6) is equivalent to positivity of
\[
P=2q(x-q)Z-x\{2q(x+1)-q^2-3\}N.
\]
After substituting (5), the following rational identity holds:
\[
P=\frac{[q(x+2)-3]Q(z,h)}
 {(q+1)^2(x+3-2q)^2(qx-2q+2x+3)^2},
\qquad z=x-1,\quad h=1-q,
\tag{7}
\]
where Q is the explicitly grouped polynomial
\[
\begin{aligned}
Q(z,h)={}&z^2(-26z^3-24z^2+64z+64)\\
&+2hz^2(11z^3-56z^2-150z-80)\\
&+h^2(10z^5+119z^4+207z^3+188z^2-96z-192)\\
&+h^3\{6z^4(19-z)+345z^3+791z^2+1068z+480\}\\
&+h^4\{z^3(87-65z)+83z^2+27z+108\}\\
&+h^5\{4z^4+71z^2+z(165-81z^2)+33\}\\
&+2h^6(z-1)(z^2-18z-15).
\end{aligned}
\tag{8}
\]
The domain and contact condition give
\[
0<z\le\frac87,\qquad 0\le h\le\frac1{20},
\qquad h<\frac{z}{z+3}.
\tag{9}
\]
In particular q(x+2)-3>0. It remains to prove Q>0.

## 4. A short lower bound for the polynomial

The three brackets multiplying h^3,h^4,h^5 in (8) are positive
on 0<=z<=8/7. For the latter two, use
\(87-65z\ge89/7>0\) and
\(165-81z^2\ge2901/49>0\). They can therefore be discarded
in a lower bound.

Discarding the positive part of the h coefficient and using h<=1/20
gives
\[
2hz^2(11z^3-56z^2-150z-80)
\ge-z^2\left(\frac{28}{5}z^2+15z+8\right).
\tag{10}
\]
For the h^2 coefficient, discard its four positive terms. By (9),
\[
-(96z+192)h^2
\ge-z^2\frac{96(z+2)}{(z+3)^2}
\ge-\frac{64}{3}z^2.
\tag{11}
\]
The final inequality follows because
\(96(z+2)/(z+3)^2\) decreases for z>=0 and equals 64/3 at zero.

The last coefficient of (8) is nonnegative for 0<=z<=1. For
1<=z<=8/7 it satisfies
\[
2(z-1)(z^2-18z-15)
\ge-\frac{498}{49}>-12.
\]
Since 0<=h<=1 and h<z/(z+3), this gives the convenient uniform bound
\[
2h^6(z-1)(z^2-18z-15)
\ge-12h^6\ge-12h^2\ge-\frac43z^2.
\tag{12}
\]
Combining (8)--(12),
\[
Q(z,h)\ge z^2J(z),\qquad
J(z)=\frac{100}{3}+49z-\frac{148}{5}z^2-26z^3.
\tag{13}
\]
Here J''(z)=-296/5-156z<0. Hence J is concave, and on [0,8/7]
it is bounded below by the smaller of its endpoint values:
\[
J(0)=\frac{100}{3}>0,\qquad
J(8/7)=\frac{61028}{5145}>0.
\tag{14}
\]
Thus Q>0. Equations (7)--(9) prove P>0 and the required derivative
inequality (6).

## 5. Complete the comparison

At beta=x the exact branch and the barrier both equal one.
The strict derivative inequality just proved holds there as well,
since p=1/x<q=1. Thus the exact branch initially lies below the
barrier. A first later contact from below would require its derivative
to be at least the barrier derivative; (2)--(6) give the opposite
strict inequality. Such a contact is impossible. This proves (1).

This upper bound is conditional on the two displayed small-shape
restrictions. No residual, norm floor, Casimir cap or physical
completion cost has been deformed in its proof.
