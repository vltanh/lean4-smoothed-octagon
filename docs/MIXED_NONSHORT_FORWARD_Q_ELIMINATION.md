# A hand elimination of the nonshort forward event factor

Date: 2026-11-08 UTC. Conditional scalar hand theorem. No interval cover,
executable sign verdict, Lean, Lake, typechecking or CI is a premise.
The ratio restrictions in the theorem are explicit hypotheses; this
note does not assert them for every actual remaining forward window.

This proves the factor-elimination inequality needed by
[MIXED_NONSHORT_FORWARD_ENVELOPE_CASIMIR_SIGN](MIXED_NONSHORT_FORWARD_ENVELOPE_CASIMIR_SIGN.md).
The proof uses one elementary logarithm bound, a quadratic in the event
factor, and an explicit polynomial concavity argument with two endpoint
signs. The coefficient parts used in that last argument are displayed
in the appendices and bounded by one common rational power rule.

## 1. The scalar theorem

Suppose
\[
\frac13\le t\le\frac25,\qquad
0\le j\le\frac1{30},\qquad k\ge1.
\tag{1}
\]
Put
\[
c=1-t,\quad x=1-2t+j,\quad p=t+x,\quad W=1+x,
\quad Y=x(x+2),\quad B=k+2tx+x^2,
\]
\[
Q=x^2+6x+6,\qquad
V=1+\frac{c^2}{W}-\frac{3c(x+2)}{Q},\qquad
\eta=\frac pW,\qquad g=1-\eta+\eta^2.
\tag{2}
\]
Let \(v\le V\), and define
\[
H=\frac{k}{t}(v-1+t^2)+t(2-t),\qquad
w_U=\frac{k^2-kt+t^2+HY+vY^2}{B^2},
\]
\[
\alpha=\frac{B(w_U-1)}{pW},\qquad
\beta=\frac{pW}{B}.
\tag{3}
\]
For any constant \(d\), set
\[
h(q)=\log q+\alpha q+\beta/q+d,
\qquad
F_\eta(q)=1+\eta^2q-\frac{\eta q\log q}{q-1},
\tag{4}
\]
with \(F_\eta(1)=g\) by continuity.

**Theorem.** For every \(q\ge1\),
\[
\boxed{h(q)-h(1)\le F_\eta(q)-g.}
\tag{5}
\]
The inequality is strict when \(q>1\). No upper bound on q is needed.

For an actual incoming secant, \(v<V\) follows from
\[
\frac{d}{dx}\left(\log(1+x)-\frac{3x(x+2)}{x^2+6x+6}\right)
=\frac{x^4}{(1+x)(x^2+6x+6)^2}>0
\]
and equality at x=0. The floor retained from the original incoming
switch is \(F_\eta(q)\le v\). Thus, once the actual ratio hypotheses
(1) hold, (5) gives the needed bound
\[
h(q)\le h(1)+v-g.
\tag{6}
\]
This transports no artificial Casimir cap or new switching premise.

## 2. The logarithm leaves one quadratic

The elementary upper bound
\[
\log q<L_+(q):=
\frac{(q-1)(q^2+10q+1)}{6q(q+1)}\qquad(q>1)
\tag{7}
\]
follows because the derivative of its right side minus \(\log q\)
is \((q-1)^4/[6q^2(q+1)^2]>0\), with value zero at one.

Write \(y=q-1\). Direct subtraction in (4) gives
\[
F_\eta(q)-g-[h(q)-h(1)]
=\eta+(\eta^2-\alpha)y+\frac{\beta y}{q}
  -\left(1+\frac{\eta q}{y}\right)\log q.
\]
The logarithm coefficient is negative. Substituting (7) therefore
gives the strict lower bound
\[
F_\eta(q)-g-[h(q)-h(1)]
>\frac{y}{6(y+1)(y+2)}\{C_0+C_1y+C_2y^2\},
\tag{8}
\]
where
\[
\begin{aligned}
C_0&=12\eta^2-6\eta-12\alpha+12\beta-12,\\
C_1&=18\eta^2-7\eta-18\alpha+6\beta-12,\\
C_2&=6\eta^2-\eta-6\alpha-1.
\end{aligned}
\tag{9}
\]
Consequently it is enough to prove positivity of this quadratic for
every \(y\ge0\).

## 3. It is enough to use k=1 and v=V

On (1), \(1/5\le x\le11/30<1/2\). Write \(U(t)=1-t+t^2\).
The exact identity
\[
U(t)-V=\frac{cx}{WQ}\{2x+3-tQ\}>0
\tag{10}
\]
has the stated sign because
\[
2x+3-tQ\ge2x+3-\frac25Q
=\frac{3-2x-2x^2}{5}>0.
\]
In particular \(v\le V<1\).

At fixed \(t,x,v\), differentiation of (3) gives
\[
\beta_k=-\frac{pW}{B^2}<0,
\]
\[
\beta_k-\alpha_k=
\frac{xc}{tpWB^2}
\left\{2t^2x^2+2t^2x+2t^2+tx^3+2tx^2+3tx
        +(1-v)(x^3+2x^2)\right\}>0.
\tag{11}
\]
Thus \(\alpha_k<\beta_k<0\). Each coefficient in (9) strictly
increases with k: for the middle coefficient,
\(-18\alpha_k+6\beta_k=18(\beta_k-\alpha_k)-12\beta_k>0\).
The other two signs follow immediately.

Also
\[
\alpha_v=\frac{Y(k/t+Y)}{BpW}>0,
\tag{12}
\]
while \(\beta\) and \(\eta\) do not depend on v. Each coefficient
in (9) strictly decreases with v. For \(y\ge0\), it therefore
suffices to prove
\[
C_0+C_1y+C_2y^2>0\quad\hbox{at }k=1,\ v=V.
\tag{13}
\]
These comparisons only concern the displayed scalar polynomial.
No data from an altered physical trajectory are being asserted.

## 4. The leading coefficient is positive

In this section and the next three, set \(k=1\), \(v=V\), and
write \(B_1=1+2tx+x^2\). The numerator of w_U increases with v by
(12). Substitution of \(v=U(t)\) gives the exact factorization
\[
B_1^2\{1-w_U(U(t))\}
=c\{t(x^4+4x^3-x^2-2x+1)+2x-x^2-4x^3\}>0.
\tag{14}
\]
Indeed, for \(x\le11/30\),
\[
1-2x-x^2\ge\frac{119}{900}>0,
\qquad
2-x-4x^2\ge\frac{986}{900}>0.
\]
Together with (10), this proves \(w_U(V)<1\), so \(\alpha<0\).
Since \(p-c=j\ge0\) and \(p+c=W\), one has \(\eta\ge1/2\).
Hence
\[
\boxed{C_2=(2\eta-1)(3\eta+1)-6\alpha>0.}
\tag{15}
\]

## 5. Concavity reduces the discriminant to two endpoints

Let
\[
\Delta=4C_0C_2-C_1^2,\qquad
\mathcal D=tpW^2QB_1>0.
\]
Equations (2)--(3) and (9) show that \(\mathcal D C_i\) are
polynomials in t,x. Put
\[
A=\frac25-t,\qquad x=\frac15+2A+j,
\quad 0\le A\le\frac1{15},\quad0\le j\le\frac1{30},
\]
\[
\mathcal P(A,j)=5^{18}\mathcal D^2\Delta
\quad\hbox{after this substitution.}
\tag{16}
\]
This is a polynomial with integer coefficients. Formula (16), with
(2)--(3) and (9), specifies it completely using only the displayed
rational expressions; all denominators have been cleared by a positive
factor.

The constant coefficient of \(\mathcal P_{jj}\) is
\[
-8750892403582200.
\]
Appendix A gives its **complete positive coefficient part** as
\[
R_0(j)+A^2R_2(j)+A^3R_3(j)+A^4R_4(j)+A^5R_5(j)+A^6R_6(j).
\tag{17}
\]
All remaining nonconstant monomials of \(\mathcal P_{jj}\) have
nonpositive coefficients and may be dropped in an upper bound.
Every displayed R has positive coefficients. The single rational
power rule \(A^ij^m\le15^{-i}30^{-m}\) therefore gives the following
bounds by substituting \(A=1/15\), \(j=1/30\) in (17).

| i | Upper bound for \(15^{-i}R_i(1/30)\) |
| --- | ---: |
| 0 | \(2\cdot10^6\) |
| 2 | \(4\cdot10^8\) |
| 3 | \(3\cdot10^{13}\) |
| 4 | \(13\cdot10^{14}\) |
| 5 | \(5\cdot10^{14}\) |
| 6 | \(6\cdot10^{13}\) |

Their sum is less than \(2\cdot10^{15}\), whereas the absolute
constant exceeds \(8\cdot10^{15}\). Thus
\[
\mathcal P_{jj}<-6\cdot10^{15}<0.
\tag{18}
\]
This is a uniform bound on the one explicit polynomial, not a box
cover or a sampled sign claim. Concavity in j gives
\[
\mathcal P(A,j)\ge
\min\{\mathcal P(A,0),\mathcal P(A,1/30)\}.
\tag{19}
\]

## 6. The endpoint j=0

Direct factorization of (16) gives
\[
\mathcal P(A,0)=4(5A+3)^6F(A),
\]
where the complete smaller polynomial is
\[
\begin{aligned}
F(A)={}&3983870151+98273339520A+222451445600A^2\\
&+9040010920000A^3+43172882200000A^4
 +28797779200000A^5\\
&-213484046000000A^6-612193280000000A^7\\
&-767218000000000A^8-547680000000000A^9\\
&-240840000000000A^{10}-64800000000000A^{11}
 -9000000000000A^{12}.
\end{aligned}
\tag{20}
\]
For \(A\le1/15\), collect the last seven terms against \(A^5\).
The sum of their absolute coefficients times \(15^{-(i-5)}\) is
\[
\frac{4177557311600000}{243}<28797779200000.
\tag{21}
\]
Thus the positive fifth-degree term absorbs all seven negative terms.
The remaining constant is strictly positive and every remaining
coefficient is nonnegative. Therefore \(\mathcal P(A,0)>0\).

## 7. The endpoint j=1/30

Appendix B gives the complete integer identity
\[
78364164096\,\mathcal P(A,1/30)=\sum_{i=0}^{18}d_iA^i.
\tag{22}
\]
In particular \(d_0=802991498030002852949756>0\). Put \(u=15A\),
so \(0\le u\le1\), and let \(b_i=d_i/(15^i d_0)\).
The displayed integers give
\[
b_0=1,\quad b_1>-4/3,\quad b_2>-1,\quad
b_3>1,\quad b_4>1,\quad b_5>2/5,\quad
b_6>1/12,\quad b_7>0.
\tag{23}
\]
All \(b_i\), \(8\le i\le18\), are negative, and their exact total is
\[
-\sum_{i=8}^{18}b_i
=\frac{3241970910032664191552}{1806730870567506419136951}
<\frac1{500}.
\tag{24}
\]
Because \(u^i\le u^6\) for \(i\ge8\), the positive term
\(b_6u^6\) absorbs (24). Dropping the resulting nonnegative sixth
term and the positive seventh term leaves
\[
\sum_{i=0}^{18}b_i u^i\ge
Q_*(u):=1-\frac43u-u^2+u^3+u^4+\frac25u^5>0.
\tag{25}
\]
Here is a short complete proof of the final sign. If \(u\le1/2\),
the first three terms already sum to at least \(1/12\).
If \(u=1/2+z\) with \(z\ge0\), ordinary expansion gives
\[
Q_*(1/2+z)=\frac{17}{60}-\frac{23}{24}z+
\frac52z^2+4z^3+2z^4+\frac25z^5.
\]
The first three terms are at least
\[
\frac{17}{60}-\frac{(23/24)^2}{10}
=\frac{1103}{5760}>0
\]
by completing the square. The other terms are nonnegative.
This proves (25), hence \(\mathcal P(A,1/30)>0\).

Both endpoint signs and (19) prove \(\mathcal P>0\), hence
\(\Delta>0\). With (15),
\[
C_0+C_1y+C_2y^2
=C_2\left(y+\frac{C_1}{2C_2}\right)^2+
\frac{\Delta}{4C_2}>0
\tag{26}
\]
for all real y at \(k=1,v=V\). Section 3 extends positivity to
all \(k\ge1,v\le V,y\ge0\). Equations (8) and (26) prove the
strict form of (5) for \(q>1\); continuity gives equality at one.

## 8. Acceptance boundary

The theorem proves precisely the scalar factor elimination (5), with
its complete stated domain and all endpoint signs. In the intended
physical application, the coefficient \(\alpha\) is formed using the
central upper-envelope norm, while h is the diagonal on the **forward
stationary line**. Those are the definitions required by (3)--(4).
The theorem does not substitute the central ceiling diagonal for that
forward diagonal.

The original incoming floor and the actual exact secant give (6)
without changing the covector or comparing costs of artificial
trajectories. The additional ratio restrictions \(t\ge1/3\) and
\(j\le1/30\), and the hypothesis used for actual Casimir monotonicity,
remain separate obligations. This note and the final scalar Casimir
sign therefore do not by themselves close the actual H-N-forward gate.

## Appendix A. Complete positive part in the concavity calculation

The six polynomials below specify all 39 positive monomials in
\(\mathcal P_{jj}\). Together with (16) they give the exact algebraic
sign-part identity used in (17)--(18). Every omitted nonconstant
coefficient in this expansion is nonpositive. Thus the proof needs
only the upper bounds on these displayed positive terms.

Use \(\operatorname{poly}(c_0,\ldots,c_d)=\sum_{m=0}^dc_mj^m\).
Then
\[
\begin{aligned}
R_0={}&390625000j^8\operatorname{poly}(
2761954056,4658597240,1808638920,311376000,20190625),\\
R_2={}&97656250j^6\operatorname{poly}(
538783950768,453590550720,0,0,0,2324400000,504765625),\\
R_3={}&31250000j^2\operatorname{poly}(
1653163319295,19335278966824,48999663529200,\\
&59216281887525,37904702109750,12829672181250,
2595754575000,703977656250,207018281250,23110546875),\\
R_4={}&312500\operatorname{poly}(
142143158820852,1605188706075900,7408279659940800,\\
&17326315380272500,22105953177496875,15444847293487500,
5551728851812500,952293071250000,\\
&180836490234375,68171210937500,8326699218750),\\
R_5={}&625000\operatorname{poly}(
422463256695264,3433305949288575,10730450965622250,\\
&15807892176927500,10131283209975000,115258927678125),\\
R_6={}&3125000\operatorname{poly}(
176969262828073,923024045674875,1174031145090750).
\end{aligned}
\tag{27}
\]

For completeness, the six weighted positive sums before the simpler
roundings in Section 5 are these exact rational numbers:

| i | \(15^{-i}R_i(1/30)\) |
| --- | ---: |
| 0 | \(472920409467725/272097792\) |
| 2 | \(80759150112520953125/(1088391168\cdot225)\) |
| 3 | \(617877506689563225828125/(7558272\cdot3375)\) |
| 4 | \(53682238679334787466328125/(839808\cdot50625)\) |
| 5 | \(111259069078374361484375/(324\cdot759375)\) |
| 6 | \(1959761344381278125000/(3\cdot11390625)\) |

The powers \(225,3375,50625,759375,11390625\) are
\(15^2,15^3,15^4,15^5,15^6\), respectively. The signs and bounds in
Section 5 now follow directly by multiplying positive integers.

## Appendix B. Complete upper endpoint identity

The coefficients in (22) are as follows. This table contains the
entire endpoint polynomial; there are no omitted coefficients.

| i | \(d_i\) |
| --- | ---: |
| 0 | 802991498030002852949756 |
| 1 | -15191761277375206104765580 |
| 2 | -165537569718346329445413625 |
| 3 | 2898394087312665703645959000 |
| 4 | 47223471919791690861745950000 |
| 5 | 281555778671938838844902700000 |
| 6 | 847456966320663541022154000000 |
| 7 | 941563033940073676116600000000 |
| 8 | -2594154431552626936865700000000 |
| 9 | -14047632872156533066920000000000 |
| 10 | -32916826556464424842800000000000 |
| 11 | -49763328476648398200000000000000 |
| 12 | -52982733045532859280000000000000 |
| 13 | -40895405644371091200000000000000 |
| 14 | -23018750052299424000000000000000 |
| 15 | -9352810738020096000000000000000 |
| 16 | -2656030898027520000000000000000 |
| 17 | -484878265344000000000000000000 |
| 18 | -44079842304000000000000000000 |
