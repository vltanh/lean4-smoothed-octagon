# The corrected short-envelope cap decreases with scale

Date: 2026-11-08 UTC. Hand proof, accepted in the
[endpoint audit](HAND_ENDPOINT_REDUCTIONS_AUDIT.md), Section 18.

The [normalized-root scale comparison](MIXED_SMALLER_SHORT_ENVELOPE_SCALE_MONOTONICITY.md)
raises the necessary outer-envelope residual. This note proves that it
also lowers the corrected Casimir expression from
[MIXED_SMALLER_SHORT_CORRECTED_ENVELOPE_CAP](MIXED_SMALLER_SHORT_CORRECTED_ENVELOPE_CAP.md).
Thus both necessary scalar tests may be moved to the explicit scale
endpoints. A comparison of the physical completion cost at the changed
scale remains a separate, open obligation.

Keep the scale note's notation
\[
S=1+x,\quad 1\le\alpha\le x\le\beta,\quad x>1,\quad
0<p\le\frac{\alpha}{\alpha+\beta},\quad
\frac34\le u\le U((1+x)^{-1}),
\]
\[
q=\rho_A,\qquad p=\tau q,\qquad
R_{p/q}^*(q)=C(p)+qL(p).
\]
Here \(L=pA_2+p^{-1}-1-A_3\), and \(A_1,A_2,A_3\)
are exactly the three coefficients displayed in that note. In particular
the incoming norm, shape, and normalized root parameter \(p\) are fixed
when \(q\) changes.

## 1. A quantitative slope inequality

Define
\[
H=S[U((1+x)^{-1})-u]\ge0.
\]
We prove
\[
\boxed{3\alpha^2L(p)>4H(2S-1).}
\tag{1}
\]
The weak order \(\alpha=x\) is admitted in this scalar lemma.
The positive short bridges themselves have \(\alpha<x\).

### First lower beta to x

Use the identity from the scale note, with \(Z=SH\):
\[
pL=uB_0^2
 +pB_0\left[\frac{x-1}{S}+H(1+\alpha^{-2})\right]
 +U(p)-u-\frac{SHp^2}{\alpha^2},
\]
\[
B_0=1+p(S-D)/\alpha^2>0.
\]
At fixed \(\alpha,x,p,u\), its right side strictly increases with
\(B_0\). Moreover
\[
\frac{\partial B_0}{\partial\beta}
=\frac{2p(x-\alpha)}{\alpha^2}\ge0.
\]
Hence lowering \(\beta\) to \(x\) can only lower \(L\), while
leaving \(H\) unchanged. The necessary domain for \(p\) persists:
\(p\le\alpha/(\alpha+\beta)\le\alpha/(\alpha+x)\).
The positive-factor proof applies at every intermediate beta.
It suffices to prove (1) at \(\beta=x\).

The difference \(3\alpha^2L-4H(2S-1)\) is affine in \(u\).
Indeed \(H\), \(E_0\), \(A_2\), and \(A_3\) are affine in \(u\).
It therefore suffices to treat the two endpoints
\[
u=\frac34,\qquad u=U((1+x)^{-1}).
\tag{2}
\]

### The upper norm endpoint

Write \(U=U((1+x)^{-1})\) and \(R=(x-1)/(x+1)\).
Here \(H=0\), and substitution in the coefficient definitions gives
\[
4UA_2-A_3^2=3,\qquad
A_3-\left(1+\frac2x\right)
=\frac{2U(\alpha-x)(2x^2-\alpha-x)}{\alpha^2x}\le0.
\tag{3}
\]
For a brief check of the first identity, write
\[
A_2=\delta^2U+\delta C+T_0,\quad A_3=2\delta U+C,
\]
\[
C=-\varepsilon R-(2S-1)/\alpha^2,\quad
T_0=\varepsilon^2+\varepsilon S/\alpha^2+S^2/\alpha^4.
\]
Then \(4UA_2-A_3^2=4UT_0-C^2=3\), using
\(4U-R^2=3\),
\(4US-2R(2S-1)=6\), and
\(4US^2-(2S-1)^2=3\).

In particular \(A_2>0\). The quadratic whose value is \(pL\)
has discriminant
\[
\begin{aligned}
(1+A_3)^2-4A_2
&=-\frac{1-U}{U}
 \left[A_3-\left(1+\frac2x\right)\right]
 [A_3-(2x+1)]\\
&\le0.
\end{aligned}
\tag{4}
\]
Thus \(pL=A_2p^2-(1+A_3)p+1\ge0\).
If \(\alpha<x\), (3) makes the discriminant strictly negative.
If \(\alpha=x\), its only possible zero occurs at
\(p=x/(x+1)>1/2\), whereas the retained domain has
\(p\le\alpha/(\alpha+x)=1/2\). Therefore \(L>0\)
in every case, proving (1) at this endpoint.

### The lower norm endpoint

Now \(u=3/4\) and \(H=(x-1)^2/(4S)\). Put
\[
z=\alpha-1\ge0,\quad y=x-\alpha\ge0,\quad
k=\alpha/p-\alpha-x\ge0,\quad B=\alpha+x+k.
\]
The following identity clears the whole inequality:
\[
\boxed{
4S\alpha B\,[3\alpha^2L-4H(2S-1)]
=12S\alpha^2k^2+\alpha P(z,y)k+Q(z,y),}
\tag{5}
\]
where the two complete polynomials are
\[
\begin{aligned}
P(z,y)={}&z(48+72z+28z^2+3z^3)\\
&+y(96+192z+78z^2+6z^3)\\
&+y^2(108+78z+3z^2)+28y^3,
\end{aligned}
\tag{6}
\]
\[
\begin{aligned}
Q(z,y)={}&z^3(8+16z+11z^2+3z^3)\\
&+yz(48+180z+208z^2+88z^3+15z^4)\\
&+y^2(72+372z+516z^2+222z^3+27z^4)\\
&+y^3(188+466z+257z^2+21z^3)\\
&+y^4(148+148z+6z^2)+36y^5.
\end{aligned}
\tag{7}
\]
These are displayed finite identities, rather than an unspecified
coefficient test. One way to verify (5) is to insert
\(p=\alpha/B\) in \(L=pA_2+p^{-1}-1-A_3\).
The coefficient of \(k^2\) is \(12S\alpha^2\).
Collecting the linear and constant terms after
\(\alpha=1+z,\ x=1+z+y\) gives (6)--(7).

All terms on the right side of (5) are nonnegative.
Because \(x>1\), at least one of \(z,y\) is positive; (7) then
gives \(Q>0\). The denominator on the left is positive.
This proves (1) at \(u=3/4\). Affinity in \(u\) and the beta
comparison finish the proof of (1).

## 2. Differentiate the explicit comparison Casimir

Use the physical scale variable
\[
s=\frac{q}{\alpha^2(1-q)}=\frac{\rho}{1-\rho}.
\]
The central upper-envelope identity from the outer-envelope note becomes
the following concave quadratic in \(s\):
\[
\boxed{
16\Gamma_*
=3-H^2-2H+2H(2S-1-H)s-H^2s^2.}
\tag{8}
\]
For a direct substitution, its earlier normalized deficit is
\[
\frac{U(r)-u}{r(1-\rho)}=H(1+s),
\]
and \(t_0=\rho/r=S s/(1+s)\). Inserting these two
expressions into the earlier identity gives (8).

Consequently
\[
\frac{\partial\Gamma_*}{\partial q}
=\frac{H(2S-1-H-Hs)}{8\alpha^2(1-q)^2}
\le\frac{H(2S-1)}{8\alpha^2(1-q)^2}.
\]
Using (1), and the retained closed scale bound \(q\le1/7\), gives
\[
\boxed{
\frac{\partial\Gamma_*}{\partial q}
<\frac{3L}{32(1-q)^2}
\le\frac{49}{384}L<\frac17L.}
\tag{9}
\]
If \(H=0\), the derivative is zero and the same strict conclusion
holds because \(L>0\). The last constant comparison is
\(343<384\).

It follows that the corrected expression strictly decreases at fixed
shape, incoming norm and normalized parameter:
\[
\boxed{
\frac{\partial}{\partial q}
 \left[\Gamma_*(q)-\frac17R_{p/q}^*(q)\right]
<-\frac{41}{2688}L(p)<0.}
\tag{10}
\]
The residual itself strictly increases, by the scale note.

## 3. The corrected cap survives the endpoint reduction

Start with the same actual root used in the corrected-cap theorem, and
put \(p=\tau_{\rm actual}\rho_{A,\rm actual}\).
At the original scale,
\[
R_{p/q}^*>0,\qquad
\Gamma_*-\frac17R_{p/q}^*
\le\Gamma_{\rm actual}<\frac{9193}{50000}.
\tag{11}
\]
By (3) of the scale note and (10) above, raising \(q\) while holding
\(p\) fixed retains both inequalities. Thus they hold at
\[
q_{\max}=\min\!\left\{
 \frac{\alpha^2}{(1+x)^2+\alpha^2-1},\,\frac17,\,\frac p2
 \right\},
\tag{12}
\]
giving respectively the central scale endpoint, outer scale endpoint,
or \(\tau=2\).

On the additional branch \(D\le1+x\), the scale note retains
\(w_*\ge3/4\) by choosing its largest eligible scale.
The same comparison (10) also carries (11) to that point.
If this instead reaches \(w_*=3/4\), its final replacement
\(\tau\to2\) increases the residual and leaves \(\Gamma_*\)
unchanged. It therefore decreases the corrected expression once more.
Thus the simultaneous endpoint \(w_*=3/4,\tau=2\) also retains
both scalar tests.

The original actual Casimir is unchanged throughout this reasoning:
the corrected expression is only a decreasing numerical lower bound
on it. An artificial endpoint is not asserted to be a normal
trajectory or to have its own competitive upper cap.

## 4. Remaining scope

The additional inequality (1) is a uniform hand estimate. Its proof
uses the affine norm parameter, the discriminant factorization (4),
and the two explicitly listed positive polynomials (6)--(7).

This establishes a simultaneous scale reduction for the necessary
root residual and corrected cap. It does not establish monotonicity
of the physical completion score when the scale changes, and it
does not prove the remaining endpoint signs. The smaller-short
hand exclusion remains open.
