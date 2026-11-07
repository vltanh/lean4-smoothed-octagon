# A uniform corrected cap for the smaller-short outer envelope

Date: 2026-11-07 UTC. Hand proof, accepted in the
[endpoint audit](HAND_ENDPOINT_REDUCTIONS_AUDIT.md), Section 14.
This note strengthens the accepted
[outer-envelope comparison](MIXED_SMALLER_SHORT_OUTER_ENVELOPE.md).
It does not exclude the remaining smaller-short domain.

The earlier comparison raises the Casimir, so it cannot carry an
uncorrected upper cap. Here its exact derivative ratio admits the
uniform bound \(1/7\). Subtracting this controlled increase gives a
lower bound on the **original actual-period Casimir** that depends
only on the fixed short geometry and its equal-secant incoming norm.
The [angle-circle score](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md)
can therefore use this bound without assigning a lower cap to an
artificial comparison covector.

## 1. Fixed actual data and the two envelope segments

Use the notation of the outer-envelope note:
\[
1\le\alpha<x\le\beta,\qquad r=(1+x)^{-1},\qquad
t_0=\rho/r\le t\le r<1/2,
\]
\[
\lambda=[1+\rho(\alpha^2-1)]^{-1},\quad
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,\quad d=\lambda\rho D,
\]
\[
r_A=\frac{\alpha}{\alpha+\beta}<\frac12,\qquad
\rho_A=\alpha^2\lambda\rho<\frac17,\qquad T=r_A/\rho_A.
\]
The scale bound is the hand reverse-centre bound from
[HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md).
The fixed common incoming norm satisfies
\[
\frac34<u\le\min\{U(r),U(r_A)\},\qquad U(s)=1-s+s^2.
\]

It also has the elementary short-bridge bound
\[
u\le V(x):=\operatorname{Sec}(1,x,x)
 \le\frac34+\frac{(x-1)^2}{12(x+1)^2}<\frac56.
\tag{1}
\]
The first inequality uses the equal-secant short-bridge order, as in
Sections 1--2 of
[MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL.md).
The second follows by integrating
\[
V(x)-\frac34
=\frac1{4(x-1)}\int_1^x\frac{(s-x)^2}{(s+x)^2}\,ds
\]
and using \(s+x\ge1+x\). No coefficient sign table is used.

Fix the parameter \(\tau\) of the actual outer descending root:
\[
2<\tau<T,\qquad R_\tau(t,v)=0.
\]
Keep this same parameter throughout both scalar comparisons: first
raise \(v\) to \(U(t)\), then decrease \(t\) to \(t_0\) along the
curve \(v=U(t)\). Define
\[
E=\frac{u-1}{r}+\frac{v-1}{t}
 +1+r+t-\rho+\log\frac{\rho}{rt},
\]
\[
w=\lambda^2v+d^2u-d\lambda E,\quad
E_L=2du-\lambda E,\quad
\Gamma=\frac{4uv-E^2}{16(1-\rho)^2}.
\]
With \(f(s)=s-s^{-1}-\log s\) and \(h(s)=\log s-1+s^{-1}\),
\[
R_\tau=\tau w-f(\tau)+u/r_A-f(1/r_A)
                  -h(1/\rho_A)-E_L.
\tag{2}
\]

The positive factor
\[
B_\tau(s)=1+\tau(\lambda s-d)>0\qquad(t_0\le s\le r)
\tag{3}
\]
is already proved in the outer-envelope note, for either sign of \(D\).

## 2. A uniform bound on the exact derivative ratio

At the actual root, its incident norm ceilings give
\[
E_{L,\mathrm{actual}}\le3\rho_A.
\tag{4}
\]
This is the elementary reverse-centre pairing estimate: insert
\(u\le U(r_A)\), \(w\le U(1/\tau)\) in the central pairing formula,
use \(\rho_A<r_A/\tau\), and differentiate its difference from
\(3\rho_A\) in \(\rho_A\).

The bound persists along both envelope segments for a simpler reason,
without an artificial root or outgoing-norm hypothesis. Raising \(v\)
raises \(E\), since \(E_v=1/t\). Along \(v=U(t)\),
\[
\frac{dE(t,U(t))}{dt}=2-\frac1t<0,
\]
so decreasing \(t\) also raises \(E\). Thus \(E_L=2du-\lambda E\)
decreases throughout, and (4) remains valid.

The residual derivatives, with their comparison directions, are
\[
(R_\tau)_v=\frac{\lambda B_\tau(t)}t>0,\qquad
\frac{d}{dt}R_\tau(t,U(t))
=\frac{\lambda(2t-1)B_\tau(t)}t<0.
\]
Thus increasing \(v\), and then decreasing \(t\), both increase the
residual. The exact ratio from the envelope proof is
\[
\frac{\Gamma_v}{(R_\tau)_v}
=\frac{2ut-E}{8(1-\rho)^2\lambda B_\tau(t)}.
\tag{5}
\]
The same expression is the ratio of derivatives along \(v=U(t)\).
To expose its sign and size, use
\[
1-\rho_A=\lambda(1-\rho),\qquad
\lambda(2ut-E)=2u(\lambda t-d)+E_L.
\]
Since \(\lambda t-d=(B_\tau-1)/\tau\), (5) becomes
\[
\boxed{
\frac{\Gamma_v}{(R_\tau)_v}
=\frac{\,2u/\tau+(E_L-2u/\tau)/B_\tau\,}
       {8(1-\rho_A)^2}
<\frac{u}{4\tau(1-\rho_A)^2}.}
\tag{6}
\]
The strict sign is justified on the entire two-segment path:
\[
\tau E_L\le3\tau\rho_A<3r_A<\frac32<2u,
\]
and \(B_\tau>0\). This argument does not assume \(D\ge0\),
\(1-\tau d\ge0\), or that an artificial endpoint retains the actual
outgoing norm floor.

Finally (1), \(\tau>2\), and \(\rho_A<1/7\) give
\[
\boxed{
\frac{u}{4\tau(1-\rho_A)^2}
<\frac{245}{1728}<\frac17.}
\tag{7}
\]
The last comparison is the integer inequality \(1715<1728\).

Both \(R_\tau\) and \(\Gamma\) increase in the direction of each
envelope segment. Their positivity statements follow from (3) and the
central incident-norm estimate \(E\le3\rho\), as in the envelope
proof. Hence integration of (6)--(7) gives
\[
0\le\Gamma_*-\Gamma_{\mathrm{actual}}
 \le\frac17\bigl(R_\tau^*-R_{\tau,\mathrm{actual}}\bigr)
 =\frac17R_\tau^*.
\tag{8}
\]
Weak inequalities in (8) cover an unchanged segment; whenever a
segment changes, its corresponding derivative bound is strict.
In particular,
\[
\boxed{\Gamma_*-\frac17R_\tau^*
 \le\Gamma_{\mathrm{actual}}<\Gamma_{\mathrm{cap}},
\qquad \Gamma_{\mathrm{cap}}=\frac{9193}{50000}.}
\tag{9}
\]
The actual strict cap is the hand whole-period cost--Casimir bound.

## 3. Remove the unknown actual root parameter

All endpoint quantities are explicit in the fixed short geometry:
\[
v_*=U(\rho/r),\qquad
E_*=(u-1)/r+r+2\rho/r-\rho,
\]
\[
w_*=\lambda^2v_*+d^2u-d\lambda E_*,
\quad E_{L,*}=2du-\lambda E_*,
\quad
\Gamma_*=\frac{4uv_*-E_*^2}{16(1-\rho)^2}.
\]
Set
\[
A_*=(u-1)/r_A+r_A+1-\rho_A-E_{L,*}.
\]
Then
\[
R_\tau^*=(w_*-1)\tau+\tau^{-1}+A_*+\log(\tau/T),
\]
\[
(R_\tau^*)''=\frac{2-\tau}{\tau^3}\le0\qquad(2\le\tau\le T).
\]
Thus its maximum \(M\) is an explicit scalar expression:
\[
M=R_{\widehat\tau}^*,\qquad
\widehat\tau=
\begin{cases}
2,&w_*\le3/4,\\
\min\!\left\{T,\dfrac2{1-\sqrt{4w_*-3}}\right\},
       &3/4<w_*<1,\\
T,&w_*\ge1.
\end{cases}
\tag{10}
\]
This list includes the weak boundary cases by continuity.
It uses only the derivative of one concave function.

Define
\[
\boxed{G_{\rm env}:=\Gamma_*-\frac17M.}
\tag{11}
\]
Since \(M\ge R_\tau^*\) at the original actual root, (9) proves
\[
\boxed{G_{\rm env}\le\Gamma_{\mathrm{actual}},
       \qquad G_{\rm env}<\Gamma_{\mathrm{cap}}.}
\tag{12}
\]
Every quantity in \(G_{\rm env}\) depends only on
\(x,\alpha,\beta,\rho,u\). The variables \(t,v\), and the unknown
actual root parameter have disappeared.

An actual positive central reverse duration gives \(t>t_0\).
The strict envelope comparison therefore gives \(R_\tau^*>0\)
at the fixed actual root, so
\[
M>0.
\tag{13}
\]
Alternatively, the strictly descending actual root supplies the positive
residual maximum already used in the outer-envelope theorem.

## 4. A necessary cost test on fixed bridge geometry alone

Let \(\mathcal F(\kappa)\) be the fixed-geometry relaxed completion
score of the angle-circle note. It is nondecreasing in \(\kappa>0\),
and the actual complete period satisfies
\(\mathcal F(\kappa_{\rm actual})\le A_{\rm oct}\).

The actual mixed-period lower bound is \(\kappa_{\rm actual}>9/8\).
The geometry-only bound \(G_{\rm ret}\) from the same note is also a
lower bound on the original actual squared Casimir. Therefore one may
use
\[
\boxed{
\kappa_{\rm env}:=\max\left\{\frac98,\,
 \sqrt{12\max\{0,G_{\rm env}\}},\,
 \sqrt{12\max\{0,G_{\rm ret}\}}\right\}
\le\kappa_{\rm actual},}
\]
\[
\boxed{
M>0,\qquad G_{\rm env}<\Gamma_{\mathrm{cap}},\qquad
\mathcal F(\kappa_{\rm env})\le A_{\rm oct}.}
\tag{14}
\]
The first two tests and the score now use the same fixed actual
equal-secant bridge geometry. They can be applied directly to the
original smaller-short period or retained through the earlier
root-preserving comparison, since that comparison keeps this geometry
and \(u\) unchanged.

The formulas do not claim \(G_{\rm env}\le\Gamma\) for a subsequent
artificial covector. They bound the original actual \(\Gamma\).
Likewise, the upper envelope's \(\Gamma_*\) is not assigned the
competitive upper cap.

## 5. Exact scope

This is a uniform analytic replacement for the previously conditional
constant in Section 6 of the outer-envelope note. Its proof consists of
the exact derivative ratio, the retained pairing inequality, and
\(1715<1728\). No numerical minimum or executable sign premise enters.

An exclusion of the fixed-geometry necessary domain (14) is still
required. In particular this note does not close the smaller-short
case, its three remaining root-comparison faces, or the full hand proof.
