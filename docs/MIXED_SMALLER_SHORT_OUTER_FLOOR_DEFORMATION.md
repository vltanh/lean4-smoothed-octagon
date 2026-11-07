# A fixed-outer-norm deformation on the nonnegative-pairing branch

Date: 2026-11-07. Hand reduction, accepted in independent internal review.
The explicit outer-scale corollary below is an additional hand consequence.

This note concerns the remaining w=3/4 face of
[MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md).
It gives a further comparison when the transported outer pairing
E_L is nonnegative. That sign is an explicit hypothesis; it is not
asserted for every point of the face. No exclusion of the terminal
faces, or of the whole smaller-short branch, is claimed.

The comparison keeps the actual short geometry, its equal-secant
incoming norm u, its physical two-turn matrix and cost fixed. It uses
the accepted redundancy of the opposite norm floor from
[MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR](MIXED_SMALLER_SHORT_NONPOSITIVE_FLOOR.md).
There is no reflection that would reverse the global-minimum order.

## 1. Root coordinates on the w=3/4 face

Use all fixed geometry quantities from the root-and-angle note:

\[
t_0=\rho/r,\quad t_0\le t\le r<1/2,\qquad
\lambda=[1+\rho(\alpha^2-1)]^{-1},\quad d=\lambda\rho D,
\]
\[
r_A=\frac{\alpha}{\alpha+\beta},\quad
\rho_A=\alpha^2\lambda\rho<1/7,\quad
T=r_A/\rho_A,\quad T_B=1/r_A.
\]

The common incoming norm obeys
\(3/4<u\le\min\{U(r),U(r_A)\}\). Put

\[
f(s)=s-s^{-1}-\log s,\quad h(s)=\log s-1+s^{-1},
\quad \varphi(s)=3s/4-f(s).
\]

At w=3/4 the root equation becomes

\[
\xi:=E_L=\varphi(\tau)+uT_B-f(T_B)-h(1/\rho_A),
\qquad 2<\tau<T.
\tag{1}
\]

Moreover

\[
\boxed{
E(\xi)=\frac{2du-\xi}{\lambda},\qquad
v(\xi)=\frac{3/4+d^2u-d\xi}{\lambda^2}.}
\tag{2}
\]

These are just the exact two-turn transport equations solved with
w=3/4; they do not change the short secants.

The function varphi strictly decreases for tau>2:

\[
\varphi'(\tau)=-\frac{(\tau-2)^2}{4\tau^2}<0,
\qquad \varphi(2)=\log2.
\]

Consequently increasing xi toward

\[
\xi_2=\log2+uT_B-f(T_B)-h(1/\rho_A)
\tag{3}
\]

decreases tau continuously toward 2. In particular the interval
\(2<\tau\le\tau_{\rm initial}<T\) retains the positive outer
reverse duration.

## 2. Continue the central relation

For a given xi, the remaining central equation is

\[
\mathcal E(t,v(\xi))=E(\xi),
\]
\[
\mathcal E(t,v)=\frac{u-1}{r}+\frac{v-1}{t}
       +1+r+t-\rho+\log\frac{\rho}{rt}.
\tag{4}
\]

Write \(\nu=U(t)-v(\xi)\). As long as nu>0,

\[
\partial_t\mathcal E=\nu/t^2>0.
\]

Thus (4) determines a unique local t, and implicit differentiation
gives

\[
\boxed{\frac{dt}{d\xi}
=-\frac{t(\lambda t-d)}{\lambda^2\nu}.}
\tag{5}
\]

No sign of D is assumed in this formula. In particular there is no
singularity at lambda*t=d. At that value t remains constant under
the comparison. On either side the direction is determined by the
displayed numerator, while the norm-ceiling boundary nu=0 is a
listed stopping face.

Starting from xi>=0, increase xi until the first of

\[
\boxed{\tau=2,\qquad t=t_0,\qquad t=r,\qquad \nu=0.}
\tag{6}
\]

If an initial point is already on one of these faces, no motion is
needed. Otherwise continuation exists to a listed face. The parameters
xi and t stay in the compact intervals [xi_initial,xi2] and [t0,r].
At any interior limit with nu>0, the positive derivative in (4) gives
a further local continuation. Thus only a listed boundary can stop it.

The opposite norm lower bound creates no extra face. From (2),
\(dv/d\xi=-d/\lambda^2\). If D<=0, v does not decrease. If D>0,
a first v=3/4 point before tau=2 would satisfy all the retained
hypotheses of the positive-diagonal floor theorem, which excludes it.
An occurrence at tau=2 is already a stopping point in (6).
The face w=3/4 is preserved identically.

## 3. Casimir and relaxed cost both move in the needed direction

The outer root still has incident norm ceilings

\[
u\le U(r_A),\qquad w=3/4\le U(1/\tau),\qquad
\rho_A<r_A/\tau.
\]

The elementary central-pairing estimate from the root-and-angle note
therefore gives xi<=3rho_A along the comparison. Starting from a
nonnegative xi, the whole path stays in

\[
0\le\xi\le3\rho_A<3/7.
\tag{7}
\]

The same Casimir can be written in the outer coordinates as

\[
\boxed{\Gamma(\xi)=
\frac{3u-\xi^2}{16(1-\rho_A)^2}.}
\tag{8}
\]

Indeed \(4uw-E_L^2=\lambda^2(4uv-E^2)\) and
\(1-\rho_A=\lambda(1-\rho)\), so (8) is exactly the original
normalization. Therefore Gamma is nonincreasing as xi increases.
It also remains strictly positive, for the explicit reason

\[
\Gamma>
\frac{9/4-9/49}{16(1-\rho_A)^2}
=\frac{405}{3136(1-\rho_A)^2}>0.
\]

There is no silently assumed persistence of ellipticity and no omitted
zero-determinant stopping face on this nonnegative-pairing branch.

The physical matrix and cost depend only on the fixed short geometry
and u. The relaxed completion score is nondecreasing in kappa at this
fixed geometry. Hence the same necessary upper Casimir cap and score
inequality persist throughout (6). In particular the improved score
may retain

\[
\kappa_{\rm eff}=
\max\{\sqrt{12\Gamma},\,9/8,\,
       \sqrt{12\max(0,G_{\rm ret})}\}
\le\kappa_{\rm actual},
\]

using the unchanged actual-period bound G_ret from the root-and-angle
note. This does not attach an actual lower Casimir bound to the
artificial covector.

### Retain the actual outgoing-turn floor as well

**Status:** accepted in independent internal hand review; see
[HAND_ENDPOINT_REDUCTIONS_AUDIT](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).

The first root-preserving comparison fixes the parameter of the actual
outer reverse root. Its actual outgoing positive turn therefore has

\[
w_{\rm actual}>m_A(\tau):=\Phi(1-1/\tau),
\]

by [EXPLICIT_TURN_NORM_FLOOR](EXPLICIT_TURN_NORM_FLOOR.md).
Write \(K_{\rm geo}=uT_B-f(T_B)-h(1/\rho_A)\) and set

\[
E_{\rm out}(\tau)=\tau m_A(\tau)-f(\tau)+K_{\rm geo},
\]
\[
\boxed{G_{\rm out}(\tau)=
\frac{4u m_A(\tau)-E_{\rm out}(\tau)^2}
     {16(1-\rho_A)^2}.}
\tag{8a}
\]

Then the same original actual period satisfies
\(\Gamma_{\rm actual}>G_{\rm out}(\tau)\).
To prove this, keep tau and all short geometry fixed and lower only
the actual outer norm to m_A. The outer pairing changes affinely as
\(E_L=\tau w-f(\tau)+K_{\rm geo}\). On this whole norm segment,
\(u\le U(r_A)\), \(w\le U(1/\tau)\) and
\(\rho_A<r_A/\tau\), so \(E_L\le3\rho_A\). Therefore

\[
\frac{d\Gamma}{dw}
=\frac{2u-\tau E_L}{8(1-\rho_A)^2}
>\frac{3/2-3r_A}{8(1-\rho_A)^2}>0.
\]

This proves the strict lower bound. In particular
\(G_{\rm out}(\tau)<\Gamma_{\rm cap}\), and
\(\sqrt{12\max(0,G_{\rm out})}\) may be included in the maximum
defining kappa_eff. These are bounds on the unchanged original actual
period, not lower bounds on the artificial w=3/4 Casimir.

This retained quantity also moves in the correct direction during
the present positive-pairing deformation. Indeed

\[
E_{\rm out}(\tau)
=\xi(\tau)+\tau[m_A(\tau)-3/4]\ge0
\]

on its entire tau interval, because \(\xi\ge0\). Differentiation gives

\[
16(1-\rho_A)^2G_{\rm out}'(\tau)
=[4u-2\tau E_{\rm out}]m_A'(\tau)
       +2E_{\rm out}[U(1/\tau)-m_A(\tau)]>0.
\tag{8b}
\]

Here m_A'>0 for tau>2, m_A<U(1/tau), and the same central-pairing
bound gives \(2u-\tau E_{\rm out}>0\). Thus decreasing tau
decreases G_out. Its upper-cap condition and its contribution to
kappa_eff are consequently preserved from the original actual tau
through this further comparison. At tau=2, m_A=3/4 and G_out equals
the deformed Casimir (8), by continuity.

## 4. A simple scale criterion for the pairing sign

The nonnegative-pairing hypothesis includes every point of this face
whose outer physical centre \(A=a\alpha\) satisfies A>=5/7.
Indeed, put z=1/tau and z0=rho_A/r_A. Keeping w=3/4 fixed,
the outer central-pairing expression has z derivative

\[
\frac{U(z)-3/4}{z^2}=\frac{(z-1/2)^2}{z^2}\ge0.
\]

Lower z to z0. The logarithm then vanishes. Lowering u to 3/4
strictly lowers the pairing further, so

\[
E_L>1-\rho_A+(r_A+z_0)
                     \left(1-\frac1{4\rho_A}\right).
\]

Both r_A and z0 are below 1/2, and r_A*z0=rho_A. Therefore
\((1/2-r_A)(1/2-z_0)>0\) gives
\(r_A+z_0<1/2+2\rho_A\). The displayed coefficient is negative,
yielding the useful universal lower bound on this face

\[
\boxed{E_L>1+\rho_A-\frac1{8\rho_A}.}
\tag{9}
\]

Its right side increases with rho_A. If A>=5/7, then
rho_A>=25/221 and

\[
E_L>\frac{246}{221}-\frac{221}{200}
=\frac{359}{44200}>0.
\tag{10}
\]

Thus any still-uncovered negative-pairing point necessarily has
A<5/7. This criterion does not assert that every smaller outer
centre has negative pairing.

## 5. Exact scope

On the part of the w=3/4 face with E_L>=0, the necessary cost/cap
conditions can therefore be moved to the outer endpoint tau=2, the
central zero-duration endpoint t=t0, or one of the already remaining
faces t=r and U(t)-v=0. The outer endpoint tau=2 is a limit of the
descending-root parameter, not an independently admissible period.

The E_L<0 part has not been covered by this deformation: increasing
E_L there would increase Gamma and need not preserve the upper cap.
The signs at the new endpoints remain to be proved. These limitations
are part of the statement.
