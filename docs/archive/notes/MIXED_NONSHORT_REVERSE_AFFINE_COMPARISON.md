# A rational secant comparison and a single upper shape endpoint

Date: 2026-11-07 UTC. Hand reductions; the remaining endpoint sign is open.

This note strengthens the reverse shape reduction using the strictly
concave weighted secant deficit proved in
[MIXED_NONSHORT_REVERSE_SHAPE_REDUCTION](MIXED_NONSHORT_REVERSE_SHAPE_REDUCTION.md).
All identities and signs used below are displayed. No sampled minimum
or executable sign test is a premise. The reduction is accepted in the
[independent endpoint review](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).

## 1. A rational upper bound for the extended reverse secant

For `0<a<d` and `r>=sqrt(ad)`, put

\[
\mu=(a+d)/2,\qquad
C(a,d)=\frac{ad(d-a)(7d+5a)}{3(a^2+6ad+d^2)}.
\]

Then

\[
\boxed{\operatorname{Sec}(a,r,d)
 <1-\frac{\mu r+C(a,d)}{(r+d)^2}.}
\tag{1}
\]

**Proof.** Let y=sqrt(d/a)>1 and r0=sqrt(ad)=ay. The first two
positive terms of `log y=2 atanh((y-1)/(y+1))` give

\[
J_{a,d}(r_0):=(r_0+d)^2[1-\operatorname{Sec}(a,r_0,d)]
 >\frac{a^2y^3(5y^2+2y+5)}{3(y+1)^2}.
\]

The strict concavity lemma gives `J'(r)>mu`. Therefore, for r>=r0,

\[
J(r)>\mu r+C_0,
\quad C_0=
\frac{a^2y(y-1)(7y^3+5y^2+9y+3)}{6(y+1)^2}.
\tag{2}
\]

Here the strict inequality at r=r0 comes from the logarithm bound;
for r>r0 the derivative comparison is strict as well. Subtraction gives

\[
C_0-\frac{a^2y(y-1)(2y+1)}3
 =\frac{a^2y(y-1)^3(3y+1)}{6(y+1)^2}>0.
\]

The simpler expression is `[sqrt(ad)(2d-a)-ad]/3`. Moreover

\[
\sqrt{ad}>\frac{4ad(a+d)}{a^2+6ad+d^2},
\]

because after multiplication by the positive denominator the difference
is `sqrt(ad)(sqrt(d)-sqrt(a))^4>0`. Since `2d-a>0`, substitution gives

\[
C_0>\frac{ad(d-a)(7d+5a)}{3(a^2+6ad+d^2)}=C(a,d).
\]

Together with (2), this proves (1).

## 2. The resulting root comparison is affine in k

Use the normalized variables of the shape reduction:

\[
p=t+x,\quad W=1+x,\quad H=t+x(x+2),\quad
B=k+2tx+x^2,\quad r=qB/W-p,\quad D=qH/W-p>0.
\]

The root has the accepted exact formula

\[
w_*=1+\frac{n_1}{DB}+\frac{n_0}{DB^2},
\]
\[
\begin{aligned}
n_1={}&H(1-t-p^2/W-p\log q)+(p-HW)v
       +p(2p^2-1+t-t^2),\\
n_0={}&p[(H^2-p^2)v+p^2(1+2(1-t)x)-HpW/q].
\end{aligned}
\tag{3}
\]

Let `mu=(t+p)/2`, `C=C(t,p)` from Section 1, and use the right side
of (1) as the upper bound Sline for `Sec(t,r,p)`. Direct multiplication
gives

\[
B^2(w_*-S_{\rm line})=L B+M,
\]
\[
L=\frac{n_1}D+\frac{\mu W}q,
\qquad
M=\frac{n_0}D+\left(\frac Wq\right)^2(C-\mu p).
\tag{4}
\]

Both L and M are independent of k. The affine function in (4) is
strictly decreasing in k, as the next section proves.

## 3. The affine coefficient is strictly negative

It suffices here to assume `0<t<1/2`, `x>0`, `q>1` and the retained
actual derivative floor

\[
v>g_{1-t}(p)=1-(1-t)p/W^2.
\]

Indeed `H-p=xW>0`, so `p-HW<0`. The expression n1 decreases in v
and in log q. Replace v by its lower derivative floor and log q by
`2(q-1)/(q+1)<log q`. This gives a strict upper bound `Lbar` for L.

With y=q-1, a direct collection of the three powers of y gives

\[
-2q(q+1)W^2D\,\bar L=P_0+P_1y+P_2y^2,
\tag{5}
\]

where

\[
P_0=2x^2(1-t)(2t^2+4tx+3x^2+2x+1),
\]
\[
\begin{aligned}
P_1=x[{}&2t(3-2t)+(9+t(7-2t-6t^2))x\\
 &+(20+8t(1-2t))x^2+(19-11t)x^3+2x^4],
\end{aligned}
\]
\[
\begin{aligned}
P_2={}&2t^2+(2t^2+9t)x+(8+18t-2t^3)x^2\\
 &+(19+13t-6t^2)x^3+(16-2t)x^4+3x^5.
\end{aligned}
\tag{6}
\]

Every coefficient is positive when `0<t<1/2`: for example,
`7-2t-6t^2>7-1-3/2>0`, and the remaining two mixed-sign coefficients
are `8+2t(9-t^2)>0` and `19+t(13-6t)>0`. All other signs in (6)
are immediate. Every denominator in (5) is positive. Consequently

\[
\boxed{L<\bar L<0.}
\tag{7}
\]

## 4. Only the upper shape endpoint remains

The incident-upper residual numerator is affine and strictly increasing
in k by
[MIXED_NONSHORT_SHAPE_MONOTONICITY](MIXED_NONSHORT_SHAPE_MONOTONICITY.md).
Write `N(k)=A_N k+B_N`, with A_N>0, and set `k_top=-B_N/A_N`.
The actual necessary boundary root satisfies `N(k)<0`, hence k<k_top.

The margin r increases with k. Thus its actual reverse inequality
`r>=sqrt(tp)` remains true throughout the comparison to k_top. Equations
(4) and (7) imply

\[
B^2(w_*-S_{\rm line})>
\left.B^2(w_*-S_{\rm line})\right|_{k=k_{\rm top}}.
\tag{8}
\]

The actual boundary reverse ceiling is `w*<Sec(t,r,p)<Sline`, so the
left side of (8) is negative. In particular the following single
endpoint inequality is necessary:

\[
\boxed{\left.B^2(w_*-S_{\rm line})\right|_{k=k_{\rm top}}<0.}
\tag{9}
\]

At k_top the incident root equals its upper norm U, so its outgoing
root equals the upper incident envelope. No physical trajectory or
Casimir cap is asserted at k_top. Conditions affected by the change of
k cannot be attached to this endpoint without their own transfer proof.

Proving that the explicit rational-or-logarithmic quantity in (9) is
nonnegative on the correctly enlarged retained domain would finish the
reverse-next exclusion. That final sign is not proved in this note.
