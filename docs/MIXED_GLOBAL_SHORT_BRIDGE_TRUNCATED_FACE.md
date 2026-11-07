# The central truncated-root value for both bridge-diagonal signs

Research proof checkpoint, 2026-11-07. This note closes the central
zero-factor value of the truncated outer-root comparison. The sign does
not require either sign of the bridge diagonal. Its complete finite
integer certificate consists of the two static CSV tables specified
below. The proof uses those displayed integer identities, elementary
logarithm bounds, and the separately proved upper-endpoint value. It uses
no floating sign claim, word-length enumeration, Lean, Lake, typecheck,
or CI. The complete two-short-bridge theorem also uses its separate
continuation lemmas; this note alone is not a whole M2 exclusion.

## 1. Statement and the genuine order restriction

Let

\[
1\le\alpha<x\le y,\qquad
x\le\beta\le x+\frac{7x(\alpha-1)}{7+2x}.
\tag{1}
\]

Set

\[
q=(1+x)(1+y),\quad P=q+\alpha^2-1,\quad
Q=\alpha(\alpha+\beta),\quad T=P/Q\ge2,\quad T_B=Q/\alpha^2,
\]
\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x.
\]

There is **no sign assumption on D**. For

\[
V(s)=1+\frac{s}{2(1+s)}-
\frac{s}{s-1}\log\frac{2s}{1+s},
\]

assume `u<=V(x), v<=V(y)`. Define the central-face scalar values

\[
E=(u-1)(1+x)+(v-1)(1+y)+1+
\frac1{1+x}+\frac1{1+y}-\frac1q,
\]
\[
w=\frac{q^2v+D^2u-DqE}{P^2},\qquad
E_L=\frac{2Du-qE}{P}.
\]

With

\[
f(t)=t-t^{-1}-\log t,\qquad
h_0(t)=\log t-1+t^{-1},
\]

the conclusion is

\[
\boxed{R_2:=2w-f(2)+uT_B-f(T_B)-h_0(P/\alpha^2)-E_L<0.}
\tag{2}
\]

In particular, (2) covers the actual truncated maximum when `w<=3/4`.
The proof of the scalar inequality does not require this norm condition;
it also retains `w=3/4`, `T=2`, equal centre scales, and the closed upper
order boundary in (1).

Here (1) is a necessary restriction from the **two genuine turn
secants**, not an arbitrary strengthening of the scalar domain. In the
notation of the audited `MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL` proof, the
same secant path satisfies

\[
\alpha_\beta=\frac\alpha\beta+
\frac\eta\xi\left(\frac x\beta+
\frac{x-\alpha}{\beta-1}\right),\qquad \eta/\xi\ge2/7.
\]

Consequently

\[
\frac{d}{d\beta}\frac{\alpha+2x/7}{\beta}
=\frac{(\eta/\xi)[x+\beta(x-\alpha)/(\beta-1)]-2x/7}{\beta^2}
\ge\frac{2(x-\alpha)}{7\beta(\beta-1)}>0.
\]

Integrating from `beta=x, alpha=1` gives (1), strictly when `beta>x`.
The central relation `q=(1+x)(1+y)` is a scalar zero-duration comparison
face. These formulas are the exact same-lift transport formulas at
actual data; the comparison face is not asserted to remain a positive
PMP trajectory.

## 2. Rational upper bound and norm coefficients

The logarithms in (2) combine to give

\[
R_2=2(w-3/4)+(u-1)T_B+1+T_B^{-1}-(TT_B)^{-1}
-E_L-\log(T/2).
\tag{3}
\]

Put `zeta=(T-2)/(T+2)` in `[0,1)`. The bound

\[
\log(T/2)\ge\frac{6\zeta}{3-\zeta^2}
=\frac{3(P^2-4Q^2)}{P^2+8PQ+4Q^2}
\tag{4}
\]

follows because the difference vanishes at zero and has derivative

\[
\frac{2}{1-\zeta^2}
-\left(\frac{6\zeta}{3-\zeta^2}\right)'
=\frac{8\zeta^4}{(1-\zeta^2)(3-\zeta^2)^2}\ge0.
\]

Replace the logarithm in (3) by the right side of (4), obtaining the
rational upper bound `Rhat`. It is affine in u and v, with both
coefficients strictly positive. For clarity, put
`S=1+x, lambda=q/P, d=D/P, b=lambda*S`. The coefficients are

\[
c_u=T_B+b-2d+2d(d-b),\qquad
c_v=\lambda(1+y)\left[1-\frac{2(D-S)}P\right].
\tag{5}
\]

The inequality `D-Q<S` and `P>=2Q` give `c_v>0`. For `D<=0`, every
nonconstant term in `c_u=T_B+b-2d+2d(d-b)` is nonnegative, and its first
two terms are positive. For `D>0`, the elementary order inequalities
give `D<S^2`, `b>2d`, and

\[
d<d_{\max}=1/T+b/q.
\]

The coefficient with the factor 2 replaced by T is no larger. If
`F(t)=T_B+b-2t+Tt(t-b)`, then

\[
F(d)-F(d_{\max})
=T(d-d_{\max})(d+d_{\max}-b-2/T)>0,
\]

because the last factor is less than `(1/q-1/2)b-1/T<0`. Moreover,

\[
F(d_{\max})=
\frac{(q-1)[(\alpha+\beta)^2-(1+x)^2]}{QP}\ge0.
\]

Thus (5) is positive for either sign of D. Raising the two norms remains
a scalar upper bound, whether or not the new auxiliary w belongs to a
root interval. The elementary cubic logarithm bound used in the central
chord proof gives

\[
V(s)\le V_+(s)=
\frac{131s^4+229s^3+163s^2+47s+6}{6(s+1)(3s+1)^3}.
\tag{6}
\]

Indeed, writing `r=(s-1)/(s+1)` gives
`V(s)=5/4+r/4-(1+r)log(1+r)/(2r)`; apply
`log(1+r)>=2a+2a^3/3`, `a=r/(2+r)`.

It is enough to show `Rhat(V_+(x),V_+(y))<0`.

## 3. The exact polynomial and its derivative identity

Write

\[
C=P^2+8PQ+4Q^2,\quad
e=q(u-1)(1+x)+q(v-1)(1+y)+q+(1+x)+(1+y)-1=qE,
\]
\[
W=q^2v+D^2u-De.
\]

The polynomial affine in u,v

\[
\begin{aligned}
\mathcal N(u,v)={}&4QCW-P^2QC
+2P^2C(u-1)(\alpha+\beta)^2+2\alpha^2P^2C-2\alpha^2PQC\\
&-2PQC(2Du-e)-6P^2Q(P^2-4Q^2)
\end{aligned}
\tag{7}
\]

is exactly `2P^2 Q C Rhat`. Let `N0=N(0,0)`,
`Nu=N(1,0)-N0`, `Nv=N(0,1)-N0`, and

\[
n(s)=131s^4+229s^3+163s^2+47s+6,\qquad
d_+(s)=6(s+1)(3s+1)^3.
\]

Define the cleared negative upper bound

\[
p=-N_u n(x)d_+(y)-N_v n(y)d_+(x)-N_0d_+(x)d_+(y).
\tag{8}
\]

All clearing factors are positive. Parameterize (1) by

\[
\alpha=1+h,\quad x=1+h+j,\quad y=x+\ell,\quad
\beta=x+\frac{7hxz}{(7+2x)(1+z)},
\tag{9}
\]

where `h,z,ell>=0` and `j>0`. Put

\[
r=(7+2x)(1+z),\quad \widetilde p=r^5p,
\]
\[
G=r\{j(j+2)+(h+j+2)\ell-2h(h+1)\}-14(h+1)hxz
=r(P-2Q)\ge0.
\tag{10}
\]

The exponent five is the degree of (8) in beta. The key integer identity
is

\[
\boxed{\partial_\ell\widetilde p=
136048896\,jz(12288z^3+40192z^2+42928z+12717)G+B.}
\tag{11}
\]

Every nonzero coefficient of B is a positive integer. Its full table is
[mixed_global_short_bridge_truncated_face_derivative_positive.csv](../explorations/mixed_global_short_bridge_truncated_face_derivative_positive.csv), with **11,438 rows**.
A row `(h,j,z,ell,coefficient)` specifies that coefficient of the
corresponding monomial; all unlisted coefficients are zero. These are
exponent-column names, not extra variables.

Thus `p_tilde` is nondecreasing in ell throughout `G>=0`. Since

\[
\partial_\ell G=r(h+j+2)>0,
\]

its minimum on the allowed ell interval occurs either at `ell=0`, or
at the first point `G=0`. This is monotonicity of the cleared polynomial;
no derivative sign for the original rational residual is asserted.

## 4. The two boundary values

### 4.1. The boundary `G=0`

This is precisely `T=2`. The logarithm in (4) is then exact, and
`Rhat=R2=R(T)` for the scalar norms substituted in it.
The independently proved initial upper-endpoint numerator in
`MIXED_GLOBAL_SHORT_BRIDGE_UPPER_ENDPOINT.md`, Section 4, is strictly negative after
raising both norms to

\[
\overline V(s)=\frac{55s^2+64s+25}{4(s+1)(17s+7)}.
\]

It also applies to `V_+`, because

\[
\overline V(s)-V_+(s)=
\frac{(s-1)^3(s^2+22s+9)}
{12(s+1)(3s+1)^3(17s+7)}>0.
\tag{12}
\]

The same positive norm coefficients (5) justify this comparison.
Only that initial endpoint value is used here; no global scale
monotonicity is assumed. Hence `p_tilde>0` on `G=0`.

### 4.2. The boundary `ell=0`

If `G>=0` at `ell=0`, then `j>h`. Indeed, `j<=h` with `h>0` would give

\[
G/r\le j(j+2)-2h(h+1)\le-h^2<0;
\]

and if `h=0`, `j>h` already follows from `j>0`.
Set `j=h+t`, with `t>0`. The second exact identity is

\[
\boxed{
\widetilde p(h,h+t,z,0)=
27518828544\,tz^4(873+603z+7169hz)(h-t)^2+A(h,t,z).
}
\tag{13}
\]

Every nonzero coefficient of A is a positive integer. The full table is
[mixed_global_short_bridge_truncated_face_equal_turn_positive.csv](../explorations/mixed_global_short_bridge_truncated_face_equal_turn_positive.csv), with **1,905 rows**;
each row `(h,t,z,coefficient)` specifies the corresponding monomial.
In particular, A contains

\[
26748301344768\,t^3+10154447732736\,t^3z^5.
\tag{14}
\]

Therefore (13) is strictly positive for `t>0`, including `h=0` or
`z=0`. This proves the second boundary value.

Together, (11)--(14) give `p_tilde>0` on the entire scalar domain.
Equations (6)--(8) now imply (2).

## 5. Closed order boundary, verification, and scope

For the closed upper boundary in (1), take the leading coefficient in
z in (11) and (13), equivalently divide by `z^5` and pass to the limit.
The resulting derivative identity again has a nonnegative coefficient
times the limiting G plus a polynomial with nonnegative coefficients.
The boundary reduction is unchanged. At `ell=0`, the second term of
(14) leaves the strictly positive reserve
`10154447732736 t^3`; at `G=0`, the upper-endpoint certificate already
retains the closed order boundary. Since `r/z` tends to `7+2x>0`, all
cleared denominators remain positive. If `h=0`, `beta=x` is covered
directly by `z=0`.

The two static CSV tables are part of the displayed finite certificate.
Identities (7)--(13) specify ordinary integer polynomial equalities that
can be verified coefficient by coefficient. The standalone replay
[mixed_global_short_bridge_truncated_face_certificate.py](../explorations/mixed_global_short_bridge_truncated_face_certificate.py) independently reconstructs the
rational numerator and the order substitution, reads and checks every
static positive coefficient, and verifies both identities and the strict
reserves. Its **14 exact identities/table checks pass** under Python
3.12 / SymPy 1.14. No optimizer or floating computation is used in replay.

This completes the central truncated value for both diagonal signs.
The combination with the central convex-root value, upper endpoint,
and audited scale/continuation results is proved in
[MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md). F, long-forward-run M2, global minimality, affine uniqueness, and
Lean kernel validation are not claimed by this scalar lemma.
