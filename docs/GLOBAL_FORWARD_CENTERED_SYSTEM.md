# A centered forward minimum system and a broad circular exclusion

Date: 2026-11-07 UTC. Exact identities and hand inequalities. No Lean,
Lake, typechecking, or CI. This proves one uniform subdomain exclusion
for F and supplies stable formulas for its complementary-domain
certificate. It does not by itself close F or M2.

## 1. The actual five-margin interface

Choose a global minimum active margin `a` in a competitive entirely
forward normal period with `N>=7`, and retain five consecutive margins
`(p,b,a,c,d_ext)`. Set

\[
U=4/a^2,\quad z=b/a,\quad w=c/a,\quad
S=1+z,\quad T=1+w,\quad K=1+U,\quad
Z=z^2+U,\quad W=w^2+U.
\]

The established minimum bounds give `11/5<U<3`, and minimality gives
`z,w>=1`. The actual outer factors are

\[
h=\frac{(p+b)(a+b)}{b^2+4},\qquad
k=\frac{(a+c)(c+d_{\rm ext})}{c^2+4},\qquad q=ST/K.
\]

The star and minimum conditions imply

\[
1<h<\frac Sz\le2,\qquad h\ge S^2/Z,
\qquad
1<k<\frac Tw\le2,\qquad k\ge T^2/W.
\tag{1}
\]

In particular `p/a=hZ/S-z` and `d_ext/a=kW/T-w`. These are the
actual exterior factors, rather than independently chosen comparison
arcs. The whole-period factor bound gives `q<7/4`; since `K<=4` and
`S,T>=2`, it also gives `z,w<5/2`.

Use the same normal multiplier and the Gram coordinates of
[GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md):

\[
u=8d_{-1},\qquad v=8d_0,\qquad E=16e_0,
\qquad \gamma^2=\det\mathsf U=\kappa^2/12.
\]

The actual three stationarity equations become

\[
E=Su+Tv-A,\qquad
n_Lu+m_Lv=R_L,\qquad m_Ru+n_Rv=R_R,
\tag{2}
\]

where

\[
\begin{aligned}
A&=1+z+w-S^{-1}-T^{-1}+K^{-1}-\log q,\\
B&=Zh/S+1-z^2S/(Zh)-z^2/S+z^3/Z-z\log h,\\
C&=Wk/T+1-w^2T/(Wk)-w^2/T+w^3/W-w\log k,\\
\alpha_L&=K(hS-z)/Z,\qquad\alpha_R=K(kT-w)/W,\\
n_L&=S^2(U-z)(h-1)/Z,\qquad
n_R=T^2(U-w)(k-1)/W,\\
m_L&=\frac{K^2}{SZ}\{q-1+(h-1)(qS-1)\},\\
m_R&=\frac{K^2}{TW}\{q-1+(k-1)(qT-1)\},\\
R_L&=\alpha_LA-B,\qquad R_R=\alpha_RA-C.
\end{aligned}
\tag{3}
\]

These equations follow from the exact same-lift interface in
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md),
Sections 1--2. In physical-margin formulas, each row of (2) is multiplied
by `a`; no multiplier is refitted. The conserved determinant is exactly

\[
\boxed{\gamma^2=\frac{K^2}{16U^2}(4uv-E^2).}
\tag{4}
\]

The two genuine exterior missing-control inequalities give

\[
u\ge F_{z/S}(h),\qquad v\ge F_{w/T}(k),\qquad
F_\xi(r)=1+\xi^2r-\frac{\xi r\log r}{r-1}.
\tag{5}
\]

The continuous value at `r=1` is `1-xi+xi^2`. In particular,
`u,v>=3/4`. Weak third-control ties are retained.

## 2. A positive cubic function replaces cancellation in logarithms

For `r>=1` define

\[
f(r)=\frac{r-r^{-1}}2-\log r.
\]

Then

\[
f(1)=0,\qquad f'(r)=\frac{(r-1)^2}{2r^2},\qquad
f''(r)=\frac{r-1}{r^3},
\]

and, writing `r=1+t`,

\[
\frac{t^3}{6(1+t)^2}\le f(1+t)\le\frac{t^3}{6}.
\tag{6}
\]

Both bounds follow by integrating `v^2/[2(1+v)^2]` over `[0,t]`.
For exact interval evaluation set `rho=(r-1)/(r+1)`. The convergent
positive expansion is

\[
f(r)=4\sum_{n=1}^{\infty}\frac{n}{2n+1}\rho^{2n+1}.
\]

Its first `m` terms are a lower bound, and the remainder is at most

\[
\frac{2\rho^{2m+3}}{1-\rho^2}.
\tag{7}
\]

This follows either by integrating the geometric series or from
`4n/(2n+1)<2`. All arguments below lie in `[1,2]` on the remaining
minimum domain, so `0<=rho<=1/3`. Formula (7) has rational endpoints
on rational intervals. The rational first and second derivatives above
can be used directly in Taylor enclosures.

There is also a stable form of (5). Put `x=z-1`, `H=h-1`. Then

\[
\boxed{
F_{z/S}(h)-\frac34
=\frac{x(x+2zH)}{4S^2}
 +\frac{zh}{S}\frac{f(h)}H.}
\tag{8}
\]

The last quotient has continuous value zero at `H=0`. Its positive
series has no small denominator:

\[
\frac{f(h)}H
=\frac4{h+1}\sum_{n=1}^{\infty}\frac{n}{2n+1}
 \left(\frac{h-1}{h+1}\right)^{2n}.
\]

Thus lower polynomial truncations supply lower norm floors and preserve
all limiting cases without subtracting quantities near `3/4`.

## 3. The centered stationarity and Casimir formulas

Put

\[
d=3-U,\quad x=z-1,\quad y=w-1,\quad H=h-1,\quad I=k-1,
\]
\[
\Phi=f(S/2)+f(T/2)+f(4/K),\qquad
 e_0=1-K/8+K^{-1}.
\]

All three summands of `Phi` are nonnegative. Direct substitution gives

\[
E_0:=\frac34(S+T)-A=e_0-\Phi.
\tag{9}
\]

Define the centered residuals and norm increments by

\[
r_L=R_L-\tfrac34(n_L+m_L),\quad
r_R=R_R-\tfrac34(m_R+n_R),\quad
\delta u=u-\tfrac34,\quad\delta v=v-\tfrac34.
\]

Thus (2) is precisely

\[
n_L\delta u+m_L\delta v=r_L,\qquad
m_R\delta u+n_R\delta v=r_R.
\tag{10}
\]

The following polynomial makes the centered left residual explicit:

\[
P(d,x)=d^2(x^2+4x+2)+8dx(x+1)+2x^2(8+4x-x^2).
\]

One has the exact identity

\[
\boxed{
\begin{aligned}
r_L={}&\frac{dx(d+2x)+H P(d,x)}{8SZ}
 +\frac{H^2z(d+4x+x^2)}{2hZ}\\
 &+\frac{K(1+SH)}Z\Phi-zf(h).
\end{aligned}}
\tag{11}
\]

The reflected expression gives `r_R`. Every displayed term except
`-z f(h)` is nonnegative on the remaining minimum domain. At the central
circular parameters `d=x=y=0`, (11) is exactly `r_L=-f(h)`, including
its cubic vanishing as `h` tends to one.

Let `D=m_L m_R-n_L n_R`. The positive factorization is

\[
\begin{aligned}
D={}&\frac{K^4(q-1)}{STZW}
\bigl[(q-1)+H(qS-1)+I(qT-1)\\
&\hspace{29mm}+HI(q+1)\{q(S+T)-q^2-1\}\bigr].
\end{aligned}
\tag{12}
\]

The actual star conditions give `1<q<min(S,T)`, so `D>0`. Therefore

\[
\delta u=\frac{m_Lr_R-n_Rr_L}{D},\qquad
\delta v=\frac{m_Rr_L-n_Lr_R}{D}.
\tag{13}
\]

These formulas recover small norm increments directly. They do not
subtract two reconstructed values close to `3/4`.

The denominator estimate is also valid on the full rectangular enclosure
`S,T in [2,7/2]`, `K in [16/5,4]`, `h,k in [1,2]`, without imposing
the star restrictions. Indeed `q>=1` and
`q<=(35/32) min(S,T)`, so

\[
S+T-q\ge(29/32)\max(S,T)\ge29/16,
\qquad q(S+T)-q^2-1\ge13/16.
\]

Thus (12) gives `D>=K^4(q-1)^2/(STZW)` throughout that rectangle.
Outside a central cube of radius `eta`, one has `q-1>=eta/4`.
This matters when bounding derivatives along a Taylor segment: the
positive denominator is controlled on the entire box, including points
that do not satisfy the actual star or cost constraints.

For the Casimir put `ell=S delta u+T delta v` and

\[
c_x=-\frac{2d(6-d)+x(24-d^2)}{4K},\qquad
c_y=-\frac{2d(6-d)+y(24-d^2)}{4K}.
\]

Then

\[
\boxed{
\begin{aligned}
16U^2(\gamma^2-3/16)
={}&-d^4/64+K^2\bigl[2e_0\Phi-\Phi^2
 +c_x\delta u+c_y\delta v\\
 &\hspace{26mm}+2\Phi\ell+4\delta u\delta v-\ell^2\bigr].
\end{aligned}}
\tag{14}
\]

In particular the rational part of the base term cancels exactly:
`K^2(9/4-e_0^2)-3U^2=-d^4/64`. The comparison with `23/125` adds
`7U^2/125` to the right side of (14). Formula (14), rather than a
difference of two values near `3/16`, is suited to an exact interval
certificate.

## 4. A broad uniform circular exclusion

**Theorem.** Assume (2)--(4), `u,v>=3/4`, `d,x,y>=0`, and

\[
s=d+x+y\le3/20,\qquad 1\le h,k\le2,
\qquad s+H+I>0.
\tag{15}
\]

Then

\[
\boxed{
\delta u+\delta v\le\frac95s^2,\qquad
\gamma^2\ge\frac{5277274431423}{28464128000000}
>\frac{37}{200}>\frac{23}{125}.}
\tag{16}
\]

This theorem needs no cost budget and no additional strict switch gap.
An actual competitive forward period satisfies the stated strict
nondegeneracy. Hence (16) excludes every actual minimum window in the
simplex (15), uniformly in both exterior factors.

### 4.1 Positive row sums

On (15), `K,Z,W>=77/20`, `S,T<=43/20`, `z,w<=23/20`, and
`Z,W<=1729/400`. Consequently

\[
\frac{S^2(U-z)}Z\ge\frac{2960}{1729}>\frac32,
\qquad
\frac{K^2}{TW}\ge\frac{16940}{10621}>\frac32.
\]

Here `U-z=2-d-x>=37/20`; the reflected inequalities also hold.
Since `q>=1` and `S,T>=2`, the coefficient formulas in (3) imply

\[
n_L\ge\tfrac32H,\quad n_R\ge\tfrac32I,
\quad m_L\ge\tfrac32(q-1+H),\quad
m_R\ge\tfrac32(q-1+I).
\]

Moreover

\[
q-1=\frac{d+2x+2y+xy}{4-d}\ge s/4.
\]

Thus both row sums `n_L+m_R` and `m_L+n_R` are at least

\[
\frac32(H+I+s/4)>0.
\tag{17}
\]

### 4.2 Cubic control of the centered residual

Equation (6), `K>=2`, and `d+x+y=s` give

\[
0\le\Phi\le\frac{x^3+y^3+d^3}{48}\le s^3/48.
\tag{18}
\]

Also `dx(d+2x)<=s^3/2` and `P(d,x)<=(86/5)s^2`. Applying the
rational bounds of Section 4.1 to (11) gives the following exact upper
estimates for its positive terms:

\[
\frac{dx(d+2x)}{8SZ}\le\frac5{616}s^3,\qquad
\frac{HP(d,x)}{8SZ}\le\frac{43}{154}Hs^2,
\]
\[
\frac{H^2z(d+4x+x^2)}{2hZ}
\le\frac{1909}{3080}H^2s\le\frac58H^2s,
\]
\[
\frac{K(1+SH)}Z\Phi
\le\frac5{231}s^3+\frac{43}{6160}Hs^2.
\]

The last line uses `s<=3/20` in its term proportional to `H`.
Since `5/616+5/231=5/168<1/32` and
`43/154+43/6160=1763/6160<3/10`, while (6) and `h<=2` give
`z f(h)>=H^3/24`, it follows that

\[
r_L\le\frac{s^3}{32}+\frac3{10}Hs^2
       +\frac58H^2s-\frac{H^3}{24}.
\tag{19}
\]

Complete the square in the last two terms:

\[
\frac58H^2s-\frac{H^3}{24}
=H\left[\frac{75}{32}s^2-
 \frac{(H-15s/2)^2}{24}\right]
\le\frac{75}{32}Hs^2.
\]

Add the reflected bound. Since `3/10+75/32=423/160<27/10`,

\[
r_L+r_R\le\frac{s^3}{16}+\frac{423}{160}(H+I)s^2
\le\frac{27}{10}s^2(H+I+s/4).
\tag{20}
\]

Adding (10), and using `delta u,delta v>=0` and (17), now gives
`delta u+delta v<=(9/5)s^2`. Division is legitimate by the last
condition in (15); no stationarity determinant is divided out.

### 4.3 Exact Casimir separation

One has `e_0>0`, `Phi>=0`, `ell>=0`, and `delta u delta v>=0`.
Also

\[
|c_x|,|c_y|\le\frac{120}{77}s,
\qquad
\ell\le\frac{43}{20}\frac95s^2=\frac{387}{100}s^2.
\]

Dropping only the nonnegative terms in (14) and using (18) yields

\[
\gamma^2\ge\frac3{16}-\frac{400}{3249}
\left[\frac{s^4}{1024}+\frac{216}{77}s^3
 +\frac{149769}{10000}s^4+\frac{s^6}{2304}\right].
\tag{21}
\]

Here `U>=57/20` and `K<=4` bound both positive prefactors in the
required direction. Every term in the bracket increases with `s>=0`.
At `s=3/20`, the loss in (21) is exactly

\[
\frac{59749568577}{28464128000000}.
\]

Subtraction proves (16). In particular the excess over `37/200` is
`11410751423/28464128000000>0`.

The nondegeneracy in (15) is essential for the algebraic formulation.
At `d=x=y=H=I=0`, the uncentered two outer rows vanish for all `u,v`;
for example `u=v=1` gives `E=7/4` and `gamma^2=5/48`. That zero-duration
base fibre is not an actual positive three-arc window.

## 5. The seven-entry cost relaxation remains a whole-period bound

For completeness, the numerical model's cost term is a valid necessary
condition. Let `G` be the symmetric physical edge function in
[GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET](GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET.md).
The cyclic action has positive partial derivatives on the whole positive
orthant. Lower every margin outside the five retained consecutive ones
to `a`. The resulting cost has the six boundary and interior edges of
`(a,p,b,a,c,d_ext,a)` and `(N-6)G(a,a)`. Since `N>=7` and `G(a,a)>0`,

\[
C\ge\frac{\sqrt{12}}8\bigl[
G(a,p)+G(p,b)+G(b,a)+G(a,c)+G(c,d_{\rm ext})
+G(d_{\rm ext},a)+G(a,a)\bigr].
\tag{22}
\]

This is a scalar lower bound; the seven-entry comparison array is not
asserted to close its frame or satisfy PMP. With `P=p/a`, `D_ext=d_ext/a`
and dimensionless entries `(1,P,z,1,w,D_ext,1)`, the same bound is
`[sqrt(12)/(2U)]` times the cyclic sum of

\[
g_U(r,t)=3rt-U-\frac{r^2}{2}\log\frac{(r+t)^2}{r^2+U}
                  -\frac{t^2}{2}\log\frac{(r+t)^2}{t^2+U}.
\]

Thus the five-parameter model retains three same-lift stationary
identities, the actual two exterior missing-control floors, the global
minimum restrictions, and a legitimate whole-period cost budget. Other
PMP and full-frame restrictions may be omitted to form a relaxation;
excluding that larger domain would be sufficient. Numerical minimizers
or penalty objectives are not rigorous lower bounds on it.

## Exact checker

[`global_forward_centered_system_certificate.py`](../explorations/global_forward_centered_system_certificate.py)
checks the centered residuals, determinant factorization, floor identity,
Casimir expansion, derivative identities, all rational corner estimates,
and the final fraction. Domain coverage, positivity, the scalar
seven-entry comparison, and the actual PMP interface are the hand
arguments above. No sampled trajectory or floating-point sign is used
in the broad-corner proof.
