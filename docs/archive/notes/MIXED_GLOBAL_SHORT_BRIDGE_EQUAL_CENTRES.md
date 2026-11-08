# Exact equal-centre face for two short bridges

Research checkpoint, 2026-11-07. This is a hand exclusion of one fixed
face of the M2 minimum problem, not a closure of M2. The neighbouring
reverse centres are assumed equal to the middle centre. No Lean, Lake,
typechecking, CI, word enumeration, or sampled sign assertion is used.

The general comparison is now completed in
[MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md)
and its independent audit. The scope of this constituent lemma is retained.

## 1. Actual data and the necessary outer root

Work in an actual finite normal closed period, where the proved reverse
centre minimum theorem gives strict inequalities against both adjacent
turn margins. Suppose three consecutive reverse centres have the same
active margin `a>0`, and the two intervening forward runs have length one. Bridge order
and the two exact turn secants then give the seven active margins

`(a,ax,ax,a,ay,ay,a)`, with `x,y>1`.

Exchange the left and right formulas so `x<=y`. All subsequent data come from the
same normal multiplier. Define

\[
f(t)=t-t^{-1}-\log t,\qquad h(t)=\log t-1+t^{-1},
\]
\[
U(r)=1-r+r^2,\qquad
V(x)=1+\frac{x}{2(1+x)}-
 \frac{x}{x-1}\log\frac{2x}{1+x}.
\]

The exact turn norms are `u=8 nuL=V(x)` and `v=8 nuR=V(y)`. Put

\[
r=\frac1{1+x},\quad s=\frac1{1+y},\quad
\rho=\frac{a^2}{a^2+4},\quad
D(x)=2+4x-2x^2,\quad d=\rho D(x).
\]

Positive duration at the middle reverse centre gives `0<rho<rs`.
The actual star conditions give further inequalities, but they are not
needed for the scalar exclusion below. Central stationarity is

\[
E=1+r+s-\rho+\log\frac{\rho}{rs}
       -\frac{1-u}{r}-\frac{1-v}{s},\qquad F=E-du.       \tag{1}
\]

Write `G_t(z)=zt-f(t)`. Equivalently

\[
E=G_{1+x}(u)+G_{1+y}(v)-h(1/\rho).                     \tag{2}
\]

Exact Gram transport to the left outer centre gives

\[
w=8\nu_{\rm out}=v-dF,\qquad E_L=2du-E=du-F.          \tag{3}
\]

Set `T0=1+y` and `T=1/[rho(1+x)]`. Then `T>T0>2`.
An actual positive reverse-centre continuation on the remaining side
requires

\[
\frac34<w<f'(T),\qquad
R_L:=L(w)-G_{T_0}(v)+2F\ge0,                          \tag{4}
\]

where

\[
\tau_*(w)=\frac2{1-\sqrt{4w-3}},\qquad
L(w)=w\tau_*(w)-f(\tau_*(w))
    =\log\tau_*(w)-1+\frac2{\tau_*(w)}.                \tag{5}
\]

Indeed the unknown remaining active margin has parameter
`tau=(a+P)/a` in `(2,T)`. Its stationarity residual is
`w tau-f(tau)-G_T0(v)+2F`. The reverse derivative condition places
the actual root after the unique maximum at `tau*`; this gives (4).
Here `f''(t)=(t-2)/t^3>0` for `t>2`, so `L'(w)=tau*(w)` and `L''>0`.
This necessary condition retains the actual transported multiplier and
the correct reverse derivative. It does not fit an independent outer
multiplier or assume an endpoint rank.

We prove `R_L<0` on the whole stated domain.

## 2. Bounds for the turn function

For every `x>1`,

\[
\frac34<V(x)<U\left(\frac1{1+x}\right)<1,
\quad
V'(x)=\frac{U(1/(1+x))-V(x)}{x(x-1)}>0,               \tag{6}
\]
\[
0<V'(x)<\frac{x-1}{4x(1+x)^2}.                       \tag{7}
\]

For a direct positivity proof set `z=2x/(1+x)` in `(1,2)` and use

`V(x)=1+z/4-z log(z)/[2(z-1)]`.

The derivative of the right-hand expression with respect to z is
`1/4-(z-1-log z)/[2(z-1)^2]>0`, by
`log z>(z-1)-(z-1)^2/2`. Its limit at z=1 is `3/4`.
The displayed exact derivative then gives the upper bound in (6), and
`U(1/(1+x))-3/4=(x-1)^2/[4(1+x)^2]` gives (7).

Since `D(x)<=4` and `D'(x)=-4(x-1)`,

\[
(VD)'=DV'-4(x-1)V
 <(x-1)\left[\frac1{x(1+x)^2}-3\right]<0.
\]

The limit of `VD` at x=1 is 3. Consequently

\[
uD(x)<3,\qquad
F_\rho=\frac1\rho-1-uD(x)>0\quad(0<\rho\le rs).      \tag{8}
\]

## 3. The stronger central residual bound

Let `F_b(x,y)=F|_(rho=rs)` be the scalar zero-duration comparison face,
and put

\[
\delta=U(s)-v>0,\qquad
H(x,y)=F_b(x,y)+\frac{(1+y)\delta}{2}.
\]

We will prove

\[
H(x,y)<0\quad(1<x\le y).                            \tag{9}
\]

The identity

\[
V(y)+(1+y)V'(y)-U(s)=(1+2y-y^2)V'(y)
\]

and direct differentiation give

\[
H_y=-\frac s2+s^2\{r[1+uD(x)]-1\}
              +\frac{1+2y-y^2}{2}V'(y).
\]

Using `r<1/2`, `uD<3`, `1+2y-y^2<=2`, and (7),

\[
H_y< -\frac s2+s^2+V'(y)
 <-(y-1)s^2\left(\frac12-\frac1{4y}\right)<0.         \tag{10}
\]

It therefore suffices to treat y=x. Set

\[
z=\frac{x-1}{x+1}\in(0,1),\qquad r=\frac{1-z}{2}.
\]

Then

\[
u=\frac54+\frac z4-\frac{1+z}{2z}\log(1+z)
\]

and the exact diagonal central residual is

\[
F_b(x,x)=
\frac{(1+z)^2\{-2z^2\log(1+z)+6\log(1+z)
                         +z^3+3z^2-6z\}}{4z(z-1)}.
\]

Its log coefficient is strictly negative. The positive atanh series gives

\[
\log(1+z)\ge\frac{2z}{2+z}
                +\frac23\left(\frac z{2+z}\right)^3.
\]

Thus

\[
F_b(x,x)\le
-\frac{z^2(1+z)^2(3z^3+11z^2+24z+24)}
       {12(1-z)(z+2)^3}.
\]

Also, because `u>3/4`,

\[
\frac{(1+x)[U(r)-u]}2<\frac{z^2}{4(1-z)}.
\]

Adding these upper bounds gives

\[
H(x,x)<
-\frac{z^2(3z^5+17z^4+46z^3+65z^2+36z)}
       {12(1-z)(z+2)^3}<0.                            \tag{11}
\]

Equations (8)--(11) prove the useful strict estimate

\[
\boxed{F(\rho)<F_b(x,y)<-\frac{T_0\delta}{2}<0.}     \tag{12}
\]

## 4. Nonpositive bridge diagonal

Suppose `d<=0`. Equations (3) and (12) give `w<=v`. Since L is
increasing,

\[
R_L\le L(v)-G_{T_0}(v)+2F.
\]

By (6), `v<f'(T0)=U(s)` and `2<tau*(v)<T0`. Therefore

\[
L(v)-G_{T_0}(v)
=\int_{\tau_*(v)}^{T_0}[f'(t)-v]\,dt
<T_0[f'(T_0)-v]=T_0\delta.
\]

Equation (12) gives `R_L<0`, contradicting (4). This includes d=0.

## 5. Positive bridge diagonal

Suppose `d>0`. Then `w>v>3/4`. On the genuine necessary root domain,

\[
d\tau_*(w)<dT=\frac{D(x)}{1+x}<2.
\]

Differentiate the scalar residual with x,y held fixed:

\[
\frac{dR_L}{d\rho}
 =[2-d\tau_*(w)]F_\rho-D(x)\tau_*(w)F>0.             \tag{13}
\]

Increase rho from its actual value to the upper endpoint of the
connected interval where `rho<=rs` and `w<=f'(T)`. This is only a
scalar comparison. It need not preserve a geometric trajectory or
the additional star inequalities. Throughout its interior, `w>v>3/4`,
`T>=T0>2`, and (13) holds. Continuity and the bounded rho interval
give one of the following two upper faces. Before w could reach 1
it must reach `f'(T)<1`; there is no missing norm endpoint.

### 5.1. The reverse derivative boundary

If `w=f'(T)`, then `F=[v-f'(T)]/d` and

\[
R_L=G_T(v)-G_{T_0}(v)
       -\left(\frac2d-T\right)[f'(T)-v]<0.
\]

Indeed `T>=T0`, `v<f'(T0)<=f'(T)`, and `2/d>T`.
The first difference is nonpositive because `G_t(v)` decreases on
`[T0,T]`, and the subtracted product is strictly positive.

### 5.2. The central zero-duration boundary

If `rho=rs`, then `T=T0`. A convex function lies below its chord, so
on `3/4<=w<=f'(T)`,

\[
L(w)\le\log2+m(T)(w-3/4),
\quad
m(T)=\frac{4T^2[\log(T/2)-1+2/T]}{(T-2)^2},
\quad 2<m(T)<T.
\]

The slope inequalities follow from the strict increase of `L'=tau*`
between endpoint values 2 and T. The exact chord endpoint identity is

\[
\log2+m(T)(v-3/4)-G_T(v)=[T-m(T)]\delta.
\]

Substitute `w=v-dF` to obtain

\[
R_L\le(T-m)\delta+(2-md)F
 <-m\left(1-\frac{dT}2\right)\delta<0,               \tag{14}
\]

where `2-md>0` and (12) were used. If both boundary equalities hold,
either argument applies. Since R_L increases up to the upper face,
the actual R_L is also strictly negative.

## 6. Exact scope

An actual positive two-short-bridge window cannot have all three
reverse centres equal. The proof allows the two bridge turn sizes to
be unequal, treats either sign and the zero value of the transported
bridge diagonal, and uses no Casimir cap. Weak missing-control ties
are harmless because only necessary incident-root inequalities were
used. Positive durations are essential; equality at the collapsed
circle is only a limit and does not contradict the strict exclusion.

For a whole-period reverse minimum, the neighbouring centres need only
be greater than or equal to the middle one. Reducing those general
centres to this equal-centre face is still an open comparison. A
minimum need not border two short forward runs. Therefore this note
alone does not close M2, prove a global descent, or establish the
unrestricted Reinhardt inequality.

## Independent audit and supplementary checks

The [joint independent internal hand audit](MIXED_GLOBAL_SHORT_BRIDGE_AUDIT.md)
reviews the same-lift, comparison-domain and coefficient-table interfaces.
The corresponding exact checker is
[`mixed_global_short_bridge_equal_centres_certificate.py`](../explorations/mixed_global_short_bridge_equal_centres_certificate.py).
These are hand and algebraic results, not Lean kernel validation.
