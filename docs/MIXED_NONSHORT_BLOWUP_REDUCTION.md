# A regular five-variable domain for the nonshort continuation test

Date: 2026-11-07. Hand algebra and an exact symbolic identity checker.
The two full interval exclusions described below are **pending**. This
note alone closes no part of M2.

The actual same-covector interface is
[MIXED_SMALLER_TURN_CONTINUATION](MIXED_SMALLER_TURN_CONTINUATION.md).
Its next-switch alternative is independent of the eventual forward-run
length. This note removes a zero denominator from that alternative's
scalar domain; it does not introduce a control-word catalogue.
The actual period here is the compact minimizing-period representative
retained in [GLOBAL_MINIMIZER_COMPACTNESS](GLOBAL_MINIMIZER_COMPACTNESS.md)
and [QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md).
Their lower active-margin bound is an input to the finite chart cover.

## 1. Three closed coordinate charts

Retain the actual notation `a,b,c,d,r,u,v,h,K,S,T,Q,W,Z,Y` of the
continuation note, with `c<=b`. Set

\[
\delta_0=K/(ST)-1,\qquad
\delta_1=(d-a)/T,\qquad
\delta_2=WZ/Q-1.
\tag{1}
\]

All three are positive at actual data. Choose an index at which their
maximum is attained and write

\[
\delta_i=\varepsilon l_i,\qquad
\varepsilon=\max_i\delta_i>0,
\qquad 0\le l_i\le1,
\]

with the selected `l_i=1`. The two other weights, together with
`a,c,epsilon`, give five independent coordinates. Ties lie in more than
one chart, which is harmless. The chart closures include `epsilon=0`.

Reconstruction uses positive denominators:

\[
\begin{gathered}
K=a^2+4,\quad T=a+c,\quad
S=\frac K{T(1+\delta_0)},\quad b=S-a,\\
d=a+T\delta_1,\quad W=T(1+\delta_1),\quad Q=d^2+4,\\
q=1+\delta_2,\quad Z=Qq/W,\quad r=Z-d,\quad Y=W^2-T^2.
\end{gathered}
\tag{2}
\]

The following rational rectangles contain every actual point:

| Selected maximum | Range of `epsilon` | Other independent coordinates |
| --- | --- | --- |
| `delta_0`, so `l_0=1` | `[0,61/4]` | `2/15<=a<=17/20`, `2/15<=c<=2`, `l_1,l_2 in [0,1]` |
| `delta_1`, so `l_1=1` | `[0,15]` | the same shape bounds, `l_0,l_2 in [0,1]` |
| `delta_2`, so `l_2=1` | `[0,15]` | the same shape bounds, `l_0,l_1 in [0,1]` |

Here `a>=2/15` is the retained compact-state lower bound, and
`a^2<12/17` implies `a<17/20`. Since `b>=c>a` and `K>ST`,
one has `c<sqrt(a^2+4)-a<2`. The full compact input supplies a useful
additional pair bound. In the physical margin normalization,

\[
p_1=2(q_*-x)/y,\quad p_2=2(q_*+x)/y,
\quad q_*=1/\sqrt3.
\]

Thus `y<=9/2` gives

\[
p_1+p_2=4/(\sqrt3y)\ge8/(9\sqrt3)>1/2.
\]

The strict last comparison follows from `256>243`. Cyclic invariance
of the common compact set permutes the three margins, so every state
pair sum exceeds `1/2`. The identity
`p_0p_1+p_1p_2+p_2p_0=4` then gives every margin strictly less than
8. In particular `T=a+c>=1/2`. If `a<=1/4`, then
`K/T^2-1<=4a^2+15<=61/4`; if `a>=1/4`, use `T>=2a` to get
`K/T^2-1<=1/a^2-3/4<=61/4`. Hence

\[
\delta_0\le K/T^2-1\le61/4.
\]

The turn log-concavity `ad<c^2` gives
`delta_1<(c-a)/a<14<15`. The strict-star inequality `dr<4` is
equivalent to `delta_2<c/d<c/a<15`. These facts justify all three
finite chart bounds, including asymmetric shapes.

The lower bound also applies to inactive controls. In the denominator
normalization of QUANTITATIVE_REGULAR_SWITCH_BOUND, equation (10),
`gamma_i>=2/(15sqrt3)` and the physical margin is
`p_i=sqrt3 gamma_i`. Thus **every state margin** is at least
`m=2/15`. At the two exterior actual switches this gives

\[
cd+m(c+d)\le4,\qquad
dr+m(d+r)\le4.
\tag{2a}
\]

They are geometric restrictions of the same compact minimizing period,
not an assumption that an inactive margin is at least the selected
global active minimum `a`.

There is one further exact restriction in the third max chart:

\[
\boxed{l_2=1\quad\Longrightarrow\quad d\le c.}
\tag{2b}
\]

Indeed put `q_c=W/T=1+delta_1`. The actual turn secant satisfies

\[
F_{d/W}(q_c)-v
=(d-c)\left[\frac1T-\frac{\log q_c}{d-a}\right].
\tag{2c}
\]

The bracket is positive for `d>a`. If `d>c`, then `d/W>1/2`. For
`xi>1/2` and `q>1`,

\[
F_\xi'(q)=\xi^2-\xi\frac{q-1-\log q}{(q-1)^2}
>\xi(\xi-1/2)>0,
\]

because the quotient is
`integral_0^1 t/(1+(q-1)t) dt<1/2`. Thus
`F_{d/W}` is strictly increasing on `q>1`. The end missing-control
inequality `v>=F_{d/W}(q)` would therefore force `q<q_c`. This
contradicts `delta_2>=delta_1` in the third max chart. Weak third ties
remain covered: (2c) is strictly positive when `d>c` even if the
actual missing gap is zero. At `delta_1=0`, `d=a<=c` already.
The restriction is equivalently
`delta_1<=(c-a)/(a+c)` and can be used as a chart-specific contractor.

## 2. The only zero root denominator

For fixed `a,b,c,d`, the forward-root equation is

\[
R_d(u)=C_d-Wv-Zw+16d h_d/Q=0,
\]

where `h,h_d,w` are the affine functions of `u` in the continuation
note. Its coefficient has the exact positive decomposition

\[
\begin{aligned}
-\partial_uR_d
={}&\frac K{aQW}\bigl[
(q-1)(aK+SY)+a(K-ST)+Sc(d-a)\bigr]\\
={}&\varepsilon D_1,
\end{aligned}
\tag{3}
\]

with

\[
\boxed{
D_1=\frac{K^2}{aQW(1+\varepsilon l_0)}
\left[a(l_0+l_2)+cl_1+a\varepsilon l_0l_2
 +T\varepsilon l_1l_2(2+\varepsilon l_1)\right].}
\tag{4}
\]

Every denominator is positive throughout the three initial rectangles.
Since one weight equals one and `a,c>0`, `D_1>0` even at
`epsilon=0`. Thus the original coefficient vanishes only where all
three degeneracies vanish simultaneously. No unrelated covector fibre
is selected by division at that point.

## 3. A centered root numerator

Use `U(x)=1-x+x^2`, and center the actual root equation at its necessary
upper norm `U(a/S)`. Define the analytic function

\[
H(z)=\frac{\log(1+z)-z+z^2/2}{z^3}
     =\int_0^1\frac{t^2}{1+zt}\,dt,\qquad H(0)=1/3.
\tag{5}
\]

Thus `log(1+z)=z-z^2/2+z^3H(z)`. Let

\[
N=dW-qY,
\]
\[
B_v=c(4-a^2)+8a+a\delta_1(c^2+4)
 +\delta_2T(\delta_1+2)
     [K+aT\delta_1(\delta_1+2)].
\tag{6}
\]

The exact coefficient of `v` in `R_d(U)` factors as

\[
\partial_v R_d
=-\frac{\delta_1T^2}{aQW}B_v.
\tag{7}
\]

It is negative for a positive turn on this domain. In particular its
vanishing at the zero-turn face is retained algebraically rather than
obtained by subtracting large interval expressions.

The numerator can be written

\[
\boxed{R_d(U)=\varepsilon^2\Phi,}
\tag{8}
\]

where

\[
\begin{aligned}
\Phi={}&\frac{\overline P}{2aQ(1+\delta_1)^2q}
-\frac{\varepsilon K N l_0^3H(\delta_0)}{QW}\\
&+\frac{\varepsilon cT l_1^3B_vH(\delta_1)}{aQW}
-\varepsilon d l_2^3H(\delta_2).
\end{aligned}
\tag{9}
\]

Here `Pbar` is a polynomial of degree at most six in `epsilon`.
The following compact definition specifies it exactly and is directly
checkable with polynomial multiplication. Treat `epsilon` as a formal
indeterminate in (2), and set

\[
\begin{aligned}
U_K&=K^2-aKT(1+\delta_0)+a^2T^2(1+\delta_0)^2,\\
v_N&=aW+c^2+(c/2)\delta_1W,\\
V_N&=-aQW^2-aqY^2+2adWY+KTN,\\
B_N&=-KT^2+2a^2T^2(1+\delta_0)+Ka^2-a^3T,\\
C_N&=Q^2q^2-d^2Qq+d^2W^2(q-1)+4cWq,\\
P={}&2aTWC_N+2qV_Nv_N-2aTWq^2U_K+2WqNB_N\\
&-aTWqKN(2\delta_0-\delta_0^2)
-aTWqdQW(2\delta_2-\delta_2^2).
\end{aligned}
\tag{10}
\]

Writing `P=sum P_i epsilon^i`, direct exact multiplication gives
`P_0=P_1=0`, `deg P<=8`, and `T^3` divides each `P_i`, for
`2<=i<=8`. Define

\[
\overline P=\sum_{i=2}^8(P_i/T^3)\varepsilon^{i-2}.
\tag{11}
\]

The leading coefficient has the useful factorization

\[
P_2/T^3=(4-a^2-2ac)[a(l_0+l_2)+cl_1]^2.
\tag{12}
\]

It is positive on the retained shape domain. In fact
`4-a^2-2ac>1`: by `c<=sqrt(a^2+4)-a`, it suffices to show
`a^2+3>2a sqrt(a^2+4)`. Squaring positive sides leaves
`9-10a^2-3a^4`, which is at least `129/289>0` when
`a^2<=12/17`. Formula (12) supplies a uniform positive corner
coefficient; it does not itself give a bound on the higher terms.

Equations (3) and (8) now solve the actual same-lift root uniquely:

\[
\boxed{u=U(a/S)+j,\qquad j=\varepsilon\Phi/D_1.}
\tag{13}
\]

In particular, since actual `epsilon>0`, the necessary upper incident
norm becomes the regular inequality `Phi<=0`. Equations (4) and (9)
give a continuous, differentiable extension of this formula to the
closed chart. That extension is a scalar comparison domain, not an
assertion that its zero-duration points are trajectories.

## 4. Center the Casimir on the entire zero-duration face

Set

\[
r_0=aT/K,\quad t_0=a/T,\quad\rho=a^2/K,
\quad U_0=U(r_0),\quad V_0=U(t_0),
\]
\[
h_0=K[-1+2(r_0+t_0)-\rho]/16.
\]

The exact identity

\[
U_0V_0K^2/64-h_0^2=3/16
\tag{14}
\]

holds for every positive shape `(a,c)`. With `x=c/T`, define

\[
\begin{aligned}
\Delta u&=(2r_0^2-r_0)\delta_0+r_0^2\delta_0^2+j,\\
\Delta v&=\delta_1(x/2-x^2)
  +\delta_1^2\{x^2/(1+\delta_1)-xH(\delta_1)\},\\
\Delta h&=\frac K{16}
 [2r_0\delta_0-\log(1+\delta_0)+\Delta v/t_0+(S/a)j].
\end{aligned}
\tag{15}
\]

These reconstruct exactly `u=U_0+Delta u`, `v=V_0+Delta v`,
and `h=h_0+Delta h`. Consequently

\[
\boxed{
\gamma^2-\frac{23}{125}
=\frac7{2000}
 +\frac{K^2}{64}(V_0\Delta u+U_0\Delta v+\Delta u\Delta v)
 -2h_0\Delta h-(\Delta h)^2.}
\tag{16}
\]

At `epsilon=0` all three increments vanish, so every point of the
entire zero-duration face has excess `7/2000>0`. It is excluded by
the competitive Casimir cap, including noncircular shapes. The leading
factor (12) gives an additional upper-norm obstruction near that face.
No all-zero-duration fibre is silently divided out.

## 5. Necessary inequalities for the fixed finite cover

After reconstruction, the domain retains the following necessary
inequalities. Replacing strict inequalities by weak inequalities only
enlarges this scalar domain.

| Source | Necessary inequalities |
| --- | --- |
| Global minimum, orientation and scale | `c>=a`, `b>=c`, `12-17a^2>=0`, `r>=a` |
| Compact state geometry, with `m=2/15` | `T,S,W,Z>=1/2`, `b,d,r<=8`, `cd+mW<=4`, `dr+mZ<=4` |
| Turn log-concavity | `c^2>=ad` |
| Incident turn norms | `u>=3/4`, `Phi<=0`, `v<=U(a/T)` |
| Actual outgoing turn derivative | `v>=g_c(d)` |
| Actual forward derivative on `d` | `w>=g_d(r)` |
| Both missing-control inequalities on `d` | `v>=F_{d/W}(q)`, `w>=F_{d/Z}(q)` |
| Local forward acuteness | `h_d>=0` |
| Whole-period Casimir bounds | `27/256<=gamma^2<=23/125` |

The turn derivative may be divided by its known positive factor:

\[
v-g_c(d)=\frac cT\delta_1
\left[\frac12-\frac{1-c/T+\delta_1}{(1+\delta_1)^2}
      -\delta_1H(\delta_1)\right].
\tag{17}
\]

Thus the bracket is a regular necessary nonnegative quantity, including
the closure at `delta_1=0`.

The upper incident inequality can likewise be divided exactly:

\[
U(a/T)-v=\frac cT\delta_1
\left[\frac cT-\frac12
-\delta_1\left\{\frac{c/T}{1+\delta_1}-H(\delta_1)\right\}\right].
\tag{17a}
\]

The following positive-factor versions of the geometric inequalities
avoid subtracting repeated rational expressions in an interval caller:

\[
\begin{aligned}
b\ge c&\iff K-T^2(1+\delta_0)\ge0,\\
c^2\ge ad&\iff c-a(1+\delta_1)\ge0,\\
r\ge a&\iff4-a^2-2ac-T^2\delta_1+Q\delta_2\ge0,\\
cd+mW\le4&\iff4-ac-mT-T(c+m)\delta_1\ge0,\\
dr+mZ\le4&\iff c-m-(d+m)\delta_2\ge0.
\end{aligned}
\tag{17b}
\]

All denominators cleared here are strictly positive on the chart.
For example `4-dr-mZ=(Q/W)[c-m-(d+m)delta_2]`.

For the local acuteness row, the actual Jacobi pairing is `e_d=h_d/Q`
by [MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md).
The triangle calculation in
[GLOBAL_STRUCTURE_FORWARD_ACUTE](GLOBAL_STRUCTURE_FORWARD_ACUTE.md),
Sections 1--2, uses only the local stationarity equation, two incident
forward derivative floors and strict star. It therefore applies to this
mixed `++` arc as well, as also explained in
[MIXED_GLOBAL_PHASE_DENSITY](MIXED_GLOBAL_PHASE_DENSITY.md), Section 1.
If `e_d<=0`, that calculation gives `gamma^2>3/16`, contrary to the
competitive cap. Hence `h_d>0` at actual data.

The two pending exclusion domains append respectively:

1. **Forward next switch:** the transported next norm `t` in the
   continuation note satisfies `t>=3/4`.
2. **Reverse next switch:** `r^2>=ad` and
   `w<=Sec(a,r,d)`.

The continuation alternative proves that every actual smaller-turn
nonshort case belongs to one of these domains. Excluding both full
continuous domains would therefore exclude arbitrary nonshort run
lengths under this assignment. The scalar tests are necessary conditions
only; no claim that every scalar point represents a genuine first event
is required or made.

## 6. Directed evaluation of the analytic remainder

Differentiating (5) gives

\[
(-1)^k H^{(k)}(z)
=k!\int_0^1\frac{t^{k+2}}{(1+zt)^{k+1}}\,dt>0.
\]

Thus `H` decreases, `H'` increases, and `H''` decreases. For a
nonnegative interval, their endpoint values give valid interval bounds.
At small arguments, put `eta=z/(1+z)`. Expanding a positive geometric
series under the integral gives, for `k=0,1,2`,

\[
(-1)^kH^{(k)}(z)
=\frac{(k+2)!}{(1+z)^{k+1}}
\sum_{n=0}^{\infty}
\frac{\eta^n}{(n+k+1)(n+k+2)(n+k+3)}.
\tag{18}
\]

After terms `0,...,M`, an upper tail bound is the first omitted
coefficient times `eta^(M+1)/(1-eta)`. This bounds the actual
derivatives, rather than differentiating a numerical approximation and
declaring it exact. At `z=0` the values are `1/3,-1/4,2/5`.
Away from zero the equivalent formulas

\[
H=N/z^3,\quad
H'=1/[z(1+z)]-3N/z^4,
\]
\[
H''=-(4+5z)/[z^2(1+z)^2]+12N/z^5,
\quad N=\log(1+z)-z+z^2/2
\tag{19}
\]

can be evaluated with directed interval logarithms. The arithmetic
engine and complete caller require their own source audit and complete
replay; these analytic formulas do not replace those checks.

## Verification and boundary

The exact checker
[`mixed_nonshort_completion_blowup_certificate.py`](../explorations/mixed_nonshort_completion_blowup_certificate.py)
verifies the common denominator, quadratic cancellation, leading
factor, remainder coefficients, negative `v` coefficient, positive
root denominator and zero-duration Casimir identity. The coefficient
cancellation by `T^3` and the actual committed C++ expressions are
independently verified by
[`mixed_nonshort_coefficients.py`](../explorations/mixed_nonshort_coefficients.py).
It reads all 53 ordered intermediates, all seven coefficient outputs and
the returned Horner polynomial, and checks them against the exact
numerator without modifying the header. The remaining reconstruction
and directed caller have the accompanying independent source audit.

The independently audited
[uniform small-parameter exclusion](MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md)
proves `Phi>0` whenever `0<=epsilon<=1/32` on the retained actual
geometry in every max chart. Positive-duration actual data would require
`Phi<=0`, so this removes the common corner. The complementary directed
cover may therefore start at `epsilon=1/32` in each of the three charts.

The complementary finite cover is not yet complete for either next-switch
branch. A node limit, a sampled sign, a partially exhausted stack, or a
zero unknown count with pending boxes is not a proof of exclusion.
