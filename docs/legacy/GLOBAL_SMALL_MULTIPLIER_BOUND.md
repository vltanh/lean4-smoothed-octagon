# A numerical switch bound for small projective cost multipliers

Date: 2026-11-07. Hand proof with explicit constants; no Lean, Lake,
typechecking, or CI.

**Completed global follow-up.**
[GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md) and
[GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md) now supply
the complementary normal-sector argument. With the complete-period
octagon cost budget and the stated state, PMP, and edge-optimality
inputs, they prove \(D>10^{-1906}\) for every normalized minimizing
lift and \(N<10^{5741}\) for every minimizing period, without
Hales--Vajjha Theorem 16.3.1. The stronger count below remains a
separate theorem for the small-multiplier sector; its proof is unchanged.

## Theorem and exact scope

Use the reduced physical-time Pontryagin equations, state bounds, and
normalization of
[QUANTITATIVE_REGULAR_SWITCH_BOUND.md](QUANTITATIVE_REGULAR_SWITCH_BOUND.md):

\[
\|X(t)\|_F\le9,\qquad
-\operatorname{tr}(Z_iX(t))\ge\frac{2}{15\sqrt3},\qquad
0<T\le\frac\pi3,
\tag{1}
\]
\[
\mathcal P=(\lambda,\Lambda_1,W),\qquad
\lambda\le0,\qquad
\|\mathcal P(0)\|=1,\qquad
W=\Lambda_R,\qquad
A=\Lambda_1-\frac32\lambda J.
\tag{2}
\]

The norm in (2) is
\(\sqrt{\lambda^2+\|\Lambda_1\|_F^2+\|W\|_F^2}\).
Assume the following optimality property throughout the interval:

> **(E4)** Every subinterval on which one fixed control coordinate
> vanishes almost everywhere agrees almost everywhere with at most four
> positive constant vertex pieces.

Define the explicit constants

\[
\begin{aligned}
K_P&=\frac{5\sqrt{30}}2,&
L_0&=2K_P+18K_P^2,\\
B_P&=27\sqrt2+36+L_0,&
M&=\exp(B_P\pi/3),\qquad m=M^{-1}.
\end{aligned}
\tag{3}
\]

Then every such trajectory whose projectively normalized cost
multiplier satisfies

\[
\boxed{\ |\lambda|\le\frac{m}{\sqrt{22}}\ }
\tag{4}
\]

agrees almost everywhere with fewer than

\[
\boxed{10^{5740}}
\tag{5}
\]

positive vertex pieces. In particular, (5) holds for every **abnormal**
lift satisfying the stated hypotheses. The simpler rational condition
\(|\lambda|\le10^{-1904}\) implies (4).

This is a numerical bound for a specified multiplier sector, not a
bound for every global minimizer. The proof permits arbitrary measurable
controls and does not assume that the trajectory already has a finite
vertex representation. It uses (E4), the explicit state bounds, the
Pontryagin equations, and the supplied-clearance theorem. It does not use
Hales--Vajjha Theorem 16.3.1 or the source steps audited in
[FINITE_BANG_BANG_SOURCE_AUDIT.md](FINITE_BANG_BANG_SOURCE_AUDIT.md).

For the remaining sector, Section 5 gives a safe normalization to
\(\lambda=-1\), with an explicit bound \(10^{3807}\) on the entire
rescaled costate. This scoped lemma does not prove its clearance;
the complete-period argument in
[GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md) now
provides it.

## 1. Projective size gives a singular clearance

Define the exact singular-distance quantity used by the quantitative
theorem:

\[
D(t)=\left(\|X(t)-J\|_F^2+\|A(t)\|_F^2+\|W(t)\|_F^2\right)^{1/2}.
\tag{6}
\]

The extended covector decomposes as

\[
\mathcal P
 =(0,A,W)+\lambda\left(1,\frac32J,0\right).
\]

Since \(\|J\|_F^2=2\), the triangle inequality gives

\[
\begin{aligned}
\|\mathcal P\|
&\le\sqrt{\|A\|_F^2+\|W\|_F^2}
  +\sqrt{1+\frac94\|J\|_F^2}\,|\lambda|\\
&\le D+\sqrt{\frac{11}{2}}\,|\lambda|.
\end{aligned}
\]

The forward and backward Gronwall bounds from the quantitative theorem
are \(m\le\|\mathcal P(t)\|\le M\). Consequently

\[
\boxed{D(t)\ge m-\sqrt{\frac{11}{2}}\,|\lambda|.}
\tag{7}
\]

For an abnormal lift this already gives \(D(t)\ge m\) everywhere.
Under (4), it gives

\[
\boxed{D(t)\ge\frac m2\qquad(0\le t\le T).}
\tag{8}
\]

No qualitative separation theorem or compactness minimum is used in
(7)--(8). The zero extended covector at \(X=J\) belongs to the displayed
singular set, but the normalized covector cannot approach that zero
with norm less than the explicit Gronwall lower bound.

## 2. Elementary numerical bounds for \(m\) and \(M\)

Every estimate in this section is an ordinary hand inequality. First,

\[
K_P<14,\qquad L_P=K_P^2<196,\qquad
L_0<28+18\cdot196=3556.
\tag{9}
\]

Using \(\sqrt2<3/2\) gives

\[
B_P<27\cdot\frac32+36+3556<3633.
\]

Also \(\pi/3<22/21\), so

\[
B_P\frac\pi3<3633\frac{22}{21}=3806.
\tag{10}
\]

For completeness, \(e<3\) follows from
\[
e=1+1+\sum_{n\ge2}\frac1{n!}
 <2+\sum_{n\ge2}2^{-(n-1)}=3.
\]
The inequality is strict because \(n!>2^{n-1}\) for \(n\ge3\).
Thus \(e^2<10\), and (10) yields

\[
\boxed{M<10^{1903},\qquad m>10^{-1903}.}
\tag{11}
\]

The elementary bound \(\pi<22/7\) can be checked without a numerical
approximation using
\[
0<\int_0^1\frac{x^4(1-x)^4}{1+x^2}\,dx=\frac{22}{7}-\pi.
\]

Since \(\sqrt{22}<5\), equation (11) also shows

\[
\frac{m}{\sqrt{22}}>
\frac{10^{-1903}}5>10^{-1904}.
\tag{12}
\]

This proves the rational sufficient condition stated after (5).

## 3. A lower bound for the explicit time coefficient

This section evaluates the **three-line** version of the quantitative
theorem. Its derivative margin differs from that of the earlier large
angular mesh; no old time coefficient is reused.

For the state inputs (1), its exact comparison and derivative margins
are

\[
\omega=\frac2{249\sqrt{15}}>10^{-3},
\qquad
\sigma=\frac1{56025\pi\sqrt2}>10^{-6}.
\tag{13}
\]

The first lower bound follows from \(\sqrt{15}<4\). For the second,
\[
56025\pi\sqrt2
 <56025\frac{22}{7}\frac32
 =\frac{1848825}{7}<10^6.
\]

Retain the names of the coefficient bounds in equations (18) and (22)
of QUANTITATIVE_REGULAR_SWITCH_BOUND. Since
\[
K_\lambda=K_W=M,\qquad
K_A=\left(1+\frac32\sqrt2\right)M<4M,
\]
direct substitution into their displayed formulas gives:

| Constant | Strict upper bound |
|---|---:|
| \(V_X=2K_PK_X\) | \(252\) |
| \(V_A=2K_AK_X+3\sqrt2K_\lambda K_X\) | \(120M\) |
| \(V_W=L_0K_W+2K_AK_X\) | \(3628M\) |
| \(K_b=2K_AK_X\) | \(72M\) |
| \(V_b=2K_XV_A+2K_AV_X\) | \(4176M\) |
| \(K_C=6\sqrt2K_\lambda K_X^2\) | \(729M\) |
| \(V_C=12\sqrt2K_\lambda K_XV_X\) | \(40824M\) |
| \(D_0=4K_X^2+4K_PK_X+2L_0K_X\) | \(64836<10^5\) |

These estimates use \(K_X=9\), (9), and \(\sqrt2<3/2\).
For example, the bounds for \(V_b\) and \(D_0\) are
\[
18\cdot120M+8\cdot252M=4176M,\qquad
324+504+18\cdot3556=64836.
\]

The four error constants therefore satisfy

\[
\begin{aligned}
F_0&<56\cdot3556+392\cdot252
       =297920<10^6,\\
G_0&<(28\cdot3628+392\cdot252)M
       =200368M<10^6M,\\
B_1&<(7112\cdot72+2\cdot4176)M
       =520416M<10^6M,\\
C_1&<(7112\cdot729+2\cdot40824
                    +2\cdot64836\cdot120)M\\
   &=20826936M<10^8M.
\end{aligned}
\tag{14}
\]

Write \(s_0=1+\tfrac32\sqrt2<4\). The threshold constants of that
theorem are

\[
c_C=\frac{3m}{2s_0}>\frac m4,\qquad
a=\min\left(\frac18,\frac{\sigma c_C}{8D_0}\right),\qquad
r=\frac{a}{1+K_XK_P},\qquad c_b=\frac a{K_X}.
\tag{15}
\]

Equations (13)--(15), \(m\le1\), and \(1+K_XK_P<127<10^3\)
give the explicit lower bounds

\[
\boxed{
a>10^{-13}m,\qquad
r>10^{-16}m,\qquad
c_b>10^{-14}m.}
\tag{16}
\]

For the first one,
\[
\frac{\sigma c_C}{8D_0}>
\frac{10^{-6}(m/4)}{8\cdot10^5}
 =\frac{m}{32\cdot10^{11}}>10^{-13}m,
\]
and \(1/8>10^{-13}m\). The other two follow by division.

The time coefficient is exactly

\[
\begin{aligned}
h_0&=\min\left(\frac1{2L_0},\frac{\omega}{4F_0}\right),\\
c&=\min\left(h_0,\frac{\omega r}{2G_0},
                    \frac{\sigma c_b}{2B_1},
                    \frac{\sigma c_C}{4C_1}\right).
\end{aligned}
\tag{17}
\]

The same hand estimates give

\[
\begin{aligned}
h_0&>10^{-10},\\
\frac{\omega r}{2G_0}
 &>\frac{m}{2\cdot10^{25}M}>10^{-26}m^2,\\
\frac{\sigma c_b}{2B_1}
 &>\frac{m}{2\cdot10^{26}M}>10^{-27}m^2,\\
\frac{\sigma c_C}{4C_1}
 &>\frac{m}{16\cdot10^{14}M}>10^{-16}m^2.
\end{aligned}
\tag{18}
\]

Here \(m=M^{-1}\) is an exact identity. Since \(m\le1\), every
entry of the minimum in (17) exceeds \(10^{-27}m^2\). Hence

\[
\boxed{c>10^{-27}m^2.}
\tag{19}
\]

No minimization over an unspecified compact set remains in (19).

## 4. The numerical piece count

Under (4), use the clearance \(\varepsilon=m/2\) from (8).
Since \(m\le1\),
\[
\min(\varepsilon,1,m)=\frac m2.
\]
The common time interval in the quantitative theorem can therefore be
taken to have length \(h=cm/2\). By (11) and (19),

\[
h>\frac12\,10^{-27}m^3
  >\frac12\,10^{-5736}
  >10^{-5737}.
\tag{20}
\]

That theorem uses at most 28 pieces on each such interval. Since
\(T_{\max}<2\),

\[
\frac{T_{\max}}h<2\cdot10^{5737}.
\]

The quantity on the right is an integer, so

\[
N\le28\left\lceil\frac{T_{\max}}h\right\rceil
 \le56\cdot10^{5737}<10^{5739}<10^{5740}.
\tag{21}
\]

This proves (5). The exponent in the statement is deliberately rounded
up. The argument proves a common bound on the number of pieces, rather
than a positive lower bound on individual durations.

The theorem applies to a trajectory if it admits **one** normalized
Pontryagin lift satisfying (4). It does not require every lift of that
trajectory to have a small cost multiplier.

## 5. Explicit normal rescaling and its completed global application

For a normalized lift outside (4), put
\[
\mu=|\lambda|>\frac{m}{\sqrt{22}}>10^{-1904}.
\]
The initial normalization implies \(\mu\le1\). Positive rescaling by
\(1/\mu\) is consequently legitimate and gives

\[
\overline\lambda=-1,\qquad
\overline\Lambda_1=\frac{\Lambda_1}{\mu},\qquad
\overline W=\frac W\mu,\qquad
\overline A=\frac A\mu.
\tag{22}
\]

The state, control, time, cost, and maximizing support are unchanged.
The exact bounds are

\[
1\le\|\overline{\mathcal P}(0)\|
  =\frac1\mu<\frac{\sqrt{22}}m<10^{1904},
\]
\[
\boxed{\|\overline{\mathcal P}(t)\|
 \le\frac M\mu
 <\frac{\sqrt{22}M}{m}
 =\sqrt{22}M^2<10^{3807}\quad(0\le t\le T).}
\tag{23}
\]

Thus normalization to cost multiplier \(-1\) is used only after an
explicit lower bound on its projective size has been proved.

There is also an explicit conversion for a normal-clearance estimate.
Define
\[
\overline D^2
 =\|X-J\|_F^2+\|\overline A\|_F^2+\|\overline W\|_F^2.
\]
Because \(0<\mu\le1\),

\[
\mu\,\overline D\le D\le\overline D.
\tag{24}
\]

In particular, a supplied bound \(\overline D\ge\delta>0\) for
the complementary normal minimizing lifts implies

\[
D\ge\frac{m}{\sqrt{22}}\,\delta
  >10^{-1904}\delta.
\tag{25}
\]

Such a bound is not proved by this scoped lemma. It is now provided by
[GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md), which
uses the actual complete-period frame endpoint and octagon cost
budget to prove \(\overline D>1/120\), then applies (24)--(25).
The full minimizing problem continues to retain its free initial
state and twisted state and costate endpoints. Equations (22)--(25)
give the explicit normalization and clearance conversion used in that
follow-up.

In these rescaled **reduced** phase coordinates the zero of
\(\overline D\) is the single point
\((X,\overline\Lambda_1,\overline W)=(J,-3J/2,0)\).
This statement omits the group frame \(g\); it does not turn the
bounded-domain description into a positive distance from that point.

## Dependencies and validation boundary

- [QUANTITATIVE_REGULAR_SWITCH_BOUND.md](QUANTITATIVE_REGULAR_SWITCH_BOUND.md)
  supplies the equations, explicit coefficient bounds, and the
  three-guard count from a supplied clearance.
- [EDGE_SWITCH_BOUND.md](EDGE_SWITCH_BOUND.md) supplies (E4) when this
  result is applied to actual global minimizers.
- The explicit state domain and the bound \(T\le\pi/3\) come from
  the elementary estimates and source inputs recorded in
  [GLOBAL_MINIMIZER_COMPACTNESS.md](GLOBAL_MINIMIZER_COMPACTNESS.md).
  The singular-avoidance portion of that note is not used.

The new clearance (7), numerical estimates (9)--(21), and normal
rescaling (22)--(25) are hand arguments. They require no numerical
trajectory, symbolic sign oracle, finite-bang-bang source theorem,
or assumed dwell time.

The result in this note remains a numerical subcase of the global
clearance problem. The common bound for all minimizing periods is
proved in [GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md)
using the complementary complete-period argument. Neither result
proves the cost comparison for all words under that ceiling or affine
uniqueness. The finite comparison remains separate from these
clearance and counting proofs; no increasing-length enumeration is
part of this note.

Two independent hand reviews checked the norm decomposition, all integer
coefficient and exponent bounds, the minimum defining \(c\), the ceiling
in the final count, the one-lift quantifier, and the normal-rescaling
inequalities. Neither found a material gap. These are internal mathematical
reviews, not external peer review or Lean kernel validation.
