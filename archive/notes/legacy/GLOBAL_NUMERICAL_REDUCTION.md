# A specific uniform switch bound from the complete-period budget

Date: 2026-11-07. Hand proof with rational clearance and an explicit
integer. No Lean, Lake, typechecking, CI, numerical trajectory,
optimization, or symbolic sign calculation.

## Stronger subsequent bound; this proof is preserved

[SINGULAR_COST_BUDGET](SINGULAR_COST_BUDGET.md) gives a direct homogeneous
costate estimate and sharper algebraic covector bounds on the common
cyclically invariant minimizer state domain. It proves D>10^-11 and
N<10^56. [MEASURABLE_EDGE_PMP_BOUND](MEASURABLE_EDGE_PMP_BOUND.md)
now supplies E4 directly. The independent cost--Casimir and Gronwall
argument below, with its exact stated hypotheses and original constants,
is retained unchanged as a valid alternative proof.

## Theorem and exact scope

Let a free-time Pontryagin trajectory satisfy the actual matrix endpoint
conditions

\[
g'=gX,\qquad g(0)=I,\qquad
g(T)=R=\exp(\pi J/3),\qquad T>0,
\tag{1}
\]

and the positive determinant-one strict-star state conditions. Retain
the reduced adjoint equations, \(\operatorname{tr}(WX)=0\), and zero
maximized Hamiltonian. The complete minimizing problem has the additional
twisted state and costate endpoints; weakening to (1) in the estimate
below does not change the conditions imposed on actual minimizers.

Use the projective normalization and Frobenius norm

\[
\lambda\le0,\qquad
\mathcal P=(\lambda,\Lambda_1,W),\qquad
\|\mathcal P(0)\|^2
 =\lambda^2+\|\Lambda_1(0)\|_F^2+\|W(0)\|_F^2=1.
\tag{2}
\]

Assume the established common state, time, and complete-period cost bounds

\[
\|X(t)\|_F\le9,\quad
-\operatorname{tr}(Z_iX(t))\ge\frac{2}{15\sqrt3},\quad
T\le\frac\pi3,
\tag{3}
\]

\[
C=-\frac32\int_0^T\operatorname{tr}(JX)\,dt
\le A_{\rm oct},\qquad
A_{\rm oct}=
2\sqrt3\,\frac{8-4\sqrt2-\log2}{2\sqrt2-1}.
\tag{4}
\]

Then **every normalized lift satisfying these hypotheses** has the
following numerical singular clearance throughout its period:

\[
\boxed{
D(t):=\left(\|X(t)-J\|_F^2+
 \|\Lambda_1(t)-\tfrac32\lambda J\|_F^2+
 \|W(t)\|_F^2\right)^{1/2}
>\varepsilon_0:=10^{-1906}.}
\tag{5}
\]

For the switch count, assume also:

> **(E4)** On each subinterval where one fixed control coordinate
> vanishes almost everywhere, the control agrees almost everywhere with
> at most four positive constant vertex pieces.

The control then has a vertex representation with

\[
\boxed{N<10^{5741}.}
\tag{6}
\]

In particular, (6) applies to actual global minimizers by the retained
compact-state, geometric/control, PMP, and edge-optimality inputs. It
does not assume a finite representation before proving the bound, and
does not use Hales--Vajjha Theorem 16.3.1 or its audited numerical
dependencies. Abnormal lifts are included.

This gives a stated finite ceiling, rather than an unspecified integer.
Its size makes it unsuitable for an immediate exhaustive calculation.
It supplies neither the cost comparison for all words under that
ceiling nor the equality and affine-uniqueness classification.

## 1. Explicit constants already established

Use the constants from the three-line quantitative theorem and
[GLOBAL_SMALL_MULTIPLIER_BOUND](GLOBAL_SMALL_MULTIPLIER_BOUND.md):

\[
\begin{aligned}
K_P&=\frac{5\sqrt{30}}2,&
L_0&=2K_P+18K_P^2,\\
B_P&=27\sqrt2+36+L_0,&
M&=\exp(B_P\pi/3),\qquad m=M^{-1}.
\end{aligned}
\tag{7}
\]

The following estimates were proved there by hand:

\[
0<m\le1,\qquad
m\le\|\mathcal P(t)\|\le M,\qquad
m>10^{-1903},\qquad
c>10^{-27}m^2.
\tag{8}
\]

Here \(c\) is the explicit time coefficient of
[QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md).
For a supplied clearance \(\varepsilon\), that theorem uses intervals
of length \(c\min(\varepsilon,1,m)\), with at most 28 pieces on each.
The coefficient estimates (8) are valid for all normalized lifts in
(3); they have no small-multiplier hypothesis.

## 2. A rational gap between the octagon and the circle

We will use

\[
\boxed{A_{\rm oct}<\frac{313}{100},\qquad
       \pi>\frac{157}{50}.}
\tag{9}
\]

Here are complete elementary bounds for both statements. First,

\[
\sqrt2>\frac{140}{99},\qquad
\sqrt3<\frac{97}{56},
\]

because \(140^2=19600<19602=2\cdot99^2\) and
\(97^2=9409>9408=3\cdot56^2\). Integrating the positive geometric
series for \(1/(1-t^2)\), or just its first three terms and its
positive remainder, gives

\[
\log2
 =2\int_0^{1/3}\frac{dt}{1-t^2}
 >2\left(\frac13+\frac1{81}+\frac1{1215}\right)
 =\frac{842}{1215}>\frac{693}{1000}.
\tag{10}
\]

The last comparison is \(842000>841995\).
The numerator in (4) is positive: \(\sqrt2<3/2\) and
\(\log2<1\) make it greater than one. Thus its factors can be
bounded in the indicated directions, yielding

\[
\begin{aligned}
A_{\rm oct}
&<\frac{97}{28}
  \frac{8-560/99-693/1000}{280/99-1}\\
&=\frac{15849121}{5068000}
 <\frac{313}{100}.
\end{aligned}
\tag{11}
\]

For the last inequality,
\(15849121<15862840=5068000\cdot313/100\).

For the lower bound on \(\pi\), let
\(\alpha=\arctan(1/5)\), \(\beta=\arctan(1/239)\).
The tangent addition formula gives

\[
\tan(2\alpha)=\frac5{12},\qquad
\tan(4\alpha)=\frac{120}{119},\qquad
\tan(4\alpha-\beta)=1.
\]

Moreover \(0<4\alpha-\beta<4/5<\pi/2\). One elementary check
of the final range is \(\pi/2=2\arctan1>1\), using
\(1/(1+t^2)>1/2\) on \([0,1)\). Hence
\(4\alpha-\beta=\pi/4\), proving Machin's identity in the form
\(\pi=16\alpha-4\beta\).

For \(x>0\), integrating
\(1-t^2<1/(1+t^2)<1\) gives
\(x-x^3/3<\arctan x<x\). Therefore

\[
\pi>
16\left(\frac15-\frac1{375}\right)-\frac4{239}
=\frac{281476}{89625}>
\frac{157}{50}.
\tag{12}
\]

The last cross multiplication is
\(14073800>14071125\). This completes (9) without decimal
approximations or numerical quadrature.

## 3. A fixed normal clearance, treating every frame-costate component

For this section alone normalize a normal lift to
\(\overline\lambda=-1\). No unit initial-covector norm is assumed
for the barred quantities. Write

\[
\overline A=\overline\Lambda_1+\frac32J,\qquad
\overline\Delta=\det\overline\Lambda_1-\frac94,
\]
\[
\overline D^2
 =\|X-J\|_F^2+\|\overline A\|_F^2+\|\overline W\|_F^2.
\tag{13}
\]

We prove

\[
\boxed{\overline D(t)>\frac1{120}\quad\text{for every }t.}
\tag{14}
\]

The adjoint equation conserves the determinant and gives
\(\overline\Lambda_1(t)=g(t)^{-1}
\overline\Lambda_1(0)g(t)\). We split into exhaustive cases.

### 3.1 Negative elliptic component

Suppose \(\det\overline\Lambda_1=\kappa^2>0\) and
\((\overline\Lambda_1(0))_{21}<0\). The full-period polar argument
in [GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md) proves

\[
C\ge\frac{4\pi\kappa}{2\kappa+3},\qquad
\kappa\le\frac{3A_{\rm oct}}{2(2\pi-A_{\rm oct})}.
\tag{15}
\]

The pointwise comparison in that argument uses an actual interior
simplex control and zero maximized Hamiltonian. The angle increment
uses the full matrix endpoint \(g(T)=R\). Thus (15) is available
for arbitrary measurable PMP controls, not just known finite words.

From (9), with positive denominators,

\[
\kappa<
\frac{3(313/100)}{2(2(157/50)-313/100)}
=\frac{313}{210}.
\]

Consequently

\[
\overline\Delta
< -\left(\frac94-\frac{313^2}{210^2}\right)
=-\frac{314}{11025}< -\frac1{40}.
\tag{16}
\]

The last comparison is \(12560>11025\).

### 3.2 Nonpositive determinant

If \(\det\overline\Lambda_1\le0\), including all parabolic,
hyperbolic, and zero matrices, then simply

\[
\overline\Delta\le-\frac94<-\frac1{40}.
\tag{17}
\]

The cases (16)--(17) both imply (14) by the same elementary norm
estimate. Expanding the determinant of
\(\overline\Lambda_1=\overline A-(3/2)J\) gives

\[
\overline\Delta
 =\frac32\operatorname{tr}(J\overline A)
  -\frac12\operatorname{tr}(\overline A^2),
\quad
|\overline\Delta|
\le\frac94\|\overline A\|_F
  +\frac12\|\overline A\|_F^2.
\tag{18}
\]

This estimate uses \(|\overline\lambda|=1\), **not** a unit
initial norm for the rescaled covector. If
\(\|\overline A\|_F\le1/120=(1/40)/3\), the right side of
(18) is at most
\((11/4)\|\overline A\|_F\le11/480<1/40\), contradicting
(16) or (17). Hence \(\|\overline A\|_F>1/120\).

### 3.3 Positive elliptic component

The only remaining case is
\(\det\overline\Lambda_1>0\) with
\((\overline\Lambda_1(0))_{21}>0\). Indeed, for a traceless
matrix \(\left(\begin{smallmatrix}a&b\\c&-a\end{smallmatrix}\right)\)
of positive determinant, \(bc=-a^2-\det\overline\Lambda_1<0\),
so \(c\ne0\).

Conjugation by \(\mathrm{SL}_2(\mathbb R)\) preserves this positive
elliptic component. This follows, for example, by writing
\(\overline\Lambda_1=\kappa hJh^{-1}\): the lower-left entry of
\(hJh^{-1}\) is the sum of the squares of the bottom row of \(h\),
and is positive. Thus at every time \(c>0\), \(b<0\), and

\[
\operatorname{tr}(J\overline\Lambda_1)=b-c<0,
\qquad
\operatorname{tr}(J\overline A)
 =\operatorname{tr}(J\overline\Lambda_1)-3<-3.
\]

Cauchy--Schwarz and \(\|J\|_F=\sqrt2\) now imply

\[
\|\overline A\|_F>\frac3{\sqrt2}>\frac1{120}.
\tag{19}
\]

This proves (14) in the final component. All normal frame costates
have been covered, including determinant zero and either elliptic sign.

## 4. Return to the specified projective normalization

Put \(\mu=|\lambda|\). If
\(\mu\le m/\sqrt{22}\), the direct norm estimate in
`GLOBAL_SMALL_MULTIPLIER_BOUND.md` gives

\[
D(t)\ge m-\sqrt{\frac{11}{2}}\,\mu\ge\frac m2
>10^{-1906}.
\tag{20}
\]

This case includes every abnormal lift.

Otherwise \(\mu>m/\sqrt{22}>0\), so divide the costates and the
cost multiplier by \(\mu\). Then \(\overline\lambda=-1\),
\(\overline A=A/\mu\), and \(\overline W=W/\mu\).
The actual state, control, cost, maximizing support, and endpoint
conditions are unchanged. Also \(\mu\le1\) by (2). Therefore

\[
\begin{aligned}
D^2
 &=\|X-J\|_F^2
   +\mu^2(\|\overline A\|_F^2+\|\overline W\|_F^2)\\
 &\ge\mu^2\overline D^2.
\end{aligned}
\]

Using (14), \(\sqrt{22}<5\), and (8),

\[
D(t)\ge\mu\overline D(t)
>\frac{m}{120\sqrt{22}}
>\frac m{600}
>10^{-1906}.
\tag{21}
\]

The last inequality follows from \(m>10^{-1903}\) and \(600<1000\).
Together (20)--(21) prove the universal numerical clearance (5).
There is no choice of a favorable lift: the argument applies to
each lift normalized by (2).

## 5. One stated integer for all minimizing periods

The rational \(\varepsilon_0=10^{-1906}\) is smaller than both
one and \(m>10^{-1903}\). Thus the quantitative counting theorem
uses \(e=\min(\varepsilon_0,1,m)=\varepsilon_0\). Its counting
interval has length

\[
h=c\varepsilon_0
>10^{-27}m^2\,10^{-1906}
>10^{-5739}.
\tag{22}
\]

Since \(T_{\max}=\pi/3<2\),
\(T_{\max}/h<2\cdot10^{5739}\). The right side is an integer,
so with 28 pieces per interval,

\[
N\le28\left\lceil\frac{T_{\max}}h\right\rceil
\le56\cdot10^{5739}<10^{5741}.
\tag{23}
\]

This is a bound for a vertex representation obtained from the counting
argument itself. Merging adjacent equal controls, including the twisted
cyclic reduction, cannot increase it. The proof permits arbitrarily
short individual pieces and establishes no uniform dwell time.

## 6. Inputs and remaining mathematical work

The proof uses the following established inputs, with separate roles:

- [GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md): the pointwise stationary
  Hamiltonian comparison and the full-period polar-angle inequality.
- [GLOBAL_SMALL_MULTIPLIER_BOUND](GLOBAL_SMALL_MULTIPLIER_BOUND.md):
  explicit Gronwall bounds, numerical coefficient estimates, and
  homogeneous normalization.
- [QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md):
  the measurable-control counting theorem with three guard lines.
- [EDGE_SWITCH_BOUND](EDGE_SWITCH_BOUND.md): (E4) for actual global
  minimizers, using its stated local edge-theorem inputs.
- [GLOBAL_MINIMIZER_COMPACTNESS](GLOBAL_MINIMIZER_COMPACTNESS.md) and
  [CONTROL_BOUNDS](CONTROL_BOUNDS.md): the common state domain and actual
  minimizing cost budget. Their qualitative singular-avoidance argument
  is not used here.

In particular, the source-dependent route
“finite bang-bang theorem, then singular avoidance, then compactness
clearance” is unnecessary for (5)--(6). The two numerical source
obligations recorded in
[FINITE_BANG_BANG_SOURCE_AUDIT](FINITE_BANG_BANG_SOURCE_AUDIT.md) are
neither used nor certified by this different argument.

The integer (6) closes the numerical boundedness step under the stated
geometric and local optimal-control inputs. It is not a practical case
catalogue and does not prove the unrestricted octagon comparison.
That comparison must still treat all admissible complete competitors
within a justified fixed bound, or replace the enormous ceiling by a
stronger global inequality or reduction. Boundary degenerations,
free initial state, exact frame/state closure, and equality cases
remain part of that task. Affine uniqueness and Lean kernel validation
remain separate obligations.

## Internal review and validation boundary

Independent internal reviews checked the fully assembled note, including
the rational cost and arctangent bounds, all three normal orbit cases,
homogeneous normalization, the abnormal/small-multiplier split, every power
and integer ceiling, and the absence of Theorem 16.3.1 in the E4 dependency.
The parent review also reopened the pinned physical-time Hamiltonian and
adjoint definitions and rederived the cost–Casimir identities. No material
issue remained in these hand reviews. This is not external peer review or
Lean kernel validation. No Lean, Lake, typechecking, or CI was run.
