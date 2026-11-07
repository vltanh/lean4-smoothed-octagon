# Reverse-period Casimir equations and the remaining cyclic obstruction

Date: 2026-11-07. Hand calculation with an independent internal
recheck of the signs, local triple, regular multiplier and strict
Casimir comparison. No Lean, Lake, typechecking, or CI.

## Scope

The pure reverse case would be excluded from competitive complete periods
if its normal PMP equations forced the negative elliptic component with
`kappa>=3/2`. The complete-period inequality in
[GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md) would then give `C>=pi>A_oct`.
The weaker lower bound
`kappa>3 A_oct/(4 pi-2 A_oct)` would also suffice.

This note does **not** prove either bound for arbitrary reverse periods.
It records the exact stationary trace equations, proves the stronger
bound for the equal-margin reverse family, and shows concretely why an
individual trace equation cannot supply the missing lower bound. The
equal-margin family is already excluded by
[REGULAR_FAMILY_COMPARISON](REGULAR_FAMILY_COMPARISON.md), so no additional
global case is closed here.

## 1. Exact equations for an arbitrary reverse period

Use the active margins and matrices of
[GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR](GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR.md).
All indices are cyclic. Put

\[
s_{i-1}=a_{i-1}+a_i,\qquad s_i=a_i+a_{i+1},\qquad
K_i=a_i^2+4,\qquad r_i=s_{i-1}s_i/K_i<1.
\]

Every `a_i` is positive, and the actual factors are `q_i=1/r_i>1`.
Write `C_i=mathcal J_{a_i}>0` for the derivative in that note. It is
not the cost of the individual arc. In explicit form,

\[
C_i=\frac14\left[
a_{i-1}+a_i+a_{i+1}
-a_i^2\left(\frac1{s_{i-1}}+\frac1{s_i}\right)
+\frac{a_i^3}{K_i}-a_i\log r_i\right].
\tag{1}
\]

For a normal lift with the actual twisted endpoints and free-state
transversality, the reverse-period first variation is

\[
-C_i=\operatorname{tr}(U V_i^-),\qquad
\det U=\frac{\det\Lambda_1}{12},\qquad
\det V_i^-=\frac{4(s_{i-1}s_i-a_i^2)}{K_i^2}>0.
\tag{2}
\]

Here every `V_i^-` is positive elliptic in the triangular coordinates.
The physical positive elliptic cone, its positive parabolic boundary,
and zero have already been excluded by the cited sector theorem. That
theorem leaves physical negative elliptic, negative parabolic, and
hyperbolic primary costates. The following argument concerns the first
of these sectors only; it does not exclude the other two.

Assume `Lambda_1` is physical negative elliptic and put
`kappa=sqrt(det Lambda_1)>0`. Then `U` is triangular positive elliptic.
For any two positive elliptic matrices `U,V`, the trace-pairing
inequality is

\[
-\operatorname{tr}(UV)\ge2\sqrt{\det U\det V}.
\]

Indeed conjugate `U` to `tJ`, `t>0`. If
`V=[[u,b],[c,-u]]`, its positive elliptic orientation gives `c>0,b<0`,
and `(c-b)^2-4 det V=(c+b)^2+4u^2>=0`.
Applying this to (2) gives the **upper** bound

\[
\boxed{\quad
\kappa\le\frac{\sqrt3\,C_i}{\sqrt{\det V_i^-}}
\quad\text{for every }i.\quad}
\tag{3}
\]

Equivalently, there are numbers `d_i>=0` such that
`C_i=2(kappa/sqrt(12))sqrt(det V_i^-) cosh(d_i)`.
Discarding these relative-position factors loses precisely the
information that would be needed for a Casimir lower bound.

## 2. The upper bound can itself be subcritical

Consider the strict-star local margin data

\[
a_i=\sqrt2,\qquad a_{i-1}=a_{i+1}=1/\sqrt2.
\]

They give `q_i=4/3`. The actual initial ordered active, growing, and
decreasing margins are `(sqrt(2),1/sqrt(2),sqrt(2))`; the terminal
ones are `(sqrt(2),sqrt(2),1/sqrt(2))`. Both triples are positive and
have pairwise-product sum four, so this is a genuine admissible
positive vertex arc. Substitution in (1)--(2) gives

\[
C_i=\frac{\sqrt2}{4}\left(1+\log\frac43\right),\qquad
\det V_i^-=\frac5{18}.
\]

Thus the right side of (3) is

\[
\frac{3\sqrt3}{2\sqrt5}\left(1+\log\frac43\right)<\frac32.
\tag{4}
\]

For an exact sign check, the alternating logarithm bound gives
`log(4/3)<1/3-1/18+1/81=47/162`, and
`3(209/162)^2<5` is the integer inequality `131043<131220`.

No full-period frame closure or PMP lift is asserted for these local
data. In particular, (4) is not a counterexample to the proposed
reverse-period lower bound. It shows that such a lower bound must use
cyclic compatibility, rather than applying the trace inequality to
one column and reversing its direction.

## 3. Equal margins give a strict supercritical Casimir

Let all margins equal `a`, and put `r=1/q in (0,1)`. Then

\[
a^2=\frac{4r}{4-r},\qquad
B=\begin{pmatrix}0&r^{-1}\\-r&r\end{pmatrix},\qquad
A=8+r-4\log r.
\]

For an equal-factor closed reverse member, the unique normal
stationary frame multiplier is

\[
U=-\frac{A}{2(4-r)^2}\left(B-\frac r2 I\right).
\tag{5}
\]

Here is a direct check, including uniqueness. The gradient in (1) is
`C_i=aA/16`. For a margin variation `v`,

\[
\delta\log q_i=-\frac{v_{i-1}+(2-r)v_i+v_{i+1}}{2a}.
\]

The matrix (5) commutes with `B`, and
`tr(U E)=rA/[2(4-r)^2]`, where `E=diag(1,-1)`.
Summing these factor derivatives therefore gives exactly
`tr(U delta M M^{-1})=-sum_i C_i v_i`.
The adjoint orbit of `E` under `B` has a nonzero fixed component and
two independent rotation components. On the corresponding three
Fourier modes, the margin-to-factor operator has nonzero numerators
`4-r` and `r(r-1)`. Thus the frame derivative has rank three, so (5)
is the multiplier of any normal PMP lift of this trajectory.

Since `(B-rI/2)^2=-(1-r^2/4)I`, the physical Casimir is

\[
\boxed{\quad
\kappa(r)=\frac{\sqrt3(8+r-4\log r)\sqrt{4-r^2}}
 {2(4-r)^2}>\frac32,\qquad 0<r<1.
\quad}
\tag{6}
\]

To prove the strict sign without differentiating (6), use
`-log r>2(1-r)/(1+r)`. Hence
`A>(r^2+r+16)/(r+1)>0`. Squaring the desired positive comparison
reduces to the exact identity

\[
\begin{aligned}
&(r^2+r+16)^2(4-r^2)-3(r+1)^2(4-r)^4\\
&\qquad=-4(r-1)^3(r^3-7r^2+32r+64)>0.
\end{aligned}
\]

The final polynomial is positive on `(0,1)` because
`64-7r^2>57` and its remaining terms are positive.
The multiplier (5) is triangular positive elliptic, so its physical
counterpart has the negative elliptic orientation required by the
complete-period cost--Casimir theorem. Thus any actual normal PMP lift
of this equal-factor closed member would satisfy `C>pi`. The calculation
does not itself assert all-control maximality for every stationary
regular member; its independently retained cost comparison is already
available in REGULAR_FAMILY_COMPARISON.

## Remaining obstruction

The arbitrary unequal-margin equations (2) still contain the conjugated
frame columns and the full central product constraint. No identity
controlling their relative positions strongly enough to produce a
Casimir lower bound has been proved here. Nor has a negative-parabolic
or hyperbolic exclusion been obtained. The existing uniform R target
therefore remains open; this calculation neither replaces it by a
finite sample nor assumes away its remaining sectors.
