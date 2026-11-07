# Explicit singular clearance away from the critical costate determinant

Date: 2026-11-07. Hand proof with explicit constants; no Lean, Lake,
typechecking, CI, numerical trajectory, or symbolic sign calculation.

**Completed global follow-up.**
[GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md) now relates the
complete-period cost to this invariant on the negative elliptic
component. [GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md)
combines that relation with the other costate components and the
small-multiplier estimate to prove \(D>10^{-1906}\) for every
normalized minimizing lift and \(N<10^{5741}\) for every minimizing
period, under the retained state, PMP, and edge-optimality inputs.
It bypasses Hales--Vajjha Theorem 16.3.1. The sector estimates proved
below keep their original, broader hypotheses.

## Theorem and scope

Use the physical-time equations and projective normalization from
[QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md):

\[
\lambda\le0,\qquad
\mathcal P=(\lambda,\Lambda_1,W),\qquad
\|\mathcal P(0)\|^2
 =\lambda^2+\|\Lambda_1(0)\|_F^2+\|W(0)\|_F^2=1.
\tag{1}
\]

All costate matrices are traceless, \(J=\left(\begin{smallmatrix}
0&-1\\1&0\end{smallmatrix}\right)\), and

\[
A=\Lambda_1-\frac32\lambda J,\qquad
D(t)^2=\|X(t)-J\|_F^2+\|A(t)\|_F^2+\|W(t)\|_F^2.
\tag{2}
\]

Define the determinant invariant

\[
\boxed{\Delta=\det\Lambda_1-\frac94\lambda^2.}
\tag{3}
\]

The following clearance statements do not require a minimizing
trajectory, a finite vertex representation, or Hales--Vajjha
Theorem 16.3.1.

1. For every \(0<\delta\le1\), if \(|\Delta|\ge\delta\), then
   \(D(t)>\delta/3\) at every time.
2. If \(|\lambda|\ge1/2\), then \(D(t)>1/13\) at every time.

For the switch counts below, impose additionally the state/time bounds

\[
\|X(t)\|_F\le9,\qquad
-\operatorname{tr}(Z_iX(t))\ge\frac{2}{15\sqrt3},\qquad
0<T\le\frac\pi3,
\tag{4}
\]

and the quantitative theorem's hypothesis:

> **(E4)** On every subinterval where one fixed control coordinate
> vanishes almost everywhere, the control agrees almost everywhere
> with at most four positive constant vertex pieces.

Then \(|\Delta|\ge\delta\), \(0<\delta\le1\), implies a vertex
representation with

\[
\boxed{N<\frac{10^{5740}}{\delta}.}
\tag{5}
\]

In particular, \(|\Delta|\ge10^{-n}\), for an integer \(n\ge0\),
gives the specific integer bound \(N<10^{5740+n}\).
The large-multiplier sector \(|\lambda|\ge1/2\) itself satisfies
\(N<10^{5740}\).

These are bounds for explicitly specified phase sectors. They do not
exclude their trajectories as global competitors, compare their costs,
or give a common numerical bound as \(\Delta\) tends to zero.

## 1. Conservation and an exact algebraic estimate

The physical Pontryagin equations include

\[
\lambda'=0,\qquad \Lambda_1'=[\Lambda_1,X].
\tag{6}
\]

For a traceless two-by-two matrix, \(\det M=-\operatorname{tr}(M^2)/2\).
Therefore, wherever the derivative exists,

\[
\frac{d}{dt}\det\Lambda_1
 =-\operatorname{tr}(\Lambda_1[\Lambda_1,X])=0.
\]

The last equality is cyclic invariance of trace. Absolute continuity
then proves that (3) is constant on the whole interval, including
through control switches. This uses no derivative of the control.

Substitute \(\Lambda_1=A+(3/2)\lambda J\) and \(J^2=-I\):

\[
\boxed{
\Delta=-\frac32\lambda\operatorname{tr}(JA)
       -\frac12\operatorname{tr}(A^2).}
\tag{7}
\]

Normalization (1) and constancy of \(\lambda\) give
\(|\lambda|\le1\). The Frobenius Cauchy--Schwarz inequality gives
\(|\operatorname{tr}(JA)|\le\sqrt2\|A\|_F\) and
\(|\operatorname{tr}(A^2)|\le\|A\|_F^2\). Since \(\sqrt2<3/2\),

\[
\boxed{
|\Delta|\le\frac94\|A\|_F+\frac12\|A\|_F^2.}
\tag{8}
\]

Suppose now that \(|\Delta|\ge\delta\), with \(0<\delta\le1\).
If \(\|A(t)\|_F\le\delta/3\), then \(\|A(t)\|_F\le1\), so
(8) gives

\[
\delta\le|\Delta|
 \le\frac{11}{4}\|A(t)\|_F
 \le\frac{11}{12}\delta<\delta,
\]

a contradiction. Thus \(\|A(t)\|_F>\delta/3\), and (2) proves
the first clearance statement. The argument controls the distance
through a costate component alone; it does not presume that the state
is far from \(J\).

## 2. A whole multiplier sector is separated automatically

For every real two-by-two matrix \(M\),

\[
\det M\le\frac12\|M\|_F^2.
\]

For instance, this follows from \(2|ad-bc|\le
a^2+b^2+c^2+d^2\). Applying it at the initial time and using (1),

\[
\Delta
\le\frac{1-\lambda^2}{2}-\frac94\lambda^2
=\frac12-\frac{11}{4}\lambda^2.
\tag{9}
\]

Consequently \(|\lambda|\ge1/2\) implies
\(\Delta\le-3/16\). If at some time \(\|A\|_F\le1/13\),
equation (8) would instead give

\[
\frac3{16}\le|\Delta|
\le\frac9{52}+\frac1{338}
=\frac{119}{676}<\frac3{16},
\]

where the last strict inequality is \(1904<2028\) after cross
multiplication. This proves

\[
\boxed{|\lambda|\ge\frac12\quad\Longrightarrow\quad
       D(t)>\frac1{13}\ \text{for all }t.}
\tag{10}
\]

No definiteness assumption on \(\Lambda_1\) was used. In particular,
the argument does not restrict it to an elliptic adjoint orbit.

## 3. Conversion to explicit integer bounds

Let \(c,m>0\) be the constants in the three-line version of
`QUANTITATIVE_REGULAR_SWITCH_BOUND.md`. The hand estimates in
[GLOBAL_SMALL_MULTIPLIER_BOUND](GLOBAL_SMALL_MULTIPLIER_BOUND.md),
Sections 2--3, give

\[
0<m\le1,\qquad m>10^{-1903},\qquad c>10^{-27}m^2.
\tag{11}
\]

Those coefficient estimates hold throughout the domain (4), independently
of the size of \(\lambda\). The small-multiplier assumption of that
note is used to obtain its clearance, not to prove (11).

For \(|\Delta|\ge\delta\), use the supplied clearance
\(\varepsilon=\delta/3\). Since \(0<\delta\le1\) and \(m\le1\),

\[
e=\min(\delta/3,1,m)\ge\frac{m\delta}{3}.
\]

The common counting interval therefore has length \(h=ce\) with

\[
h>\frac\delta3\,10^{-27}m^3
 >\frac\delta3\,10^{-5736}
 >\delta\,10^{-5737}.
\tag{12}
\]

There are at most 28 pieces on each such interval. Using \(\pi/3<2\)
and \(\lceil x\rceil\le x+1\),

\[
\begin{aligned}
N&\le28\left\lceil\frac{\pi/3}{h}\right\rceil\\
 &<28\left(\frac{2\cdot10^{5737}}\delta+1\right)\\
 &\le\frac{28(2\cdot10^{5737}+1)}\delta
 <\frac{10^{5740}}\delta.
\end{aligned}
\tag{13}
\]

This proves (5) and its power-of-ten specialization. Concatenation and
merging equal neighboring vertices give the stated representation; a
twisted cyclic reduction can only reduce its piece count.

For (10), one can retain the stronger clearance \(\varepsilon=1/13\).
Now \(e\ge m/13\), and (11) gives

\[
h>\frac1{13}10^{-5736}>10^{-5738}.
\]

The integer \(2\cdot10^{5738}\) bounds \((\pi/3)/h\) strictly,
so

\[
N\le56\cdot10^{5738}<10^{5740}.
\tag{14}
\]

The constants are deliberately coarse. These inequalities require no
lower bound for individual arc durations and no previously established
finite-word representation.

## 4. The critical invariant and the completed global follow-up

The small-multiplier theorem handles
\(|\lambda|\le m/\sqrt{22}\). Equation (10) handles
\(|\lambda|\ge1/2\). The remaining projective multiplier range is
therefore confined to

\[
\frac m{\sqrt{22}}<|\lambda|<\frac12.
\tag{15}
\]

This restriction alone does not supply a lower bound for \(|\Delta|\).
For any separately chosen \(n\), (5) handles the additional sector
\(|\Delta|\ge10^{-n}\), while the shrinking band
\(|\Delta|<10^{-n}\) is not treated by these scoped estimates.
Passing to larger \(n\) does not give one common numerical count near
\(\Delta=0\). The complete-period cost argument linked below supplies
the additional restriction for minimizing trajectories.

For the normal rescaling \(\mu=|\lambda|\),
\(\overline\Lambda_1=\Lambda_1/\mu\), \(\overline\lambda=-1\),
the invariant transforms exactly as

\[
\overline\Delta
 =\det\overline\Lambda_1-\frac94
 =\frac{\Delta}{\mu^2}.
\tag{16}
\]

The explicit normal-sector bounds and conversion of a normal
\(\overline D\)-clearance to \(D\) are given in Section 5 of
[GLOBAL_SMALL_MULTIPLIER_BOUND](GLOBAL_SMALL_MULTIPLIER_BOUND.md).
[GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md) now uses the full frame
endpoint and cost budget \(C\le A_{\rm oct}<\pi\) to separate the
negative elliptic normal component from the critical determinant.
[GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md) treats the
other components, proves \(\overline D>1/120\) for every normal lift
under that budget, and carries out the projective conversion. These
are additional complete-period arguments, rather than conclusions
of (15)--(16) alone.

There is a relevant source limitation: the coordinates of
[Hales--Vajjha Section 14.1](https://arxiv.org/html/2405.04331v1#Ch14.S1)
fix \(\lambda=-1\) and \(\det\Lambda_1=9/4\). This is precisely
the critical slice \(\overline\Delta=0\). A tube certified only
inside that slice would not cover a full neighborhood transverse to it.
The distinct source-enclosure obligations are recorded in
[FINITE_BANG_BANG_SOURCE_AUDIT](FINITE_BANG_BANG_SOURCE_AUDIT.md).
They belong to the earlier qualitative route; the complete-period
cost argument and its numerical clearance do not use or certify
those source computations.

## Validation boundary

Conservation (6), the determinant expansion (7), both clearance results,
and all numerical conversions above are hand arguments. The counting
step uses the conditional regular-domain theorem and (E4), but never
uses the qualitative singular-clearance argument or the external
finite bang-bang theorem. Applications to actual minimizers still retain
the compact-state and edge-optimality source inputs identified in the
linked notes.

The result in this note isolates explicit portions of the global
clearance problem. The all-lift clearance and uniform minimizing-period
integer are now proved in
[GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md), with
its additional complete-period hypotheses. The cost comparison for
all words under that ceiling and affine uniqueness remain separate.
No increasing-length word enumeration is part of these sector proofs.

Two independent internal hand reviews checked the assembled conservation
proof, both strict clearance estimates, every coefficient and ceiling bound,
the normal-rescaling identity, and the source's critical-slice hypotheses.
No material gap was found. This records mathematical review, not external
peer review or Lean kernel validation.
