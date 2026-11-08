# A sharper reverse angle and a uniform mixed-density restriction

Date: 2026-11-07 UTC. Hand corollaries of the proved reverse-centre
comparison. No Lean, Lake, typechecking, or CI.

## Statement and scope

Every reverse centre of a competitive finite normal geometric period
satisfies the stronger bound

\[
\boxed{\cos\phi<\frac14,\qquad \phi>\frac{5\pi}{12}.}
\tag{1}
\]

Here `phi in (0,pi)` is the unsigned, negatively oriented angle in
the same positive elliptic costate metric as
[MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION](MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md).
That note already closes sufficient M1 using a weaker angle bound.
Its proof and case scope are unchanged.

Let a remaining mixed period have `m` double reverse runs, `P`
forward switches, and

\[
E=P-m=\#\{\text{arcs with incident signs }++\}.
\]

Then every minimizing period satisfies

\[
\boxed{m\le 2E+3.}
\tag{2}
\]

Together with the independent constrained-index theorem in
[MIXED_GLOBAL_PHASE_DENSITY](MIXED_GLOBAL_PHASE_DENSITY.md), this gives

\[
\boxed{m\le\min(2E+3,E+8).}
\tag{3}
\]

This is a uniform density restriction, not a bound on `E`, a finite
period catalogue, or a closure of M2. The angular part uses the actual
geometric winding and complete-period Casimir cap. The second bound
in (3) additionally uses the previously proved constrained-index and
rank-three interface.

Section 3 also proves the lower Casimir bound `gamma^2>27/256`, or
equivalently `kappa>9/8`, for every competitive mixed period. This
additional compact-domain restriction uses full-period winding;
it is not asserted for an arbitrary local normal PMP window.

## 1. A second exact cutoff in the same scalar comparison

The comparison theorem already proved in the cited M1 note says that,
if `0<c=cos phi<1/2`, then

\[
\gamma\ge\Gamma_{\rm sym}(c),
\qquad
B(\rho_c)=\frac32c,
\qquad B(\rho)=1-\rho+\log(4\rho),
\]

\[
\Gamma_{\rm sym}(c)^2
=\frac{9/4-B(\rho_c)^2}{16(1-\rho_c)^2}.
\tag{4}
\]

The path and its derivative signs in that proof use only `0<c<1/2`.
The hypothesis `c>=3/10` appears only at its final numerical cutoff.
Thus the same already proved comparison applies to the new range
`c>=1/4` considered here.

Both `B` and the last expression increase strictly with `rho` on the
relevant interval `0<rho<1/4`. The actual normal multiplier satisfies

\[
\gamma^2\le\frac{97969}{529200}.
\tag{5}
\]

Assume `c>=1/4`. At `rho_0=5/32`,

\[
0<\frac{27}{32}-\frac35
<B(5/32)
=\frac{27}{32}+\log(5/8)<\frac38.
\tag{6}
\]

For the upper bound, put `x=3/13`. Direct integration gives

\[
\log(5/8)
=-2\int_0^{3/13}\frac{ds}{1-s^2}
<-2\left(\frac3{13}+\frac{(3/13)^3}{3}\right)
=-\frac{1032}{2197}<-\frac{15}{32}.
\tag{7}
\]

The first strict inequality follows from
`1/(1-s^2)>1+s^2` for `s>0`. The final rational cross-product
difference is `69`. The lower bound in (6) uses
`log x>(x-1)/x` at `x=5/8`.

Thus `rho_c>5/32`, and monotonicity in (4) gives

\[
\gamma^2\ge\Gamma_{\rm sym}(c)^2
>\frac{9/4-(3/8)^2}{16(27/32)^2}
=\frac5{27}
=\frac{98000}{529200}
>\frac{97969}{529200}.
\tag{8}
\]

This contradicts (5). If `cos phi<=0`, the desired bound is already
immediate; hence `cos phi<1/4` in all cases.

Finally

\[
\cos(5\pi/12)=\frac{\sqrt6-\sqrt2}{4}>\frac14.
\]

Indeed `sqrt(6)>1+sqrt(2)` follows successively from
`3>2sqrt(2)` and `9>8`. Since cosine decreases on `(0,pi)`,
this proves both assertions in (1).

## 2. The exact mixed angular-defect budget

At a `++` arc let `theta_i in (0,pi/2)` be its positively oriented
costate-metric angle. The strict upper bound is the local forward
acuteness theorem, extended to mixed periods in
[MIXED_GLOBAL_PHASE_DENSITY, Section 1](MIXED_GLOBAL_PHASE_DENSITY.md#1-forward-pairings-are-positive-also-inside-mixed-periods).
No bound `theta_i<pi/3` is used.

There are `E` forward same-sign arcs and `m` reverse centres. The
gauged angle at a reverse centre is `pi-phi_j`. The actual winding
theorem gives

\[
\sum_{++}\theta_i+\sum_{--}(\pi-\phi_j)
=n\pi,\qquad n=\frac{P+m-1}{3}
=\frac{E+2m-1}{3}.
\]

Rearrangement yields the exact identity

\[
\boxed{
\sum_{++}\left(\frac\pi3-\theta_i\right)
+\sum_{--}\left(\phi_j-\frac\pi3\right)
=\frac\pi3.}
\tag{9}
\]

Every reverse summand is greater than `pi/12` by (1). Every forward
summand is greater than `-pi/6` by acuteness. Therefore

\[
\frac\pi3>\frac{m\pi}{12}-\frac{E\pi}{6},
\qquad m<2E+4.
\]

As `m,E` are integers, this proves (2). The already established
index bound is `m<=E+8`, proving (3). Triple ties, unequal factors,
the twisted seam and arbitrarily short positive arcs remain within
the stated domain; the proof introduces no uniform duration bound.

## 3. A whole-mixed lower Casimir bound

There are `P=E+m` edges in the collapsed cycle. Since a mixed period
has `m>=1`, its actual winding satisfies

\[
\frac nP=\frac{P+m-1}{3P}\ge\frac13.
\]

Thus some positively gauged angle `theta` is at least `pi/3`.
Every gauged angle is strictly less than `2pi/3`: at a forward site
this follows from acuteness, while at a reverse centre the angle is
`pi-phi<7pi/12<2pi/3` by (1). Consequently the selected edge has

\[
\frac\pi3\le\theta<\frac{2\pi}3,
\qquad \sin\theta\ge\frac{\sqrt3}{2}.
\]

At any surviving edge the same metric Gram identity gives

\[
\gamma=K_i\sqrt{\nu_{i-1}\nu_i}\sin\theta.
\]

Here `K_i=a_i^2+4>4`. Every switch-vector norm in the remaining
mixed domain is at least `3/32`: forward edges have the forward
switching bound, and reverse edges adjoin turns with their strict
secant bound. The turn identifications and sign gauge leave these
norms unchanged. Hence

\[
\boxed{
\gamma>4\cdot\frac3{32}\cdot\frac{\sqrt3}{2}
=\frac{3\sqrt3}{16},\qquad
\gamma^2>\frac{27}{256},\qquad
\kappa=\sqrt{12}\,\gamma>\frac98.}
\tag{10}
\]

Together with the established competitive upper cap, this confines
the primary costate to a fixed positive Casimir interval on the
whole mixed domain. The existence of the selected angle comes from
the actual complete-period winding. A short local window does not
have that input and may have a much smaller Casimir.

## Supplementary exact checker

Run

```
python3 explorations/mixed_global_reverse_angle_density_certificate.py
```

The checker verifies the fixed rational comparisons, the angular
count identities and the lower-Casimir normalization. The logarithmic comparison, the reused scalar
monotonicity, the actual normal-covector interface and the geometric
winding are the displayed hand arguments.
