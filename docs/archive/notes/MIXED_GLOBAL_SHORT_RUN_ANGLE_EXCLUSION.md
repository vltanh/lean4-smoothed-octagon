# A Casimir angle gap closes the all-short mixed case

Date: 2026-11-07 UTC. Complete hand exclusion of the sufficient M1
domain. No Lean, Lake, typechecking, or CI.

## Result and scope

At every reverse-run centre of a competitive finite normal geometric
period, let `phi` be the unsigned angle between its two adjacent switch
vectors in the positive elliptic costate metric. Then

\[
\boxed{\cos\phi<\frac3{10}.}
\tag{1}
\]

The angle is in `(0,pi)`, with the actual negative Wronskian orientation.
The proof uses the same actual normal covector throughout. It does not
assume equal factors, reflection symmetry, a rank condition, or a
uniformly positive switching derivative. The comparison path below is
an auxiliary scalar inequality, not a proposed trajectory variation.

For the complete all-short domain `(--+)^m`, the actual geometric
winding gives

\[
\sum_{j=0}^{m-1}\phi_j=\frac{m+1}{3}\pi,
\qquad m\equiv2\pmod3.
\tag{2}
\]

If `m>=5`, its average angle is at most `2pi/5`, whereas (1) makes
every angle strictly larger than `2pi/5`. This is impossible. The
remaining `m=2` branch was already excluded by the strict cost bound in
[MIXED_GLOBAL_SHORT_RUN_PERIOD](MIXED_GLOBAL_SHORT_RUN_PERIOD.md).
Consequently the sufficient whole-period M1 case is **closed**.

The case assignment is the proved one: a mixed period with any forward
run of length at least two is assigned to M2; otherwise every forward
run has length one and the whole sign sequence is `(--+)^m`.
This conclusion does not exclude arbitrary local M1 occurrences inside
periods assigned to M2. F and M2 still require their own complete
comparisons.

## 1. Actual reverse-centre data and the common Casimir

The normality, run-minimum and ellipticity results are respectively
[GLOBAL_NORMALITY](GLOBAL_NORMALITY.md),
[MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md),
and [MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md).
Every surviving reverse run has exactly two switches. At its centre,
write the active margin as `a`, and its two adjacent active margins as
`p,n`. Then `a<p,n`. Put

\[
K=a^2+4,\qquad
\rho=\frac{a^2}{K},\quad
r=\frac a{a+p},\quad t=\frac a{a+n}.
\]

The positive centre factor gives

\[
0<r,t<\frac12,\qquad 0<\rho<rt<\frac14.
\tag{3}
\]

Let the two adjacent metric norms be `nu_-,nu_+`, their pairing be
`e`, and the positive metric determinant be `gamma^2`. Use the
normalizations

\[
u=8\nu_-,\qquad v=8\nu_+,\qquad E=16e,
\qquad U(s)=1-s+s^2.
\]

The turn secants give `u,v>3/4`. The actual reverse-switch derivative
inequalities give the upper bounds

\[
\frac34<u\le U(r),\qquad \frac34<v\le U(t).
\tag{4}
\]

We deliberately retain weak upper inequalities; transversality is not
needed for the new scalar comparison. The exact normal centre
stationarity equation is

\[
\boxed{
E=1+r+t-\rho+\log\frac{\rho}{rt}
 -\frac{1-u}{r}-\frac{1-v}{t}.}
\tag{5}
\]

The Gram determinant and the angle definition give, with `W=sqrt(uv)`,

\[
\cos\phi=\frac{E}{2W},\qquad
\gamma=\frac{\sqrt{4uv-E^2}}{4(1-\rho)}
       =\frac{W\sin\phi}{2(1-\rho)}.
\tag{6}
\]

These are the normalizations in
[MIXED_REVERSE_CENTRE_PHASE_BOUND](MIXED_REVERSE_CENTRE_PHASE_BOUND.md).
The physical primary-costate Casimir is `kappa=sqrt(12) gamma`.
The complete-period cost bound, including the actual twisted endpoint,
therefore supplies

\[
\boxed{\gamma\le\gamma_{\max}
=\frac{313}{210\sqrt{12}}.}
\tag{7}
\]

Here the rational bound uses `C<=A_oct<313/100` and `pi>157/50`, as
proved in [GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md)
from [GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md). Conservation alone
would not give (7).

For reference, (3)--(5) already imply `cos phi<1/2`. Indeed increasing
`u,v` to their upper bounds gives

\[
E\le-1+2r+2t-\rho+\log\frac\rho{rt}<3\rho.
\]

For the last inequality write `z=rho/(rt)<1` and use

\[
E-3\rho\le
 -(1-2r)(1-2t)+4rt(1-z)+\log z<0.
\]

The elementary inequality `log z<=z-1` and `4rt<1` prove the strict
sign. Since `2W>3/2`, (6) gives `cos phi<2rho<1/2`.

## 2. A scalar comparison at a fixed positive angle cosine

Suppose for contradiction that

\[
\frac3{10}\le c:=\cos\phi<\frac12.
\tag{8}
\]

In this section `c` is fixed. Enlarge the lower bounds in (4) to
`u,v>=3/4`; this permits boundary comparisons. In the expression (5)
solve

\[
E(r,t,\rho,u,v)=2\sqrt{uv}\,c
\tag{9}
\]

for `rho`. The derivative `E_rho=(1-rho)/rho` is strictly positive on
`0<rho<1`. Hence the solution is locally unique and smooth, and its
continuation is controlled by the explicit bounds below. Set

\[
\Gamma=\frac{\sqrt{uv}\sqrt{1-c^2}}{2(1-\rho)}.
\]

This agrees with `gamma` at the original data. Subscripts in the next
identities mean differentiation at fixed `c`, with (9) imposed:

\[
\frac{\partial\log\Gamma}{\partial r}
=-\frac{\rho[U(r)-u]}{r^2(1-\rho)^2}\le0,
\tag{10}
\]

\[
\frac{\partial\log\Gamma}{\partial u}
=\frac{Q}{2u(1-\rho)^2},\qquad
Q=(1-\rho)^2+\rho E-\frac{2\rho u}{r}.
\tag{11}
\]

The same formulas hold with `(r,u)` and `(t,v)` interchanged.

### The strict sign in (11)

Using (5), `u<=U(r)` and `v>=3/4` gives

\[
Q\ge1+\rho\left[t+\log\frac\rho{rt}
 -\frac2r-\frac1{4t}\right].
\]

Write `z=rho/(rt) in (0,1)`. The right-hand side is

\[
1-2tz+rz\left[t^2-\frac14+t\log z\right].
\]

The coefficient in brackets is negative, so replacing `r<=1/2` by
`1/2` lowers this expression. The resulting expression decreases
strictly as `t` increases to `1/2`. Consequently

\[
\boxed{Q\ge1-z+\frac z4\log z>0.}
\tag{12}
\]

For the final sign, the expression on the right is zero at `z=1`
and has derivative `(log z-3)/4<0` on `(0,1)`. Thus decreasing `u`
at fixed `c,r,t,v` decreases `Gamma`.

### A path that remains inside the comparison domain

Hold `(t,v,c)` fixed. First increase `r`, with `u` fixed, until
`u=U(r)`. The function `U` decreases from `1` to `3/4` on
`[0,1/2]`, so this point exists and is no earlier than the starting
`r`. Along this first part,

\[
\frac{\partial\rho}{\partial r}
=-\frac{\rho[U(r)-u]}{r^2(1-\rho)}\le0.
\]

Hence `rho/(rt)` decreases, and (3) persists. Equations (10)--(12)
show that `Gamma` does not increase.

Next increase `r` along the boundary `u=U(r)` until
`(r,u)=(1/2,3/4)`. Here the total derivative is

\[
\frac{\rho'}\rho
=\frac{1-2r}{1-\rho}
 \left(\frac1r-\frac{E}{2u}\right)
<\frac1r.
\tag{13}
\]

To verify the last inequality, use `E=2sqrt(uv)c>0` and
`rho<rt<=r/2<2r`. The displayed left-hand side is no greater
than `(1-2r)/(r(1-rho))`, which is strictly smaller than `1/r`.
Thus `rho/(rt)` again decreases. The solution cannot reach `rho=0`
on this finite parameter interval, because the logarithm in (5)
would tend to minus infinity while every other term and the right
side of (9) remain bounded. It also stays below `rt<=1/4`, so the
positive inverse derivative in (9) does not degenerate.

Along this second part, (10) is zero and (11) is positive, whereas
`u'=2r-1<=0`. Hence `Gamma` again does not increase. All upper and
lower bounds remain valid. Apply the same construction to `(t,v)`.
It follows that

\[
\boxed{\gamma\ge\Gamma_{\rm sym}(c),}
\tag{14}
\]

where the comparison data are

\[
r=t=\frac12,\qquad u=v=\frac34,
\]

and their unique `rho_c in (0,1/4)` satisfies

\[
B(\rho_c):=1-\rho_c+\log(4\rho_c)=\frac32c.
\tag{15}
\]

In particular

\[
\Gamma_{\rm sym}(c)^2
=\frac{9/4-B(\rho_c)^2}{16(1-\rho_c)^2}.
\tag{16}
\]

This proves an inequality between scalar data. The intermediate
points are not asserted to be PMP arcs, complete periods, or geometric
competitors, so no endpoint-preserving variation or rank theorem is
being used.

## 3. Exact rational separation from the competitive cap

The expression on the right of (16) increases strictly with `rho`
on the relevant interval. Here is a direct logarithmic check. Write

\[
z=4\rho,\qquad
h(z)=1-z/4+\log z,\qquad
k(z)=4/z-1+\log z.
\]

The sign of its derivative is the sign of `9/4-h(z)k(z)`. Moreover

\[
\frac{d}{dz}[h(z)k(z)]
=-\frac{(4-z)^2}{4z^2}\log z>0
\qquad(0<z<1),
\tag{17}
\]

and `h(1)k(1)=9/4`. This proves the required strict increase. Also
`B'(rho)=(1-rho)/rho>0`, so `Gamma_sym(c)` increases with `c`.

At the fixed rational value `rho_0=17/100`, the elementary logarithm
bounds give

\[
0<\frac{83}{100}-\frac8{17}
<B(17/100)
<\frac{83}{100}-\frac8{21}
=\frac{943}{2100}<\frac9{20}.
\tag{18}
\]

The lower logarithm bound is `log x>(x-1)/x`; the upper one is
`log x<2(x-1)/(x+1)` for `0<x<1`, applied to `x=17/25`.
Both follow by differentiating the respective remainders and fixing
their value at one.

Thus (8) and (15) imply `rho_c>17/100`. Equations (16)--(18) yield

\[
\gamma^2\ge\Gamma_{\rm sym}(c)^2
>\frac{9/4-(9/20)^2}{16(83/100)^2}
=\frac{20475}{110224}
>\frac{97969}{529200}
=\gamma_{\max}^2.
\tag{19}
\]

The final rational comparison has positive cross-product difference
`36834944`. This contradicts (7), proving (1).

## 4. The whole all-short period cannot close competitively

For clarity, the angle sum (2) uses the actual geometric lift, not
only a central endpoint matrix. The proof in
[MIXED_GLOBAL_PROJECTIVE_WINDING](MIXED_GLOBAL_PROJECTIVE_WINDING.md)
gives gauged winding `n pi`, with `n=(2m-1)/3` for the all-short
cycle. Each of its `m` negatively oriented centre angles is changed
from `-phi_j` to `pi-phi_j` by that gauge. Therefore

\[
m\pi-\sum_j\phi_j=n\pi,
\]

which is exactly (2), including the actual twisted seam.

Finally

\[
\cos(2\pi/5)=\frac{\sqrt5-1}{4}>\frac3{10},
\]

since `sqrt(5)>11/5`. Equation (1) therefore gives
`phi_j>2pi/5` for every centre. If `m>=5`,

\[
\sum_j\phi_j>\frac{2m}{5}\pi
\ge\frac{m+1}{3}\pi,
\]

contradicting (2). All inequalities are strict where required, and
no positive lower bound on individual durations was introduced.
The admissible multiplicities are `m=2 mod 3`; hence only `m=2`
remains, and its already proved cost bound is

\[
C>2\sqrt6-\sqrt3>\pi>A_{\rm oct}.
\]

This closes the sufficient M1 domain uniformly, without enumerating
its multiplicities or its unequal factors. The earlier angular-index
bound excluding `m>=11` remains valid but is no longer needed for
the M1 conclusion.

## Supplementary exact checker

Run

```
python3 explorations/mixed_global_short_run_angle_certificate.py
```

All 21 exact identities and rational inequalities pass with Python
3.12.14 and SymPy 1.14.0. The checker verifies the derivative identities,
the comparison polynomial and the rational separation. It is supplementary to the
displayed path, logarithmic signs and actual-PMP/winding interface;
it is not a substitute for those hand arguments.
