# Independent audit of the reverse-angle gap and M1 closure

Date: 2026-11-07 UTC. Independent internal hand review of
[MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION](MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md).
No Lean, Lake, typechecking, or CI was run.

## Result

The proof passes this review. Every reverse centre in the stated
competitive normal closed-period domain satisfies `cos(phi)<3/10`.
Combining this with the actual geometric angle sum excludes the entire
all-short family with `m>=5`; the separate existing strict cost bound
excludes `m=2`. Thus the sufficient whole-period M1 assignment is
closed. The theorem does not exclude local M1 occurrences inside a
period assigned to M2, and does not close F or M2.

The review separately checked the actual covector normalization, all
comparison-domain boundaries, the fixed-angle implicit derivatives,
both monotone path segments, the exact rational cutoff, and the
twisted-period angle sum. The auxiliary path is used only to compare
scalar data. It is not asserted to preserve endpoints or to generate
an admissible competitor.

## 1. The actual data meet every scalar hypothesis

At a surviving reverse centre the previously proved strict centre
minimum gives `a<p,n`; the positive reverse factor gives
`rho<rt`. Hence `0<r,t<1/2` and `0<rho<rt<1/4`.
Each reverse switch abuts a turn, so the exact turn secant gives
`u,v>3/4`. The reverse switch inequalities give
`u<=1-r+r^2` and `v<=1-t+t^2`. Weak upper bounds suffice throughout;
the new proof does not assume uniform switch transversality.

Substituting the active-margin variables into the actual normal
stationarity equation gives (5), with `u=8nu_-`, `v=8nu_+`, and
`E=16e`. The Gram identity gives

\[
\gamma^2=\frac{4uv-E^2}{16(1-\rho)^2},\qquad
\cos\phi=\frac{E}{2\sqrt{uv}}.
\]

The same physical primary covector has
`kappa=sqrt(12) gamma`. The complete-period cost--Casimir estimate
therefore gives exactly the cap in (7). The proof uses neither a
newly chosen stationary multiplier nor conservation alone in place
of that budget-dependent cap. Its preliminary `cos(phi)<1/2`
estimate also checks directly, including when `E<=0`.

## 2. Fixed-angle differentiation and the strict derivative sign

With the positive cosine `c` held fixed, differentiating
`E=2sqrt(uv)c` gives

\[
\rho_r=-\frac{\rho[U(r)-u]}{r^2(1-\rho)},\qquad
\rho_u=-\frac{\rho}{1-\rho}
\left(\frac1r-\frac{E}{2u}\right).
\]

Substitution in `Gamma=sqrt(uv)sqrt(1-c^2)/(2(1-rho))`
gives (10)--(11), with the stated signs and factors.

The positivity of `Q` is essential. Independently of the monotonic
minimization used in the source note, its displayed lower bound has
the following decomposition, where `z=rho/(rt)`:

\[
\begin{aligned}
Q\ \ge{}&1-z+\frac z4\log z\\
&+z(1-2t)\left[1-\frac{r(1+2t)}4\right]
+z(rt-\tfrac14)\log z.
\end{aligned}
\]

The last two terms are nonnegative on the closed comparison domain
`r,t<=1/2`, `z<1`; the first line is strictly positive. This verifies
`partial_u log(Gamma)>0` also at the boundary values used by the
comparison. Interchanging `(r,u)` and `(t,v)` gives the same result.

## 3. The two path segments exist and stay admissible

At fixed `u`, increasing `r` until `U(r)=u` lowers both `rho`
and `Gamma`; the product `rt` increases. Therefore the strict bound
`rho<rt` persists. The endpoint exists because `U` decreases from
one to `3/4` on `[0,1/2]`.

Along the subsequent boundary segment `u=U(r)`, the exact logarithmic
derivative is (13). Positivity of `E`, together with
`rho<rt<=r/2`, gives `rho'/rho<1/r`. Thus `rho/(rt)` decreases
on this segment too. At `r=1/2` the left derivative is zero and
the strict final comparison with `1/r` still holds. Since
`U'(r)=2r-1<=0`, the already checked derivative signs show that
`Gamma` does not increase.

These finite segments cannot terminate at `rho=0`: all other terms
in the fixed-angle equation remain bounded, whereas `log(rho)`
would diverge to minus infinity. The other boundary cannot be reached
because `rho/(rt)` decreases and `rt<=1/4`. The implicit derivative
`E_rho=(1-rho)/rho` is therefore nonzero throughout. Repeating the
argument for `(t,v)` yields the claimed comparison with
`r=t=1/2`, `u=v=3/4`, without silently reversing a domain inequality.

## 4. Symmetric monotonicity and the rational separation

The symmetric equation is
`B(rho)=1-rho+log(4rho)=3c/2`, with `B'>0`.
For `z=4rho`, direct differentiation verifies

\[
\frac{d}{dz}
\left[(1-z/4+\log z)(4/z-1+\log z)\right]
=-\frac{(4-z)^2}{4z^2}\log z>0.
\]

Its value at one is `9/4`, which is precisely the comparison needed
for the strict increase of the symmetric squared Casimir with `rho`.
The lower logarithm bound at `rho=17/100` makes `B` positive,
so the subsequent squared upper bound is legitimate. The exact gaps
are

\[
\frac9{20}-\frac{943}{2100}=\frac1{1050}>0,
\]
\[
\frac{20475}{110224}-\frac{97969}{529200}
=\frac{287773}{455707350}>0.
\]

Thus every `c>=3/10` contradicts the correctly normalized competitive
cap. There is no floating-point or numerical optimization premise in
this separation.

## 5. The whole-period conclusion and validation boundary

For all-short periods the collapsed cycle has `m` reverse edges and
the actual gauged winding is `n=(2m-1)/3`. Each raw clockwise angle
`-phi_j` becomes `pi-phi_j` under the sign gauge. Thus
`sum phi_j=m pi-n pi=(m+1)pi/3`, including the twisted seam.
This uses the actual geometric lift, not only scalar matrix trace
or centrality.

The exact inequality `cos(2pi/5)>3/10` makes every angle larger
than `2pi/5`. For every `m>=5`, their required average is at most
`2pi/5`, giving the asserted contradiction uniformly. The retained
two-centre cost theorem treats the only smaller allowed multiplicity.

The supplementary command

```
python3 explorations/mixed_global_short_run_angle_certificate.py
```

passed all 21 exact checks during this review. Those checks support
the algebra; the domain continuation, logarithm inequalities, normal
PMP interface, and full-period winding argument are the hand proofs
reviewed above. No material correction to the theorem is required.
This is internal mathematical review, not external peer review or
kernel validation.
