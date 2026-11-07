# Independent audit of the reverse-centre phase bound

Date: 2026-11-07 UTC. Independent internal hand review of
[MIXED_REVERSE_CENTRE_PHASE_BOUND](MIXED_REVERSE_CENTRE_PHASE_BOUND.md).
No Lean, Lake, typechecking, or CI.

## Result

The scalar inequality, its full normalization, the negative pure-angular
block, and the constrained-index subtraction are valid on the stated
actual minimizing domain. The resulting uniform exclusion of all-short
periods with `m>=11` is justified. The allowed remaining multiplicities
`m=5,8` are correctly retained, and no full M1/F/M2 comparison or full
dual-Hessian sign is asserted.

## 1. Scalar domain and strict inequalities

I reconstructed the change of variables from the actual reverse-centre
stationarity and Gram determinant identities. The strict centre minimum
and positive centre factor give `0<r,t<1/2` and `0<rho<rt<1/4`.
The incident turns give `3/4<u,v<1`; reverse switching gives the
upper thresholds `U=1-r+r^2`, `V=1-t+t^2`. The formula for `E=16e`
and the determinant normalization `gamma^2=K^2(4uv-E^2)/256` have
the correct factors.

When `E>0`, raising `u,v` to their thresholds keeps `E` positive
and below its upper-corner value `B`. The inequality `B<3rho`
holds over the entire rectangle and also over the later interval
`rho<=s<=rt`, not merely at the initial point. The displayed
monotonicity argument in `4rho` proves this with strict margins.

The derivative reserve is correctly oriented:

\[
-\mathcal L_u-E(1-r)/r
>\frac{1-5\rho+7\rho^2-\rho r}{r}
\ge\frac1{16r}>0.
\]

The negative sign of `2rho-1+r` is essential when inserting
`E<3rho`; the proof uses it correctly. The same estimate applies
to `v`. During integration the running `E` increases, so replacing
it by its original value gives a valid lower bound for the gain.

At the upper corner, I independently differentiated `L_*` and
checked both endpoint factorizations. Its second derivative is positive
through the required interval, while its first derivative remains
negative because it is increasing and still negative at `rt`.
Therefore its value exceeds the strictly positive endpoint value.
These facts prove the strengthened estimate (15), including every
boundary equality allowed before the strict positive-period inequalities
are applied.

The case `E<=0` is correctly separated before this argument. It needs
no division by the cross pairing and makes the final phase inequality
immediate.

## 2. Translation back to the actual coefficients

The strict reverse switching coefficients are
`beta_-=(U-u)/4`, `beta_+=(V-v)/4`. I checked the exact relations

\[
a^2\gamma^2-Ke=K^3\mathcal L/256,
\]

and

\[
2T^2-Ke[M+2(\omega_-+\omega_+)]
=\frac{a^2K}{32}
\left\{\mathcal L-E\left[
\frac{1-r}{r}(U-u)+\frac{1-t}{t}(V-v)\right]\right\}.
\]

They agree with the margin ratios used in the independently checked
all-short Schur complement. In particular `M=8a^2/K^2` and
`T=2a^2 gamma/K` have not lost a factor of two in passing from
the joint Hessian to the reduced residual.

## 3. The angular Schur block

The all-short margin block is positive definite, so eliminating it
preserves the negative index. On `alpha=0`, the residual is exactly
the displayed expression (18). The effective bridge conductance is
the series combination of its three positive edge conductances and
is therefore below each adjoining conductance.

I checked the matrix-order step

\[
0<L_{\rm eff}\le\operatorname{diag}(M_j+2g_{j-1}+2g_j),
\]

and its reversed inverse inequality. For `e_j>0`, the scalar theorem
then makes every coefficient in (20) strictly negative. For `e_j<=0`
that coefficient is already strictly negative because `T_j>0`.
Thus the whole periodic pure-phase subspace has precisely the
one obvious constant zero direction and is strictly negative on its
`m-1` dimensional complement. Antiperiodicity of the underlying
vectors does not alter periodicity of these scalar phase coefficients.

## 4. Full constrained index and scope

The ordinary Jacobi index is used only through the independently
audited augmented-index bridge. With `P=m` and the actual geometric
winding `n=(2m-1)/3`, subtraction of the nonzero range block and
**all three** frame-constraint saddle pairs gives

\[
m-1-2(m-n-1)-3=(m-8)/3.
\]

For every allowed `m>=11` this is positive. The full frame rank three
comes from the existing rank-five local M1 window, so the negative
tangent integrates to an exact nearby closed competitor. The strict
state/factor conditions and the retained geometric realization justify
its admissibility. This is a true minimizing-period exclusion, not
merely a negative unconstrained derivative or a formal differential
kernel vector.

The argument supplies no positive lower index for `m=5` or `m=8`;
the note does not claim one. The separate two-centre cost argument
handles `m=2`. The ordinary Jacobi winding/inertia alone is not being
identified with the cost index, and the radial/angular Schur coupling
remains explicitly open.

## Exact supplementary check

I ran

```
python explorations/mixed_reverse_centre_phase_certificate.py
```

with Python 3.12.14 and SymPy 1.14.0. All 13 exact identities pass.
These identities supplement the independent inequality and interface
review above. This audit is internal mathematical review, not external
peer review or Lean kernel validation.
