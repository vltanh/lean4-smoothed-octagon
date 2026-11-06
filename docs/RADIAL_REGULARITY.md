# A regular radial parametrization of a worst disk

`SmoothedOctagon/RadialRegularity.lean` supplies the initial regular positive `C¹` boundary
parametrization required by the upstream boundary regularity argument. Its main theorem starts
with an actual worst disk:

```lean
theorem rein_bd_isPositiveBoundaryParam_of_isWorstDisk
    (hK : IsWorstDisk K) :
    IsPositiveBoundaryParam K (rein_bd K)
```

Here `rein_bd` is the upstream radial parametrization, not an additional curve chosen in the
hypotheses. Write

\[
u(\theta)=(\cos\theta,\sin\theta),\qquad
g(\theta)=\operatorname{gauge}_K(u(\theta)),\qquad
b(\theta)=\frac{u(\theta)}{g(\theta)}.
\]

The proof shows that `b` is `C¹`, its derivative never vanishes, its image is exactly the
boundary of `K`, and it has positive orientation. The exact orientation formula is

\[
\boxed{\det(b(\theta),b'(\theta))=\frac{1}{g(\theta)^2}>0.}
\]

The result also holds for any centrally symmetric convex disk with a unique supporting line
at every boundary point. This more general theorem is exported as
`rein_bd_isPositiveBoundaryParam_of_unique_support`.

## The geometric input

The [upstream definition of `rein_bd` and its radial boundary lemmas](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Reinhardt.lean)
already give

\[
g(\theta)>0,\qquad b(\theta)\in\partial K,
\qquad \operatorname{range}(b)=\partial K.
\]

The missing part addressed here is the differentiability and regularity of `b`.
`SmoothedOctagon/SupportNormal.lean` supplies a continuous normalized supporting covector
`n(θ)` at each point `b(θ)`, satisfying

\[
n(\theta)\cdot b(\theta)=1,
\qquad n(\theta)\cdot y\leq\operatorname{gauge}_K(y)
\quad\text{for every }y\in\mathbb R^2.
\]

The first identity and `g(θ) > 0` imply

\[
n(\theta)\cdot u(\theta)=g(\theta).
\]

The covectors are continuous; differentiability of `n` is unnecessary. The following slope
argument is the analytic step that uses exactly this amount of regularity.

## Differentiating a supported contact value

The reusable theorem `hasDerivAt_of_continuous_supporting_family` has the following data:

- A curve `u : ℝ → ℝ²` differentiable at `x`, with derivative `u′`.
- A covector family `n : ℝ → ℝ²` continuous at `x`.
- A scalar function `f` with `n(t) · u(t) = f(t)` for every `t`.
- The supporting inequalities `n(s) · u(t) ≤ f(t)` for every `s,t`.

It proves

\[
f'(x)=n(x)\cdot u'.
\]

For a complete hand proof, put `Δu = u(t) − u(x)`. The supporting inequality for `n(x)` at
`u(t)`, together with contact at `x`, gives

\[
n(x)\cdot\Delta u\leq f(t)-f(x).
\]

The supporting inequality for `n(t)` at `u(x)`, together with contact at `t`, gives the other
bound:

\[
f(t)-f(x)\leq n(t)\cdot\Delta u.
\]

For `t ≠ x`, define

\[
A(t)=n(x)\cdot\frac{\Delta u}{t-x},\qquad
B(t)=n(t)\cdot\frac{\Delta u}{t-x},\qquad
q(t)=\frac{f(t)-f(x)}{t-x}.
\]

If `t > x`, division preserves the two inequalities and `A(t) ≤ q(t) ≤ B(t)`. If `t < x`,
division reverses them and `B(t) ≤ q(t) ≤ A(t)`. Thus on both sides,

\[
\min(A(t),B(t))\leq q(t)\leq\max(A(t),B(t)).
\]

Differentiability of `u` gives `Δu/(t−x) → u′`. Continuity of `n` gives `n(t) → n(x)`, so
both `A(t)` and `B(t)` converge to `n(x) · u′`. Their minimum and maximum have the same
limit, and the squeeze theorem proves the asserted derivative.

The Lean proof follows this bilateral argument using
[`hasDerivAt_iff_tendsto_slope`](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/Calculus/Deriv/Slope.lean)
and the
[order squeeze theorem](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Topology/Order/Basic.lean).
Its use of minimum and maximum is what handles negative difference quotients without a
one-sided differentiability assumption.

## The angular gauge is `C¹`

Apply the preceding theorem to the unit direction `u`, the continuous radial supporting
covectors, and `f = g`. Contact was established above, and domination by the gauge gives all
cross-support inequalities. Since

\[
u'(\theta)=(-\sin\theta,\cos\theta),
\]

we obtain the exact derivative

\[
\boxed{g'(\theta)=n(\theta)\cdot(-\sin\theta,\cos\theta).}
\]

The right-hand side is continuous: `n` is continuous, sine and cosine are continuous, and the
coordinate dot product is a sum of products. Consequently `g` is `C¹` by the
[`contDiff_one_iff_deriv` criterion](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/Calculus/ContDiff/Deriv.lean).
The source exports the derivative as `hasDerivAt_radialGauge_of_support` and the `C¹` result
as `radialGauge_contDiff_of_support`.

## Regularity and positive orientation of the boundary

Because `g(θ)` is positive everywhere, its reciprocal is `C¹`. Multiplication by the smooth
unit direction gives a `C¹` radial boundary curve. Its derivative is

\[
b'(\theta)=\frac{u'(\theta)}{g(\theta)}
-\frac{g'(\theta)}{g(\theta)^2}u(\theta).
\]

Bilinearity of the determinant gives

\[
\begin{aligned}
\det(b,b')
&=\frac{1}{g^2}\det(u,u')
 -\frac{g'}{g^3}\det(u,u)\\
&=\frac{1}{g^2},
\end{aligned}
\]

using `det(u,u) = 0` and
`det(u,u′) = cos² θ + sin² θ = 1`. Positivity of the gauge makes this determinant strictly
positive. In particular `b′` cannot be zero. The existing radial boundary and coverage
lemmas give the remaining image condition in `IsPositiveBoundaryParam`.

`rein_bd_det2_deriv_of_support` records the determinant identity before specializing to
unique supporting lines. The exports `rein_bd_det2_deriv_of_unique_support` and
`rein_bd_det2_deriv_of_isWorstDisk` remove the explicit supporting family from the theorem
hypotheses.

## Why an actual worst disk satisfies the hypotheses

[Upstream Lemma 2.2.5](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Reinhardt.lean)
proves that each worst lattice-packing disk has a unique supporting line at every boundary
point. Upstream `ch2_isWorstLatticeDisk_iff_isWorstDisk` identifies the relevant worst-disk
predicates, and `rein_good_of_worst` packages the geometric consequences. The final theorem
uses these results to obtain its support hypotheses from `IsWorstDisk K` itself.

Together with `BoundaryTrace.lean`, this supplies all inputs to
[`lemma2_4_2`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Boundary.lean)
for a normalized worst disk: the concrete six traces are continuous, form normalized
multi-points, lie on the boundary, and trace `0` equals the now-regular positive curve
`rein_bd K`. The downstream construction can therefore obtain regular positive `C¹` curves
for all six indices. A common arclength change of parameter is the subsequent input to the
upstream global Lipschitz-derivative theorem.

## Source and validation status

The implementation uses the pinned polygon revision
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f` and mathlib revision
`9d581dfff2e41de989072ea63abf3daf69311520`. The support-family input is proved in the adjacent `SupportNormal.lean`
module, and the new slope, gauge, derivative, and parametrization declarations all have
proof bodies.

Validation is source review and the hand proof above. Lean compilation, Lake builds,
kernel checking, and CI were **not run**. This module supplies the initial analytic
parametrization step in G2; it does not assert a candidate density lower bound or global
octagon minimality.
