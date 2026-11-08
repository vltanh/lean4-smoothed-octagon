# Reconstructing the balanced disk of a low-cost cyclic frame

`SmoothedOctagon/ReverseGeometry.lean` constructs a centrally symmetric convex disk
from a global cyclic smooth frame satisfying the star and curvature conditions.
It proves simplicity and convexity instead of assuming a boundary parametrization.
The construction is the geometric part of the low-cost reverse comparison.

**Validation: not run.** This is source-level Lean with the hand proof below. Lean
compilation, Lake commands, kernel validation, and CI have not been run. The module
introduces no axiom, `sorry`, or `admit`.

## Precise input and constructed output

Let `T > 0`. The inputs are a global matrix frame `g` and state `X` with:

- Every entry of `g` is `C¹`, `det g(t) = 1`, and `g(0) = I`.
- `X` is continuous and globally Lipschitz entry by entry.
- `g′(t) = g(t) X(t)` and `IsStarState (X t)` for every real `t`.
- `g(t + T) = g(t) R` for every real `t`.
- Each contact curve `σ_j(t) = g(t) s_j*` has nonnegative signed curvature almost
  everywhere: `det(σ_j′, σ_j″) ≥ 0`.
- The actual Reinhardt cost satisfies `reinhardtCost T X < π`.

The curvature input is an analytic differential constraint on the specified matrix
curves, not an assumption that they already bound a convex disk. A separate cyclic
extension theorem must obtain these global inputs from an integral-admissible
trajectory before the present theorem applies to that whole class.

The constructed set is explicit:

\[
K=\operatorname{radialHull}(\sigma_0,0,6T)
 =\{r\sigma_0(t):0\le t\le6T,\ 0\le r\le1\}.
\]

The theorem `lowCost_cyclicFrame_isBalancedPair` concludes

```lean
IsBalancedPair (cyclicFrameDisk g T) (frameContact g) T ∧
  IsCircleRepresentation (frameContact g)
```

Here `frameContact g j t = g t *ᵥ sixthRoot j`. The conclusion includes convexity,
compactness, nonempty interior, central symmetry, regularity, derivative Lipschitz
bounds, normalized contact determinants, curvature and star conditions, simplicity
on a full period, and the exact frontier image.

## The six contacts and their analytic properties

The cyclic frame identity and the standard contact identity `R s_j* = s_{j+1}*`
give

\[
\sigma_j(t+T)=\sigma_{j+1}(t).
\]

By induction,

\[
g(t+nT)=g(t)R^n,\qquad
\sigma_0(t+nT)=\sigma_n(t).
\]

Since `R⁶ = I`, the frame and each contact curve have full period `6T`. The
normalized determinant-one frame maps the standard six-point configuration to a
multi-point. The star-state inequalities have the concrete meaning

\[
X(t)s_j^*=\alpha_j(t)(s_{j+1}^*-s_j^*)+
 \beta_j(t)s_{j+1}^*,\qquad\alpha_j(t),\beta_j(t)>0.
\]

Multiplying by `g(t)` and using the frame differential equation gives the star
condition for `σ_j′`. Taking the determinant with `σ_j` yields

\[
\det(\sigma_j,\sigma_j')
 =(\alpha_j+\beta_j)\frac{\sqrt3}{2}>0.
\]

Every contact is nonzero and has nonzero derivative. Its continuous lifted polar
angle is therefore strictly increasing. This fact alone does not imply simplicity;
the total angle must still be proved to be one full turn.

## One full turn for the reflected row

Write

\[
g(t)=\begin{pmatrix}p(t)&q(t)\\r(t)&s(t)\end{pmatrix},
\qquad\delta(t)=(p(t),-q(t)).
\]

This is the reflected first row from [LOW_COST_WINDING.md](LOW_COST_WINDING.md).
The low-cost theorem already proves that its lifted angle at `T` is exactly
`π / 3`. Direct multiplication of the frame shift by `R` gives the stronger
geometric identity

\[
\delta(t+T)=R\delta(t).
\]

Viewed as a complex number, this multiplies the curve by `exp(iπ/3)`. The derivative
is multiplied by the same factor, so its logarithmic derivative `z′/z` is
`T`-periodic. Integrating gives the additive lifted-angle formula

\[
\theta_\delta(t+T)=\theta_\delta(t)+\theta_\delta(T).
\]

Repeating it six times proves

\[
\theta_\delta(6T)=6\frac\pi3=2\pi.
\]

No periodic-curve injectivity theorem is used in this argument.

## Transferring winding to the boundary contact

The first contact is the first column,

\[
\gamma(t)=\sigma_0(t)=(p(t),r(t)).
\]

The determinant-one equation prevents `γ(t)` from being an opposite positive
multiple of `δ(t)`. Indeed, if

\[
(p,r)=-c(p,-q),\qquad c>0,
\]

then `(1+c)p=0`, so `p=0`, and `r=cq`. Therefore

\[
\det g=ps-qr=-cq^2\le0,
\]

contrary to `det g=1`.

Both curves begin at `(1,0)`. The logarithmic-integral construction gives continuous
angle lifts `θ_γ` and `θ_δ` beginning at zero, together with their positive radial
factors. If

\[
\theta_\gamma(t)=\theta_\delta(t)+\pi,
\]

exponential reconstruction would give exactly an opposite positive-scalar relation
between the vectors, with scalar

\[
c=\exp\bigl(\operatorname{Re}L_\gamma(t)
 -\operatorname{Re}L_\delta(t)\bigr)>0.
\]

The source proves this contradiction explicitly as
`firstContact_angle_ne_row_add_pi`.

The continuous angle difference begins at zero and cannot reach `π`. The
intermediate value theorem consequently gives

\[
\theta_\gamma(6T)-\theta_\delta(6T)<\pi.
\]

Thus `θ_γ(6T) < 3π`. Periodicity and exponential reconstruction also give

\[
\theta_\gamma(6T)=2\pi n\quad(n\in\mathbb Z).
\]

Strictly positive angular speed and `6T > 0` imply `n > 0`. The upper bound implies
`n < 2`, so `n = 1` and

\[
\boxed{\theta_\gamma(6T)=2\pi.}
\]

This is `lowCost_firstContact_full_angle`. In particular, the proof does not use
simplicity to derive the winding count that will establish simplicity.

## Simplicity, convexity, and the boundary

Suppose two times in `[0,6T)` give the same value of `γ`. Their exponential
representations imply that their lifted angles differ by an integer multiple of
`2π`. If the times are distinct, strict angle growth makes that difference positive.
The angle range on the half-open interval is contained in `[0,2π)`, so the difference
is strictly less than `2π`, a contradiction. The source packages this argument in
`curve_injOn_of_full_angle`.

The curve is now an actual upstream `PlaneCurve.IsStarCurve` with period `6T`.
Its derivative is globally Lipschitz: the normalized state is globally Lipschitz,
the frame is periodic, and `g′=gX`; the previously proved
`frame_velocity_lipschitz_periodic` and fixed-vector matrix action yield the needed
bound for every `σ_j′`.

The upstream theorem `IsStarCurve.convex_radialHull` applies the supplied a.e.
nonnegative curvature and this derivative bound to prove that `K` is convex.
The same star-curve library proves compactness, that the origin lies in the interior,
and

\[
\partial K=\gamma([0,6T)).
\]

The contact shift represents every `σ_j` as a parameter translation of `γ`.
Periodicity transfers simplicity and the full frontier image to every contact.
Finally the multi-point identity gives

\[
\sigma_0(t+3T)=\sigma_3(t)=-\sigma_0(t),
\]

which proves central symmetry of the radial hull. At time zero, `g(0)=I` gives the
standard contact configuration, so the balanced pair is in circle representation.

## Relation to the reverse comparison

The theorem constructs a geometric competitor with all balanced-pair clauses from
the stated global cyclic frame. Upstream `eqn_cost`, using the already proved contact
shift, then identifies its area with the trajectory cost. Upstream
`greatestPackingDensity_of_isBalancedPair` identifies its density with that area
divided by `√12`.

Applying this construction to every low-cost integral-admissible trajectory still
requires the cyclic extension theorem to supply the global frame, regularity,
curvature, and cost-preservation inputs. High-cost trajectories are handled by a
separate explicit geometric competitor. No reverse comparison is asserted merely
from the existence of the forward realization.

## Sources

The upstream dependency is pinned at
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`.

- [StarCurve.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/Basic/Analysis/Convex/StarCurve.lean):
  continuous logarithmic angles, `IsStarCurve`, compactness, interior, and frontier.
- [StarCurveConvex.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/Basic/Analysis/Convex/StarCurveConvex.lean):
  `IsStarCurve.convex_radialHull` from a.e. nonnegative curvature and Lipschitz velocity.
- [SmoothedPolygonDisk.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean):
  general public lemmas `oct_isMultiPoint_mulVec`, `oct_star_mulVec`,
  `oct_det2_pos_of_star`, `oct_injOn_shift`, `oct_image_Ico`, and periodic reduction.
  These lemmas are reused with arbitrary matrix curves; the construction does not
  assume that the curve belongs to the smoothed-polygon candidate family.
- [AreaFormula.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch3/AreaFormula.lean):
  the sixth-root rotation identities and `eqn_cost`.
