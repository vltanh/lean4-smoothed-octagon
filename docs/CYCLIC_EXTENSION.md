# Extending an arbitrary admissible segment to global cyclic geometry

[`SmoothedOctagon/CyclicExtension.lean`](../SmoothedOctagon/CyclicExtension.lean)
starts from the actual integral-form `IsReinhardtAdmissible` definition and
constructs global frame and state curves. It joins six rotated copies of the
original segment and repeats them periodically. Values, derivatives, Lipschitz
regularity, and almost-everywhere curvature are proved across the joins.

**Validation: not run.** The file contains source-level Lean proof bodies and the
hand argument below. Lean compilation, Lake commands, kernel validation, and CI
have not been run. The module introduces no axiom, `sorry`, or `admit`.

## Input and output

The sole hypothesis of
`exists_cyclic_extension_of_isReinhardtAdmissible` is

```lean
h : IsReinhardtAdmissible T u g X
```

Thus `u` is merely measurable, the two state equations are given in integral
form on `[0,T]`, and the terminal conditions are

\[
g(0)=I,\qquad g(T)=R,\qquad X(T)=R^{-1}X(0)R.
\]

The theorem constructs global curves `G,Y : ℝ → Mat2` with:

- `G(t) = g(t)` and `Y(t) = X(t)` for every `t ∈ [0,T]`, including both endpoints.
- Every entry of `G` is `C¹`; `Y` is continuous and globally Lipschitz entry by entry.
- `det G(t) = 1`, `IsStarState (Y t)`, and `G′(t) = G(t)Y(t)` for every real `t`.
- `G(0) = I`, `G(t+T) = G(t)R`, and `Y(t+T) = R⁻¹Y(t)R` globally.
- `G` has full period `6T`.
- All six contact curves `G(t)sⱼ*` have nonnegative curvature almost everywhere.
- `reinhardtCost T Y = reinhardtCost T X` exactly.

The construction does not assume that a contact curve is simple or that its
radial hull is convex. Those are subsequent geometric reconstruction obligations.
It also does not extend the control as an additional output. The global frame,
state, and curvature conclusions are the data used for reconstruction.

## Interval regularity comes from admissibility

The input curves may be arbitrary outside `[0,T]`. The construction uses their
values only inside that interval. Before extending them, it invokes
[`AdmissibleRegularity.lean`](../SmoothedOctagon/AdmissibleRegularity.lean).

The two integral equations imply continuity of `g` and `X` on the closed
interval. The control simplex is compact, and the continuous star-state path
stays in the strict domain where the denominator in `controlP` is nonzero.
Consequently the state right-hand side is uniformly bounded, even though the
control need not be continuous. Its integral equation gives a Lipschitz bound
for `X`.

The product `gX` is continuous, so the frame integral equation gives a classical
derivative `g′ = gX` at every interior point, with the corresponding within-set
derivative at the endpoints. The state equation holds almost everywhere.
The upstream algebraic curvature identity then supplies the contact curvature
inequalities almost everywhere in `(0,T)`.

No additional assumption on the measurable control is introduced in this step.

## The finite-copy construction

The upstream generic function `poly_pw A B T f` is

\[
f_{A,B}(t)=A^n f(t-nT)B^n,
\qquad n=\lfloor t/T\rfloor_{\mathbb N},
\]

on nonnegative time. If `f(T) = A f(0) B`, the formulas on neighboring cells
agree at the shared endpoint. The upstream lemma `poly_pw_of_mem_Icc` therefore
provides the cell formula on a closed cell, including its right endpoint.

The new generic definition is

\[
\operatorname{cyclicMatrixExtension}(A,B,T,f)(t)
  = f_{A,B}(\operatorname{red}_{6T}(t)),
\]

where `red₆T(t) = t − floor(t/(6T))·6T` lies in `[0,6T)`.

When `A⁶ = B⁶ = I`, the finite-copy function has period `6T` on nonnegative
time. Its periodic extension therefore agrees with it there. The one-cell
identity extends to all real times:

\[
F(t+T)=A F(t)B.
\]

The actual frame and state are the specializations

\[
G=\operatorname{cyclicMatrixExtension}(I,R,T,g),
\qquad
Y=\operatorname{cyclicMatrixExtension}(R^{-1},R,T,X).
\]

The identities `R⁶ = I` and `(R⁻¹)⁶ = I` are proved upstream. This construction
uses natural matrix powers on a finite set of cells. It does not require an
integer-power representation of singular or otherwise arbitrary matrices.

## Matching values and derivatives at the joins

The admissible terminal equations are precisely the required value matches:

\[
g(T)=g(0)R,\qquad X(T)=R^{-1}X(0)R.
\]

For the frame velocity `v(t) = g(t)X(t)`, they also imply

\[
\begin{aligned}
v(T)
 &=R\bigl(R^{-1}X(0)R\bigr)\\
 &=X(0)R\\
 &=v(0)R.
\end{aligned}
\]

Thus the velocity matches with exactly the same twist as the frame. The
extension of `v` is continuous, including at the joins.

The theorem `cyclicMatrixExtension_hasDerivAt` uses the upstream integral gluing
lemma `poly_pw_isIntegralCurve` on `[0,NT]` for arbitrarily large natural `N`.
The joined frame is the integral of the joined continuous velocity. The
fundamental theorem of calculus then gives its derivative at every positive
time, including the internal cell endpoints. Periodicity transfers this
derivative statement to every real time.

On each cell, the algebraic cancellation

\[
g(r)R^n\bigl(R^{-n}X(r)R^n\bigr)
  =g(r)X(r)R^n
\]

identifies that extended velocity with `GY`. Hence `G′ = GY` everywhere. Both
factors are continuous, so each entry of `G′` is continuous and `G` is `C¹`.

This argument establishes the derivative at the seams. It does not simply
discard them as a countable exceptional set in the final classical frame
equation.

## Global Lipschitz regularity of the state

Each state cell is a translate of `X` followed by left and right multiplication
by fixed matrices. Its entries are finite linear combinations of the original
entries, so they are Lipschitz on that closed cell.

For adjacent intervals `[a,b]` and `[b,c]`, a single continuous scalar function
with Lipschitz constants `L₁,L₂` on the two intervals is Lipschitz on their union.
For points on opposite sides of `b`, use

\[
|f(x)-f(y)|\le |f(x)-f(b)|+|f(b)-f(y)|.
\]

Both terms are bounded with the common constant `L₁ + L₂`, and
`|x-b| + |b-y| = |x-y|` when `x ≤ b ≤ y`. Induction gives a finite Lipschitz
constant on any finite collection of cells. Closed-cell endpoint matching is
essential in this argument.

The source applies the induction to twelve cells, covering two full periods
`[0,12T]`. The periodic-extension helper
`lipschitzOnEntrywise_univ_of_periodic` then gives a global entrywise Lipschitz
bound for `Y`. Its proof translates nearby arguments into the two-period
interval and uses boundedness for arguments farther apart.

## Determinant and star constraints

Every argument used to evaluate the original `g` or `X` lies in `[0,T]`. Since
`det g = 1` there and `det R = 1`, every frame cell has determinant one.

The state in cell `n` is `R⁻ⁿX(r)Rⁿ`. The upstream lemma
`poly_isStarState_conj_pow` proves that this conjugation preserves all the
normalized star-state conditions. Therefore the global state remains a star
state at every real time, including the joins.

## Almost-everywhere curvature across all cells

The frame shift implies the contact shift

\[
\sigma_j(t+T)=\sigma_{j+1}(t),
\qquad \sigma_j(t)=G(t)s_j^*.
\]

Translation in the domain commutes with Lean's totalized derivative operator.
Applying this twice gives the same shift for both the first and second
derivatives, without requiring differentiability at the exceptional points.

Consequently the proposition

\[
p(t):\quad
\text{for every }j,\quad
\det(\sigma'_j(t),\sigma''_j(t))\ge0
\]

has period `T`: the shift only permutes the six indices. On `(0,T)`, the extended
contacts agree locally with the original contacts, so both derivatives agree
there and the original almost-everywhere curvature result applies.

The theorem `ae_of_periodic_ae_on_Ioo` now transfers this local assertion to the
whole real line. For each integer `n`, translation invariance of Lebesgue
measure gives the corresponding assertion at `t − nT`. A countable intersection
allows all integer translates simultaneously. Outside the countable grid
`{nT : n ∈ ℤ}`, the representative `t − floor(t/T)T` lies in the open interval
`(0,T)`. Periodicity of `p` completes the proof.

The construction never assumes that the original state equation has only
countably many exceptional points. Its arbitrary null set is transported by
measure-preserving translations; only the separate join grid is countable.

## Exact agreement and cost

The closed-cell formula with cell index zero gives

\[
G(t)=g(t),\qquad Y(t)=X(t)\qquad(0\le t\le T).
\]

Thus the original state, its terminal values, and the integrand defining the
Reinhardt cost are preserved on the complete integration interval. The final
cost equality follows by pointwise congruence of the interval integral. No
change of variables or inequality is involved.

## Main declarations

| Declaration | Result |
| --- | --- |
| `cyclicMatrixExtension` | Explicit six-copy periodic construction |
| `cyclicMatrixExtension_eqOn` | Agreement on the original closed cell |
| `cyclicMatrixExtension_shift` | Global twisted one-cell shift |
| `cyclicMatrixExtension_continuous` | Continuity through all joins |
| `cyclicMatrixExtension_hasDerivAt` | Global derivative from matching continuous velocity |
| `cyclicMatrixExtension_lipschitz` | Global entrywise Lipschitz regularity |
| `ae_of_periodic_ae_on_Ioo` | Periodic almost-everywhere transport |
| `contactCurvature_ae_of_cyclic_shift` | Global all-contact curvature from one open cell |
| `exists_cyclic_extension_of_isReinhardtAdmissible` | Complete construction from an actual admissible segment |

The global smooth-arc hypotheses of `LowCostWinding.lean` can now be supplied
from an actual admissible segment. With the additional cost bound, that module
rules out extra winding. The subsequent `ReverseGeometry.lean` construction
uses the resulting winding and the global curvature inequalities to address
simplicity and convexity.

## Pinned sources

The upstream polygon dependency is pinned at
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`.

- [Defs.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean)
  and [ControlProblem.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch3/ControlProblem.lean):
  the integral trajectory and actual admissibility definitions.
- [DiscreteK.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch7/DiscreteK.lean):
  `poly_pw`, its closed-cell and continuity lemmas, `poly_pw_isIntegralCurve`,
  rotation cancellations, and preservation of star states by rotation powers.
- [SmoothedPolygonDisk.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch7/SmoothedPolygonDisk.lean):
  `oct_red`, `oct_ext_eq`, positive-time shifts, and the sixth-power rotation identities.
- [MatrixFTC.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/Basic/Analysis/Calculus/MatrixFTC.lean):
  differentiation of the matrix integral equation at an interior continuity point.
- [AdmissibleRegularity.lean](../SmoothedOctagon/AdmissibleRegularity.lean):
  the actual interval continuity, state Lipschitz bound, frame derivative, and
  almost-everywhere contact curvature.
- [ControlTrajectory.lean](../SmoothedOctagon/ControlTrajectory.lean):
  the global Lipschitz extension of a periodic matrix curve from two periods.

The following Mathlib APIs were inspected at the resolved pin
`9d581dfff2e41de989072ea63abf3daf69311520`:

- [MeasureTheory/Group/Measure.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/MeasureTheory/Group/Measure.lean):
  `measurePreserving_add_right`, generated by the additive version of the
  corresponding right-multiplication theorem.
- [QuasiMeasurePreserving.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/MeasureTheory/Measure/QuasiMeasurePreserving.lean):
  `QuasiMeasurePreserving.ae`.
- [Deriv/Shift.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/Calculus/Deriv/Shift.lean):
  `deriv_comp_add_const`, including its validity without a differentiability hypothesis.
- [Deriv/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/Calculus/Deriv/Basic.lean):
  local equality of first and second derivatives through `Filter.EventuallyEq.deriv`.
- [Algebra/Ring/Periodic.lean](https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Algebra/Ring/Periodic.lean):
  `Function.Periodic.sub_int_mul_eq`.
