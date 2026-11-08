# A quantitative certificate for the switching expression

## Result and status

The new result in `SmoothedOctagon/SwitchingMargin.lean` is the exact inequality

\[
\frac{r(r-y)^3}{4(r+y)}\le f(y,r)
\qquad (2\le y\le r\le4),
\]

where **`f` is the existing `SmoothedPolygons.hmaxF`**, imported from the reference
project. In particular,

\[
\boxed{\frac{(r-y)^3}{8}\le f(y,r).}
\]

Thus the certificate is strictly positive away from the diagonal and vanishes on
the diagonal. The hand proof below is complete. The Lean source contains proof
bodies, but **compilation and kernel verification have not been run**.

The reference project's `HMaxInequality.lean` already proves the qualitative
results `hmaxF_nonneg` and `hmaxF_pos` by differentiating in `y`. The contribution
here is a quantitative rational margin and a short, independent scalar proof.
This module imports the original definition from `StrongTransversality.lean`; it
does not import `HMaxInequality.lean` or reuse its derivative argument.

## Source expression

[Hales and Vajjha, *Packings of Smoothed Polygons*, §7.5, proof of Lemma 7.5.3](https://arxiv.org/html/2405.04331v1#S7.SS5)
reduces a switching-function sign condition to the function

\[
\begin{aligned}
f(y,r)={}&2r(y-1)y\log r\\
&-(r-y)\bigl(r(y-1)+y(-5+2y)+y^2\log(4/y)\bigr)\\
&-2r(y-1)y\log y.
\end{aligned}
\]

The reference declaration is
[`SmoothedPolygons.hmaxF`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch7/StrongTransversality.lean).
Its pinned qualitative comparison is
[`HMaxInequality.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch7/HMaxInequality.lean).

The variables in this lemma are scalar coordinates from the source's change of
variables. In particular, this `y` is not the initial upper-half-plane coordinate
`y₀`. The source uses `y = 1 + 3y₀²` and
`r = y exp(√3 y₀ t)` on the specified strong-lift arc.

## Hand proof

Write

\[
d=r-y,\qquad A=y\bigl(y^2+r(y-2)\bigr).
\]

On the triangle, `y` and `r` are positive, and `d` and `A` are nonnegative.
For positive arguments, the elementary logarithm inequalities are

\[
\log u\ge\frac{2(u-1)}{u+1}\quad(u\ge1),
\qquad
\log v\le v-1\quad(v>0).
\]

Apply them to `u = r/y` and `v = 4/r`. This yields two nonnegative residuals:

\[
L=\log(r/y)-\frac{2d}{r+y}\ge0,
\qquad
U=\frac{4-r}{r}-\log(4/r)\ge0.
\]

Define the rational certificate

\[
G=
\frac{d^2(4-r)(r^2+3ry+4y^2)}{4r(r+y)}
+\frac{rd^3}{4(r+y)}.
\]

The exact residual identity is

\[
\boxed{f(y,r)-G=A L+y^2d\,U.}
\]

To check it, first replace `log r − log y` by `log(r/y)` and use
`log(4/y) = log(r/y) + log(4/r)`. The coefficient of `log(r/y)`
is `A`, and the coefficient of `log(4/r)` is `−y²d`. Clearing the
positive denominators `r` and `r + y` reduces the remaining identity to
polynomial algebra. This is exactly the identity written in
`hmaxF_margin_identity`.

The right side is nonnegative, so `G ≤ f(y,r)`. This comparison actually
holds for all `2 ≤ y ≤ r`; no upper bound on `r` is used yet.

When `r ≤ 4`, the first summand of `G` is nonnegative. Discarding it gives

\[
f(y,r)\ge\frac{rd^3}{4(r+y)}.
\]

Since `y ≤ r`, we have `r/(r+y) ≥ 1/2`. Consequently

\[
f(y,r)\ge\frac{d^3}{8}.
\]

If `r > y`, then `d > 0`, so this last quantity is positive. If `r = y`,
substitution in the source definition gives `f(y,y) = 0`. These two cases prove
the exact zero characterization on the triangle.

## Declaration map

| Declaration in namespace `SmoothedOctagon` | Content |
| --- | --- |
| `hmaxF_margin_identity` | Exact two-residual identity for the upstream expression |
| `hmaxF_rational_lower_bound` | Full certificate `G ≤ hmaxF` for `2 ≤ y ≤ r` |
| `hmaxF_cubic_lower_bound` | `r(r-y)³ / (4(r+y)) ≤ hmaxF` on the triangle |
| `hmaxF_uniform_cubic_lower_bound` | `(r-y)³ / 8 ≤ hmaxF` on the triangle |
| `hmaxF_nonneg_from_margin` | Nonnegativity recovered from the quantitative bound |
| `hmaxF_pos_from_margin` | Strict positivity off the diagonal |
| `hmaxF_eq_zero_iff_from_margin` | Complete zero set `r = y` on the triangle |

The private ratio-logarithm lemma uses
`Real.le_log_one_add_of_nonneg`; the upper bound uses
`Real.log_le_sub_one_of_pos`. Both declarations were inspected in
[`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` at `v4.36.0-rc2`](https://github.com/leanprover-community/mathlib4/blob/v4.36.0-rc2/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean).

## What this does and does not settle

The quantitative estimate controls one explicit scalar expression used along
the reference project's strong-lift arcs. The upstream theorem `chi32_eq`
identifies this expression, with a prefactor, with a switching function for those
arcs. This file proves the bound directly on `hmaxF`; it does not claim a new
correspondence theorem for arbitrary trajectories.

The margin approaches zero as `r − y` approaches zero. It supplies no positive
uniform dwell time, no uniform bound on the number of switches or sides, and no
comparison of the total area of arbitrary smoothed polygons with the octagon.
It therefore strengthens a local inequality used by the program without closing
the global Reinhardt conjecture or a global candidate-exclusion gate.

No numerical search, Lean compilation, or CI execution was used for this result.
