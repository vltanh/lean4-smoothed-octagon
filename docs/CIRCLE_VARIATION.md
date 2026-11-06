# Exact local improvement of a circular subarc

## Status and the competitor class excluded

This is a **hand proof**, not a new Lean development. It proves that a normalized
cyclic balanced disk with a nonempty circle-state interval can be replaced by
another centrally symmetric convex disk with strictly smaller greatest packing
density. The deformation is constructed, its geometric constraints are checked,
and its area decrease is exact. No admissibility condition for the perturbed
curve is left as an assumption.

The exclusion of singular circular subarcs is a **known result**, Hales–Vajjha,
[*Packings of Smoothed Polygons*, Theorem 8.2.7](https://arxiv.org/html/2405.04331v1#Ch8.S2).
The calculation below specializes their variation to obtain an exact hyperbolic
formula and supplies the periodic splice and geometric checks explicitly.
This does not prove the unrestricted octagon comparison, affine uniqueness,
finite switching, or a bound on the number of polygon sides.

The precise excluded case is an interval on which the normalized matrix state
is `X = J`. It describes a multi-curve of circular arcs after one fixed
area-preserving linear change of coordinates. An isolated visit to `J`, a short
nearby trajectory, and a chattering trajectory accumulating there are different
cases and are not excluded merely by this result.

No Lean file for this variation was created. Lean compilation, Lake, kernel
validation, CI, and numerical or symbolic computation were not run.

## 1. Starting geometry and the local improvement statement

Write

\[
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
Q(t)=\begin{pmatrix}\cos t&-\sin t\\\sin t&\cos t\end{pmatrix},
\qquad R=Q(\pi/3),
\]

and let `s_j`, for `j` modulo six, be the six unit vectors at angles `jπ/3`.
Use the established cyclic balanced representation of a normalized disk `K`:

\[
g:\mathbb R\longrightarrow\mathrm{SL}_2(\mathbb R),\quad
g(0)=I,\quad g(t+T)=g(t)R,\quad
\sigma_j(t)=g(t)s_j,\qquad T>0.
\]

The frame is `C¹` with locally Lipschitz derivative. The six contact curves
have the common boundary of `K` as their image, each once over `[0,6T)`.
They obey the strict star condition and have nonnegative signed curvature
almost everywhere. Their midpoint determinants are normalized to `√3/2`.
These are the existing balanced representation hypotheses, not extra
regularity imposed on a candidate control.

Put `X(t)=g(t)⁻¹g′(t)`. Suppose that

\[
X(t)=J\quad\text{on a nonempty open interval }U\subset(0,T).
\]

We will construct, for every sufficiently small nonzero real `ε`, a new cyclic
balanced disk `K_ε` with

\[
\boxed{\displaystyle
\operatorname{area}(K_\varepsilon)
=\operatorname{area}(K)
-3\int_a^b\sinh^2(\varepsilon\chi(t))\,dt
<\operatorname{area}(K).}
\tag{1}
\]

Here `[a,b]` is a closed nondegenerate interval strictly inside `U`, and `χ` is
any nonzero smooth function with compact support strictly inside `(a,b)`.
Both disks have greatest packing density equal to their area divided by
`√12`, so (1) gives a strict density improvement. In particular, a disk of
globally least greatest packing density cannot contain such an interval.

## 2. Normalize the circular piece and choose an actual bump

On `U`, the equation is `g′=gJ`. Differentiating `g(t)Q(-t)` gives zero, so it
is constant on every interval contained in `U`. Thus, for `a≤t≤b`,

\[
g(t)=A Q(t-a),\qquad A=g(a),\quad\det A=1.
\tag{2}
\]

This argument needs only the original `C¹` regularity. Formula (2) then shows
that the frame is smooth on the circular piece. No second derivative of the
original frame is assumed away from that piece.

For a concrete bump, choose `a<c<d<b` and set

\[
\chi(t)=
\begin{cases}
\exp\!\left(-\dfrac1{(t-c)(d-t)}\right),&c<t<d,\\
0,&\text{otherwise}.
\end{cases}
\]

This function is smooth, is positive on `(c,d)`, and has support `[c,d]`.
All derivatives vanish at `c,d`: each one-sided derivative is a finite sum
of a rational function times the displayed exponential, and exponential
decay dominates every pole at the endpoints. In particular, `χ` is
identically zero on neighborhoods of `a,b`, and also near `0,T`.

The vanishing on neighborhoods matters. Merely prescribing `χ(a)=χ(b)=0`
would match frame values but would not by itself match derivatives.

## 3. The explicit hyperbolic deformation

For `θ=t-a`, define

\[
K(\theta)=
\begin{pmatrix}
\cos\theta&-\sin\theta\\
-\sin\theta&-\cos\theta
\end{pmatrix},\qquad
r(t)=\varepsilon\chi(t),
\]

\[
\Psi_\varepsilon(t)
=\cosh r(t)\,I+\sinh r(t)\,K(\theta).
\tag{3}
\]

Everything is defined by elementary scalar functions. No matrix exponential
existence or differentiation result is needed. Direct multiplication gives

\[
K^2=I,\quad KK'=J,\quad K''=-K,\quad
\operatorname{tr}(JK)=\operatorname{tr}(JK')=0,
\quad J^2=-I.
\tag{4}
\]

Since `K` has trace zero and determinant `-1`,

\[
\det\Psi_\varepsilon=\cosh^2r-\sinh^2r=1,
\qquad
\Psi_\varepsilon^{-1}=\cosh r\,I-\sinh r\,K.
\tag{5}
\]

Write `C=cosh r` and `S=sinh r`. Differentiating (3) and using (4) yields

\[
\Psi_\varepsilon^{-1}\Psi_\varepsilon'
=r'K+CSK'-S^2J.
\tag{6}
\]

Consequently,

\[
\boxed{\displaystyle
\operatorname{tr}\!\left(J\Psi_\varepsilon^{-1}
\Psi_\varepsilon'\right)=2\sinh^2r.}
\tag{7}
\]

This is an exact identity. In particular, there is no unspecified remainder
whose sign must be controlled.

On `[a,b]`, replace the frame by

\[
g_\varepsilon(t)=A\Psi_\varepsilon(t)Q(t-a).
\tag{8}
\]

Using `Q′=QJ` and the commutation of `Q` with `J`, the new logarithmic
derivative `Y_ε=g_ε⁻¹g_ε′` satisfies

\[
Y_\varepsilon
=J+Q^{-1}(\Psi_\varepsilon^{-1}\Psi_\varepsilon')Q,
\]

\[
\boxed{\displaystyle
-\frac32\operatorname{tr}(JY_\varepsilon)
=3-3\sinh^2(\varepsilon\chi(t)).}
\tag{9}
\]

The left constant matrix `A` cancels from this calculation. The ordinary
trace of `Y_ε` is zero; (7) and (9) concern the pairing `tr(JY_ε)`.
In general `det Y_ε` is not one. We will compare geometric areas directly,
so no change of time variable or control-admissibility assertion is needed.

## 4. Splice the perturbation with the correct cyclic symmetry

On the base time cell `[0,T]`, set

\[
E_\varepsilon(t)=A\Psi_\varepsilon(t)A^{-1}.
\]

Extend this matrix function with period `T` to the whole real line. It is
smooth across the cell joins because it is identically `I` on neighborhoods
of both ends of the base cell. Define the global perturbed frame by

\[
G_\varepsilon(t)=E_\varepsilon(t)g(t).
\tag{10}
\]

From now on let `Y_ε=G_ε⁻¹G_ε′` denote its global logarithmic derivative;
on `[a,b]` it agrees with the expression in Section 3.

On the chosen circular interval this is exactly (8). Elsewhere in the base
cell it equals `g`. The construction gives, without an approximation,

\[
\det G_\varepsilon(t)=1,\quad G_\varepsilon(0)=I,
\quad G_\varepsilon(t+T)=G_\varepsilon(t)R.
\tag{11}
\]

In particular `G_ε` has full period `6T`, and

\[
G_\varepsilon(t+3T)=-G_\varepsilon(t).
\tag{12}
\]

On a translated circular piece the explicit formula is

\[
G_\varepsilon(t+nT)
=A\Psi_\varepsilon(t)Q(t-a)R^n
\quad(a\le t\le b).
\tag{13}
\]

Thus the perturbations on the six contact pieces are related by the required
contact permutation; they are not six independently chosen replacements.

The original frame is `C¹,¹` on a full period. Multiplication by the smooth
periodic `E_ε` preserves this property: the derivative is `E_ε′g+E_εg′`,
and each product is Lipschitz on the compact period interval. Values and
first derivatives agree at its endpoints. Repetition therefore gives the
required global Lipschitz bounds for the contact derivatives.

## 5. The geometric inequalities survive for a definite small parameter

Set `σ_j^ε(t)=G_ε(t)s_j`. Since every `G_ε(t)` has determinant one, the
multi-point identities hold exactly:

\[
\sigma_j^\varepsilon+\sigma_{j+2}^\varepsilon+
\sigma_{j+4}^\varepsilon=0,\quad
\sigma_{j+3}^\varepsilon=-\sigma_j^\varepsilon,\quad
\det(\sigma_j^\varepsilon,\sigma_{j+1}^\varepsilon)=\sqrt3/2.
\tag{14}
\]

Only the six compact pieces `[a+nT,b+nT]` in one full period can change.
On each such piece the unperturbed contacts are `A Q(t-a)R^n s_j`.
Because `det A=1` and the vectors `R^n s_j` have unit length, at `ε=0`

\[
\det(\sigma_j,\sigma_j')=1,
\qquad \det(\sigma_j',\sigma_j'')=1.
\tag{15}
\]

The star decomposition there is

\[
\sigma_j'
=\frac1{\sqrt3}(\sigma_{j+1}-\sigma_j)
+\frac1{\sqrt3}\sigma_{j+1}.
\tag{16}
\]

All the entries of (13), and their first two time derivatives, depend
continuously on `(ε,t)`. The star coefficients are continuous as well:
they solve a two-by-two linear system whose determinant has the fixed
nonzero magnitude `√3/2` by (14).

The index sets are finite and `[a,b]` is compact. Therefore there is a
single `ε₀>0` such that whenever `|ε|<ε₀`, on all changed pieces and for
all six contacts:

- `det(σ_j^ε,(σ_j^ε)′)>0`, so angular motion is strictly positive.
- `det((σ_j^ε)′,(σ_j^ε)″)>0`.
- Both star coefficients are strictly positive.

This is a uniform compactness argument with a positive baseline margin,
not a pointwise choice of parameters. Outside these pieces the contacts
are unchanged. Hence angular positivity and the strict star condition
hold everywhere, while nonnegative curvature holds almost everywhere on
the full curve. The contacts remain regular because angular positivity
rules out a zero derivative. The construction imposes no smoothness on
the original curve away from the circular pieces.

## 6. Simplicity, convexity, and the common boundary are conclusions

There are no missing global embedding assumptions in the perturbation.
For every real `s`, the matrices `G_s(t)` are invertible. Thus

\[
(s,t)\longmapsto G_s(t)s_0
\]

is a homotopy of nonvanishing closed curves between the original boundary
and the perturbed one. Its winding number about the origin is unchanged:
it is one. For `|ε|<ε₀`, the polar-angle derivative of `σ_0^ε` is positive
everywhere. Its continuous angle lift therefore increases strictly by
exactly `2π` over `[0,6T]`. Every ray is met exactly once per half-open
period, and two different parameters in `[0,6T)` cannot give the same
point. This proves simplicity and the radial graph property.

Let `K_ε` be the radial region bounded by this curve. The radius is a
continuous positive function of the polar angle, so this region is compact,
has the origin in its interior, and has boundary exactly the curve.

It is convex. One standard form of the planar curvature criterion says
that a simple regular `C¹` closed curve with Lipschitz tangent and
nonnegative signed curvature almost everywhere bounds a convex region.
Indeed, its lifted tangent angle is locally absolutely continuous; its
derivative is the signed curvature numerator divided by squared speed.
It is therefore nondecreasing. The turning number of a positively
oriented simple closed curve is one, so the tangent angle makes exactly
one turn, and each tangent line supports the enclosed region. This proves
convexity. The pinned upstream `IsStarCurve.convex_radialHull` provides
precisely this criterion in the regularity class used here.

Equation (12) gives central symmetry of `K_ε`. Equation (11) and
`Rs_j=s_{j+1}` give

\[
\sigma_j^\varepsilon(t+T)=\sigma_{j+1}^\varepsilon(t).
\tag{17}
\]

Consequently all six contacts are translates in time of `σ_0^ε`. They have
the same boundary image and are each simple over the common period `6T`.
Together with (14), the regularity and curvature checks, and the star
condition, this verifies every balanced-pair requirement. Their initial
values remain the sixth roots because `G_ε(0)=I`.

## 7. Exact area and density comparison

The area identity does not require `det Y_ε=1`. To see this directly,
split the full boundary integral into six cyclic pieces and use (17):

\[
\begin{aligned}
\operatorname{area}(K_\varepsilon)
&=\frac12\int_0^{6T}
 \det(\sigma_0^\varepsilon,(\sigma_0^\varepsilon)')\,dt\\
&=\frac12\int_0^T\sum_{j=0}^5
 \det(G_\varepsilon s_j,G_\varepsilon' s_j)\,dt\\
&=\frac12\int_0^T\sum_{j=0}^5\det(s_j,Y_\varepsilon s_j)\,dt.
\end{aligned}
\]

The six unit vectors satisfy `Σ_j s_j s_jᵀ=3I`, and
`det(v,w)=-vᵀJw`. Hence the last line is

\[
-\frac32\int_0^T\operatorname{tr}(JY_\varepsilon(t))\,dt.
\tag{18}
\]

Outside `[a,b]` in this base period the frame and its derivative are
unchanged. On `[a,b]`, (9) gives exactly (1). The integral in (1) is
strictly positive for nonzero `ε`: at a point where `χ≠0`, its integrand
is positive, and continuity makes it positive on a nondegenerate interval.

The normalized balanced density theorem gives

\[
\delta(K_\varepsilon)
=\frac{\operatorname{area}(K_\varepsilon)}{\sqrt{12}}
=\delta(K)-\frac3{\sqrt{12}}
  \int_a^b\sinh^2(\varepsilon\chi(t))\,dt
<\delta(K).
\tag{19}
\]

This is an actual geometric competitor. It contradicts global least
greatest packing density. The known normalized representation of an
actual worst disk makes the exclusion applicable to that disk. Through
the established geometric/control comparison it also excludes a circle-state
interval in a full control minimizer. If a Pontryagin lift is present,
the zero-reduced-costate interval rigidity gives `X=J`, so a full-control
singular subarc is excluded as well. No inference from a nonunique
maximizing edge to a full-control singular arc is used.

## 8. Quantitative content and its limits near the circle

### A fixed bump has a definite quadratic deficit

Let `I₂=∫_a^b χ(t)² dt>0`. For `|ε|‖χ‖∞≤1`, the elementary inequalities
`|x|≤|sinh x|≤e|x|` give

\[
3\varepsilon^2 I_2
\le\operatorname{area}(K)-\operatorname{area}(K_\varepsilon)
\le3e^2\varepsilon^2 I_2.
\tag{20}
\]

For a fixed interval and bump, this is a useful explicit deficit. The
area second derivative at zero is `-6I₂`; the exact formula contains
only even powers of `ε` and provides more than a signed asymptotic term.

### A sufficient perturbation scale for short supports

Use the Euclidean operator norm and put `M_k=‖χ^(k)‖∞`, for `k=0,1,2`.
From (3), when `|ε|M₀≤1`,

\[
\begin{aligned}
\|\Psi_\varepsilon-I\|_\infty
&\le e|\varepsilon|M_0,\\
\|\Psi_\varepsilon'\|_\infty
&\le e|\varepsilon|(M_0+M_1),\\
\|\Psi_\varepsilon''\|_\infty
&\le e\bigl(|\varepsilon|(M_0+2M_1+M_2)
             +\varepsilon^2M_1^2\bigr).
\end{aligned}
\tag{21}
\]

These follow by differentiating (3), using
`‖K‖=‖K′‖=‖K″‖=1`, and bounding `cosh|r|+sinh|r|` by `e`.
They make the smallness required in Section 5 explicit in terms of the
bump's derivative bounds.

For a fixed nonzero smooth bump `ψ` supported in `(-1,1)`, take

\[
\chi_\delta(t)=\psi((t-t_0)/\delta),\qquad
\varepsilon=c\delta^2,\qquad 0<\delta\le1.
\]

The three bounds in (21) are bounded by expressions tending to zero
with `c`, uniformly in `δ`. For example the last is at most

\[
e\bigl(c(\|\psi\|_\infty+2\|\psi'\|_\infty+
\|\psi''\|_\infty)+c^2\|\psi'\|_\infty^2\bigr).
\]

Thus one fixed sufficiently small `c>0` makes this family feasible on
any contained circular support interval. But its guaranteed area gain
is proportional to `δ⁵`, because

\[
\varepsilon^2\int\chi_\delta^2
=c^2\delta^5\int_{-1}^1\psi^2.
\tag{22}
\]

This describes a safe family of perturbations, not an assertion that
the best possible perturbation always has that order.

There is also a more general obstruction to a uniform local deficit.
A circular interval of length `ℓ` contributes `3ℓ` to (18). A
star-preserving replacement has positive cost density: for a traceless
raw state `[[a,b],[c,-a]]`, the star inequalities give `c>0`, `3b+c<0`,
and therefore `-(3/2)tr(JX)=(3/2)(c-b)>0`. Any improvement supported in
that interval is consequently less than `3ℓ`. As `ℓ→0`, no such local
construction can supply a positive absolute improvement independent
of interval length. This does not rule out a different global estimate.

### An explicit comparison for a nearby frame

The exact identity also measures how much closeness is sufficient for
the cost sign, separately from geometric feasibility. On the chosen
interval write `H=A⁻¹g` and `B=Ψ_ε⁻¹Ψ_ε′`. Left multiplication by
`AΨ_εA⁻¹` changes the cost by the negative of

\[
D(g)=\frac32\int_a^b
\operatorname{tr}\!\left((H J H^{-1})B\right)dt.
\]

For the circular frame, `H=Q(t-a)` and `D(g)=3∫sinh²(εχ)`. If

\[
\eta=\sup_{[a,b]}\|H J H^{-1}-J\|,
\]

then the two-dimensional bound `|tr(UV)|≤2‖U‖‖V‖` gives

\[
\left|D(g)-3\int_a^b\sinh^2(\varepsilon\chi)dt\right|
\le3\eta\int_a^b\|B(t)\|dt.
\tag{23}
\]

Thus the cost still decreases whenever

\[
\eta\int_a^b\|B\|dt
<\int_a^b\sinh^2(\varepsilon\chi)dt,
\tag{24}
\]

provided the perturbed curves also satisfy the separately checked star
and curvature constraints. On a fixed interval a sufficiently small
`C²` neighborhood of the circular frame supplies those positive margins.
Closeness of the state `X` to `J` alone does not control the curvature,
which also involves its derivative.

In the shrinking family above, `∫‖B‖=O(δ²)` while the right side of
(24) is comparable to `δ⁵`. A sufficient closeness threshold therefore
shrinks on the order of `δ³`. This local perturbation argument yields a
quantitative test but supplies no uniform neighborhood excluding all
near-circle trajectories, and no unrestricted octagon lower bound.
The separate [whole-trajectory tube bound](NEAR_CIRCLE_BOUND.md) uses a
global endpoint and cost argument to exclude trajectories that stay in a
specified tube for their entire duration. That is a different hypothesis
from a short near-circle subarc and does not conflict with the shrinking
local improvement described here.

## Sources and relation to the current proof obligations

- Hales–Vajjha, [§8.2, especially Theorems 8.2.3, 8.2.6, and 8.2.7](https://arxiv.org/html/2405.04331v1#Ch8.S2):
  the singular-state identification and the published exclusion by variation.
  The conclusion excluded here is already known; it is not new closure of
  Reinhardt's conjecture.
- Pinned upstream [balanced and state definitions](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean).
- Pinned upstream [convexity criterion](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/Basic/Analysis/Convex/StarCurveConvex.lean),
  `IsStarCurve.convex_radialHull`.
- Pinned upstream [area identity](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch3/AreaFormula.lean),
  `eqn_cost`; its hypotheses do not impose `det X = 1`.
- Pinned upstream [balanced packing-density identity](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/BalancedDensity.lean),
  `greatestPackingDensity_of_isBalancedPair`.

For the former G3e singular-arc obligation, this is the substantive local
comparison: a proper circular subarc yields a fully checked geometric
competitor. It does not require construction of a new normalized control.
The unrestricted comparison among noncircular competitors, including
arbitrary switching patterns, remains a separate mathematical task.
