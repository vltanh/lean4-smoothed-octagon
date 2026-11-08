# Every selected minimizer window is eligible, and a cheaper splice is geometric

Date: 2026-11-07. This is the P0 hand audit for the fixed five-template
route. No Lean source, compilation, Lake command, typechecking, or CI is
part of this note.

## Conclusion and dependencies

The window restrictions in `BOUNDED_REDUCTION.md`, including the radial
sector restriction **after left normalization**, do apply to an actual
global minimizer. A finite strict-star replacement with the same frame
and state at its two ends gives a genuine cheaper geometric competitor.
In particular, no winding or sector condition on the replacement needs
to be silently assumed.

The proof below makes those assertions precise. It uses the published
finite bang-bang theorem, the established geometric normalization of
actual worst disks, and the usual balanced-disk characterization. These
are named mathematical inputs, not claims that the repository's
corresponding Lean drafts have been validated.

This audit proves **no** local cost improvement. L1--L5 remain separate
analytic obligations. It also does not re-prove all algebraic identities
in the retained through-five comparison; Section 6 checks that its
quantifiers and equality conclusion have the scope needed after a
uniform bound.

## 1. The precise published finite reduction

Hales--Vajjha, *Packings of Smoothed Polygons* (2024),
[Theorem 16.3.1](https://arxiv.org/html/2405.04331v1#Ch16.S3), states that a
global minimizer of the Reinhardt optimal control problem is bang-bang
with finitely many switches. The same theorem identifies the geometric
minimizer as a finite-sided polygon with its corners rounded by the
specified hyperbolic arcs.

This theorem includes the exclusions needed here. Its proof invokes the
edge-extremal result and finite switching away from the singular locus,
excludes positive intervals on the singular locus, and excludes
finite-time accumulation there using the periodic boundary conditions.
It would be incorrect to replace it by only the finite-switching result
away from the singular locus. We use the final theorem, including its
treatment of that locus. Isolated exceptional control values have no
effect on an integral trajectory and may be assigned arbitrarily.

Thus, after deleting zero-duration pieces and merging equal neighboring
controls, the normalized minimizer has a finite positive vertex word.
The theorem supplies no numerical upper bound on its length.

The geometric starting point is an actual worst centrally symmetric
convex disk, normalized to a balanced circle representation. Write its
contact curves as

\[
\sigma_j(t)=g(t)s_j^*,\qquad
 g(0)=I,\quad g(t+T)=g(t)R,
\quad X(t+T)=R^{-1}X(t)R.
\]

Here the six contacts traverse the boundary once over `6T`, `det X=1`,
and `g'=gX`. The exact cost is its normalized area. These are the
geometric and control facts in the book's Sections 2.4 and 3.1--3.6,
also spelled out in `ADMISSIBLE_REALIZATION.md`. The octagon competitor
gives

\[
C\leq A_{\rm oct}<\pi. \tag{1}
\]

The strict last inequality is the explicit octagon formula, not the
conjectural claim that the octagon is minimal.

The terminal conjugation used here is the one derived in Sections 3.5,
4.5 and 6.6: `X(T)=R^{-1}X(0)R`. The last sentence of Problem 3.6.2
prints the opposite conjugation. The pinned
[control definition](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch3/ControlProblem.lean)
explicitly records and corrects this misprint. The global initial state
is free; its value is fixed when replacing any selected window.

## 2. Twisted rebasing and a six-piece interval within one period

Extend the trajectory by

\[
G(t+T)=G(t)R,\qquad Y(t+T)=R^{-1}Y(t)R,
\qquad i(t+T)=i(t)+1\pmod3. \tag{2}
\]

At a cut `s`, set

\[
\widehat g(t)=G(s)^{-1}G(s+t),\qquad
\widehat X(t)=Y(s+t). \tag{3}
\]

Then `g-hat(0)=I`, `g-hat(T)=R`, and the twisted endpoint condition for
`X-hat` holds. The frame equation is left invariant; the state equation
is unaffected by left multiplication of the frame. Since `J` commutes
with `R`, the cost density has period `T`, so rebasing preserves the
whole-period cost. Formula (2), rather than an untwisted repeated word,
is essential.

Cyclic relabeling is implemented by an actual conjugation. For `C=R^r`,
replace `(g,X)` by `(C^{-1}gC,C^{-1}XC)` and control label `i` by
`i+r` modulo three. Since `Cv_j=v_{j+r}` and `det C=1`, its sector
test at `j` is the old test at `j+r`. The cost is unchanged because
the original cost matrix commutes with `R`. Both local endpoints are
conjugated together; the initial identity and global terminal rotation
are preserved. No local terminal frame is set equal to `R` by this step.

Merge equal controls across the twisted seam as well as in the interior,
and choose the cut at a genuine switch. If `N` is the resulting number
of positive pieces per period, the consecutive switch signs are
`N`-periodic even though the labels are only periodic up to the `+1`
shift. For `N>=6`, any block of six consecutive pieces occupies an
interval of duration `tau<=T` after a rebase at its first switch. When
`N=6`, it occupies exactly a whole period. For `N>6`, its duration is
strictly less than `T`. No second copy of a shorter-period arc is used.

The old forward-alternation variation uses a local interval with fixed
initial state and both final endpoints preserved. Its derivation is
independent of the frame before the window. It therefore applies to
(3), including cuts that cross the old seam. The positive uniform star
margin on its compact interval and the exact two-constraint implicit
function argument justify the small replacement; time is free.
Consequently the `+-+` exclusion required by the sign-run coverage
argument survives this rebase. See `FORWARD_ALTERNATION_EXCLUSION.md`,
Sections 1--5, for its actual constrained-Hessian calculation.

## 3. Eligibility, including the normalized radial sectors

### Window eligibility lemma

Take any six positive consecutive pieces of a normalized actual
minimizer with `N>=6`, and rebase at the first piece as in (3). In the
triangular coordinates of `BOUNDED_REDUCTION.md`, the resulting window
satisfies **every** condition in its Section 4:

1. Its initial margins have the chart `p=(a,b,(4-ab)/(a+b))`, where
   `a>0`, `b>0`, `ab<4`.
2. Each of its six factors is greater than one, and all seven
   switching states are strictly in the star domain.
3. Its normalized cost is at most `delta_oct`.
4. Every normalized contact lies in the stated sector, with the stated
   strict interior inequalities.

#### Proof of the state and cost clauses

The traceless determinant-one state has positive margins and obeys

\[
p_0p_1+p_1p_2+p_2p_0=4.
\]

Solving for `p_2` gives the asserted chart. Left normalization changes
`g` only, so it does not change `X` or any margin. On a vertex piece the
active margin `A` is positive and constant. Its duration `t>0` gives
`q=exp(2t/A)>1`. The exact transitions are

\[
(A,B,C)\longmapsto
\bigl(A,(A+B)q-A,(A+C)/q-A\bigr).
\]

The decreasing margin reaches its minimum at the final endpoint; the
other two margins are constant or increasing. Hence the full-arc star
tests are precisely the endpoint tests recorded in the reduction.
There is no extra interior minimum to exclude.

The normalized cost density is `(p_0+p_1+p_2)/4>0`. A window of duration
at most one period therefore has cost at most the whole-period cost,
and (1) gives the required sublevel inequality. This argument permits
arbitrary unequal positive durations and arbitrary initial state.

#### Proof of the sector clause

Let `K` be the actual normalized convex disk in the coordinates being
used, and apply the linear map `G(s)^{-1}` to the **whole disk**. The
image `K_s` is still a convex disk with the origin in its interior.
Its initial six contacts are now `v_j`, and their successors are
`v_(j+1)`, since

\[
G(s)^{-1}G(s)v_j=v_j,\qquad
G(s)^{-1}G(s+T)v_j=Rv_j=v_{j+1}. \tag{4}
\]

A convex disk with the origin in its interior intersects every ray in
exactly one boundary point. Its positively oriented boundary therefore
has a strictly ordered radial traversal. The transformed contact
`g-hat(t)v_j` follows the boundary arc from `v_j` to `v_(j+1)` over
`0<=t<=T`; it does not pass the latter contact earlier. Linear
normalization has not substituted an unrelated angular comparison:
it has transformed the disk, the two end rays, and the traversed arc
together.

Use the oriented bracket `[v,w]=-det(v,w)` in triangular coordinates.
Then `[v_j,v_(j+1)]=1`. The angular gap of these adjacent rays is less
than a half turn. Every point of the open boundary arc between them
is strictly in their radial cone. Consequently

\[
[v_j,\widehat g(t)v_j]>0,\qquad
[\widehat g(t)v_j,v_{j+1}]>0\quad(0<t<T). \tag{5}
\]

At `t=0` the first bracket is zero and the second is one. At `t=T`
the second is zero and the first is one. Restricting (5) to the chosen
window `0<=t<=tau<=T` proves exactly the inequalities used in the
reduction. A proper window has both brackets positive at its final
endpoint. A whole-period window is allowed to reach the successor ray
there. Cyclic relabeling permutes these six identical tests. This proves
the lemma.

The advertised finite test has the required scope. On each piece,
the frame increment is

\[
I+\frac A4\bigl((r-r^{-1})X-(r+r^{-1}-2)XD_i\bigr),
\qquad 1\le r\le q.
\]

Every bracket in (5) is a Laurent polynomial in `r` with degrees
between `-1` and `1`. Multiplication by `r>0` yields a quadratic.
Endpoint and interior-vertex tests, together with the stated strictness
requirements, cover the complete interval. No sample mesh is used.

## 4. Exact endpoint data and the splice

Fix the initial state `X_0` and normalize the initial frame to `I`. For
a word and its factors let

\[
F=\prod_{k=1}^m T_{i_k}(q_k),\qquad
H=Q_{i_m}(q_m)\cdots Q_{i_1}(q_1),\qquad
X_e=HX_0H^{-1}.
\]

The products have opposite orders because one evolves the tangent
matrix on the right and the other conjugates the state on the left.
Writing `V=gX`, integration gives

\[
V_e=X_0F,\qquad g_e=X_0F X_e^{-1}. \tag{6}
\]

Thus equal `(F,X_e)` with fixed `X_0` means equal final `(g,X)`, and
conversely. A local word is not required to have `F=R`.

Suppose an eligible window of duration `tau` is replaced by a finite
strict-star trajectory of duration `tau_new>0`, with the same initial
and final `(g,X)` and smaller cost. Undo its initial left normalization,
retain the prefix of the original trajectory, and translate the suffix
in time by `tau_new-tau`. At both joins, the frame and state agree.
The two one-sided frame derivatives agree as well, because each is
the same product `gX`. The joined state is continuous and piecewise
smooth; its derivatives are bounded on finitely many compact pieces.
It is Lipschitz, the frame is `C^1`, and the a.e. state equations glue
to the integral equations by integral additivity. Changing a control
at finitely many joins has no effect.

The terminal time is positive and free. Both global terminal conditions
remain exactly the original ones, and cost additivity gives a strict
decrease. The replacement does not need to match the old physical
duration or either old state derivative. Those are not admissible
endpoint constraints.

## 5. Why the new closed trajectory is a genuine disk

This section verifies the reverse geometric bridge for the finite-piece
competitors actually used by L1--L5. It avoids treating a matrix endpoint
as an unproved assertion that the curve winds only once.

Return temporarily to ordinary orientation and the standard rotation
`R` by `pi/3`. Let `(g,X)` be the spliced closed trajectory. Its cost
`C_new` is less than `A_oct`, hence less than `pi`. Extend it globally by
(2). Endpoint matching makes the extension `C^1` with Lipschitz state.
For each contact `gamma_j=g s_j^*`, the star condition gives

\[
\det(\gamma_j,\gamma_j')>0. \tag{7}
\]

The control state equation gives nonnegative a.e. signed curvature.
One can check this directly: put `P=Z_u/tr(Z_u X)`. For traceless
two-by-two matrices, `PX+XP=tr(PX)I=I`, while `X^2=-I`; hence

\[
g''=g(X^2+X')=-2gXP.
\]

Since `det(gX)=1`, the contact curvature sign is that of
`-2 det(s_j^*,Z_u s_j^*)/tr(Z_u X)`. The determinant in its numerator
is the appropriate nonnegative simplex coordinate, and the trace
denominator is negative. This proves the required sign on every
smooth piece, hence almost everywhere. Continuity of `g'` prevents
any extra corner at a join.

Write `g=[[p,q],[r,s]]` and take the reflected first row
`d=(p,-q)`. For `X=[[a,b],[c,-a]]`, define

\[
Q_X(z_0,z_1)=-b z_0^2-2a z_0z_1+c z_1^2.
\]

The determinant and star conditions give `c>0` and

\[
cQ_X(z)=(cz_1-az_0)^2+z_0^2,
\qquad
Q_X(z)+Q_X(-z_1,z_0)=(c-b)|z|^2.
\]

Thus the continuous angular lift `theta_d`, initially zero, satisfies

\[
0<\theta_d'\le c-b,
\qquad \frac32\theta_d(T)\le C_{\rm new}<\pi.
\]

The endpoint matrix yields `theta_d(T)=pi/3+2pi n`. Positivity and the
upper bound force `n=0`. The twisted extension rotates this row by
`pi/3` on each successive cell, so `theta_d(6T)=2pi`.

The first contact is `gamma=(p,r)`. It can never be an opposite
positive multiple of `d`: such a relation would give `p=0`, `r=hq`
with `h>0`, and `det g=-h q^2<=0`. The continuous angle difference
`theta_gamma-theta_d` starts at zero and therefore cannot reach `pi`.
At `6T`, periodicity and (7) give

\[
\theta_\gamma(6T)=2\pi m>0,
\qquad \theta_\gamma(6T)<3\pi.
\]

Hence `m=1`. By (7) the angular lift is strictly increasing, so the
contact is a simple radial traversal of one full turn.

For completeness, nonnegative curvature now implies convexity without
an additional winding assumption. Let `phi` be the continuous tangent
angle. By (7), its angle from the radial direction lies in `(0,pi)`.
This angle gap is periodic, so `phi` also advances by exactly `2pi`
over `6T`. Its a.e. derivative is nonnegative by the curvature sign.
For a fixed initial tangent, the signed distance of the curve from
its oriented tangent line first increases while the tangent advances
through a half turn, then decreases back to zero during the second
half turn. It is therefore nonnegative throughout. Every tangent
line supports the curve on the same side, proving that its radial
hull is convex. Compactness, positive radial minimum, and
`gamma(t+3T)=-gamma(t)` give a centrally symmetric convex disk with
nonempty interior.

The determinant-one frame preserves the multi-point identities and
the star conditions. The balanced-disk characterization in
[Hales--Vajjha, Section 2.4.3](https://arxiv.org/html/2405.04331v1#Ch2.S4.SS3)
then supplies the balanced disk and its density normalization. The area
identity can also be seen directly from Green's formula:

\[
\begin{aligned}
\operatorname{area}(K_{\rm new})
 &=\frac12\sum_{j=0}^5\int_0^T
       \det(s_j^*,X(t)s_j^*)\,dt\\
 &=-\frac32\int_0^T\operatorname{tr}(JX(t))\,dt
   =C_{\rm new}.
\end{aligned}
\]

The middle equality uses `sum_j s_j^*(s_j^*)^t=3I`. Consequently
`delta(K_new)=C_new/sqrt(12)`, strictly below the original minimum.
This is the desired contradiction. The argument establishes why
replacement-sector tests are unnecessary; it does not silently drop
the sector condition on **input** minimizer windows.

## 6. Scope of the final through-five and equality step

The retained through-five statements quantify over all admissible
positive vertex factors and their initial states, not merely over
equal-duration regular polygons. They have the scope needed here:

- The fixed-edge/rebasing argument rules out fewer than four pieces
  and reduces the four-piece word to `0120` up to cyclic relabeling.
- `FOUR_LINK_HAND_PROOF.md` proves its asymmetric minimum and gives
  equality only when all four factors are `sqrt(2)` with the stated
  forced initial state. Explicit constant-control uniqueness identifies
  the resulting normalized octagon curve.
- `FIVE_ARC_PROGRESS.md` classifies the seven surviving five-letter
  words into a description that rebases and merges to four pieces,
  the `01020` orbit, or the reverse `02102` orbit. The two genuine
  five-piece comparisons are strict, so neither creates an additional
  equality case.

Rebasing acts on the disk by an invertible linear map; cyclic relabeling
is a rotation of the contact labels. If every minimizer could be shown
to have `N<=5`, the four-piece equality statement would therefore
classify its balanced normalization as a linear image of the octagon.
Undoing the initial normalization gives affine rigidity of the original
centrally symmetric disk. This is the required equality transfer; no
claim that equality in area alone determines an arbitrary trajectory
is being inserted.

### Explicit identification with the concrete octagon

The equality data give a useful direct check. Relabel to the four-piece
word `2012` and put `N=2sqrt(2)-1`. In the rational basis of the
four-link proof, the initial state and active margins are

\[
X_0=\begin{pmatrix}0&-\sqrt N\\1/\sqrt N&0\end{pmatrix},
\qquad a_i=\frac2{\sqrt N}.
\]

All factors are `sqrt(2)`, so each physical duration is
`log(2)/(2sqrt(N))`. Undoing `B=diag(1,sqrt(3))` gives
`Phi(0,sqrt(N/3))`. These are exactly `y_0(1)`, `tsw(1)` and the
control sequence of the pinned concrete octagon. Successive uniqueness
of the smooth vertex flows identifies the entire frame and state on
`[0,tf(1)]`; this is also the statement of
[`polygon_trajectory_unique`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch7/SmoothedPolygon.lean).

For the conditional rigidity conclusion, retain the actual realization
of each arbitrary worst disk `K`; the finite-vertex theorem changes its
control only on a null set, not its boundary. If `e` is its initial
normalization, `s` is the rebase cut and `C=R^r` is the relabeling, the
classified frame is

\[
\widehat g(t)=C^{-1}G(s)^{-1}G(s+t)C.
\]

The six contact arcs over `[0,T]` give its complete boundary by the
cyclic contact relation. Their equality with the octagon arcs therefore
gives `C^{-1}G(s)^{-1}eK=K_oct`: both compact convex disks are radial
hulls of those boundaries. Explicitly,

\[
K=e^{-1}G(s)C(K_{\rm oct}).
\]

The displayed map is nonsingular and linear, which is the required
affine equivalence in the centered disk class. No unrelated equal-cost
minimizer is substituted in this argument.

## Audit boundary

The precise minimizer-window eligibility lemma and finite-piece splice
bridge above discharge the P0 scope questions for the stated route,
using the published reduction and the retained comparison certificates.
There is no sector-rebasing obstruction and no missing winding condition
in that implication. This conclusion is at the level of hand mathematics.

The universal local improvement inequalities remain unproved. Their
truth, full-domain rank degeneracies, and stationary variations are
not consequences of this audit. The uniform bound `N<=5`, unrestricted
minimality, affine rigidity, and Lean/kernel validation remain open.

An independent premises audit agreed on the finite-source, twisted-rebase,
sector, and splice implications. A separate equality review checked the
forced four-piece state, physical times, trajectory identification, and
explicit linear map above. These reviews found no additional premise gap;
they do not re-audit every retained comparison identity or prove a local gate.

### Source entry points

- [Hales--Vajjha (2024)](https://arxiv.org/html/2405.04331v1),
  Sections 2.4, 3.1--3.6 and Theorem 16.3.1.
- `ADMISSIBLE_REALIZATION.md`, `LOW_COST_WINDING.md`,
  `REVERSE_GEOMETRY.md`, and `REVERSE_COMPARISON.md` for the existing
  geometric/control constructions and their separate validation boundary.
- `VERTEX_WORD_REDUCTION.md` and `FORWARD_ALTERNATION_EXCLUSION.md`
  for the actual twist and local forward-alternation certificate.
- `BOUNDED_REDUCTION.md`, Sections 4--5, for the exact local domain
  and endpoint map audited here.
- `FOUR_LINK_HAND_PROOF.md`, `FIVE_ARC_PROGRESS.md`, and
  `REVERSE_FIVE_ARC.md` for the retained terminal comparisons.
