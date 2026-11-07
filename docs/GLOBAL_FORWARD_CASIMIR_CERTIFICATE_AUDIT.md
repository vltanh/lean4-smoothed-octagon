# Independent audit of the forward completion certificate

Date: 2026-11-07 UTC. Independent mathematical and exact-source review.
No Lean, Lake, typechecking, or CI.

**Status:** F is closed at the hand-proof and exact rational-certificate
level, relative to the imported global interfaces listed below. The
prerequisite linear-budget and neighbor-contraction checkers have both
been independently replayed successfully. The broad circular exclusion
has an exact hand proof and supplementary algebra checker. The full
complementary-domain source and mathematical interface were independently
reviewed before its successful exact replay; the resulting complete
cover and exit counts have now been checked against that unchanged
source. This is not a Lean compilation or kernel-checking claim.

## 1. Dependency order and global scope

The reviewed implication chain is:

1. The actual finite competitive all-forward period has the true twisted
   state/frame and costate seam, free-initial-state normal transversality,
   and a single normalized primary costate.
2. All-forward state coordinates give `N=3k+1`. Therefore the case `N>=6`
   has `N>=7`, and the five retained consecutive minimum-window indices
   are distinct.
3. The established minimum bounds are `4/3<a^2<20/11`; thus
   `11/5<U=4/a^2<3`. All neighboring margins are at least `a`.
4. The global cost bound and negative elliptic costate give the
   normalized Casimir cap `gamma^2<23/125`. The conversion is
   `kappa^2=det Lambda_1=12 gamma^2`, with physical normal multiplier
   `lambda=-1`. The acute-pairing theorem gives `E=16e>0`.
5. The scalar seven-entry lower bound gives the linear neighbor budget.
   That budget and the actual exterior switching floors give the
   neighbor contraction `z,w<5/4`.
6. The centered three-stationarity system determines `u,v,E` from the
   five variables `(U,z,w,h,k)` away from the circular base. The broad
   circular lemma covers a neighborhood of that base. The remaining
   interval certificate must exclude its compact complement.

This chain is acyclic. In particular, the linear budget and neighbor
contraction use no conclusion of the final Casimir certificate, and the
broad circular lemma uses only the actual stationarity equations and
`u,v>=3/4`, without a cost budget.

The three-stationarity system is a necessary condition for an actual
whole period. Its multiplier is the transported actual normal covector.
An exclusion of this larger necessary-condition domain does not require
a constructed competitor, a change in the frame endpoint, or a
constrained-index theorem. No local three-arc window is being asserted to
close by itself.

This review checks the stated core interfaces and new certificates. It
does not independently reconstruct the imported geometric correspondence,
compact-state theorem, or every earlier global-normality argument.

## 2. Five-margin and cost-model normalization

The physical rows in
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md)
are exactly `a` times the dimensionless rows of
[GLOBAL_FORWARD_CENTERED_SYSTEM](GLOBAL_FORWARD_CENTERED_SYSTEM.md).
The central variables are

\[
u=8d_{-1},\quad v=8d_0,\quad E=16e_0,
\qquad
\gamma^2=\frac{(a^2+4)^2}{256}(4uv-E^2)
=\frac{(1+U)^2}{16U^2}(4uv-E^2).
\]

The same Jacobi recurrence reconstructs both outer pairings and norms.
Substituting them in the two outer normal stationarity identities gives
exactly the two rows used by the checker. The missing-control inequalities
at the actual exterior switches give the two displayed floors, including
equality at a third-control tie.

The minimum and strict-star conditions are correctly encoded by

\[
1\le z,w<U,\qquad
\frac{(1+z)^2}{z^2+U}\le h<1+\frac1z,
\qquad
\frac{(1+w)^2}{w^2+U}\le k<1+\frac1w.
\]

The identities `p/a=h(z^2+U)/(1+z)-z` and its right reflection recover
the original exterior margins. In particular, `1<h,k<2` follows for
actual positive windows.

The seven-entry scalar lower bound also has the correct count. Lower
all other entries of the `N`-cycle to `a`, using positivity of every
cyclic action partial derivative on the positive orthant. This retains
six edges joining `(a,p,b,a,c,d_ext,a)` and `(N-6)G(a,a)`. Since
`N>=7` and `G(a,a)>0`, the seven-entry cyclic expression is a lower
bound on the full physical cost. No interpolation is asserted to retain
PMP or frame closure. Scaling by `a=2/sqrt(U)` gives the factor
`sqrt(12)/(2U)` used in the five-parameter model.

## 3. Independent review of the linear budget

The proof in [GLOBAL_FORWARD_LINEAR_BUDGET](GLOBAL_FORWARD_LINEAR_BUDGET.md)
uses the correct edge monotonicity and ordinary concavity in the neighbor
margin. At fixed sum `z+w=5(U-1)/3`, the smallest two-edge sum occurs at
`(1,(5U-8)/3)` or its reflection. This comparison remains inside
`1<=z,w<=U` throughout `11/5<=U<=3`.

Both logarithm arguments are at least one. Replacing them by the stated
upper rational bound therefore lowers the edge cost. The denominator
has positive factors, the three quadratic discriminants are negative,
and all twelve coefficients after the interval substitution are strictly
positive. The final comparison multiplies an already positive expression
by the valid lower bound `sqrt(3)>173/100`.

An independent run of
[global_forward_completion_linear_budget.py](../explorations/global_forward_completion_linear_budget.py)
passed its exact denominator, degree, coefficient, endpoint,
discriminant, and constant checks.

## 4. Independent review and replay of the neighbor contraction

The residual and rational approximation in
[GLOBAL_FORWARD_NEIGHBOR_CONTRACTION](GLOBAL_FORWARD_NEIGHBOR_CONTRACTION.md)
have the required signs. The linear budget itself implies

\[
w\le(5U-8)/3<U\quad(U\le3),\qquad z\le w<U.
\]

Thus the positivity of the first stationary row and the monotonicity of
the minimum exterior factor remain valid on the stated closed comparison
domain, even though its statement does not repeat the star inequalities.
The actual second exterior floor is bounded below by its value at the
minimum permitted factor. Both rational floor approximants are lower
bounds, and the coefficients multiplying their negatives are nonnegative.

The four-variable exact checker was independently compiled and replayed.
It returned precisely:

| Check | Independent result |
|---|---:|
| Processed nodes | 8183 |
| Empty-domain leaves | 6 |
| Negative Taylor-bound leaves | 4086 |
| Unprocessed boxes | 0 |
| Depth-limit boxes | 0 |
| Maximum depth | 20 |

This matches the claimed deterministic replay. Its source, rational
approximants, contractions, outward arithmetic and Taylor operations
were reviewed independently; the replay is not the only basis of this
assessment.

## 5. Full complementary-domain formulas

The full checker is
[global_forward_completion_casimir_certificate.cpp](../explorations/global_forward_completion_casimir_certificate.cpp).
Its centered expressions match the exact identities in the centered
system note. In particular, the algebraically equivalent stable choices

\[
e_0=\frac34+\frac{d(K+2)}{8K},\qquad
c_x=-\frac32x-\frac{dS(K+2)}{4K}
\]

are correct, as are their reflected expressions. The code's `excess`
is exactly `gamma^2-23/125`, including its constant `7/2000`.

The actual cubic function `f` is enclosed by fourteen positive-series
terms plus the rigorous tail beginning at exponent 31. It uses the
correct analytic first and second derivatives in its jet; derivatives
of a finite approximation are not substituted for those of `f`.

The floor routine has a different, intentional role: it is a fixed
rational *lower bound* on `F_x(h)-3/4`, using ten terms of the positive
series for `f(h)/(h-1)`. Its value, gradient and Hessian all refer to that
same rational lower bound. The code therefore distinguishes actual
analytic functions from one-sided rational relaxations correctly.

The first five returned quantities must be nonnegative at every actual
candidate: the two centered row residuals after subtracting lower norm
floors, the two reconstructed norm excesses, and `E`. The last sign test
requires `excess>0`, contradicting the actual strict Casimir cap.

The positive outer determinant is evaluated on the whole box and must
have a strictly positive interval lower endpoint before reconstruction
is used. The code never substitutes an actual-domain-only denominator
bound into a Taylor enclosure on a larger rectangle. All component
functions are smooth on the boxes on which a Taylor test succeeds.

## 6. Cover, contractions, and singular limits

The exact initial roots cover the complement of the central cube with
`eta=1/32`:

- `U<=3-eta`, with both neighbors in `[1,5/4]`;
- `U>=3-eta` and `z>=1+eta`, with `w` in `[1,5/4]`;
- `U>=3-eta`, `z<=1+eta` and `w>=1+eta`.

Their shared boundary faces are retained. The omitted cube satisfies
`(3-U)+(z-1)+(w-1)<=3/32<3/20`, so the broad hand lemma applies uniformly
in `h,k`. Its explicit nondegeneracy condition is satisfied by every
actual positive window. The completely zero-duration central base has
an algebraic covector fibre and is correctly excluded from the hand
lemma's quantifiers.

Ordering `z<=w` is an algebraic symmetry of the necessary-condition
system: reflect the exterior factors and exchange `u,v`. It does not
assert that the physical time-reversed path is a new PMP trajectory.

Every contraction is necessary on the retained domain. In particular,
`S^2/(z^2+U)` increases with `z` and decreases with `U`; on the full
rectangular domain `z<=5/4<11/5<=U`, so that monotonicity needs no
unstated conditional assumption. Replacing strict budget, factor and
star inequalities by weak inequalities enlarges the domain. Zero-factor
boundary faces and weak third-control ties are therefore retained rather
than discarded by strictness.

## 7. Review of the exact interval engine

Both checkers use arbitrary-size GMP integer/rational arithmetic. The
80-bit dyadic grid controls expression growth; it is not floating-point
proof arithmetic. Each rounded lower endpoint uses exact integer floor,
and each rounded upper endpoint uses exact integer ceiling.

I checked addition, subtraction, all four endpoint products, reciprocal
intervals, and squares including an interval crossing zero. Reciprocal
and analytic-function failures cause subdivision, never an exclusion.
The automatic gradient and Hessian rules use the correct two product
cross-terms and unary chain rule.

For the second-order Taylor enclosure about the exact rational midpoint,
centered coordinate squares lie in `[0,r_i^2]`, whereas off-diagonal
products lie in `[-r_i r_j,r_i r_j]`. The factor `1/2` and both symmetric
Hessian entries are retained. The entire box is convex and the Hessian
bounds cover every segment used in Taylor's formula. Intersecting this
bound with direct interval evaluation is valid.

The deterministic bisection preserves both closed halves. A nonempty
stack or a depth-limit box causes failure. A denominator problem cannot
be silently counted as a successful leaf. The only floating arithmetic
in the reviewed sources prints elapsed wall time.

## 8. Completion status and reviewed source versions

The prerequisite independent replays and the full source/derivation
review are complete, with no mathematical or arithmetic defect found.
The full complementary-domain checker then exited successfully with the
following exact branch counts, independently compared with its source:

| Check | Completed exact replay |
|---|---:|
| Initial root boxes | 3 |
| Processed nodes | 20999 |
| First row/floor residual negative, reason 10 | 5436 leaves |
| Second row/floor residual negative, reason 11 | 995 leaves |
| Reconstructed right norm below its floor, reason 13 | 65 leaves |
| Casimir excess strictly positive, reason 20 | 4005 leaves |
| Total certified leaves | 10501 |
| Unprocessed boxes | 0 |
| Depth-limit boxes | 0 |
| Maximum depth | 23 |

The full binary-forest identity is exact:
`20999 = 2*10501 - 3`. There are no unreported leaf reasons, discarded
nonempty boxes, unresolved singular boxes, or remaining stack entries.
The source hash below is unchanged from the pre-replay independent
review. The replay printed its explicit `PASS` result after checking the
empty stack and zero depth-limit count. Its elapsed time was 998.89
seconds; elapsed time has no role in the proof.

The independently reviewed source, successful complete replay, broad
circular hand lemma, and preceding necessary-condition reductions
therefore establish the stated F exclusion. The full replay itself was
performed once by the parent worker; this audit independently reviewed
the source, domain cover, interfaces, output counts and completion,
rather than claiming a second full replay.

Reviewed SHA-256 source identifiers:

- Neighbor checker:
  `f01101766e0712271fbed5902703c38c896527203d0fce6f8cc3524b664da01f`.
- Full Casimir checker:
  `ff891cf53948eda3e2a77d135e2d9b75012930814f8aae154bd70ab61cb719d0`.

These identify the reviewed implementations; a later source change
requires reviewing the affected operations and refreshing this record.
