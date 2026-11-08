# Lighter polynomial proofs: replacement ledger

This work starts from `main` at
`128a58e456f52fb16768820d564a620fa6313448`. The archived notes are the
source statements; the replacement standard is the user's request of
8 November 2026.

A replacement is accepted here only after its mathematical sign, domain,
caller, and expanded-identity sizes have been checked. A numerical probe
or a large alternative coefficient expansion does not close a row.
The previous archived hand-proof acceptance does not establish that the
requested signs meet this stricter standard. In particular, the S1
generated coefficient tables remain an open hand-proof dependency.

## Already formalized signs, in requested priority order

| Priority | Requested sign | Replacement status |
|---|---|---|
| N1 | `MIXED_NONSHORT_LARGE_GAP_LOW_T_SIGN` (1), `k=1` | **Complete hand caller replacement.** The [new unit sign and caller argument](NONSHORT_LOW_T_CALLER.md) use monotonicity in `h`, three proved faces, and shape monotonicity. The actual low-t branch of `fh_small_gap_j` supplies the new necessary condition through `fh_window_comb`. The old residual's standalone scalar statement is not claimed. Lean integration remains open. |
| N2 | `MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION` (10), `k=1` | **Complete hand replacement.** The [fourth-derivative proof](NONSHORT_LOW_RATIO_LINK.md) closes the original sign using the base quadratic, monotonicity, and factored remainder. The largest expanded identity has 41 monomials and degree eight. Lean integration remains open. |
| N3 | `MIXED_NONSHORT_LARGE_GAP_UPPER_SHAPE_SIGN`, `k=1+j` | **Hand dependency removed** from the actual low-t caller by the [completed N1 replacement](NONSHORT_LOW_T_CALLER.md). The wider old scalar face is not re-proved; its exact caller and changed intermediate premise are explicit. Lean integration remains open. |
| N4a | `MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_EXCLUSION` (13), `k=29t²/4` | **Complete hand replacement on the original domain.** The [h reduction](NONSHORT_HIGH_RATIO_LOWER_REDUCTION.md) and [terminal face](NONSHORT_HIGH_RATIO_LOWER_FACE.md) prove a normalized residual at least `13/4`; norm monotonicity gives the original sign. Lean integration remains open. |
| N4b | The same caller's upper face, `k=1+j` | **Hand dependency removed** by [shape monotonicity](NONSHORT_HIGH_RATIO_SHAPE.md) and the completed N4a lower sign. The original `fh_LGB_core` statement closes with its unchanged necessary-condition premise. Lean integration remains open. |

N4b is a caller-preserving weakening, not a claim on an enlarged face
outside the actual feasible shape interval. The exact caller is
`fh_LGB_core` in `SmoothedOctagon/Exclusion/Mixed/FwdHand/LargeGap.lean`.
Its lower endpoint `hA` is now supplied by the new N4a proof; shape
monotonicity replaces `hB` and `fh_comb_pos_of_ends`. Thus every entry in
the first requested table has a complete hand replacement or an explicit
caller-preserving dependency removal. None has yet been integrated into Lean.

## H-S signs, in requested priority order

| Priority | Gate and note | Replacement status |
|---|---|---|
| S1.1 | `MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN` (16)--(21), Section 5 | Full sign open; first H-S priority. The [actual small-shape branch's `F0` sign](SHORT_OUTER_LOW_SHAPE_TERMINAL.md) is complete. Its `F1` sign and the S/A branches remain open; [beta concavity](SHORT_OUTER_BETA.md) is available for `F1`. |
| S1.2 | `MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN` (20)--(25), Appendices A--C | Open. |
| S1.3 | `MIXED_SMALLER_SHORT_OUTER_SCALE_LARGE_RATIO_SIGN` (7) | Open. |
| S1.4 | `MIXED_SMALLER_SHORT_CENTRAL_TAU_TWO_SIGN` (3) and `MIXED_SMALLER_SHORT_CENTRAL_DURATION_FACES` (5) | Open. |
| S2.1 | `MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_SIGN` (5) | Open. |
| S2.2 | `MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_SIGN` (11)--(18) | Open. |
| S3.1 | `MIXED_SMALLER_SHORT_DISPLACEMENT_OUTER_FACE` (7)--(21) | Open. |
| S3.2 | `MIXED_SMALLER_SHORT_DISPLACEMENT_CENTRAL_FACE`, Section 2 (4)--(10) | Open. |
| S4 | `MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES` (4)--(30) | Open. |
| S6 | `MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION` (20)--(31) | Open. |

These are the finite requested obligations. The three corrections below
are recorded separately and are not counted as polynomial replacements.

## Repaired H-S interfaces

The [errata and explicit proofs](HS_ERRATA.md) repair all three reported
issues in their original notes:

- Root shear: prove `W>0` and `V>0` before asserting `F>0` and `G>0`
  or multiplying by their denominators. The actual shape yields
  `m≥335/19`, `beta*x-alpha≥54/19`, and `Q≥70/19`.
- Cost exclusion: supply the actual outer cap `rho_A<1/7` from the
  reverse-centre scope theorem at the original competitive period.
  The later scalar continuation uses its critical-angle argument.
- Tau-two scale monotonicity: explicitly require
  `u≥3/4+(x-1)²/[28(x+1)²]`; the actual incoming secant supplies this
  hypothesis and the named caller keeps it unchanged during comparison.

The new expanded correction identities have at most six monomials and
degree at most four. The high-ratio endpoint derivative checks have
11, 15, 12 and 5 monomials, in two variables and degree at most six.
All necessary polynomials and the size counts are printed in the notes.
Independent mathematical and exact-algebra reviews accepted the
high-ratio caller reduction and the low-ratio base quadratic; the three
corrections were separately reviewed against their actual domains and
source callers. The N2 collection link is now supplied by four boundary
calculations and a fourth derivative, with differentiation performed before
expansion. Independent reviews checked its source cancellation, all sixteen
boundary polynomial blocks, the thirty-two normalized face comparisons,
and the eight fourth-derivative identities.

## Additional completed reductions

For N1, the new multipliers are `a=7/2-10(q-1)` and
`m=8j+8(q-1)-1/6`. Their actual necessary condition and rational
substitution signs are proved in the [shape note](NONSHORT_LOW_T_SHAPE.md).
Its positive shape derivative reduces both shape endpoints to the unit
shape, whose full sign is now proved by the [caller argument](NONSHORT_LOW_T_CALLER.md).
The [unit-face proof](NONSHORT_LOW_T_UNIT_FACE.md)
closes `h=1/4` using a cubic square completion and four univariate signs.
Every expanded identity in that face proof has at most nine monomials,
degree at most eight, and coefficients of at most twelve digits.
Independent reviews reconstructed the original residuals and checked all
printed coefficient identities and scalar comparisons in both notes.

The [outer-gap unit face](NONSHORT_LOW_T_OUTER_FACE.md) is also complete.
It differentiates its coefficient functions twice before expanding,
then checks their values and first derivatives at `x=1/2`. The seven
second-derivative identities have at most nine monomials and degree eight.
The normalized residual is greater than 10 at `q=1`, and its derivative
in `q` is greater than 500 throughout that face. An independent review
checked the original affine source, all sixteen coefficient polynomials,
the seven derivative identities, the fourteen boundary values, and the
remaining sign comparisons.

The [higher-derivative note](NONSHORT_LOW_T_CURVATURE.md) proves
`H^3 S>0`, positive lower-face second derivatives, and `H^4 S>500000`
on explicit rectangles containing the required comparison segments.
It differentiates the three source products before expanding any
coefficient, and then reduces their signs one variable at a time.
Its largest printed cleared coefficient is 73,815,815,160; the derivative
and sign identities have degree at most seven. An independent review
reconstructed the source and checked all 77 printed polynomials.

The [initial derivative proof](NONSHORT_LOW_T_INITIAL_DERIVATIVE.md)
gives `H S>=68` at `h=1/4` on an enlarged domain containing both the
actual initial face and the outer comparison's base. It first decreases
in `y`, then uses a separate negative directional second derivative
to reduce the resulting line to two scalar endpoints. Every expanded
identity has at most nine monomials and degree eight; the largest
cleared coefficient is 492,759,115,600. The
[completed transport argument](NONSHORT_LOW_T_H_REDUCTION.md) combines
these derivative lemmas through a cubic Taylor lower bound. It uses four
pieces with simple rational endpoints, and proves `H S>0` throughout
the original domain. Its 41 printed sign and derivative polynomials
have at most nine monomials and degree eight.

The [maximum-duration face](NONSHORT_LOW_T_QMAX.md) closes the last
boundary. It proves `P_j>=500 M` through an explicit sum of positive
products, uses the [small auxiliary signs](NONSHORT_LOW_T_QMAX_AUXILIARIES.md),
and obtains `P>39`. The source identity is checked by a sixth derivative
and six boundary jets; the zero-gap value uses a fifth derivative and
scalar jets. Its largest printed sign polynomial has 44 monomials and
degree eight, and every individual expanded coefficient remains within
twelve digits. Independent reviews checked the source, every printed
polynomial, all derivative and boundary identities, and the integral
roundings. The [caller note](NONSHORT_LOW_T_CALLER.md) explicitly replaces
the actual low-t branch's old multiplier call; it does not infer the new
negative residual from the old `fh_LGA_core` hypothesis.

The [N2 base quadratic](NONSHORT_LOW_RATIO.md) is greater than 4 on its
full domain; its three square identities each have 21 monomials and total
degree eight. The [N2 monotonicity proof](NONSHORT_LOW_RATIO_MONOTONICITY.md)
gives derivative lower bounds 3500, 12400 and 5400. The
[N2 remainder proof](NONSHORT_LOW_RATIO_REMAINDER.md) gives
`C3>700`, `C4>3900`, and nonnegative remaining coefficients.
Both latter proofs use explicitly printed univariate factors with at most
nine monomials and degree at most eight. The
[completed link](NONSHORT_LOW_RATIO_LINK.md) combines these ingredients to
prove `Pi>4h^3(1+h)^3+700j^3+3900j^4`, on the original domain and in fact
for all nonnegative `j` with `0<=q-1<=h`. Its eight fourth-derivative
identities have 26, 39, 41, 41, 41, 40, 33 and 24 monomials.
The exact Lean caller is `hA` in `fh_lowRatio_core` in
`SmoothedOctagon/Exclusion/Mixed/FwdHand/LowRatio.lean`; its upper endpoint
`hB` and shape-concavity step can be retained. The new proof replaces the
unit-shape certificate and its large link, without changing the sign or
shrinking its domain.

The two S1 outer reductions preserve the norm dependencies. For the first
residual, beta concavity at fixed norm reduces beta to its two admissible
endpoints, followed by norm concavity. For the second residual on its
low-shape strip, both the uniform-floor curve and the beta-dependent
upper-norm curve decrease in beta. The latter total derivative is less
than `-143/1274880`; freezing that upper norm during beta comparison
would not justify the reduction. The first reduction still leaves four
bivariate terminal signs for `F1`. The second now feeds
[shape monotonicity](SHORT_OUTER_ALPHA_LOW_SHAPE.md) and the
[completed actual B-branch `F0` sign](SHORT_OUTER_LOW_SHAPE_TERMINAL.md).
That proof uses a single split at `x=5/3`, small derivative identities, and
a scalar endpoint enclosure with certified margin `167/144000000`.
Its largest expanded identity has 29 monomials and degree eight.
The narrower conclusion omits extraneous generated-table points with
`a<1` or without the actual cap; the original note's actual branch caller
still closes for its `F0` alternative. The rational comparison has a
thinner endpoint margin than the old bound; its benefit is the small
algebraic verification, not additional slack.

The [shared rational logarithm bound](LOG_BOUND.md) has a seven-monomial,
degree-six derivative identity and a factored curvature proof. Its direct
incoming-norm majorant has 19 monomials and degree five in two variables.
It gives a rigorously bounded error at `x=2` of at most `1/8608908`.
This is a reusable bound, not a completed S1, S3 or S4 replacement.

The [high-ratio lower-shape proof](NONSHORT_HIGH_RATIO_LOWER_REDUCTION.md)
uses the same constant multipliers 4 and 1. It first proves `-H^2 S>30000`
on a rectangle, then proves the initial `-H S>680`, reducing the sign
to `h=1/4`. Its seven second-derivative identities have at most forty
monomials and degree eight. On the [terminal face](NONSHORT_HIGH_RATIO_LOWER_FACE.md),
concavity in `y` leaves a zero face and a line. A 21-monomial, degree-five
ninth derivative controls the line through small scalar jets, with one
split at `x=2/5` and a final tangent bound `S>=13/4`.
Every expanded identity has degree at most eight and coefficients of at
most twelve digits. The source collection includes explicit intermediate
polynomials and an order of operations keeping even the individual
expanded contributions below twelve digits; the largest is 916,895,167,299.
Independent reviews reconstructed the original source and checked all
identities, interval bounds, scalar roundings, and the unchanged caller.

## Validation boundary

Exact rational symbolic calculations check transcription and monomial
counts. The displayed identities and inequalities supply the hand
arguments. No Lean compilation, Lake, typechecking, or CI has been run;
existing Lean proofs, certificate files, and dependency pins are unchanged.
No lower memory or timing measurement is claimed.

The remaining priorities stay open until a complete replacement meets
the requested dimension and size bounds. Smaller coefficients alone,
a sampling result, or a formula defining an unprinted polynomial will
not be used as evidence of closure.
