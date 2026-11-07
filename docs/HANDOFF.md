# Authoritative handoff — Reinhardt smoothed octagon

**Status (2026-11-07): the unrestricted Reinhardt cost inequality and affine uniqueness are NOT proved.** The research branch is a draft. The accepted current work consists of hand proofs, independent internal mathematical reviews, and supplementary exact algebra/rational checks; no Lean compilation, kernel validation, Lake or CI has been run.

## Immediate handoff: exact next actions

**No full M2 nonshort certificate is recorded as completed in this PR.** An earlier multi-process run or a reported million-plus processed boxes is **not** completion: no branch is excluded until the complete original-root record (or a verified rooted chain) has an empty pending frontier and zero unknown boxes. Do not assume an external process continues after a session ends.

| Gate | Domain / required next actual switch | Acceptance |
| --- | --- | --- |
| M2.0 (DONE) | Smaller turn is short; and separately the nonshort `0<=epsilon<=1/32` corner | Audited short-side 107,977-node cover; hand small-parameter theorem |
| **M2.1-F (OPEN)** | Smaller turn nonshort; next **forward** switch has transported norm `>=3/4` | Completed three-chart cover, original roots or independently verified exact chain |
| **M2.1-R (OPEN)** | Smaller turn nonshort; next **reverse** switch satisfies the extended-turn secant bound | Same complete cover acceptance, independently for branch 1 |
| **M2.1-V / M2.2 (OPEN)** | Independently verify both execution forests; then audit exhaustive whole-period passage | Exact record accounting, mathematical interface, all boundaries |
| **G4 / G5 (OPEN)** | Conditional terminal cost/equality assembly and final audit | Sharp global statement with all premises and trust boundaries identified |

**Frozen technical target:** [the same-covector next-switch alternative](MIXED_SMALLER_TURN_CONTINUATION.md), [five-variable/maximal-chart reduction](MIXED_NONSHORT_BLOWUP_REDUCTION.md), [epsilon hand theorem](MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md), and [interval-caller source/domain audit](MIXED_NONSHORT_INTERVAL_CERTIFICATE_AUDIT.md). The complement consists of **three closed chart roots per branch**, `a in [2/15,17/20]`, `c in [2/15,2]`, two free weights in `[0,1]`, the chosen maximal weight one, `epsilon in [1/32,61/4]` for chart 0 and `[1/32,15]` for charts 1/2. Overlaps and degeneracies are intentional. The next actual switch is the first event **on the same continuous normal PMP covector**, not an independent local lift or arbitrary later switch.

**Run/replay:** the exact commands, recorded C++/MPFR trust boundary and full-cover acceptance rules are at [CERTIFICATE_REPLAY](CERTIFICATE_REPLAY.md). A direct standalone replay may use:

```sh
g++ -std=c++17 -O3 explorations/mixed_nonshort_completion_interval_certificate.cpp -lmpfr -lgmp -o /tmp/mixed_nonshort_completion_interval_certificate
/tmp/mixed_nonshort_completion_interval_certificate 2000000 0  # forward successor
/tmp/mixed_nonshort_completion_interval_certificate 2000000 1  # reverse successor
```

Alternatively, replay the audited [cover-chain coordinator and verifier](EXACT_COVER_CHAIN.md):

```sh
python explorations/mixed_nonshort_completion_cover_chain.py /tmp/mixed_nonshort_cover_chain
python explorations/mixed_nonshort_cover_chain_verify.py /tmp/mixed_nonshort_cover_chain/manifest.json
```

The coordinator's destination directory must be new. For each branch accept only a **complete three-root** cover (serial or full exact child forest), zero pending/unknown, clean arithmetic flags, matching frozen source/executable hashes, verified record-by-record parent/child correspondence, and the aggregate `N=2L-3`. A successful child prefix or integer count in isolation cannot close M2. If the cover stalls, use the emitted verified frontier to identify a **specific missing uniform contractor/hand inequality**, not a fresh word-length enumeration. Do not edit the frozen C++ caller/headers without re-auditing and updating its source identifiers.

**Commit protocol:** close/check off a gate only after its result and independent review are recorded and pushed. Keep [CHECKLIST](../CHECKLIST.md) and this handoff authoritative, the [replay guide](CERTIFICATE_REPLAY.md) reproducible, and the PR draft until M2, G4 and G5 are complete. Historical local notes and former diagnostic scripts are under [docs/legacy](legacy/INDEX.md) and [explorations/legacy](../explorations/legacy/README.md), not alternative roadmaps.

**Start here on every future session.** Use [the active finite ledger](../CHECKLIST.md), [active proof map](ACTIVE_MAP.md), and the specific theorem notes named below. Superseded plans and local investigations are in [legacy](legacy/INDEX.md).

## Objective and sufficient case partition

The aim is the **sharp octagon cost inequality with equality only in the affine octagon class**, for every admissible twisted closed minimizing trajectory. Existing sign-run coverage, whole-period geometric/PMP inputs, and global normality reduce every competitive finite minimizer with at least six pieces to these sufficient global classes:

| Case | Whole-period assignment | Status |
| --- | --- | --- |
| R | Entirely reverse | **CLOSED** |
| M3 | Mixed with a reverse run of forbidden length | **CLOSED** |
| M1 | Mixed, every forward run length one (after M3) | **CLOSED** |
| F | Entirely forward, at least six pieces | **CLOSED** |
| M2 | Mixed, a forward run length at least two (after M3) | **OPEN** |

These are **entire minimizing-period classes**, not assertions that all local six-piece windows can be shortened. A local M1-shaped window can still occur inside a period assigned to M2. The historical unconditional six-window L3/M1 shortening claim is **false** and must not be reinstated.

## Established dependencies (read only as needed)

- Actual twisted state/frame and costate endpoints, free initial state, normal PMP and true switch interface: [GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md), [MINIMIZER_WINDOW_PMP](MINIMIZER_WINDOW_PMP.md), [NORMAL_TIE_BRANCHING](NORMAL_TIE_BRANCHING.md), and [NORMAL_SWITCH_RIGIDITY](NORMAL_SWITCH_RIGIDITY.md).
- Under the named geometric/compact-domain/standard PMP inputs, [SINGULAR_COST_BUDGET](SINGULAR_COST_BUDGET.md), [MEASURABLE_EDGE_PMP_BOUND](MEASURABLE_EDGE_PMP_BOUND.md) and [QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md) give normalized singular clearance \(D>10^{-11}\) and minimizer size \(N<10^{56}\). This theoretical bound is not a practical word catalogue. [GLOBAL_NORMALITY](GLOBAL_NORMALITY.md) excludes abnormal finite closed lifts.
- [GLOBAL_REVERSE_PERIOD_EXCLUSION](GLOBAL_REVERSE_PERIOD_EXCLUSION.md) closes R by a four-arc minimum-margin needle contradiction. [MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md) closes M3 and forces every surviving reverse run to have exactly two switches.
- [MIXED_GLOBAL_SHORT_RUN_PERIOD](MIXED_GLOBAL_SHORT_RUN_PERIOD.md) and [MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION](MIXED_GLOBAL_SHORT_RUN_ANGLE_EXCLUSION.md) close the sufficient all-short M1 domain for every multiplicity by the two-centre cost comparison and exact winding contradiction.
- [MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md) supplies negative ellipticity in the remaining global cases; the [spectral cost–Casimir inequality](GLOBAL_SPECTRAL_COST_CASIMIR.md) sharpens the earlier bound to `C >= (pi/3)(kappa+3/2)`, strictly off the circle. The [endpoint defect test](GLOBAL_ENDPOINT_DEFECT_TEST.md) computes the same-covector angle without quadrature and bounds the admissible cost of every continuation window. Neither result closes F or M2. The [augmented index](MIXED_GLOBAL_AUGMENTED_INDEX.md) and [turn elimination](MIXED_GLOBAL_TURN_ELIMINATION.md) retain endpoint curvature, rank and all three frame constraint pairs.

## F closed: one uniform whole-period obstruction

[GLOBAL_FORWARD_PERIOD_EXCLUSION](GLOBAL_FORWARD_PERIOD_EXCLUSION.md) closes
**F1 and F2** with an independently reviewed hand reduction and exact rational
cover. At a global minimum of any actual all-forward period with `N>=6`
(hence `N>=7`), the same normal covector satisfies three stationary
identities and both exterior switching floors. The full cost budget gives
`gamma^2<23/125` and the linear neighbor budget; the independently replayed
neighbor certificate gives `1<=z,w<5/4`.

The [centered system](GLOBAL_FORWARD_CENTERED_SYSTEM.md) excludes the circular
region by hand, with `gamma^2>37/200`. The exact complementary-domain replay
processed **20,999 nodes**, excluded all **10,501 leaves**, and returned
**zero unresolved or depth-limit boxes**, maximum depth 23. Its source and
actual-period interface have an [independent internal audit](GLOBAL_FORWARD_CASIMIR_CERTIFICATE_AUDIT.md).
The all-zero-duration algebraic fibre is explicitly outside the positive
window theorem. Weak ties, unequal factors, exterior switches and the
twisted seam remain covered. No word-length enumeration, rank assumption,
or numerical sign is used as a premise.

The earlier bounds `N<=61`, `4/3<a_min^2<20/11` and `q_min<7/4` remain valid
intermediate results; there is no remaining F length-by-length task.

## Open M2: finish the nonshort-forward-run minimum

In a remaining **mixed competitive normal period**, every reverse run has exactly two switches and some forward run has length at least two. The global smallest active margin lies at a reverse-run centre and **touches a forward run of length at least two** (the two-short-bridge alternative is excluded by [MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md)). At every competitive reverse centre,

\[
\rho=\frac{a^2}{a^2+4}<\frac{3}{20},\qquad a^2<\frac{12}{17}
\]

by [MIXED_REVERSE_CENTRE_SCALE_BOUND](MIXED_REVERSE_CENTRE_SCALE_BOUND.md). All reverse-centre angles exceed \(75^\circ\), and with \(m\) reverse centres and \(E\) forward same-sign arcs, \(m\le\min(2E+3,E+8)\), and \(\gamma^2>27/256\) ([angle/density](MIXED_GLOBAL_REVERSE_ANGLE_DENSITY.md)). The [Schur turn-elimination theorem](MIXED_GLOBAL_TURN_ELIMINATION.md) retains the global Casimir and exact constrained index \(\mathrm{index}_{-}(Q_{\mathrm{closed}})=\mathrm{index}_{-}(S)-k-3\).

The fixed continuation interfaces choose the **smaller adjacent turn**.
The [smaller-short branch is now closed](MIXED_SMALLER_SHORT_PERIOD_EXCLUSION.md).
Its [two-turn cost/angle interface](MIXED_GENERAL_SHORT_DEFECT_INTERFACE.md)
and [six-variable necessary domain](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md)
retain both actual turn secants, the transported outer reverse root,
stationary-control slack, and the complete-period defect budget. The
completed directed MPFR replay processed **107,977 nodes**, excluded all
**53,989 leaves**, and left **zero unresolved boxes**, maximum depth 37.
The [independent audit](MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT.md) verifies
the source, domain, arithmetic, completed counts and unchanged hashes.
The shared [engine](INTERVAL_ARITHMETIC_ENGINE.md) also passed 116,914
independently replayed exact/analytic checks.

It therefore remains to exclude the **smaller-nonshort branch**. The
[next-switch alternative](MIXED_SMALLER_TURN_CONTINUATION.md) requires
either a transported forward norm at least `3/4` or a reverse turn norm
below the stated extended secant. Both alternatives still require a
uniform exclusion. The [interface audit](MIXED_MINIMUM_CONTINUATION_INTERFACE_AUDIT.md)
accepts the necessary-condition reduction. The [radial completion bound](GLOBAL_RADIAL_COMPLETION_BOUND.md)
also supplies a nonnegative cost for restoring the omitted radial
coordinate of any window.

The nonshort [five-variable reduction](MIXED_NONSHORT_BLOWUP_REDUCTION.md)
uses three closed maximal-parameter charts and an exact cancellation of
the simultaneous zero-duration denominator. The [hand corner theorem](MIXED_NONSHORT_SMALL_PARAMETER_EXCLUSION.md)
excludes `epsilon<=1/32` uniformly. The published complementary caller,
all contractors, coefficient expressions and LP proposal helper have an
[independent source audit](MIXED_NONSHORT_INTERVAL_CERTIFICATE_AUDIT.md).
Neither branch has a committed completed original-root cover record;
no partial frontier or zero unknown count alone closes a branch.

**M2.1 (OPEN):** At the **global minimum reverse centre whose smaller turn belongs to a nonshort forward run**, exclude both next-switch alternatives using the actual external switches and **same continuous PMP lift**. The smaller-short case is closed; do not assume a minimum must touch *two* long runs.

**M2.2 (OPEN):** Uniformly exclude all admissible M2 periods: arbitrary nonshort run lengths, unequal margins, bridge-diagonal signs, weak third ties, singular/zero-duration limits, rank defects and the twisted seam. A local star escape or negative onsite form is not enough without the global extension/constraints.

## Final assembly after M2

**G4 (OPEN):** The [conditional assembly](GLOBAL_COST_EQUALITY_ASSEMBLY.md)
uses all five sufficient whole-period exclusions to reach \(N\le5\).
The [terminal comparison and equality audit](SMALL_PERIOD_COST_EQUALITY_AUDIT.md)
is complete, with 72 exact checks independently replayed: arbitrary
four-piece factors, strict mixed-five comparison, all terminal words,
and equality transport for the original disk. The uniform R theorem
excludes reverse-five minimizing periods directly. M2 must still close
before this assembly proves the unrestricted cost inequality and affine
uniqueness.

**G5 (OPEN):** The [independent dependency review](GLOBAL_COMPLETION_INDEPENDENT_AUDIT.md)
accepts the realization, measurable-control, finite-before-normal,
same-covector, complete-period and affine-equality chain conditional on
the remaining nonshort covers and their final completion review. The
external premises and arithmetic trust boundaries are explicit. Lean
proof and CI remain deferred by the current instructions.

## Working protocol

1. Work on M2.1, not a new side quest. State one falsifiable uniform inequality with exact quantified domain and the whole-period conditions it uses.
2. Use numerical/SymPy probes only to discover failures or guide a hand proof. Exact certificates must be reproducible, with all factors, normalizations, signs and coefficient tables documented.
3. Keep the true initial state, final frame/state, costate twist, exterior switches, cost budget, endpoint curvature and all three frame constraints. A locally valid PMP segment is not a globally minimizing period.
4. Obtain a separate internal mathematical review; commit and push verified increments, updating [CHECKLIST](../CHECKLIST.md) and this file only on actual progress.
5. Preserve invalid routes and completed special cases in [legacy](legacy/INDEX.md). Never claim a final Reinhardt proof while M2 or final cost/equality assembly is open.

**Exit criterion:** F closed, M2 closed, assembled sharp octagon cost inequality and affine uniqueness proved and audited. No credible percent-of-effort or completion date is known.
