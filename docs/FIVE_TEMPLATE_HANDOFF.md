# Handoff — bounded-case proof plan for the Reinhardt conjecture

**Checkpoint (2026-11-07): L3 on the stated local superset is refuted even
with arbitrary measurable replacements. The revised complete-switch PMP
package has a proved necessary domain; all five analytic targets remain open.**

**Start here, then** `docs/SWITCH_COMPLETE_REDUCTION.md` (revised domains and
conditional theorem), `docs/BOUNDED_REDUCTION.md` (coverage and original domain),
`CHECKLIST.md` (status), `docs/FORWARD_ALTERNATION_EXCLUSION.md`
(proved local descent), and `docs/WORD_HOLONOMY.md` (endpoint algebra).

## Executive decision

Read [LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md)
first. It proves that eligible `021210` windows of arbitrarily small cost
can admit no cheaper endpoint-matching replacement with at most six pieces.
Then read [LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md):
the strengthening allows arbitrary measurable simplex competitors and all
terminal times. It checks ASZ's sufficient-optimality theorem on one fixed
padded reference, then globalizes small trims by compactness and the edge dual.
The current domain is a necessary superset of actual minimizing windows;
no closed-minimizer embedding of these counterexamples is claimed. The next
proof gate is a uniform analytic result on the revised necessary domain,
proved in [SWITCH_COMPLETE_REDUCTION.md](SWITCH_COMPLETE_REDUCTION.md), or
another genuinely uniform reduction. Adding replacement pieces alone is not
a repair of the original claim.
The original five sufficient statements
cannot all be proved as written.

An additional necessary condition is now proved in
[MINIMIZER_WINDOW_PMP.md](MINIMIZER_WINDOW_PMP.md): every selected window
starts and ends at genuine switches, so the same PMP lift has an inactive
tie at both external endpoints. Full endpoint rank makes that lift unique
at the exact L1 input and the sufficiently small padded L3 examples, whose
external active controls are strictly unique. Thus those examples cannot
be the selected six complete pieces of an actual minimizer. This gives a
justified domain restriction, not a universal improvement theorem.

[LOCAL_FORWARD_ENDPOINT_FILTER.md](LOCAL_FORWARD_ENDPOINT_FILTER.md)
gives four exact L1 boundary gaps and two scalar interval-endpoint tests.
It also proves that asymmetric eligible local-PMP windows satisfying both
external ties persist; do not infer equal factors from these conditions.

Do not try to evade the padded-family obstruction merely by extending its
outer arcs to the next PMP switches:
[PADDED_L3_PMP_CONTINUATION.md](PADDED_L3_PMP_CONTINUATION.md) proves that,
for sufficiently small cores, the unique lift reaches the strict-star
boundary first on both sides. This scoped exclusion leaves the general
revised L3 target open.

**Do not resume comparing closed words of lengths 7, 8, 9, ...** The finite
closed-word comparisons through five pieces, and two six-piece closed orbits,
are assets, but without a complexity bound they do not exhaust minimizers.

The hand coverage argument in `docs/BOUNDED_REDUCTION.md` shows: *assuming
the established forward-alternation exclusion*, any finite cyclically reduced
global minimizer with `N >= 6` has a six-arc window of one of the following
types, after cyclic relabeling. The proof accounts for the **twisted cyclic
seam**. This is a structural coverage theorem, **not** a uniform bound.

| Gate | Six control labels | Five switch signs | Original-domain improvement |
| --- | --- | --- | --- |
| L1 | `012012` | `+++++` | **OPEN** |
| L2 | `021021` | `-----` | **OPEN** |
| L3 | `021210` | `--+--` | **FALSE** on the stated domain even with arbitrary measurable replacements |
| L4 | `010201` | `+--++` | **OPEN** |
| L5 | `021012` | `---++` | **OPEN** |

The revised domains in SWITCH_COMPLETE_REDUCTION add the full free-time PMP
and both external ties. Their necessity and conditional sufficiency are
proved; **all five revised analytic targets are open**, including revised L3.
The table above records the original larger-domain statements.

**Required theorem for each revised gate:** For **every** six-positive-factor window
of its specified type that can occur in a minimizer of cost at most the
octagon's, construct an ACTUAL strict-star admissible replacement with
*exactly the same initial and final frame and state*, with **strictly lower
cost**. Physical elapsed time may change. The replacement may have six
pieces. Its word may differ, but if using the finite replacement search,
limit it to at most six pieces.

Each gate quantifies over **all asymmetric parameters**, not just symmetric,
generic-rank, sampled, closed, or bounded-box tuples. The original domain
is now proved too broad for L3 even without a replacement cap. L1, L2, L4, and L5
remain open. The revised target uses the explicit domains D_i^sw in
SWITCH_COMPLETE_REDUCTION; do not silently substitute either the original
larger domain or only a symmetric, normal-by-assumption, or sampled subset.

## Why the package suffices, conditionally

1. Use the actual global-minimizer existence, geometric/control
   correspondence, and published finite bang-bang minimizer theorem.
2. If a minimizer has `N >= 6` positive vertex pieces in its cyclically
   reduced one-period word, the hand sign-run coverage gives L1–L5 within
   ONE period (rebase the actual twisted trajectory if necessary).
3. Proving that gate gives a cheaper piecewise admissible competitor:
   splice at equal **(g, X)** endpoints and translate subsequent times.
   This contradicts global minimality.
4. Thus `N <= 5` for every global minimizer. Apply the existing complete
   **through-five** hand comparison and equality classification.
5. Transfer the cost and equality statements through the geometric bridge
   to global density minimality and affine rigidity.

This is a conditional implication, not an announced proof of Reinhardt.
The published finite bang-bang theorem is **not** a uniform length bound.
Existing Lean reductions and all new hand certificates require eventual
validation; the current workflow forbids compilation/CI.

## Concrete next-session sequence (strict acceptance gates)

### P0 — Audit the precise premises before attempting cost estimates

**Completed as a hand proof:** [MINIMIZER_WINDOW_AUDIT.md](MINIMIZER_WINDOW_AUDIT.md).
The published finite reduction and retained comparison certificates remain
named inputs. This audit proves eligibility and the splice; it does not prove
an analytic exclusion or independently recheck every through-five identity.

- [x] Recheck that every *actual* global minimizer has the requisite
  finite vertex representation, including possible singular/edge portions;
  identify the exact published result and its hypotheses.
- [x] Recheck that the forward `+-+` exclusion can be spliced into an
  arbitrary minimizer, including windows that meet the **twisted seam**.
- [x] Recheck that every six-arc window selected by the coverage proof
  satisfies **all** chosen eligibility restrictions. In particular audit
  the sector inequalities after left-normalizing the window frame. If
  this is unjustified, **drop that restriction** from the local theorem
  rather than omit legitimate minimizer windows.
- [x] Recheck that the geometric/control bridge permits the improved
  integral trajectory and that the through-five equality claim has the
  scope needed for affine rigidity.

**P0 exit criterion:** a precise hand lemma proving that every selected
minimizer window lies in each gate's stated domain, with no unproved
endpoint, orientation, or sector assumption. If any premise fails, mark
it open; do not count L1–L5 as a sufficient package until repaired.

### P1 — Prove or diagnose the first universal LOCAL gate (start with L1)

**Exact obstruction already found:** [LOCAL_FORWARD_SIX.md](LOCAL_FORWARD_SIX.md)
gives an input satisfying all eligibility conditions where the same-word
endpoint fiber has a strict local cost minimum. Its rank is five, first
variation is zero, and constrained second variation is greater than `1/200`.
Do not try to prove a universal negative-Hessian assertion. The broader L1
claim remains open: test different-word or nonlocal replacements, or prove
additional necessary conditions for windows in actual global minimizers.

[LOCAL_FORWARD_NEEDLE_AUDIT.md](LOCAL_FORWARD_NEEDLE_AUDIT.md) strengthens
the exact example to a strict strong local minimum in the augmented
normalized free-log-time problem. All full-arc gaps and ASZ hypotheses
are checked, so nearby arbitrary-control descent also fails. The distant
replacement below remains compatible with that conclusion.

The explicit obstruction has now been resolved by a different word:
[LOCAL_FORWARD_NONLOCAL_REPLACEMENT.md](LOCAL_FORWARD_NONLOCAL_REPLACEMENT.md)
proves an exact six-piece `012021` replacement with cost decrease greater
than `1/100000`. Do not repeat that one-input search; the missing task is
a proof over the full L1 domain, including other stationary inputs.

Its independent appendix gives a second rational slice and a standard-library
Fraction checker, together with an unspecified nearby-input continuation.
Neither witness gives full-domain coverage.

**Interior rank classification is complete for L1:**
[LOCAL_FORWARD_RANK.md](LOCAL_FORWARD_RANK.md) proves full rank five on
the entire positive strict-star domain, hence rank two after suffix
elimination. This uses arbitrary initial state and all unequal factors.
It gives no uniform boundary conditioning or cost descent.

[LOCAL_FORWARD_PMP_LIMIT.md](LOCAL_FORWARD_PMP_LIMIT.md) then proves
normality and uniqueness of a minimizing window's normalized adjoint.
It also shows why local first-order PMP plus mere twisted periodic
extendibility is insufficient: existing standard polygons supply eligible
full-PMP six-windows of arbitrarily small cost, while their displayed
whole periods exceed the octagon budget. Keep that total-period budget
when trying a stronger necessary-condition route.

L1 remains an analytic target, but the refuted L3 premise already blocks
the original five-case route. The following L1 work is retained for a repair,
**not** presumed easier or true. Use the exact initial-state chart

`p=(a,b,(4-ab)/(a+b))` with `a>0,b>0,ab<4`, and six factors
`q_1,...,q_6>1`. On an arc with control `i`, active margin `A=p_i`,
and other cyclic margins `B=p_(i+1)`, `C=p_(i-1)`, use

```text
p_i'       = A
p_(i+1)'   = (A+B) q - A
p_(i-1)'   = (A+C)/q - A
duration   = (A/2) log q
J_arc      = (A/8) [(A+B)(q-1)+(A+C)(1-q^(-1))-A log q].
```

Impose strict star positivity at all seven switching states (equivalent
to positivity on each full arc), the eligible cost range, and the
geometric sector tests if P0 validates them.

Let `F=T_(i_1)(q_1)...T_(i_6)(q_6)`, and let `p_end` be the exact
updated margins. For **fixed initial p**, the local endpoint is
`E(q)=(F,p_end)`; preserving this pair is equivalent to preserving
both the final frame and state. **Do not set `F=R` on a local window.**
Do not change initial `p` during a splice.

Use the two explicit positive-factor inverses for a distinct-label
triple in `docs/BOUNDED_REDUCTION.md`, §6, to solve the final three
factors from the required tangent product. This leaves a three-variable
parameterization and two terminal-state equations.

- [x] Classify the L1 endpoint rank on its entire positive domain:
  it is five, or two after the suffix elimination. There are no interior
  rank-one/rank-zero exceptions. See LOCAL_FORWARD_RANK.
- [ ] On regular endpoint fibers, calculate the derivative of the
  exact cost. When nonzero, use the implicit function theorem to
  obtain a genuine strictly cheaper curve satisfying both endpoints.
- [ ] At stationary points, compute the **constrained** second
  variation (including multipliers and any curvature of the endpoint
  fiber). A negative direction supplies strict descent. A zero/positive
  test does **not** close the gate.
- [ ] Handle any degenerate stationary or singular-rank locus exactly;
  if same-word variations fail, test a different word with at most six
  pieces and the *same local (g, X) endpoints*. A numerical solver output
  is neither existence nor a counterexample certificate.
- [ ] Supply the hand inequality on the **entire** eligible open
  parameter domain and explicit strict-star splice justification;
  describe all boundary/limiting cases needed for that argument.

**L1 exit criterion:** one self-contained hand proof of the universal
strict local replacement, or a precise obstruction to the chosen
method. A theorem for *globally closed* `012012` does not count.

### P2 — Repeat against the fixed remaining list

- [ ] L2: `021021` (reverse-cyclic; do not infer from L1 by an unproved
  time-reversal/reflection symmetry).
- [x] Diagnose L3: `021210` is refuted on the stated domain for arbitrary
  measurable replacements by LOCAL_REVERSE_SIX_GLOBAL_MINIMUM; the
  self-contained at-most-six foundation is LOCAL_REVERSE_SIX_OBSTRUCTION. This is a refuted
  sufficient lemma, not a proved analytic exclusion or a global counterexample.
  The earlier, distinct
  [LOCAL_L3_STRONG_MINIMUM.md](LOCAL_L3_STRONG_MINIMUM.md) supplies an exact
  eligible strict strong local minimum in the normalized free-log-time
  formulation. Universal nearby improvement, including arbitrary nearby
  controls, is false. A distant cheaper replacement for that particular
  equal-factor input is not excluded by its local theorem.
- [ ] L4: `010201` (a reverse run of exactly two). Full-domain endpoint
  rank five is proved in LOCAL_SIX_VARIATION. Its exact eligible stationary
  family has all five compensated missing-control switch needles positive;
  do not assume a negative switch needle always exists. The full replacement
  target remains open.
- [ ] L5: `021012` (a longer reverse run). Full endpoint rank five is now
  proved throughout its positive strict-star domain by LOCAL_L5_ENDPOINT_RANK;
  its five-piece prefix already supplies five independent columns. This
  makes the minimizing lift normal and unique, but does not prove descent.

Reuse the *same* endpoint-map and constrained-variation machinery.
Prefer a **shared theorem** that closes multiple gates simultaneously
over five repeated ad hoc calculations. At every gate record either a
complete hand exclusion, a proven reduction to earlier gates, or the
specific obstruction. Do not increment a case merely because its
symbolic equations or numerical optimum were computed.

### P3 — Explicit boundary and falsification pass

- [ ] Test numerical suggestions against exact endpoint residuals,
  strict positivity for entire arcs, fixed initial state, and any
  validated geometric eligibility requirement.
- [ ] Treat factor collapse `q -> 1`, loss of strict-star margin,
  `q -> infinity`, and unbounded initial states when they matter.
  Compactifying coordinates is **not** a compactness theorem.
- [ ] Keep rank-deficient loci; a generic-dimension argument is
  insufficient.
- [ ] If a gate fails in the full stated domain, distinguish a
  **counterexample to the universal LOCAL improvement theorem** from
  a counterexample to Reinhardt. Revise the bounded route, possibly
  using PMP restrictions on *minimizing* windows or a direct global
  calibration; do **not** resume ever-growing whole-word enumeration.

**P3 exit criterion:** every asserted local improvement is uniform on
its precisely stated domain, with no silently discarded face or rank.

### P4 — Only after L1–L5: assemble the unrestricted hand proof

- [ ] State global minimizer existence and the finite bang-bang bridge.
- [ ] Apply the one-period five-template coverage and exact splice to
  prove the unconditional uniform bound `N<=5`.
- [ ] Invoke the earlier asymmetric through-five comparison and
  independently check its equality/affine-class transfer.
- [ ] Write the complete standalone mathematical proof; mark source
  formalization, Lean compilation, and kernel audit as separate,
  presently deferred obligations.

**P4 exit criterion:** global lower bound + separate affine equality
classification, supported by a complete hand proof. Never mark the
conjecture solved at completion of P0 or at an analytic count below 5/5.

## Exact scope traps / known dead ends

1. The completed **CLOSED** six-arc `012012` comparison does not prove
   the **LOCAL** L1 statement: the local tangent product is usually not
   `R`, and the initial state cannot vary in a splice.
2. Six factor variables minus five endpoint constraints suggests one
   degree of freedom only at **regular rank**. L1 now has a full-domain
   hand rank proof, as does L4 in LOCAL_SIX_VARIATION. LOCAL_MIXED_SIX_RANK now proves full rank five for L3 on its entire
   positive strict-star domain, without a cost or symmetry assumption.
   LOCAL_L5_ENDPOINT_RANK likewise proves rank five for L5 from a five-piece
   prefix. Singular fibers for L2 remain a separate obligation and may
   be isolated or have higher-dimensional components.
3. The old forward alternating four-arc argument rules out a particular
   orientation; reversing its sign reverses the Hessian sign. Do not
   assume an analogous reverse exclusion.
4. The fixed-edge, ordering, holonomy, circle, and regular-family results
   do not give a global word-length bound.
5. The numerical local-fiber probe has failures and covers only a small
   box; treat it as exploratory evidence, not a proof.
6. A finite list of proposed universal inequalities is not a bounded
   **enumeration of actual minimizers**. The original list now contains
   a false L3 premise, and a corrected sufficient list would still need
   complete analytic proofs.
7. The eligible exact input in `LOCAL_FORWARD_SIX.md` is a strict
   same-word local minimum. A universal local-deformation-only proof of L1
   is false; its full different-word/nonlocal replacement claim is unresolved.
8. The eligible L3 input in `LOCAL_L3_STRONG_MINIMUM.md` is a strict strong
   local minimum even among arbitrary nearby controls. The result gives
   no global radius and therefore is not a full L3 counterexample.

## Handoff status and reporting contract

**Proved or supplied as hand arguments:** five-template combinatorial
coverage (conditional on forward-alternation exclusion); exact local
endpoint formulas; the complete comparison through five positive
pieces; two closed six-piece comparisons.

**Completed prerequisite:** P0 window-eligibility and finite-splice hand audit.

**Revised conditional package:** SWITCH_COMPLETE_REDUCTION proves the
necessary-domain and finite-splice implication. All five revised analytic
targets are open; none is counted as a proved exclusion.

**Additional rank theorem:** LOCAL_MIXED_SIX_RANK proves full endpoint rank
five throughout L3; minimizing windows are normal with a unique normalized
adjoint. The original broader L3 replacement claim remains false.

**Additional necessary conditions:** genuine external-switch ties, their
exact L1 active-margin filter, and exclusion of the displayed endpoint-unique
L1/L3 examples from selected complete windows. They do not close a local gate.

**Refuted:** L3 on the stated local superset, including its arbitrary-finite
and arbitrary-measurable replacement relaxations. The stronger proof adds
ASZ Theorem 2.6 as a checked external input.

**Open:** L1, L2, L4, L5; a repaired L3/domain or another uniform reduction
(**0/5 analytic exclusions proved**);
unconditional bound `N<=5`; global cost inequality; affine rigidity.

**Forbidden next milestone:** a closed seven-arc or longer comparison,
unless it first supplies a genuine uniform reduction theorem.

**On each session:** commit a mathematical hand certificate or falsifiable
obstruction; update `CHECKLIST.md` and PR description with exact status;
give the next worker the *one* next proof gate, the precise failed
inequality/rank case if relevant, and reproduction commands for any
exploration. Do not compile Lean or run CI under the current agreement.

## Citations and review entry points

- [Finite template coverage and endpoint domain](BOUNDED_REDUCTION.md)
- [Proof ledger](../CHECKLIST.md)
- [Local forward-alternation variation](FORWARD_ALTERNATION_EXCLUSION.md)
- [Fixed-edge variation](EDGE_SWITCH_BOUND.md)
- [Cyclic rebase and word ordering](VERTEX_WORD_REDUCTION.md)
- [Arbitrary-word holonomy](WORD_HOLONOMY.md)
- [Through-five comparison](FOUR_LINK_HAND_PROOF.md),
  [noncyclic five](FIVE_ARC_PROGRESS.md), [reverse five](REVERSE_FIVE_ARC.md)
- [Failed naïve local shortening](LOCAL_SHORTENING_OBSTRUCTION.md)
- [Incomplete local numerical exploration](../explorations/local_six_fiber_probe.py)
- Hales, *On the Reinhardt Conjecture* (2011), §7.6:
  https://arxiv.org/abs/1103.4518
- Hales–Vajjha, *Packings of Smoothed Polygons* (2024),
  finite bang-bang theorem and the missing uniform bound:
  https://arxiv.org/abs/2405.04331

The original L3 sufficient statement has been refuted; the conjecture and
unconditional complexity bound remain open. No Lean compilation,
typechecking, Lake, CI, or kernel validation was run.


