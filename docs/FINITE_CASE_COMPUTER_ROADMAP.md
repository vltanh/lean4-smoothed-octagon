# Finite structural case atlas and computer-assisted global comparison

Date: 2026-11-07 UTC. Active **research plan**, not a completed proof.
No Lean, Lake, typechecking, or CI. Mathematical outputs must ultimately
be hand proofs (tables of finite exact inequalities are permitted).
This plan supersedes the idea of enumerating closed words up to 10^56.

## 0. What is bounded, and what is not

The current hand notes establish, under the stated geometric,
compact-state, and standard PMP inputs, singular clearance D>10^-11 and
N<10^56 positive pieces for every minimizing period; see
[SINGULAR_COST_BUDGET](SINGULAR_COST_BUDGET.md) and
[MEASURABLE_EDGE_PMP_BOUND](MEASURABLE_EDGE_PMP_BOUND.md). These results
make the problem finite **in principle**, but the numerical bound is not
a computationally practical catalogue.

[GLOBAL_NORMALITY](GLOBAL_NORMALITY.md) proves that a finite twisted
closed PMP extremal cannot be abnormal. Its endpoint/PMP interface,
backwards zero identities, triple-tie lemma and twisted run argument
have passed an [independent internal hand audit](GLOBAL_NORMALITY_AUDIT.md).
The restored companion script passes 22 exact algebra checks. Thus every
global minimizing lift may be normalized to lambda=-1 under the stated
inputs. Compactness gives a qualitative common bound on those normal
lifts; no explicit numerical phase box follows from that corollary.
Normal triple/nontransverse ties still require separate treatment.

The existing coverage proof in [BOUNDED_REDUCTION](BOUNDED_REDUCTION.md)
says that every minimizing cyclic word with N>=6 has one six-complete-piece
window of a fixed type below. Its precondition is the established forward
alternation exclusion. The window belongs to the geometrically eligible,
cost-competitive, *complete-switch* PMP domain from
[SWITCH_COMPLETE_REDUCTION](SWITCH_COMPLETE_REDUCTION.md): one continuous
lift, whole-arc vertex maximality, and ties at **both external switches**.
The old unconditional local improvement premise is FALSE for M1 even
with arbitrary measurable replacements. This revised programme does
not revive it.

The new target for each type is **not** “every local window can be
shortened.” The target is:

> No globally minimizing, strictly admissible, cost-competitive, twisted
> closed period containing a selected window of this type can have N>=6.
> It is enough to prove, throughout the complete-period domain, that
> its normal PMP extension fails, reaches the star boundary, exceeds
> the octagon budget, has a genuine negative constrained variation, or
> admits an exact strictly cheaper endpoint-preserving competitor.

This is a uniform statement about real global minimizers. Simply
finding a noncompetitive PMP orbit or an isolated descent direction does
not exclude an entire case.

## 1. Five fixed cases

| ID | Six labels | Sign pattern | Reusable existing input | Exact new case target |
|---|---|---|---|---|
| F: pure forward | 012012 | +++++ | Full local endpoint rank five; standard-family whole-period negative index, but asymmetric case open | Uniform negative *closed-period* variation or cost/return obstruction for all competitive all-forward occurrences |
| R: pure reverse | 021021 | ----- | Exact seven-piece descent on equal-factor state-cyclic inputs; rank-four example is above the competitive cost cap | Rule out competitive closed reverse occurrences using edge needle, rank-degenerate, and limiting alternatives |
| M1: short mixed | 021210 | --+-- | Full local rank five; proven finite escape for an explicit small-core phase region; original broad local replacement is false | Expand escape/cost/index coverage across the remaining complete-period PMP region |
| M2: mixed transition | 010201 | +--++ | Full local rank five; switch-only descent is not universally valid | Find a whole-arc needle, global index, or continuation certificate for all complete-period candidates |
| M3: long reverse run | 021012 | ---++ | Full local rank five from prefix 02101 | Find a uniform phase-return obstruction or exact global variation for these mixed runs |

The patterns cover arbitrary N>=6 without testing N sequentially.
They should be prioritized by reusable analytical structure; **do not
assume equal difficulty or count subfamilies as closed rows**.

## 2. Small verifiable gates, repeated for each case

Each of F, R, M1, M2, M3 has exactly three explicit gates.

- **A: Necessary-condition atlas (numerical exploration).** Write and
  independently cross-check exact vertex factor/state/frame/cost formulas;
  normalize the initial state by p0p1+p1p2+p2p0=4; derive the five
  fixed-endpoint Jacobian rows, normalized cost gradient, and two exterior
  needle-gap pairs. Screen whole-arc missing-control gaps. Keep singular
  endpoint ranks rather than dividing by them. Numerical roots and signs
  are *hypotheses*, never certified universal assertions.
- **B: Full-period fate test (numerical exploration).** Continue any
  surviving candidate with one genuine PMP cotangent lift through both
  external ties and the twisted seam. Classify its first certified fate as
  star-boundary escape, strictly over-budget cost, failed twisted
  state/costate/frame closure, negative constrained second variation,
  or an exact cheaper endpoint-preserving competitor. If none is
  established, record **UNKNOWN**; do not enlarge the word catalogue.
- **C: Uniform certificate (hand proof).** Prove that the fates cover the
  *entire* case domain. Use exact symbolic identities, rational interval
  bounds on explicit compact cells, or a small rigorous table with
  boundary-face arguments. Handle singular ranks, simultaneous or cubic
  ties, q_i->1, and arbitrary unequal factors. Mark case **CLOSED** only
  here, after a second independent mathematical audit.

These are 15 finite, specifically checkable gates; A/B completion means
only that an *investigation* is complete, not that the analytic target is
established. No individual floating-point sample can close gate C.

Two cross-case obligations are tracked separately:

- **T (ties and multiplier exceptions):** the GLOBAL_NORMALITY audit is
  complete, removing abnormal minimizer lifts. Retain normal triple ties
  and nontransverse switches
  (GLOBAL_COST_CASIMIR Section 6 gives an exact cubic example).
  If convenient, stratify the *normal* frame costate into negative
  elliptic, positive elliptic, and nonelliptic determinant sectors,
  without assuming one sector exhausts the problem.
- **B (boundary and equality):** compactify small positive factor
  limits q_i->1 and the admissible state boundaries; prove that the
  vanishing-face comparisons inherit the correct shorter-word
  inequalities, allowing zero cost gaps at the octagon. Use the
  retained through-five equality classification once all five case
  certificates are proved.

## 3. A reproducible numerical oracle, not another unconstrained optimizer

The first diagnostic is
[structural_case_probe.py](../explorations/structural_case_probe.py).
It deliberately uses **no nonlinear optimizer**. It evaluates the
actual fixed-initial-state vertex endpoint, computes its 5x6 derivative
by complex-step, solves for a normal endpoint multiplier by a least-squares
linear system, and reports the stationarity residual.

Only when the endpoint Jacobian has rank five, the whole window is strict
star, and the residual is small, it computes compensated missing-vertex
needles. For a cut and an inserted factor exp(epsilon), the reported
normalized gap is

    Delta = d(C/sqrt(12))/d epsilon - nu dot d(endpoint)/d epsilon.

At an actual maximizer all missing-control Delta values are nonnegative;
at a genuine adjacent switch the corresponding gap is **zero**. The
numerical thresholds only screen; signs near zero require exact work.

The additional [closed-period index oracle](../explorations/closed_period_index_probe.py)
evaluates the actual five closed endpoint constraints with the initial
state free. It includes the endpoint-curvature term when computing the
constrained Hessian. Its first three deterministic checks are the
standard N=4,7,10 forward periods, with numerical negative indices
0,2,4 respectively. This agrees with the retained standard-family
hand theorem but **does not** extend it to asymmetric candidates.
See [CASE_ATLAS_EXPERIMENT_001](CASE_ATLAS_EXPERIMENT_001.md).
The [octagon boundary oracle](../explorations/octagon_boundary_probe.py)
separately tests a four-insertion all-reverse degeneration and uses
SciPy to correct five complete-period endpoint coordinates. Both
scripts are regression diagnostics, not globally certified solvers.

For any selected six-complete-piece window, the next oracle must use
**the same PMP lift** to continue the trajectory and enforce:

    g(0)=I, g(T)=R,
    X(T)=R^-1 X(0) R,
    Lambda_1(T)=R^-1 Lambda_1(0) R,
    W(T)=R^-1 W(0) R,
    C<=A_oct.

No local tangent product F=R is imposed on an arbitrary six-window.
Only a **complete closed period** is required to satisfy that frame
equation. Candidate continuation and its quantitative error control
are future B-gate work, not yet implemented.

Prefer deterministic continuation and root isolation over random SLSQP.
When a numerical assertion looks uniform, replace it by rational interval
arithmetic/analytic inequalities with a separately checked compact
domain. Symbolic simplification is a discovery tool; human-readable
matrix identities and cost signs are the final certificate.

## 4. First exact-input diagnostics and what they teach

The initial execution (Python 3.13.5, NumPy 2.3.5, complex-step 10^-28;
IEEE double arithmetic) is recorded in
[CASE_ATLAS_EXPERIMENT_001](CASE_ATLAS_EXPERIMENT_001.md).

- An exact known stationary F window has two *strictly positive*
  exterior missing-control gaps. Thus it is **not** a selected
  six-complete-piece minimizer window, despite stationarity and strict
  interior maximality.
- A known stationary M1 window also has positive gaps at both external
  cuts; its known local strong optimality is consistent with this.
- A standard forward N=7 extremal yields a locally stationary F window
  with **one zero external gap at each end** and positive other gaps.
  Its full-period cost is about 3.13865534, whereas
  A_oct is about 3.12605443. This is an exact-family example showing
  that local full PMP plus both external ties is **insufficient without
  the complete-period cost budget**.
- Five generic determinant-one windows fail stationarity numerically;
  no PMP gap claims are inferred from those generic samples.

These are checks of *known* behaviors, not additional global
exclusions and not a count of closed cases. In particular, no numerical
plot or optimizer output proves an unrestricted inequality.

## 5. Priority and stopping criteria

1. **Finish cross-case T**: the independent normality audit is complete.
   Treat remaining normal triple/nontransverse branches in continuation;
   the abnormal proof does not exclude those normal branches.
2. **Extend M1 escape**: its existing finite escape region offers the
   clearest monotone full-period certificate. Compute the exact
   complement and identify a finite set of alternatives, not a larger
   list of whole words.
3. **Reverse R**: test all positive/competitive L2 endpoint-rank
   alternatives and needle signs, especially boundary limits; do
   not assume the above-budget rank-four example is competitive.
4. **Forward F**: use the known closed-period Fourier index as a
   template for asymmetric return maps. The standard N=7 candidate
   failing the budget is a validation check, not a universal proof.
5. **M2 and M3**: screen complete-switch PMP boxes using the same
   oracle; prioritize any rigorous inequality shared between them.
6. **Boundary/equality B**: certify every remaining zero-duration,
   singular-rank, and nontransverse cell and apply through-five
   equality exactly once after global N<=5 (or direct inequality).

At the end of each session update the case matrix with: the exact
domain, a reproducible positive/negative witness or UNKNOWN, a
universal hand lemma if proved, and the next smallest **finite**
analytic obligation. Stop a case if its proposed universal claim is
false; record the counterexample and revise the domain, rather than
manufacture additional word lengths or count partial samples as closure.

## Status

| Case | A: numerical necessary atlas | B: complete-period fate | C: uniform proof |
|---|---|---|---|
| F | **First deterministic run** | Standard N=4/7/10 Hessian pilot; asymmetric continuation OPEN | OPEN |
| R | **First deterministic run** | OPEN | OPEN |
| M1 | **First deterministic run** | Small-core escape subregion only | OPEN |
| M2 | **First deterministic run** | OPEN | OPEN |
| M3 | **First deterministic run** | OPEN | OPEN |
| T: ties/normality | Normality proved; 22 exact algebra checks | Independent normality audit complete | Normality CLOSED; normal ties OPEN |
| B: boundaries/equality | Octagon insertion obstruction known | OPEN | OPEN |

**Unrestricted Reinhardt cost inequality: OPEN. Affine uniqueness: OPEN.
Lean kernel validation: DEFERRED.**
