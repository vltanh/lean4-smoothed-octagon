# Global reduction plan after the failed local-improvement premise

Date: 2026-11-07. **Active hand-proof plan and next-worker entry point.**
The unrestricted Reinhardt conjecture, affine uniqueness, and Lean kernel
validation remain open. No increasing-length closed-word enumeration is
authorized by this plan.

## 1. Decision and exact target

Work with the **complete minimizing period and its normalized Pontryagin
lift**. Preserve the free initial state, both frame/state terminal equations,
the twisted costate equations, and the complete-period cost budget.

The original five-template coverage theorem remains correct. Its proposed
universal local improvement package does not: some eligible L3 windows
are global minima for their fixed endpoints even among arbitrary measurable
controls and free terminal times. More replacement pieces do not repair
that statement. The old
[FIVE_TEMPLATE_HANDOFF](FIVE_TEMPLATE_HANDOFF.md) and
[BOUNDED_REDUCTION](BOUNDED_REDUCTION.md) are retained as diagnostic records
and reusable coverage arguments, rather than the controlling proof plan.

The replacement target is:

> Produce a certified **specific integer** N_max such that every actual
> global minimizer has a cyclically reduced period with at most N_max
> positive vertex pieces; then make the resulting fixed finite comparison
> and equality proof. A direct global theorem N<=5 would finish the
> comparison using the existing through-five certificates.

An existential uniform bound is useful progress, but it does not identify
that finite list. A finite list of open lemmas, or finiteness for each
individual trajectory, is not a specific bound either.

## External-input boundary

[FINITE_BANG_BANG_SOURCE_AUDIT](FINITE_BANG_BANG_SOURCE_AUDIT.md) records
what is and is not certified about the cited finite bang-bang theorem.
Hales--Vajjha Theorem 16.3.1 uses unstable-curve escape and basin-containment
calculations described numerically in the checked manuscript. Those steps
have not been independently enclosed or proved here. The G2 qualitative
implication and existential global count retain that external input;
compactness in G1 and the G3 count for a supplied clearance do not use it.
A self-contained final proof must certify or replace the relevant source
inputs. This audit does not assert that the cited theorem is false.

## 2. Fixed sequence of proof obligations

| Gate | Acceptance condition | Current status |
| --- | --- | --- |
| G1. Complete-period domain and compact lifts | Prove the actual boundary conditions and compactness after projective normalization, including abnormal limits. | **Hand proof complete.** See GLOBAL_PERIODIC_PMP and GLOBAL_MINIMIZER_COMPACTNESS. |
| G2. Uniform regularity of minimizers | Separate every normalized minimizing lift from the full singular locus, uniformly over all minimizers and times. | **Qualitative separation deduced using external Theorem 16.3.1:** some epsilon_* > 0 exists. Its computational source inputs and a certified numerical value remain separate obligations. |
| G3. Uniform switch complexity | Bound switches uniformly on a supplied compact regular phase domain, including near-degenerate ties; make the constants usable with G2. | **Complete conditional quantitative theorem.** GLOBAL_CLOSED_VARIATION proves the uniform existence result; QUANTITATIVE_REGULAR_SWITCH_BOUND supplies an explicit N(epsilon), with every coefficient fixed. A numerical epsilon is still needed. |
| G4. Fixed finite comparison and equality | After a numerical N_max, prove the remaining closed comparisons and equality classification for exactly that fixed set. | **Blocked by the quantitative bound.** Through-five comparison/equality are retained assets. No new larger-word list has been started. |

G2 and G3 are separate obligations. The compactness proof alone does not
bound switches. A local switch theorem with unspecified neighborhoods
does not provide a numerical N_max. Neither of these limitations may be
hidden by stating that the remaining search is "finite."

The complete-period cost constraint is C<=A_oct. Periodicity and first-order
PMP alone are insufficient: the standard forward polygons already provide
non-octagonal periodic extremals, with noncompetitive whole-period cost.

## 3. Work already carried through this plan

### 3.1 Exact global PMP interface

[GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md) derives the full problem on
the actual five-dimensional state manifold. In the original notation,

\[
g(0)=I,\qquad g(T)=R,\qquad X(T)=R^{-1}X(0)R,
\]

\[
\Lambda_R(T)=R^{-1}\Lambda_R(0)R,\qquad
\Lambda_1(t)=g(t)^{-1}\Lambda_1(0)g(t).
\]

The second line uses free-initial-state transversality and spatial
costate conservation. A full-rank local endpoint map excludes abnormal
occurrences and determines the unique normalized adjoint. Thus a global
extension cannot avoid a local continuation obstruction by selecting
different multipliers or by stopping at the terminal seam.

These interface facts support the following actual exclusion; by themselves
they are not new cost comparisons.

### 3.2 A finite continuation test excludes the L3 counterexample family

[GLOBAL_PERIOD_BUDGET](GLOBAL_PERIOD_BUDGET.md) gives an explicit region
of state/costate space from which the uniquely optimal vertex is forced
until the strict-star boundary. In rotated control-1 coordinates put

\[
q=1/\sqrt3,\quad W=(q-a)^2w,\quad
\mathscr R=\frac{(1+W)(q-a)}{2qW}.
\]

The sufficient inequalities are

\[
0<a<q,\quad p_w\le0,\quad\mu\le a^2,\quad
B<0,\quad B_S\le0,\quad\mathscr R\ge5.
\]

The note defines the adjoint quantities and derives all their equations.
The two competing Hamiltonian gaps stay strictly unfavorable until a
finite boundary exit. The logarithm estimate is exact:

\[
\log 5>\frac85,
\qquad
\log r>2(1-1/r)\quad(r\ge5).
\]

Every small reverse-core L3 window in the established range
0<b<=q/10000, with sufficiently small positive outer pads, satisfies
the test after rotation. The initial derivative has an exact finite-b
sign proof; no floating-point integration or unspecified small-b cutoff
is a premise.

Consequently these windows **cannot occur as any subwindow of any closed
twisted-periodic PMP extremal**, irrespective of its total cost or number
of pieces. This is stronger than the concurrent
[complete-piece endpoint filter](MINIMIZER_WINDOW_PMP.md), which only
disqualifies the particular external cuts as genuine switches.

Their fixed-endpoint global optimality remains valid. The contradiction
was in the old sufficient domain, not in Reinhardt. The continuation
test handles this entire family and a larger explicit phase region;
it does **not** exclude every L3 input or close any universal local gate.

### 3.3 Compactness and a uniform qualitative singular clearance

[GLOBAL_MINIMIZER_COMPACTNESS](GLOBAL_MINIMIZER_COMPACTNESS.md) normalizes
the cost multiplier together with all five actual cotangent coordinates
at the start of the period. It keeps abnormal limits and proves compactness
using the exact affine control transformation, uniform state/costate
convergence, and weak-star convergence of controls.

The complete-period frame and cost conditions give explicit time bounds:

\[
\frac{\log2}{9}\le T\le\frac{A_{oct}}3<\frac\pi3.
\]

The published finite bang-bang minimizer theorem and the vertex-arc
singular-endpoint exclusion show that **every** normalized lift of every
minimizer avoids the full singular locus. The compact family therefore
has a common positive distance epsilon_* from that locus.

This is a uniform statement over actual minimizers. It is not asserted
for all competitive local extremals or all arbitrary periodic PMP lifts.
It supplies no numerical epsilon_* and no dwell-time bound.

### 3.4 One finite bound for all global minimizers

[GLOBAL_CLOSED_VARIATION](GLOBAL_CLOSED_VARIATION.md) proves a separate
uniform local count near every nonsingular phase for trajectories satisfying
the minimizer edge-optimality condition. Write the reduced switching
covector equation as

\[
W'=\mathcal L(t)W+b(t).
\]

Transport its homogeneous part to place the covector in one fixed plane.
At a simple zero its first derivative is uniformly near a nonzero vector.
At a double zero outside the full singular locus its second derivative is
uniformly near a nonzero control-independent vector. These estimates hold
for all nearby initial phases and measurable controls.

Choose the three pairwise comparison lines in that plane and make a
small common rotation so each closed sector excludes one control vertex. Every projection
onto a line's normal has at most one or two zeros. The remaining time
intervals use only a fixed edge, and edge optimality bounds each by four
pieces. A finite cover of the compact family of minimizing phases gives

\[
N\le28\left\lceil\frac{A_{oct}}{3h}\right\rceil
\]

for common h>0. Therefore, using the external finite bang-bang input,
**one finite integer bounds all global minimizers**, not merely each
minimizer separately. The proof has
received three separate internal hand reviews.

This establishes a uniform existence theorem, not a computed case catalogue.
It does not give a lower bound on individual arc lengths. The following
quantitative strengthening fixes all constants apart from the clearance.

### 3.5 Effective conversion of clearance into a switch bound

[QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md)
proves

\[
\boxed{\quad N(\varepsilon)=28
\left\lceil\frac{T_{\max}}{c\min(\varepsilon,1,m)}\right\rceil.\quad}
\]

Here c>0 and m>0 are given by explicit finite formulas in that note.
The state inputs are K_X=9, Gamma=2/(15*sqrt(3)), and T_max=pi/3.
Three comparison lines and four possible small rotations give an explicit
margin sigma=1/(56025*pi*sqrt(2)), which is propagated through c. The
constants are intentionally coarse. Normal and abnormal lifts are retained.
The exact normalization is

\[
\|(\lambda,\Lambda_1,W)(0)\|=1,\qquad
A=\Lambda_1-\tfrac32\lambda J,\quad W=\Lambda_R,
\]

and the supplied clearance is

\[
\bigl(\|X-J\|_F^2+\|A\|_F^2+\|W\|_F^2\bigr)^{1/2}
\ge\varepsilon.
\]

For small epsilon this is an O(1/epsilon) bound. The proof uses an
explicit uniform Hamiltonian width, the three rotated guard lines, and the exact
estimate ||[[J,X],X]||_F >= 4||X-J||_F. Every time and derivative error
budget is given. There is no further unproved switch-count step after a
numerical clearance has been supplied. The compactness theorem proves
that some clearance exists in this normalization, but does not evaluate it.

### 3.6 A numerical subcase independent of the finite bang-bang input

[GLOBAL_SMALL_MULTIPLIER_BOUND](GLOBAL_SMALL_MULTIPLIER_BOUND.md) proves
\[
D\ge m-\sqrt{11/2}\,|\lambda|.
\]
Thus one normalized lift with `|lambda|<=m/sqrt(22)` has clearance at least
m/2 throughout its period. Exact evaluation of the coarse coefficient
bounds gives **N<10^5740**, including every abnormal lift. The rational
condition `|lambda|<=10^-1904` suffices. This theorem uses the explicit
state bounds, PMP, and E4, not Theorem 16.3.1 or a pre-existing finite
vertex representation.

The complementary normal lifts have `|lambda|>10^-1904`. They may safely
be rescaled to cost multiplier -1, with entire extended-covector norm
below `10^3807`. Their reduced singular locus is the single point
`(X,Lambda_1,W)=(J,-3J/2,0)`, with the frame omitted. The exact conversion
of a future rescaled clearance is recorded in that note. A bounded
phase domain does not itself exclude a neighborhood of its singular point;
that remains the principal numerical gate for the uncovered normal lifts.

## 4. Immediate continuation and stopping rules

1. **Completed:** prove and independently review the local uniform switch theorem.
   Transport the switching covector into a fixed two-dimensional plane;
   use finitely many guard lines whose scalar projections have uniformly
   nonzero first or second derivatives. Between their zeros a fixed
   control vertex is excluded. The established forward-alternation
   theorem bounds each remaining two-control block. Do not differentiate
   a piecewise switching function through control jumps without proof.
2. **Completed:** make that regular-domain estimate quantitative for an explicitly
   supplied singular clearance. State its dependence on the state domain,
   multiplier normalization, and clearance. If a step fails, record the
   actual missing inequality; do not substitute pathwise finiteness.
3. **Active research gate:** obtain a **numerical** singular clearance, or an explicit global
   continuation/index exclusion with the same boundedness consequence.
   This remains the principal research gate. The current L3 escape region
   is a useful exclusion certificate, not a cover of the whole phase domain.
   The precise target is a stated positive rational epsilon_0 in the
   normalization of Section 3.5. It is enough to supply one such lift
   for each minimizer; proving the stronger claim for all normalized
   minimizing lifts is also sufficient. Sampled phase values or a
   positive minimum on an unjustified truncation do not meet this gate.
4. Only when these steps give a certified integer may G4 enumerate its
   fixed set. If instead a global second-variation argument proves N<=5
   directly, use the retained through-five comparison and equality transfer.

The parallel variation check is also complete for the standard forward
family: [GLOBAL_FORWARD_INDEX](GLOBAL_FORWARD_INDEX.md) proves at least
2(k-1) negative directions for its N=3k+1 period. Its hand Fourier
calculation uses the full twisted-closed endpoint fiber, including
initial-state variation and all three frame constraints. The rank-three
implicit function theorem produces actual cheaper closed variations for
k>=2. This validates the method uniformly in that family, which was
already excluded by the retained cost comparison. It is not a new excluded
global class or a theorem for arbitrary asymmetric words.

## 5. Preserved contributions and validation boundary

Read the current [ledger](../CHECKLIST.md),
[source map](../SOURCE_MAP.md), and [audit](../DEEP_AUDIT_CHECKLIST.md)
for the exact scope of earlier certificates. The concurrent L1 needle
audit, different-word replacement, external-switch conditions, explicit
L1 filter, and full-domain L3 and L5 rank theorems are preserved. They remain
available for proving exclusions on parts of the global phase domain.

[LOCAL_FORWARD_REGULAR_DESCENT](LOCAL_FORWARD_REGULAR_DESCENT.md) adds an
exact same-word local improvement for every state-cyclic forward reference
with 1<q<=5/4 and an unspecified open neighborhood of each. It covers the
standard complete-switch windows and nearby asymmetric inputs, but not the
whole revised L1 domain. The standard global family was already cost-excluded;
this is reusable local variation information, not a new global family count.

The concurrent [SWITCH_COMPLETE_REDUCTION](SWITCH_COMPLETE_REDUCTION.md)
records revised necessary domains for all five local words. All five
analytic improvement targets on those domains remain open; that conditional
route is retained alongside the global one. The independent
[PADDED_L3_PMP_CONTINUATION](PADDED_L3_PMP_CONTINUATION.md) derives the
small-family boundary obstruction in different coordinates and also proves
a two-sided continuation cost obstruction. Our finite escape test adds an
explicit core-size range and a larger phase-region criterion; it does not
represent a second excluded global family.

Acceptance is a hand proof with the actual hypotheses, endpoints,
normalization, and boundary cases checked. Independent reviews here are
internal mathematical reviews, not external peer review or kernel
validation. The new global interface, compactness, finite escape, and
uniform local switch proofs have received separate hand reviews.

No Lean file is added or changed by this plan. Do not compile Lean, run
Lake or typechecking, or add, modify, or execute CI. Continue making small
coherent proof commits on the existing PR branch with [skip ci], keeping
the ledger, README, source map, audit, handoff, and PR description aligned.
