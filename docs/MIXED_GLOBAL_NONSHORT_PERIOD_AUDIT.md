# Independent audit of the uniform whole-M2 exclusion

Date: 2026-11-07. Independent internal mathematical review. No Lean,
Lake, typechecking or CI; no new expensive arithmetic replay was needed
for this assembly audit.

**Verdict: ACCEPTED.** The implication in
[MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION](MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION.md)
excludes the entire remaining M2 assignment for an actual competitive
minimizing period with at least six positive pieces after zero pieces
are deleted and equal neighboring controls are merged through the
twisted seam. The audited constituent exclusions cover every case
selected by the proof. No missing run length, orientation, successor
event, comparison chart or endpoint-rank case remains in this passage.

This accepts gate **M2.2** at the stated hand/computer-assisted proof
level. The unrestricted cost and affine-equality conclusions still
belong to their separate final assembly and dependency audit. The
geometric/PMP inputs and the arithmetic execution trust boundary retain
their named scope.

## 1. The minimum and smaller-turn choices are exhaustive

The finite active-margin sequence is positive and cyclic: at the true
seam the control labels and state margins are permuted together. Thus a
global smallest active margin exists and its comparison with every
other active margin survives any choice of cut.

[MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md)
gives the two possible neighboring sign patterns `++++` and `+--+`.
A mixed period has a reverse centre, whose established phase bound
places its squared margin below `4/3`; therefore the global minimum has
the same upper bound. The small-forward-minimum theorem excludes the
first pattern. Its three interior indices are distinct because this
theorem is explicitly restricted to at least six positive pieces.
Consequently the selected minimum is a reverse centre, strictly smaller
than its four nearest displayed neighbors. Repeated minima elsewhere
in the period remain possible and are retained.

The compact and reverse-centre bounds give `a>=2/15` and
`a^2<12/17`. The Casimir bounds used later are invariants of the given
whole-period normal covector, not parameters fitted to this window.
The two-short-bridge result is correctly used only to rule out short
runs on both sides; it is never used to require both sides to be long.

There are exactly two possibilities for the forward run beside the
chosen smaller adjacent turn: length one, or length at least two.
Either adjacent turn may be chosen when their margins are equal.
The short theorem includes equality in that ordering, and the nonshort
domain retains `c<=b`. In particular, a tie with one short and one
nonshort side is covered whichever side is chosen.

## 2. Orientation retains the physical problem and its covector

The reflection/time-reversal used here is the actual symmetry proved
in Sections 1--3 of
[MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md).
For the physical reflection `S=diag(1,-1)`, it transforms the state by
`X -> -SXS` and both reduced body costates by
`Lambda -> -S Lambda S`, with time reversed and the corresponding
control-label permutation. The physical multiplier `lambda=-1`
does not change sign. Physical cost, all Hamiltonian inequalities,
free-initial-state transversality and the frame/state/costate twists
are preserved.

The active margins are reversed in order without rescaling; the
switch signs are read in reverse order without being negated.
Thus the smaller-short and smaller-nonshort oriented interfaces apply
to the same minimizing problem. No independent edge multiplier or
locally fitted normal lift enters this argument.

For the nonshort orientation the actual consecutive labels and margins
are `0(p),1(b),0(a),2(c),0(d),1(r)`, with
`a<c<=b`, `a<b`, `p>a`, `d>a` and `r>=a`.
The first five inequalities follow from the reverse-centre structure;
the last uses the global active minimum. The second forward switch
after the chosen turn is exactly the nonshort assumption.

## 3. The two next-switch branches cover the first actual successor

Finiteness and positive durations supply the next actual switch after
arc `r`. After equal neighboring controls are merged, it goes to one
of the other two labels, hence is forward or reverse. This remains
true when the successor crosses the chosen seam.

The [continuation interface](MIXED_SMALLER_TURN_CONTINUATION.md) and
its [audit](MIXED_MINIMUM_CONTINUATION_INTERFACE_AUDIT.md) give:

| Actual successor | Necessary condition retained | Exclusion used |
| --- | --- | --- |
| Forward | Transported next norm `t>=3/4` | Both forward endpoint covers |
| Reverse | `w<=Sec(a,r,d)` and `r^2>=ad` | Reverse boundary cover |

In the reverse case the next reverse centre `A` is an active margin of
the same period, so `A>=a`, including equality. Positive duration gives
`A<d`; turn log-concavity gives `r^2>Ad`. Together with the outgoing
reverse-switch inequality this justifies extension of the secant
average from `[A,d]` to `[a,d]`. In the forward case the actual outgoing
derivative supplies the floor independently of the subsequent active
margin and eventual run length.

The proof uses the first actual successor, not an arbitrary later root
of a switching expression. A run of length exactly two falls into the
reverse row; longer runs fall into the forward row. Nothing requires a
bound on the run length.

## 4. Seam continuation does not double-count cost

Sections 1--3 of [GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md) extend
the same actual state and costates by their prescribed conjugations,
with simultaneous cyclic relabeling of the controls. This validates
all necessary switching and transport identities through a seam.
It does not invoke the separate full-rank-window theorem in that file.

The short-side cost and polar-angle argument is applied only to its
two consecutive actual turn arcs. With at least six positive pieces
they are distinct and form a proper subinterval of one period after
moving the cut; the complement has positive duration. The complete
period's positive polar angle is `pi/3`, so the strict window-angle
filters and the completion budget apply to precisely that interval.
The two actual secant equalities are what identify its rational scalar
cost expression with its physical cost.

Longer padded displays may meet an already named cyclic index; for
example the next event after six displayed arcs may reach the first
cyclic index when there are six pieces. Such displays supply only
necessary identities of the continued lift. Repeated indices impose
additional equalities, which may safely be omitted in an enlarged
scalar comparison domain. No cost or angle of a multi-period display
is charged to a one-period budget, and no displayed window is assumed
to be a closed competitor.

## 5. The artificial-boundary passage loses no actual chart

The accepted boundary comparison increases `b` to `b*=K/(a+c)-a`
along the unique scalar first-root equation with `a,c,d,r,v` fixed.
Its explicitly negative root coefficient and differential identity
preserve the incident upper norm and give `w*<w_actual`. This is a
scalar comparison, not a new trajectory or an endpoint deformation.

The maximum is recomputed after that comparison:
`epsilon'=max(delta1,delta2)`, with the artificial `delta0=0`.
The hand small-parameter theorem applies at `l0=0` when
`epsilon'<=1/32`. Its complement is covered by the two closed maximum
charts `l1=1` and `l2=1`, including their overlap and all maximum ties.
This also covers original points whose largest parameter was
`delta0`; their original maximum is not used to decide the boundary
corner. The incoming missing-control inequality justifies `d<=c`
in chart 2.

The compact bound used for inactive margins is `m=2/15`, not the
selected active minimum `a`. In particular the contractions
`cd+m(c+d)<=4` and `dr+m(d+r)<=4` follow from actual compact states.
No assumption that all inactive margins are at least `a` is made.

The low-a exclusion uses neither successor alternative and hence
supplies `a>1/2` before either forward endpoint cover is invoked.
There is no circular dependence on the forward conclusion. The reverse
comparison retains the secant ceiling but transfers no Casimir cap.
For the forward case, the actual norm floor gives
`w*<=w_actual<=wcap`; concavity gives an exhaustive alternative between
the two endpoint Casimir tests. It does not require both endpoints to
satisfy the cap and does not assume that the cap is preserved by
`b -> b*`.

## 6. Ties, vanishing durations, edge controls and rank defects

Weak third-control ties are retained as weak Hamiltonian inequalities.
The argument does not replace them by generic strict third-control
gaps. The strict inequalities for positive actual incident arcs are
those already established by the actual-switch and reverse-centre
theorems; closed comparison faces remain in the scalar domains.

No uniform positive lower bound on an individual arc duration is used.
Zero pieces are deleted before the finite cyclic representation is
chosen. If that reduces the representation to at most five pieces it
belongs to the separate terminal classification. Vanishing-duration
comparison faces use analytic secants/divided differences and the
cancelled root formulas. At `epsilon'=0` no positive actual nonshort
window is asserted; the hand corner controls the positive neighborhood
and its regular directional extension without adding a free singular
root norm.

Measurable and edge-valued minimizing controls enter through
[singular clearance](SINGULAR_COST_BUDGET.md), the
[measurable-edge theorem](MEASURABLE_EDGE_PMP_BOUND.md), and the
[finite-representation theorem](QUANTITATIVE_REGULAR_SWITCH_BOUND.md),
before [global normality](GLOBAL_NORMALITY.md) is used. The M2 proof
therefore adds no finite-word hypothesis to the original competitor
class and does not rely on approximation by a growing word catalogue.

No endpoint differential is inverted and no constrained descent is
inferred from an ordinary Hessian. The only root inversion is the
one-dimensional equation with its proved strict coefficient sign.
The argument applies to an actual normal lift even if an endpoint map
has deficient rank or the normalized lift is not unique.

## 7. Accepted exclusions and the scope of closure

The assembly uses the following completed covers through their named
theorems and independent source/domain/completion audits:

| Domain | Roots | Nodes | Excluded leaves |
| --- | ---: | ---: | ---: |
| [Smaller short side](MIXED_SMALLER_SHORT_CERTIFICATE_AUDIT.md) | 1 | 107,977 | 53,989 |
| [Common low-a boundary](MIXED_NONSHORT_LOW_A_BOUNDARY_AUDIT.md) | 2 | 74,772 | 37,387 |
| [Reverse boundary](MIXED_NONSHORT_REVERSE_BOUNDARY_AUDIT.md) | 2 | 106,134 | 53,068 |
| [Forward lower endpoint](MIXED_NONSHORT_FORWARD_BOUNDARY_AUDIT.md) | 2 | 37,940 | 18,971 |
| [Forward upper endpoint](MIXED_NONSHORT_FORWARD_BOUNDARY_AUDIT.md) | 2 | 60,976 | 30,489 |

Each accepted forest has zero pending and unresolved records and
satisfies `nodes = 2*leaves - roots`. The new boundary sources and
complete fresh replays were separately audited; this whole-period
review does not substitute a count identity for those acceptance
records. No partial record from the superseded five-variable cover
chain is a premise.

The smaller-short contradiction and the two actual-successor
contradictions exhaust the chosen minimum. They uniformly exclude M2
for all stated positive unequal factors and all finite run lengths.
Together with the separately accepted R, sufficient whole-period M1,
M3 and F exclusions, this discharges the remaining at-least-six-piece
case of the fixed whole-period partition. The through-five cost and
equality argument, its external inputs and the final unrestricted
conclusion are the subject of
[GLOBAL_COST_EQUALITY_ASSEMBLY](GLOBAL_COST_EQUALITY_ASSEMBLY.md) and
its independent global review.
