# A fixed five-template route to a uniform bound

**Historical sufficient route.** Follow
[GLOBAL_REDUCTION_PLAN](GLOBAL_REDUCTION_PLAN.md) for the active plan.
The new global notes prove an existential uniform switch bound by compactness
and a uniform regular-domain theorem; no numerical integer is yet available.
They also exclude the small padded L3 counterexample family from every closed
PMP occurrence by finite forced exit. The local coverage and failed sufficient
statements recorded below retain their original scope.

Date: 2026-11-06. Priority: establish boundedness before further whole-word comparisons.

## Status: coverage proved; the original L3 sufficient statement is false

**Revised candidate:** [SWITCH_COMPLETE_REDUCTION.md](SWITCH_COMPLETE_REDUCTION.md)
defines stronger necessary input domains using one whole-window PMP lift and
both external-switch ties. Their necessity and the conditional five-target
implication are proved; all five revised cost-improvement assertions are open.
The original larger-domain statements below are preserved with their original
status, including the false L3 premise.

**Update (2026-11-07):** [LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md)
proves that some eligible `021210` windows admit no cheaper replacement with
at most six positive vertex pieces. The independently reviewed strengthening
[LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md)
removes that cap: sufficiently small members are globally optimal for their
fixed endpoints among all measurable simplex controls and all terminal times.
It adds the explicitly checked ASZ sufficient-optimality theorem. The costs
can be arbitrarily small.
The original sufficient package below therefore cannot be completed on its
stated domain. The coverage proof and conditional implication remain valid;
L1, L2, L4, and L5 remain open. These local examples have not been shown to
occur in actual closed minimizers, so this is not a counterexample to
Reinhardt or Hales's geometrically embedded link-reduction conjecture.

[MINIMIZER_WINDOW_PMP.md](MINIMIZER_WINDOW_PMP.md) now proves an additional
necessary condition for selected windows of six complete pieces: the same
PMP lift has an inactive Hamiltonian tie at both external endpoints. It
excludes the exact endpoint-unique L1 input and the sufficiently small
padded L3 examples from selected complete minimizer windows. The explicit
L1 equations are in
[LOCAL_FORWARD_ENDPOINT_FILTER.md](LOCAL_FORWARD_ENDPOINT_FILTER.md).
These restrictions do not establish a universal replacement on the remaining
domain; the original larger-domain claims below retain their recorded status.

This note supplies a complete hand proof of a finite coverage statement:

> If a finite, cyclically reduced minimizing trajectory has at least six
> positive vertex pieces, then it contains one of five specified six-piece
> windows, after a cyclic relabeling of the controls.

The proof uses the existing local exclusion of forward four-piece alternation.
It does NOT assert that the five windows have already been excluded.

The originally proposed package consists of five local improvement
statements on explicit fixed-dimensional domains. Their conjunction would
force every global minimizer to have at most five pieces, but its L3 premise
is false. A repair must supply additional necessary conditions for actual
minimizers or a different uniform reduction. The existing comparison through
five pieces and its equality classification are retained. Increasing-length
whole-word enumeration does not repair this failed sufficient lemma.

**Not established by this local package:** a uniform switch bound, any of the five universal local
improvement statements, the unrestricted cost inequality, or kernel validation.
A finite list of inputs to an implication is not a proof of those inputs.

## 1. Exact finite catalogue

The labels 0,1,2 are vertex controls, not polygon sides. For consecutive
unequal labels write + if the label increases by one modulo three, and -
if it decreases by one. The five templates are:

| ID | Five successive switch signs | Six control labels | Universal local exclusion |
| --- | --- | --- | --- |
| L1 | +++++ | 012012 | Open |
| L2 | ----- | 021021 | Open |
| L3 | --+-- | 021210 | **False on this domain even with arbitrary measurable replacements** |
| L4 | +--++ | 010201 | Open |
| L5 | ---++ | 021012 | Open |

Only cyclic relabeling is used in this table. Time reversal, reflection,
and arbitrary permutations are unnecessary for the coverage proof.

Each INPUT consists of two initial-state coordinates and six positive
arc factors. Initial/final states and unequal durations are unrestricted
apart from the explicit eligibility tests in Section 4. The ambient input
dimension is eight, independent of the total length of a surrounding word.
The targets are whole parameter domains, not sampled factor tuples.

The original sufficient local statement for each row was:

> Every eligible six-piece window of that type has an actual strict-star
> replacement, with the SAME initial and final frame AND state, and strictly
> smaller cost. The replacement may have up to six vertex pieces; elapsed
> time is free.

Allowing six pieces is deliberate. A strictly cheaper six-piece replacement
already contradicts minimality. We do not need a path that reaches a
five-piece boundary, an attained minimum on a noncompact fiber, or an
iterative shortening algorithm. A nearby same-word variation is sufficient,
but is not assumed to exist. A replacement with a different word of at most
six pieces also closes the local statement. There are only finitely many
such replacement words (189 nonempty reduced words before symmetries).

## 2. Hand proof that these five templates cover every longer minimizer

### 2.1 Use the actual twisted cyclic extension

The original terminal conditions are

    g(0)=I,  g(T)=R,  X(T)=R^(-1) X(0) R.

The actual cost-preserving extension and rebasing in VERTEX_WORD_REDUCTION
extend control labels by i(t+T)=i(t)+1 modulo three. Choose the beginning
of a period at a genuine switch, and merge equal neighboring controls,
including the twisted seam. Let N be the number of positive pieces per
period in this cyclically reduced description.

If the labels in one period are i_0,...,i_(N-1), put i_N=i_0+1.
Every neighboring pair is distinct. The switch signs are periodic with
period N, even though the labels themselves have a twist. In particular
one must NOT impose the ordinary untwisted seam i_N=i_0. Their signed sum
is congruent to 1 modulo three; the proof below does not need this extra
restriction.

When N>=6, any five consecutive signs correspond to six consecutive
positive arcs fitting within ONE period. If the window crosses the old
cut, rebase the actual trajectory at its first switch. A six-arc window
spanning several copies of a shorter period is not allowed. This distinction
is essential: the four-piece octagon has an indefinitely repeated + sign
sequence, but does not have six arcs within its one-period interval.

### 2.2 The already excluded pattern is +-+

FORWARD_ALTERNATION_EXCLUSION proves that a positive four-arc window

    i, i+1, i, i+1

has a strictly cheaper endpoint-preserving replacement. Its sign pattern
is +-+. Thus a minimizing trajectory with N>=6 has no +-+ anywhere in
its periodic sign sequence, including across the twisted seam.

If both signs occur, every maximal run of - signs has length at least two:
a run of exactly one - between + signs would be +-+.

### 2.3 The run argument is exhaustive

There are three possibilities.

1. Every sign is +. Five consecutive signs are +++++, giving L1.
2. Every sign is -. Five consecutive signs are -----, giving L2.
3. Both signs occur. Choose a maximal run of + signs.

In the third case:

- If the chosen + run has length one, its two neighboring - runs each
  have length at least two. It supplies --+--, giving L3.
- If the + run has length at least two and the preceding - run has length
  exactly two, include the + immediately before that - run and the first
  two + signs afterward. This supplies +--++, giving L4.
- If the + run has length at least two and the preceding - run has length
  at least three, take the last three - signs and first two + signs.
  This supplies ---++, giving L5.

These alternatives exhaust all run lengths. Starting the control labels
at 0 gives exactly the table in Section 1. This proves coverage for EVERY
N>=6, not just for a tested maximum N. No computer enumeration is a premise.

The five cyclic sign types are genuinely different for this coverage
argument. For example constant +, constant -, repetitions of --+,
repetitions of --+++, and repetitions of ---++ demonstrate the respective
run regimes. These are combinatorial examples, not assertions of existence
of minimizing trajectories with those signs.

## 3. Why closing the five local cases would finish the conjecture

Use the published finite bang-bang theorem for a global minimizer, the
geometric/control correspondence, and the existing through-five hand
comparison with its equality case.

Let an arbitrary global minimizer be given. Its cost is at most the concrete
octagon cost A_oct, and its reduced vertex description is finite. If N>=6,
Section 2 produces a window in one of L1-L5. The window is eligible as
explained below. A proved local improvement for that row could be spliced
into the full trajectory, preserving g and X at both seams. Translate the
rest of the trajectory by the change in elapsed time. The terminal frame,
twisted state endpoint, and integral state equations are unchanged, while
total cost strictly decreases. This contradicts global minimality.

Consequently all global minimizers would have N<=5. The previously proved
comparison through five pieces gives cost >=A_oct, while the octagon gives
the reverse inequality. Its equality classification then applies to every
minimizer and gives the affine class of the octagon.

In symbols, with the cited reduction and existing hand results as inputs,

    (L1 and L2 and L3 and L4 and L5)
        implies every global minimizer has at most five pieces
        implies Reinhardt minimality and affine rigidity.

This is a proved CONDITIONAL implication, whose original L3 premise is now
refuted. None of its five analytic exclusions is complete. Strict cost improvement is enough;
we need not actually construct a six-to-five replacement in every case.

## 4. Explicit, fixed-dimensional eligibility domain

The complete P0 eligibility and splice proof is in
[MINIMIZER_WINDOW_AUDIT.md](MINIMIZER_WINDOW_AUDIT.md). It validates the
input-sector test after left normalization and the reverse geometric bridge
for a finite cheaper replacement; it proves none of L1--L5.

### 4.1 State coordinates

Use the triangular coordinates of FIVE_ARC_PROGRESS. The generators and
vertex tangent matrices are

    D_0=[[-1,0],[0,1]],
    D_1=[[1,-2],[0,-1]],
    D_2=[[1,0],[2,-1]],

    T_0(q)=[[q,0],[0,1/q]],
    T_1(q)=[[1/q,q-1/q],[0,q]],
    T_2(q)=[[1/q,0],[1/q-q,q]].

For p_j=tr(D_j X), strict-star states satisfy

    p_j>0,    p_0*p_1+p_1*p_2+p_2*p_0=4.

Choose p_0=a>0 and p_1=b>0 with ab<4. Then

    p_2=c=(4-ab)/(a+b)>0,
    X=(1/2)[[-a,a+c],[-a-b,a]].

Thus there are exactly two free initial-state coordinates; no additional
initial-shape parameter is hidden. Left multiplication of the whole frame
normalizes the window's initial frame to I without changing X or cost.

### 4.2 Six factors and full-arc feasibility

For each of the six pieces take q_k>1. On label i, with initial margins
(a,b,c)=(p_i,p_(i+1),p_(i-1)), the endpoint update is

    p_i -> a,
    p_(i+1) -> (a+b)q-a,
    p_(i-1) -> (a+c)/q-a.

Its duration is (a/2)log q. One margin is constant, one increases, and one
decreases; consequently positivity of all endpoint margins is equivalent
to strict-star membership throughout the whole closed arc. Equivalently
1<q<1+c/a. Require these tests at each of the six stages.

The normalized cost J=C/sqrt(12) is the sum of the exact arc costs

    J_i=(a/8)[(a+b)(q-1)+(a+c)(1-1/q)-a log q].

The competitive-window cost condition is J<=delta_oct, where

    delta_oct=(8-4sqrt(2)-log 2)/(2sqrt(2)-1).

Every window of a global minimizer satisfies it, since the total cost is
at most A_oct and the cost density is strictly positive.

### 4.3 Retain the geometric sector restriction

A generic long local control segment need not be a nonrepeating part of a
balanced convex boundary. Do not silently remove this restriction from
a proposed link-reduction theorem.

In the present coordinates put

    v_0=(1,1), v_1=(1,0), v_2=(0,-1), v_(j+3)=-v_j,
    R=[[0,1],[-1,1]],    [v,w]=-det(v,w).

Then R v_j=v_(j+1) and [v_j,v_(j+1)]=1. The minus sign compensates for
the orientation-reversing change to the triangular coordinates. For a
window starting at frame I require, at each time s,

    [v_j,g(s)v_j]>=0,   [g(s)v_j,v_(j+1)]>=0  for every j.

For 0<s<duration both inequalities are strict. At the initial endpoint
the first is zero; at the final endpoint the second may be zero if the
window is the whole fundamental interval.

An actual minimizing balanced boundary satisfies these conditions: after
rebasing, each component starts at its j-th contact and proceeds simply
in the positive direction toward the next contact at time T. A subwindow
ending no later than T remains in the corresponding radial sector.
Convexity and the origin being interior give a single positively ordered
radial traversal. This uses the actual geometric representation, not only
the matrix endpoint g(T)=R.

The restriction is finite algebra, not a new unknown curve. For a partial
arc of factor r in [1,q], initial state X, and active margin a, its frame
increment is

    F_i(X,r)=I+(a/4)[(r-r^(-1))X-(r+r^(-1)-2)X D_i].

This follows by the constant-control integration, or directly from
V=gX, V'=-(2/a)VD_i, and the state conjugation equation. Multiplying by
the fixed preceding frame shows that each sector determinant is a Laurent
polynomial of degree at most one in r. Multiply by r>0: each condition is
an ordinary quadratic inequality on [1,q]. Its minimum is checked at the
two endpoints and, when relevant, its single interior vertex. The strict
interior conditions must also be checked when the minimum is zero.
There are finitely many such tests (opposite j indices duplicate them).

These restrictions intentionally describe a necessary superset of windows
of a global minimizer. L3 on this explicit superset is now refuted, even
with arbitrary measurable replacements; the other four targets remain open.
The counterexample invalidates that sufficient claim, not Reinhardt, and
must not be hidden by changing the word-length or replacement-piece cutoff.

## 5. The exact local endpoint map is not the closed-word endpoint map

Define polynomial state half-factors

    Q_0(q)=[[1,0],[0,q]],
    Q_1(q)=[[q,1-q],[0,1]],
    Q_2(q)=[[q,0],[q-1,1]].

They equal sqrt(q) times the true half-factors; the scalar cancels in
conjugation. For fixed initial X_0 set

    H=Q_(i_6)(q_6)...Q_(i_1)(q_1),
    X_end=H X_0 H^(-1),
    F=T_(i_1)(q_1)...T_(i_6)(q_6).

The two product orders are different. Exact endpoint preservation means

    F_new=F_old AND X_end,new=X_end,old.                 (E)

Indeed V_end=X_0 F and g_end=X_0 F X_end^(-1). Thus (E), with the initial
state fixed, preserves both actual endpoints. Preserving only F, its trace,
or a holonomy eigenvalue is insufficient.

There is NO condition F=R for a general local window. That is why the
completed global closed-word comparison for 012012 does not close L1.
Similarly a deformation changing the initial state cannot be inserted
into a fixed interior window.

A replacement with at most six vertex pieces uses exactly the same update,
endpoint, and cost formulas, with its own finite word and nonnegative
log factors; factor-one pieces are deleted. Require positive state margins
at every endpoint. This constructs a genuine piecewise-smooth integral
trajectory. The replacement need not independently satisfy the original
window's sector test: after splicing it is an actual lower-cost closed
control competitor, and the geometric/control comparison supplies the
contradiction. A small same-word variation normally retains the sector
conditions as well, but this is not needed as a hidden extra premise.

## 6. Three endpoint equations can be eliminated exactly

All five chosen words end in three DISTINCT labels. The tangent product
of such a triple has an explicit inverse on its positive-factor cell.
It suffices to record the two cyclic orientations.

If M=[[A,B],[C,D]]=T_0(p)T_1(q)T_2(r), direct multiplication gives

    p^2=(A+B)/(C+D),
    q^2=1+B(C+D),
    r^2=D/(C+D).

If M=T_0(p)T_2(q)T_1(r), the corresponding identities are

    p^2=(A+B)/(C+D),
    q^2=1/[A(C+D)],
    r^2=(A+B)/A.

All denominators are positive on the image of a positive triple. The
positive square roots uniquely recover its factors. Cyclic relabeling
handles the other permutations. These formulas also prove local smooth
invertibility; it is not merely a dimension count.

For a fixed local tangent endpoint F_target, choose the first three
factors, form their product P, and apply the appropriate inverse to
M=P^(-1)F_target. This eliminates the three tangent-endpoint equations
exactly. Near the original positive tuple the required open factor cell
persists. Only two terminal-state equations remain on three variables.

At points where these two equations have rank two, the endpoint fiber is
one-dimensional. A nonzero first variation supplies descent. At a
stationary point, a negative constrained second variation also supplies
an exact local improvement. These are proposed certificates, not asserted
sign theorems for L1-L5.

There is now an exact obstruction to asserting that such a negative
variation always exists: [LOCAL_FORWARD_SIX.md](LOCAL_FORWARD_SIX.md) gives
an eligible L1 input with rank-five endpoint map, zero first constrained
variation, and strictly positive second variation. It is a strict local
minimum on its same-word endpoint fiber. A different-word or nonlocal
replacement remains possible, so this does not refute L1 itself.

The [full-arc needle audit](LOCAL_FORWARD_NEEDLE_AUDIT.md) proves that this
same input is a strict strong local minimum in the augmented normalized
free-log-time formulation, even among arbitrary nearby controls. Its
published sufficient-optimality theorem is checked explicitly; no global
comparison with distant replacements follows from that theorem.

For this exact input, [LOCAL_FORWARD_NONLOCAL_REPLACEMENT.md](LOCAL_FORWARD_NONLOCAL_REPLACEMENT.md)
now supplies two exact six-piece `012021` replacement certificates with cost
decrease greater than `1/100000`. An implicit-function argument continues
them to nearby eligible inputs. Neither certificate covers the full L1 domain.

[LOCAL_L3_STRONG_MINIMUM.md](LOCAL_L3_STRONG_MINIMUM.md) gives a stronger
nearby-method obstruction for L3: an eligible input with a positive constrained
Hessian and strict full-arc control inequalities is a strict strong local
minimum in an explicitly normalized free-log-time formulation. This includes
arbitrary nearby controls. The proof supplies no global exclusion of distant
cheaper replacements, so it does not refute the stated L3 existence claim.

The distinct small-window construction in
[LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md) now
does refute that at-most-six existence claim. It combines an exact edge
dual, a compactness argument, positive interior third-control gaps, and two
normal endpoint coordinates. This is a global comparison with every word
of length at most six, not an inference from local optimality alone.
The separate GLOBAL_MINIMUM note goes further: it verifies strong optimality
for one fixed padded reference, then uses compactness and the edge dual to
globalize its sufficiently small trims among arbitrary measurable controls.

For L1, [LOCAL_FORWARD_RANK.md](LOCAL_FORWARD_RANK.md) now proves that the
full endpoint rank is five throughout the positive strict-star domain, so
these two remaining equations have rank two everywhere. The proof resolves
the state endpoints in active margins and signs four explicit determinant
terms. It applies without cost or sector restrictions. It does not assert
uniform conditioning as factors collapse or margins approach zero.

The independent paired-holonomy determinant in
[LOCAL_SIX_VARIATION.md](LOCAL_SIX_VARIATION.md) also proves full rank five
throughout L4. [LOCAL_MIXED_SIX_RANK.md](LOCAL_MIXED_SIX_RANK.md) proves
full rank five throughout L3, using the rank-three edge endpoint map and
two independent asymmetric normal columns. Rank zero and rank one points
are also resolved throughout L5 by the five-prefix proof in
[LOCAL_L5_ENDPOINT_RANK.md](LOCAL_L5_ENDPOINT_RANK.md). They MUST still be
treated for L2. In particular,
dimension counting alone proves neither a smooth fiber nor a decreasing
direction. Stationary points cannot be discarded in any template. Failure of
this same-word local method alone does not settle different-word replacement.
The separate L3 counterexample does settle its original target negatively;
neither result is permission to resume enumeration at larger N.

### A sufficient variant may use more replacement pieces

The bound of six on the replacement word is an additional sufficient target,
not a requirement of the global-minimality contradiction. If every eligible
input in each of the same five templates has any actual strictly cheaper
finite-piece replacement with the same endpoints, Section 3 still applies.
The improved full trajectory may have more pieces: it is used only to
contradict minimality of the original trajectory.

For example, [LOCAL_REVERSE_SIX.md](LOCAL_REVERSE_SIX.md) proves an exact
seven-piece improvement for every q>1 in the equal-factor, state-cyclic
reverse-six subfamily. It supplies no universal L2 theorem. The original
at-most-six L3 statement is false, and LOCAL_REVERSE_SIX_GLOBAL_MINIMUM
now refutes its arbitrary-finite-replacement relaxation too. The logical
sufficiency of that relaxation remains true, but it cannot be established
on this stated superset. More replacement pieces do not repair the route;
additional necessary global-minimizer conditions or another uniform theorem
are required. No growing whole-word enumeration is justified.

## 7. Bounded dimension versus a certified bounded search

Each input has eight real coordinates. One can put them in a bounded box:
write p_j=S lambda_j, lambda_j>0, sum lambda_j=1, and

    S=2/sqrt(lambda_0 lambda_1+lambda_1 lambda_2+lambda_2 lambda_0),
    t_k=(q_k-1)/(q_k+1) in (0,1).

This is a parameter compactification, NOT a certified finite numerical
search. At the simplex vertices S can diverge; as t_k approaches 1, q_k
and its logarithm diverge; t_k approaching 0 is arc collapse. Boundary
asymptotics, lost star margins, singular endpoint ranks, and vanishing
variation margins cannot be omitted. An interval mesh on a smaller box
would prove only a restricted statement.

Existing exclusions alone do not imply a cutoff. The arbitrarily long
words (012)^m0 pass the cyclic ordering test and avoid forward alternation.
The new standard regular-family cost comparison handles specific equal-arc
members, not arbitrary asymmetric words with this pattern.

## 8. Literature, provenance, and validation boundary

- Hales, On the Reinhardt Conjecture (2011), Section 7.6, Conjecture 56
  formulates endpoint-preserving six-to-five link reduction, and Lemma 58
  explains its use with the five-link comparison:
  https://arxiv.org/html/1103.4518#S7.SS6
- Hales-Vajjha, Packings of Smoothed Polygons (2024), Theorem 16.3.1
  supplies the finite bang-bang minimizer theorem. Appendix B.4 explicitly
  does not supply a uniform edge bound:
  https://arxiv.org/html/2405.04331v1#Ch16.S3
  https://arxiv.org/html/2405.04331v1#A2.S4
- Local inputs: FORWARD_ALTERNATION_EXCLUSION.md and
  VERTEX_WORD_REDUCTION.md. Terminal comparison: FOUR_LINK_HAND_PROOF.md,
  FIVE_ARC_PROGRESS.md, and REVERSE_FIVE_ARC.md. State/endpoint formulas:
  WORD_HOLONOMY.md and the triangular factors in FIVE_ARC_PROGRESS.md.

The new contribution of this note is the FIVE-TEMPLATE coverage proof and
an explicit bounded-dimensional sufficient package, not a proved new
local cost exclusion or a claim of priority for link reduction itself.

The run proof and endpoint inversion formulas are hand arguments. A finite
transition-graph check can cross-check coverage without enumerating any
maximum total length. Exploratory floating-point searches on endpoint
fibers are not certificates, especially when a solver fails to converge.
The coverage proof in Sections 1-2 has received an independent hand review of
the exact sign catalogue, twisted seam, run argument, and one-period window
condition. This review does not establish the analytic local claims. There is
no claim of Lean compilation or kernel validation for the new reduction.

## Stop rule

Whole-word case expansion is paused. Work counts toward the boundedness
checkpoint only if it proves or refutes one of L1-L5 on its ENTIRE stated
domain, or supplies a genuinely different uniform bound with a complete
coverage theorem. Rewriting these unproved or refuted statements as checked boxes,
proving another closed six-piece family, or increasing the tested N does
not close this checkpoint.

