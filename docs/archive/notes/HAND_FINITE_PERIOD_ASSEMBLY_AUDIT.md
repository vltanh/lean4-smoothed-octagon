# Final review of finiteness, normality and the whole-period split

Date: 2026-11-08 UTC. **Accepted Sections 3--4 of
[HAND_COST_EQUALITY_THEOREM](HAND_COST_EQUALITY_THEOREM.md).**
This is an independent review of the finite-before-normal ordering,
the identity of the actual lift, and the exhaustive uniform period
exclusion. The companion
[short-period interface review](MIXED_SMALLER_SHORT_HAND_PERIOD_AUDIT.md)
accepts S7 and its H-S scope. The unrestricted competitor comparison,
terminal cost formulas, affine equality transport and external geometric
source boundary have their own separate final review.

## 1. What this part of the assembly is allowed to assume

Begin with the retained geometric minimizing realization from Section 2
of the final theorem. At this point it is an actual global minimizer in
the original measurable-control class, has its state and frame twisted
endpoints, is competitive with the explicit octagon, and lies in the
common compact strict-star state domain. Its control is not yet assumed
piecewise constant. There is no normality assumption.

The compact-state input concerns every point of this same realization
and all three physical margins, including inactive controls. Its
geometric source boundary is audited separately in
[COMPACT_DOMAIN_SOURCE_AUDIT](COMPACT_DOMAIN_SOURCE_AUDIT.md).
The later finite bang-bang and singular-basin theorems from the external
source are not imported by this dependency path.

## 2. Finiteness genuinely comes first

The order of application is essential and is correct.

| Step | Exact hand input | What has not yet been assumed |
| --- | --- | --- |
| Initial free-time lift | [GLOBAL_PERIODIC_PMP, Sections 1--3](GLOBAL_PERIODIC_PMP.md) | Neither a finite representation nor normality. |
| Positive singular clearance | [SINGULAR_COST_BUDGET](SINGULAR_COST_BUDGET.md) | Abnormal lifts and all conserved-determinant sectors remain allowed. |
| Four-piece edge property E4 | [MEASURABLE_EDGE_PMP_BOUND](MEASURABLE_EDGE_PMP_BOUND.md) | The original edge control may be arbitrary measurable. |
| Finite vertex representation | [QUANTITATIVE_REGULAR_SWITCH_BOUND](QUANTITATIVE_REGULAR_SWITCH_BOUND.md) | No minimum individual duration, generic switching or normality. |
| Normality and physical normalization | [GLOBAL_NORMALITY, Sections 1--6](GLOBAL_NORMALITY.md) | Finiteness is now available; the same original lift is used. |

The first PMP is on the actual endpoint submanifold with free initial
state. It retains the state-costate twist as well as the group-costate
endpoint. The reduced state covector represents its actual cotangent
class; an ambient multiple of the state matrix is not mistaken for a
nontrivial multiplier.

The singular-budget theorem uses the original whole-period endpoint and
competitive cost. It supplies its positive clearance in a unit norm on
the full extended cotangent vector, including the cost multiplier. The
normal and abnormal possibilities are both included. In particular it
does not divide by the cost multiplier before normality is proved.

### Why the separate edge multiplier does not break the same-lift chain

The E4 theorem deliberately uses a separate fixed-endpoint PMP for an
edge restriction of the actual minimizer. This is legitimate because
it proves a property of the original control, not a replacement for its
full-system covector. The monotone abscissa transformation is invertible,
preserves null sets and the physical endpoint data, and leaves physical
terminal time free. A cheaper nearby edge segment would splice into the
original period with the same state and frame endpoints and smaller
full cost. Hence the actual restriction is a local minimum of the
transformed edge problem.

Its integrating factor gives

\[
F'=-\rho(p_s+\lambda x^2),\qquad \rho>0.
\]

If the polynomial is nonzero it has at most two real zeros, so Rolle's
theorem gives at most three zeros of F and at most four vertex pieces.
If the polynomial vanishes identically, nontriviality makes F a nonzero
constant. Both abnormal cases are explicitly included. Thus E4 states
that the original control itself agrees almost everywhere with at most
four pieces on every missing-control interval. No newly chosen edge
covector is used later for full-period stationarity or a Casimir budget.

The quantitative guard theorem applies E4 to the same original lift and
its clearance. Its explicit finite integer bound follows from hand norm
and derivative estimates. Its large size is immaterial: the final proof
uses only finiteness and never enumerates words up to that number.
There is no reliance on a numerical escape experiment or a prior
finite-switch theorem.

The resulting changes are only on null sets, followed by deletion of
zero durations and merging equal neighbors, including the genuine
seam. These preserve the integral state and frame, cost, endpoint data
and original adjoint equations almost everywhere. The original
Pontryagin lift therefore remains a lift of the finite positive
representation.

## 3. Normality belongs to that same finite period

The normality theorem assumes a finite positive strict-star vertex
representation with the actual twisted complete-period state, frame
and state-costate endpoints. It excludes every abnormal nontrivial
lift by direct same-covector identities and a cyclic sign contradiction.
Its result is stronger than existence of some unrelated normal
multiplier: the original lift is normal.

No endpoint-rank assumption, uniqueness of a multiplier or symmetric
factor hypothesis is invoked. Zero missing-control Hamiltonians and
triple ties are handled explicitly. Backwards matrix identities used
for a vanishing pairing do not assert backwards Hamiltonian
inequalities or an admissible negative-time competitor.

The last contradiction uses the actual extension

\[
i_{j+N}=i_j+1\pmod3.
\]

If an abnormal lift survived the local tests, its signs would alternate,
so its labels would have period two and use two labels. The twist makes
that label set invariant under addition by one modulo three, which is
impossible for a two-element subset. The local tests may cross more than
one seam because they use only the necessary PMP equations of the actual
extended lift, not optimality of a repeated multi-period competitor.

The initial maximizing convention has \(\lambda\le0\), so exclusion
of zero gives \(\lambda<0\). Positive homogeneous rescaling to
\(\lambda=-1\) preserves all signs and both cotangent endpoint
relations. This same physically normalized covector is used in every
subsequent period exclusion.

## 4. The period partition is exhaustive

For a finite positive representation with N at least six, every switch
is forward or reverse modulo the label cycle. There are exactly the
following possibilities.

1. **All switches reverse.** The
   [reverse-period theorem](GLOBAL_REVERSE_PERIOD_EXCLUSION.md) applies at
   a minimum of the finite cyclic active-margin sequence. Its local
   necessary-PMP contradiction has no lower length restriction.
2. **All switches forward.** The
   [all-forward hand theorem](HAND_FORWARD_PERIOD_EXCLUSION.md) applies
   with its original exterior switching floors and whole-period budget.
   The actual twist forces \(N\equiv1\pmod3\), so N at least six
   means N at least seven. Its seven charged indices are therefore
   distinct even at the shortest possible length.
3. **The period is mixed.** The
   [minimum-structure theorem](MIXED_GLOBAL_MINIMUM_STRUCTURE.md) first
   forces every maximal reverse run to have exactly two switches.
   Every surviving mixed period is then treated by the smaller-turn
   split below.

For the last case, every global margin minimum has pattern either
four forward switches or a reverse-run centre. The completed
[small-forward-minimum hand proof](SMALL_FORWARD_MINIMUM_HAND_PROOF.md)
excludes a four-forward-switch minimum with squared margin at most
\(4/3\). An actual reverse centre exists and its squared margin is
less than \(2/3\), by the sharpened reverse-centre scale theorem.
A global minimum is no larger than that centre, so it cannot have the
four-forward pattern. A global minimum reverse centre is therefore
available, including when the minimum is repeated.

Choose its smaller adjacent turn. Reflection combined with time reversal
preserves the physical cost multiplier, all simplex Hamiltonian
inequalities, both cotangent endpoints, and the positive margin data.
Thus it gives the orientation required by each scalar interface. Equal
turns are permitted; either is a smaller choice.

The chosen turn is on either a short or a nonshort forward run. In the
short case the now completed
[H-S theorem](MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md) applies.
In the nonshort case,
[MIXED_SMALLER_TURN_CONTINUATION, Sections 1--3](MIXED_SMALLER_TURN_CONTINUATION.md)
uses the next actual switch, which is either forward or reverse. The
[forward hand theorem](MIXED_NONSHORT_FORWARD_HAND_EXCLUSION.md) and
[reverse hand theorem](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md) exclude
these two alternatives respectively. The transported outgoing norm is
that of the same original covector. The first forward root is the
genuine first event, not a freely selected later stationary root.

This split does not assume that either neighboring run is nonshort.
If both are short, the chosen side still satisfies H-S. In particular a
mixed period in which all forward runs have length one is included
directly. A separate local shortening statement, or a lemma forcing a
neighboring nonshort run, is unnecessary.

The nonshort continuation may cross the seam; the genuine extension
provides its next switch and the original costate transport. There is
no word-length cutoff beyond finiteness. Every mixed comparison keeps
its actual first switches, unequal positive factors and original
whole-period budget. Artificial scalar points are not assigned a new
physical closure, fitted multiplier or unproved competitive cap.

All three cases are impossible. Therefore the actual minimizing
representation has \(N\le5\), exactly the conclusion needed by the
separate terminal hand count.

## 5. No hidden executable exclusion is retained on this path

The operative statements are the hand theorems linked above. Several
older source files also preserve later computational results or
historical status text. Their exact role here is narrower:

- The small-forward-minimum proof retains the actual identities and
  easy faces in Sections 1--5 of the older note and replaces its large
  H5 coefficient table with the integral and cubic argument.
- The nonshort continuation supplies its hand same-covector identities,
  genuine successor alternative and justified boundary comparisons.
  Its later links to interval-cover completions are not the active
  nonshort exclusion; the two newer hand theorems supply those signs.
- The smaller-short six-variable note supplies its hand actual
  interface in Sections 1--5. The older directed-interval forest is
  not an S7 input. The new ratio, displacement, extended Casimir,
  root-to-shear and physical-cost hand theorems give the exclusion.
- The old neighboring-nonshort conclusion and the refuted unconditional
  local shortening assertion are not used by the direct smaller-turn
  split. No historical coefficient table proving either is needed.

The finite polynomial signs in the active notes are explicit
identities and ordinary coefficient bounds with elementary sign
arguments. Companion reconstruction scripts can check transcription,
but executing them is not a mathematical premise. There is no retained
root/leaf accounting, floating-point sign, numerical optimizer or
exhaustive word generator in Sections 3--4's implication.

This review finds no circular normality assumption, change of global
lift, omitted complete-period class or unproved physical transportation
in the reviewed portion of the final theorem. It accepts the finite
normal representation and the uniform deduction \(N\le5\). It is an
internal mathematical review, not external peer review or Lean kernel
verification.
