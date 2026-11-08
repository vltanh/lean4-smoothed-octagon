# Independent audit of the mixed-run minimum theorem

Date: 2026-11-07 UTC. Independent internal hand review of
[MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md).
No Lean, Lake, typechecking, or CI was run.

## Verdict and exact scope

The theorem is valid with its stated hypotheses. A finite normal
strict-star mixed PMP period has reverse runs of length exactly two.
This excludes the entire M3 domain, including arbitrary unequal positive
factors, degenerate ties, every primary-costate sector, and runs crossing
the twisted seam. Together with the separate pure-reverse theorem, it
leaves the pure-forward case F and mixed cases M1/M2. It does not prove
the global cost comparison or affine uniqueness.

The stronger three-arc conclusion discussed below is also valid:

\[
\boxed{a_1^2>a_0a_2\quad\text{on every positive normal PMP triple }i,j,i.}
\]

That strict log-concavity is a necessary condition, not a further
exclusion of a complete mixed case.

## 1. Physical reflection, cotangent signs, and endpoints

The reflection is checked in the physical matrices, before using any
triangular coordinates. With `S=diag(1,-1)` and `rho(i)=-i mod 3`,
`SJS=-J` and `SZ_iS=-Z_rho(i)`. Therefore
`X_tilde=-SXS`, `P_tilde=-SPS`, and reversal of time give the original
positive state dynamics. For `X=Phi(x,y)` the transformed point is
`Phi(-x,y)`, so every strict-star inequality and the positive physical
cost density are preserved.

The costate transformation is the same negative conjugation for
`Lambda_1` and `Lambda_R`, while the ambient representative `Lambda_2`
has positive conjugation. This agrees with
`Lambda_R=[Lambda_2,X]` and preserves the actual two-dimensional state
cotangent class. Direct trace substitution gives the original maximizing
Hamiltonians with permuted labels and the **unchanged** cost multiplier.
In particular normal `lambda=-1` stays `-1`.

The displayed reduced state-covector equation agrees term by term with
[GLOBAL_PERIODIC_PMP, equation (5)](GLOBAL_PERIODIC_PMP.md). Differentiating
the transformed costates gives precisely that equation and the primary
costate equation; no omitted ambient-normal component is used. The
identity `S R^-1 S=R` then verifies the frame, state, and both costate
twists. These checks justify applying the reverse-four theorem after
reflection and time reversal to a local window as well as a complete
period.

Active margins are permuted by the same label reflection, without a
scale factor. Their chronological order reverses, while switch signs
are read backwards without changing sign. Consequently the prohibition
of a third-position minimum in `0210` transfers exactly to its second
position. This is an actual normal-PMP transformation, rather than a
formal symmetry of words.

## 2. The same normal covector on a two-control edge

The three-arc proof uses the given full-system covector. This is essential:
a separately obtained multiplier for an auxiliary fixed-endpoint edge
problem could be abnormal and would not give the displayed normal source.

In physical coordinates, the common positive clock on vertices 1 and 2
has `dx/dt=y`. Direct multiplication with `F=gK(x)` and `w=y^-2` gives

\[
F_x=FwE_{21},\qquad
w_x=b_iw,\qquad
b_1=2/(q-x),\quad b_2=-2/(q+x).
\]

Dividing the physical running cost by the clock and multiplying by
`2/3` gives exactly `1+(1+x^2)w`. The canonical cotangent change followed
by multiplication by `-2/3` converts the physical maximizing convention
to the stated minimizing convention. A state-dependent positive clock
adds only a multiple of the original Hamiltonian to the adjoint equation;
that multiple vanishes on the active free-time zero-Hamiltonian locus.
Thus one continuous transformed covector applies across both switches.

The group velocity is a multiple of `E_21`, so its paired component
`m=<M,E_21>` is constant on both arcs and across their joins. This proves
that the same `mu=-1-m` occurs in

\[
p_w'=\mu-x^2-b_ip_w,
\qquad
\mathcal H_2-\mathcal H_1=-(b_1-b_2)wp_w.
\]

The positive coefficient `(b_1-b_2)w` fixes the signs: vertex 1 requires
`p_w<=0`, and vertex 2 requires `p_w>=0`. Both joining ties therefore
have `p_w=0`. The two adjoint right-hand sides agree there, so the weak
derivative inequalities remain valid at quadratic or cubic contacts and
at triple ties. The physical margin ratio is
`p_1/p_2=(q-x)/(q+x)`. These facts give the stated middle-minimum
contradiction without a transverse-switch assumption.

## 3. Strict log-concavity at every change of direction

There is a useful stronger consequence of the same calculation. For a
`1,2,1` triple with switch abscissas `s<t`, the weak signs give

\[
s^2\le\mu\le t^2,
\]

and hence `s+t>=0`. Equality would force `s=-t` and
`mu=s^2=t^2`. On the positive middle arc choose any positive integrating
factor `rho` with `rho'=b_2 rho`. Then

\[
(\rho p_w)'=\rho(\mu-x^2)>0\qquad(s<x<t).
\]

Its integral is strictly positive, contradicting the two zero endpoint
values. Thus `s+t>0`. If `A` is the middle active margin, the physical
ratios give

\[
\frac{a_0a_2}{A^2}
=\frac{(q-s)(q-t)}{(q+s)(q+t)}<1.
\]

All four factors are positive by strict star. For `2,1,2`, the weak
signs instead give `t^2<=mu<=s^2`; the same integrating-factor argument
excludes equality and yields `s+t<0`. The ratio above is inverted, so
again `a_0a_2<A^2`. Cyclic rotation treats every pair of distinct labels.
This proves the displayed strict log-concavity, including degenerate ties.

## 4. Minimum within each bounded reverse run

The two turning-factor formulas are exact positive-factor feasibility
relations. At a `(+,-)` turn they give `a_next<a_previous`; at a
`(-,+)` turn they give the opposite strict inequality.

A minimum of the active margins on the arcs of a bounded negative run
cannot occur at either endpoint: feasibility at the adjoining turn
would make that endpoint a forbidden middle minimum on an alternating
triple. A run with one negative switch has only these impossible
endpoints. For a run with at least three negative switches, every
interior arc is second or third in a reverse-four window wholly within
the run. A run minimum there violates one of the two reverse-four
minimum principles. This includes equal minima; no uniqueness is
assumed when selecting a minimum.

The only remaining run length is two. Its sole interior active margin
is strictly below the other two and, by the two turning feasibility
relations, below the two exterior active margins as well. This proves
the five-arc `01020` conclusion exactly as stated.

The actual twisted extension makes the active-margin and switch-sign
sequences periodic. It therefore makes every reverse run in a mixed
period bounded, including a run crossing the selected seam. The argument
uses local necessary-PMP conditions and constructs no multi-period
replacement. A short period presents no geometric-splicing or endpoint
rank issue. Global normality and finite representation are used only
when applying this necessary condition to all global minimizers.

## 5. Remaining limitation

The certified short-pad witness already contains a positive normal PMP
`01020` window with a strict middle minimum among all five active
margins. The note correctly preserves this obstruction to a purely local
first-order exclusion. It makes no claim that the witness has complete
return, admissible global geometry, or minimizing second variation.

The classification into `++++` and `+--+` at a global active-margin
minimum is a fixed consequence of the proved inequalities. It does not
exclude either remaining location. In particular a minimum among
reverse-run centers alone cannot be treated as a minimum among **all**
active margins elsewhere in the period.

No new symbolic certificate is needed for these direct hand
implications. The reverse-four algebra retains its separate exact
checker and independent audit. This review is internal mathematical
review, not external peer review or Lean kernel validation.
