# The control-independent Hamiltonian locus

`SmoothedOctagon/SingularLocus.lean` implements the pointwise content of
Hales–Vajjha, *Packings of Smoothed Polygons*, [Lemma 8.2.1](https://arxiv.org/html/2405.04331v1#Ch8.S2).
The statements concern arbitrary star states and reduced costates. They do not
assume the symmetric polygon family, an explicit constant-control segment, or a
normalization of its costate lift.

## Exact hypotheses

Write `Z_i = controlMatrix (vertex i)`, `Z_u = controlMatrix u`, and
`⟨A,B⟩ = trace(A B)`. The state satisfies

\[
\operatorname{tr}X=0,\qquad \det X=1,\qquad \rho_0(X),\rho_1(X),\rho_2(X)>0.
\]

The reduced costate satisfies

\[
\operatorname{tr}\Lambda_R=0,\qquad \langle\Lambda_R,X\rangle=0.
\]

The other costate `Λ₁` and multiplier `lam` are arbitrary: their contribution to
the Hamiltonian is independent of the control. A Pontryagin extremal provides
the displayed state and reduced-costate conditions, but no extremal is assumed
or constructed in this module.

## Weighted Hamiltonian identity and support

Put

\[
D(u)=\langle X,Z_u\rangle,\quad N(u)=\langle\Lambda_R,Z_u\rangle,
\quad K=\langle\Lambda_1-\tfrac32\lambda J,X\rangle.
\]

The upstream star-condition theorem gives `D(u) < 0` throughout the simplex.
Linearity gives `D(u) = Σ u_i D(e_i)` and `N(u) = Σ u_i N(e_i)`. Since
`H(u) = K - N(u)/D(u)`,

\[
D(u)H(u)=\sum_i u_iD(e_i)H(e_i).
\]

For any real comparison value `M`, this is equivalently

\[
(-D(u))(M-H(u))
=\sum_i u_i(-D(e_i))(M-H(e_i)).
\]

Every weight `u_i(-D(e_i))` is nonnegative and is positive when `u_i > 0`.
Consequently, an upper bound on the three vertex values is an upper bound on
the entire simplex. If `u` is maximizing, take `M = H(u)`. The right-hand terms
are nonnegative and sum to zero, so `u_i > 0` forces `H(e_i) = H(u)`. This is
the explicit support rule proved by `maximizing_control_support`.

## Three equal vertex values force a zero reduced costate

Suppose all three vertex Hamiltonians coincide. Their ratios `N(e_i)/D(e_i)`
then have a common value `c`. Hence

\[
\langle\Lambda_R-cX,Z_i\rangle=0\qquad(i=0,1,2).
\]

These three linear measurements separate traceless matrices. To check this
directly, write `A = [[α,β],[γ,-α]]`; its measurements are

\[
\beta+\gamma/3,\qquad 2\alpha/\sqrt3-2\gamma/3,\qquad
-2\alpha/\sqrt3-2\gamma/3.
\]

Their simultaneous vanishing first gives `γ = 0`, then `α = 0` and `β = 0`.
Thus `Λ_R = cX`. Perpendicularity and the determinant normalization yield

\[
0=\langle\Lambda_R,X\rangle
=c\langle X,X\rangle=-2c,
\]

so `c = 0` and `Λ_R = 0`. Conversely, `Λ_R = 0` removes the entire
control-dependent Hamiltonian term. This proves both the vertex test and
constancy on the full simplex.

If `Λ_R ≠ 0`, two vertex values differ. Choose the lower-valued vertex. It
cannot have positive weight in any maximizing control, by the support rule.
Thus one fixed coordinate vanishes at every maximizer. Combined with the
upstream nonempty-face theorem, this is the vertex-or-edge conclusion of
Lemma 8.2.1. The source theorem records the concrete proper-edge containment;
it does not assume an independently provided face classification.

## Declaration inventory

- `traceForm_controlMatrix_eq_vertex_sum`: linearity in vertex coordinates.
- `eq_zero_of_traceForm_control_vertices_eq_zero`: the three control matrices
  separate traceless matrices under the trace form.
- `hamiltonian_denominator_mul_eq_vertex_sum`: exact weighted vertex identity.
- `hamiltonian_gap_eq_vertex_sum`: exact weighted gap identity.
- `hamiltonian_le_of_vertex_le`: three vertex upper bounds imply a simplex bound.
- `hamiltonian_isMax_iff_vertexwise`: the maximum condition needs only three
  comparisons.
- `maximizing_control_support`: every positive coordinate of a maximizer is
  supported on a maximizing vertex.
- `hamiltonian_vertices_equal_iff_reducedCostate_eq_zero`: the three-way tie test.
- `hamiltonian_constant_on_simplex_iff_reducedCostate_eq_zero`: full control
  independence is equivalent to a zero reduced costate.
- `hamiltonian_maximizers_in_proper_edge`: a nonzero reduced costate confines all
  maximizers to one proper simplex edge.

## Role and remaining obligations

This identifies the pointwise control-independent locus. It does not identify
that locus with the full singular trajectory locus: a single time with
`Λ_R = 0` does not imply `X = J` or prescribe `Λ₁`. Those conclusions in the
published Theorem 8.2.3 use vanishing of `Λ_R` on an interval and the costate
equations. Likewise, a nonunique maximizer confined to an edge does not imply
that the Hamiltonian is constant on the whole simplex.

The existence of a Pontryagin lift for an arbitrary control minimizer remains
a separate proof obligation. Elimination of singular intervals, finite
switching, a uniform switch bound, and the global octagon cost bound are not
conclusions of this module. In particular, proper-edge containment at a
single time is not a bang-bang theorem for a trajectory.

## Validation

Source and hand-algebra review only. Lean compilation, kernel checking, Lake,
and CI were **not run**, in accordance with `AGENTS.md`. No new axiom or proof
placeholder is used. These source proofs are not represented as kernel-verified
theorems.
