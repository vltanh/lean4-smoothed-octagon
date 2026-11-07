# Independent audit of the complete mixed turn elimination

Date: 2026-11-07 UTC. Independent internal hand review of
[MIXED_GLOBAL_TURN_ELIMINATION](MIXED_GLOBAL_TURN_ELIMINATION.md).
No Lean, Lake, typechecking, or CI was run.

## Result and boundary

The turn-block inertia and all displayed Schur formulas pass review.
The physical and auxiliary variables at the `2m` turns give exactly
`2m` positive and `2m` negative pivots, with no zero pivot in the
full block. Its elimination leaves the stated `2P+1` variables,
including the global Casimir variation. The exact remaining index is

\[
\operatorname{ind}_-(Q_{\rm closed})
=\operatorname{ind}_-(\mathcal S)-k-3.
\]

This supplies an explicit reduced matrix, without proving its further
negative index. Its baseline restriction is the previously proved
`k>=-3`, so no new family is counted as excluded.

## Full Hessian and isolated turns

Expanding each signed square in (3) gives the correct adjacent
physical, mixed, and auxiliary Hessian entries. The diagonal residual
is exactly the onsite expression (4), after using the actual normal
stationarity equations. The Casimir variable is normalized as
`zeta=delta(gamma)/gamma`; its mixed term is therefore precisely
`-2*zeta*sum(J_ai*v_i)`, with no initial square term.

At an isolated turn, positive duration gives `epsilon*(t-s)>0`.
Thus the auxiliary coefficient in (5) is strictly negative, while
the physical coefficient is positive by the two strict switching
coefficients. The determinant is strictly negative. The shift in (7)
and completion in the auxiliary variable give the positive coefficient
`kappa=gamma^2/(4*nu*epsilon*(t^2-s^2))`. Retaining the physical
linear term and the turn gradient gives exactly (8).

At fixed Casimir, the identity (9) follows by a second completion.
Its series-conductance term is nonnegative because it is the Schur
complement of a positive weighted path Laplacian. This sign applies
to the replacement edge form, not to the remaining onsite terms or
to the form with arbitrary Casimir variation.

## Adjacent turns, including the zero bridge diagonal

For a short forward run between reverse centres, the strict centre
minima and the two positive turn factors imply
`a,d<min(b,c)`. All three norms are the same `nu>3/32`. The
physical matrix `A` is positive definite: its quadratic form is a
sum of the three positive conductance terms with the endpoints fixed.

Direct expansion of (12) verifies its auxiliary determinant
`-gamma^4*D/(16*nu^2*s^2*t^2*u^2)` and the physical Schur term
`A-(4*nu/D)*l*l^T` when `D` is nonzero. If `D<0`, the two
auxiliary directions are negative and the physical Schur term is
positive. If `D>0`, the auxiliary block has one eigenvalue of each
sign. The test vector `(b,c)` then gives

\[
D\Omega<Q^2/16<4\nu Q^2.
\]

For the first inequality, the reverse switching upper bounds and
`nu>3/32` give each incident conductance contribution less than the
corresponding squared margin difference divided by 64. The strict
bound on `D`, the lower bound on `Q`, and
`x^2+y^2<(x+y)^2` for the two positive differences complete the
comparison. No all-short angle sum is used. The rank-one physical
Schur term is positive on `l`-perpendicular vectors and negative
at `(b,c)`, giving exactly one eigenvalue of each sign.

The full determinant (13) is nonzero at `D=0`, since
`l^T*adj(A)*l>0`. All strict local domain inequalities persist in
a small neighborhood of this point. Continuity of the eigenvalues
therefore gives the same full inertia across the zero bridge
diagonal; no inverse of the singular auxiliary block is asserted.

## Remaining matrix and actual index subtraction

The rank-one inverse formula gives (15) with the denominator
`4*nu*L-D`. It is positive for `D<=0` immediately and for `D>0`
by Cauchy--Schwarz and the preceding strict test-vector comparison.
Both sides extend continuously to `D=0` through the invertible full
turn block. The two actual turn gradients give exactly the displayed
Casimir vector. This verifies all terms of the replacement, including
the terms that would be lost by holding the multiplier fixed too early.

Turn components have size one or two and do not couple directly to
one another in the principal block. Summing their inertias and then
applying the previously proved full-rank three-constraint index
formula yields (2): `N=3n+m+1` makes its subtraction exactly
`n-m+3=k+3`. The prescription in Section 5 retains every remaining
edge, onsite term, and Casimir coupling once.

All 23 supplementary exact checks pass. The domain signs, singular
boundary continuation, component assembly, and actual endpoint/index
interface are the hand arguments reviewed above. This is internal
review, not external peer review or kernel validation.
