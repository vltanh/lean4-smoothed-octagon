# Independent audit of the pure cyclic costate-sector restriction

Date: 2026-11-07 UTC. Independent internal hand review of
[GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR](GLOBAL_STRUCTURE_CYCLIC_COSTATE_SECTOR.md).
This is not external peer review or Lean kernel validation. No Lean, Lake,
typechecking, or CI was run.


**Later global resolution:** [GLOBAL_REVERSE_PERIOD_EXCLUSION](GLOBAL_REVERSE_PERIOD_EXCLUSION.md)
now closes the entire pure-reverse case R by a minimum-margin PMP
contradiction, independently of the Casimir/sector route studied here.
The earlier limitations below describe this note's own argument; they
do not leave global R open. F and the three mixed cases remain open.

## Finding

The theorem is valid for a complete normal pure-forward or pure-reverse
PMP period, with positive durations, strict-star states, the actual full
frame/state endpoints, and free-initial-state cotangent transversality.
The physical primary costate is nonzero and lies outside the closed
positive elliptic cone. Unequal factors and endpoint rank defects are
included; no inverse endpoint map is used.

The theorem supplies no negative-elliptic lower Casimir bound and does
not exclude hyperbolic or negative parabolic primary costates. It is not
a cost comparison or an index theorem. F and R remain open.

## 1. Actual reverse arcs and the scalar sign

The reverse vertex update starts with active/growing/decreasing margins
`(a_i,a_{i-1},b_i)` and ends with `(a_i,b_{i+1},a_{i+1})`.
Solving that update gives `q_i=K_i/(s_{i-1}s_i)>1`, with
`b_i=(4-a_{i-1}a_i)/s_{i-1}`. This verifies the reverse factor using
an actual forward-in-time control arc. No time reversal is assumed.

On summing the nonlogarithmic reverse arc terms, the two terms adjacent
to one pair combine as

\[
(a_i+a_{i+1})b_{i+1}-2a_i a_{i+1}=4-3a_i a_{i+1}.
\]

Together with `log q_i=-log r_i`, this gives `J=-mathcal J`.
The forward sign is the retained cyclic action formula.

Differentiating the cyclic action, the three logarithm contributions
containing `a_i` give

\[
8\mathcal J_{a_i}=3(a_{i-1}+a_{i+1})-2a_i\log r_i
 -\frac{a_{i-1}^2+a_i^2}{s_{i-1}}
 -\frac{a_i^2+a_{i+1}^2}{s_i}
 +\frac{2a_i^3}{K_i}.
\]

Using `(a^2+b^2)/(a+b)=a+b-2ab/(a+b)` yields exactly equation (4)
of the proof note. With `rho=s_{i-1}/a_i`, `sigma=s_i/a_i`, and
`tau=K_i/a_i^2`, one has `r_i=rho*sigma/tau`. Direct substitution
then gives the three-term decomposition (5). All three arguments
exceed one, and the two displayed derivatives are positive there.
Thus every derivative of the signed action is positive throughout the
positive orthant. The opposite signs for the actual forward/reverse
cost follow.

## 2. Frame derivatives and the cyclic seam

For either product, differentiating one factor in `log q_i` gives the
right-trivialized column `Z_i=Ad_{P_i} E`. Differentiation of
`log r_i=log s_{i-1}+log s_i-log K_i` affects exactly the two neighboring
sums and the central denominator. This gives the displayed three-column
combination, with its sign reversed for the reverse product.

The elementary identities for `B(q)^{-1}EB(q)+E` and
`E+B(q)EB(q)^{-1}` have the stated upper/lower triangular forms. Their
substitution gives the reverse column (8), including its positive
lower-left entry. The forward computation gives (7) and its negative
lower-left entry. Substituting the respective physical factors gives
in both cases

\[
\det V_i=4(s_{i-1}s_i-a_i^2)/K_i^2>0.
\]

These are elliptic columns, and their components are preserved by the
determinant-one prefix conjugations. At the seam the complete frame
product is central. Its adjoint action is identity, so the periodic
column formulas remain valid there. Centrality is required at the base
period; nearby variations need not already satisfy frame closure.

## 3. Boundary pairing, orientation and zero

The active-margin family satisfies state closure identically while
varying the initial state freely. Differentiating
`g_T=X_0 F X_T^{-1}` at `F=R` and `X_T=R^{-1}X_0 R` gives

\[
\delta g_T\,g_T^{-1}
 =\operatorname{Ad}_{X_0}(\delta F\,F^{-1}).
\]

The two initial-state terms in this matrix equation cancel. The initial
and terminal state-cotangent pairings cancel separately by the actual
free-state transversality. With maximizing cost multiplier `lambda=-1`,
the first variation is cost equals terminal-minus-initial cotangent
pairing. The conserved spatial primary costate therefore gives

\[
J_{a_i}=\operatorname{tr}(UV_i),\qquad
U=\frac1{\sqrt{12}}X_0^{-1}\Lambda_1^{\mathrm{tri}}(0)X_0.
\]

This verifies the positive sign and the use of the same actual PMP
multiplier. Full rank is unnecessary for this implication.

A nonzero matrix in the closed negative triangular elliptic cone pairs
strictly negatively with every negative elliptic column and strictly
positively with every positive elliptic column. The proof note's
conjugation to `-tJ` also covers its nonzero parabolic boundary.
These signs contradict the scalar derivatives in the forward and
reverse cases, respectively. Zero contradicts either nonzero scalar
derivative directly.

The triangular coordinate change has negative determinant and exchanges
the two elliptic cones. The additional conjugation by `X_0`, whose
determinant is one, and the positive cost scaling preserve them. Hence
the excluded triangular cone is exactly the physical closed positive
cone claimed in the theorem. The conserved spatial-covector equation
transports this conclusion to the whole period.

## 4. What the argument does not establish

The scalar action was differentiated before imposing the three frame
constraints. Its strict partial derivatives are not feasible descent
directions on that constraint manifold. A constrained Hessian also has
the endpoint-curvature term; the cone argument does not control it.

The theorem applies to entire one-direction periods. A pure-direction
six-piece window inside a mixed period has no central local frame
product or free-initial-state periodic boundary identity. Applying this
result to such a window would be invalid. The existing sign-run coverage
can instead assign every mixed period to M1, M2, or M3; pure F/R periods
are the two remaining global classes. This is a sufficient organization
of the existing coverage proof, not a newly excluded competitor class.

The added sign-only obstruction is also exact: the positive parabolic
triangular matrix `U_0=[[0,-1],[0,0]]` pairs with every frame column with
the required derivative sign. The hyperbolic perturbation
`U_epsilon=[[epsilon,-1],[0,-epsilon]]` preserves all those finitely many
strict signs for small nonzero `epsilon`. This includes columns of
central-monodromy periods. These matrices are not claimed to satisfy
the actual stationarity equalities. The example correctly demonstrates
that a sector strengthening must use more than column orientation and
cost-derivative signs.

No material mathematical correction was needed. The complete-period
cost inequality, all five uniform case-C targets, and affine rigidity
remain open.
