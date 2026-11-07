# Independent audit of the all-short variation formulas

Date: 2026-11-07 UTC. Independent internal hand review of
[MIXED_GLOBAL_SHORT_RUN_VARIATION](MIXED_GLOBAL_SHORT_RUN_VARIATION.md),
Sections 1--4. No Lean, Lake, typechecking, or CI was run.

## Result and boundary

The bridge-order lemma, exact endpoint-preserving scale family, and
full radial/angular Schur-complement formula pass this review. The
same actual normal multiplier is retained in every identity. The note
does not prove that its full residual is negative modulo rotation.
The subsequent phase estimate in
[MIXED_REVERSE_CENTRE_PHASE_BOUND](MIXED_REVERSE_CENTRE_PHASE_BOUND.md)
is a separate sign argument; it is not a premise of this audit.

## 1. Turn averages and bridge order

For a bridge `(a,b,c,d)` the factor inequalities and the strict
reverse-centre minima give `a,d<min(b,c)`. Dividing the two exact
turn-secant equations by their interval lengths gives the same
`nu` in equation (2), with the displayed factor `1/8`. The incident
reverse and forward switching inequalities give exactly (3).

For `c>b>a`, the affine interval parameterizations in the proof satisfy
`r>r'` and `rr'<1` away from the final endpoint. The identity
`r/(1+r)^2=(1/r)/(1+1/r)^2` and strict monotonicity on `(0,1)`
therefore give (5), including when `r` crosses one. If `d>=a`, adding
the interval `[a,d]` to the second average adds values strictly above
`8nu`, unless its length is zero. Combining these facts, and then
reversing the bridge, proves all three cases of
`sign(d-a)=sign(c-b)`. Removing `[b,c]` when `c>=b` gives (6);
integration gives the stated formula (7). Its equality conditions use
both the strict endpoint inequalities and the bridge-order lemma.

## 2. Full endpoint preservation and scale derivative

Expanding the collapsed diagonal gives

\[
D^{\rm Jac}=a^2+d^2+2ab+2cd-2bc.
\]

Solving this identity for `b` after setting
`K_j(lambda)=lambda K_j` gives precisely (8). Its denominator is
nonzero because `a_j<c_j`. Both the diagonal and every off-diagonal
of the collapsed recurrence are multiplied by the same positive
`lambda`. Its transfer matrices consequently remain unchanged.
Because the actual original monodromy is central, the change of the
active-margin reconstruction basis conjugates that same central matrix
to itself. Thus this construction preserves the full frame endpoint,
as well as the state endpoint; preserving only the trace is not being
used. Strict admissibility persists in a neighbourhood of one.

Differentiation gives `a_j'=K_j/(2a_j)` and
`(D_j^{\rm Jac})'=D_j^{\rm Jac}`. Applying the actual turn equations
to the derivative of the signed cyclic action yields the unsimplified
expression following (10). Expanding `G_a`, collecting the two
contributions at each centre, and substituting
`f(t)=t-t^-1-log t`, `h(t)=log t-1+t^-1` gives (9)--(10), with
the displayed factors `1/16`. Normal stationarity makes their sum
zero; no sign of an individual summand follows.

## 3. Complete joint Hessian, including vector curvature

The normalization `I_S=gamma S^-1 J_0` gives `I_S^2=-I` and
`S I_S=gamma J_0`. With the negative centre Wronskian,
`z_(j-1)^T S I_S z_j=gamma/K_j`, so the sign of the mixed
radial/angular term in (13) is negative as written. Expanding
`2 tr(S W^T H W)` and using the exact kernel recurrence yields
the whole vector block (13), including its factor two.

The actual fixed-vector margin block from the augmented-index note
has positive conductances on all three bridge edges and the positive
centre potential `8a_j^2/K_j^2`. Substituting relative margin
variations gives (12), which is positive definite on all `3m`
margin variables. Direct differentiation of the collapsed diagonal
and the two centre-adjoining off-diagonals gives (14). In particular,
the angular coefficient is `T_j=2a_j^2 gamma/K_j`; its cross term
is `-4 r_j T_j(eta_j-eta_(j-1))`. The terms involving `e_j` are
retained in both (13) and (14).

## 4. The two successive square completions

The two-turn matrix is

\[
\begin{pmatrix}u+v&-v\\-v&v+w\end{pmatrix},\qquad
\det=uv+uw+vw>0.
\]

Its displayed inverse gives the series conductance `uvw/Delta`,
the two linear coefficients `F^L,F^R`, and the negative contribution
`-4B alpha^2` in (15). The remaining centre matrix is the positive
weighted cycle Laplacian plus the strictly positive centre potential.
The remaining linear term is exactly `4r^T Xi`; its square completion
therefore contributes `-4 Xi^T L_eff^-1 Xi`. This verifies all factors
and signs in the residual (16).

Both eliminations are congruences with positive definite blocks, so
they preserve the negative index. The coefficients `alpha,eta` are
periodic even when the actual vector sequence is antiperiodic, and
`alpha=0`, `eta=constant` is the common rotation kernel. Positivity
of the eliminated blocks alone does not determine the sign on its
complement. The stated conditional count `2m-1` and its transfer to
`2(n-1)` use all three frame-constraint saddle pairs, as required by
[MIXED_GLOBAL_AUGMENTED_INDEX](MIXED_GLOBAL_AUGMENTED_INDEX.md).

No correction to the reviewed formulas is required. This audit is an
internal mathematical review, not external peer review or kernel
validation.
