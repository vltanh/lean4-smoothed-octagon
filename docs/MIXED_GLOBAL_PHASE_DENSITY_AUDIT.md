# Independent audit of the mixed phase-density theorem

Date: 2026-11-07 UTC. Independent internal hand review of
[MIXED_GLOBAL_PHASE_DENSITY](MIXED_GLOBAL_PHASE_DENSITY.md).
No Lean, Lake, typechecking, or CI.

## Verdict and scope

The negative phase graph, complete constrained-index subtraction, and
uniform inequality `2m<=P+8` for actual competitive minimizers are valid.
This excludes every period violating that inequality together, with
arbitrary unequal factors and forward-run lengths. It does not close
all of M2, the two remaining all-short multiplicities, or F.

## Local signs and the same multiplier

The forward acuteness proof requires only the two neighbouring forward
switch inequalities, the equal-sign normal stationarity identity,
strict-star products, positive forward factor, and the determinant cap.
All these hold at a `++` arc inside a mixed period, with the same
actual primary multiplier. No pure-forward monodromy is used in the
local scalar proof after those inputs have been supplied. Thus its
strict positive cross pairing is correctly extended to such arcs.

The reverse-centre estimate applies at every `--` arc by the already
proved strict centre minimum. Its incident switch norms are the norms
at turns, as required in the scalar argument. No local replacement of
the actual normal covector is made.

## Direct reconstruction of the joint quadratic form

Before gauging, the off-diagonal entry at a surviving edge is
`delta_i K_i`, with `delta_i=+1` or `-1`. The kernel equation and
`I_S^T S I_S=S` give the pure-phase contribution
`-2 delta_i K_i e_i (eta_i-eta_(i-1))^2`.

For an independent cross-term check, the off-diagonal margin derivative
is `2 delta_i a_i v_i`. Its contribution to
`4 tr(S Y^T H_v W)` is

\[
8\delta_i a_i v_i(\eta_i-\eta_{i-1})
 y_{i-1}^TSI_Sy_i
=-\frac{8\gamma a_i v_i}{K_i}(\eta_i-\eta_{i-1}),
\]

because `y_(i-1)^T S I_S y_i=-gamma delta_i/K_i`.
The differentiated diagonal contributes zero. Turn identifications
are fixed linear relations, so their collapse adds no derivative term.

Each reverse centre is separated from the next by turn indices. Fixing
all other margin variations therefore leaves the diagonal positive
block `D_j=M_j+omega_j^-+omega_j^+`. Completing its one-variable
square gives precisely the graph
`r_j=2T_j Delta_j eta/D_j` and the correction
`-4T_j^2(Delta_j eta)^2/D_j`.

For a positive reverse cross pairing, the proved stronger denominator
`M_j+2omega_j^-+2omega_j^+` bounds this smaller `D_j` strictly.
For a nonpositive pairing the sign is immediate. Every coefficient
of every surviving phase difference is consequently negative.
The collapsed cycle is connected, so the graph has exactly one zero
phase direction, common rotation, and a negative subspace of dimension
`P-1`. Periodic scalar phases are legitimate even when the underlying
vectors have an antiperiodic boundary condition.

## Actual constrained index and competitors

The independently audited augmented-index bridge subtracts
`2(P-n-1)` negative range directions and **all three** negative
constraint-pair directions. Applying it to the constructed graph yields

\[
P-1-2(P-n-1)-3=2n-P-2=(2m-P-8)/3.
\]

This integer is positive precisely in the asserted excluded region.
The same bridge supplies rank three for the remaining full frame map
on the state-closed margin family, so a negative constrained tangent
integrates to an exact nearby closed competitor. Its strict state and
factor inequalities persist, and the retained geometric realization
justifies the cost comparison. Thus the theorem excludes actual
minimizers, not merely unconstrained stationary tuples.

Using `P-2m=3k+1`, the equivalent lower bound is `-k-3`, as stated.
For all-short periods `P=m`, it agrees with the separate bound
`(m-8)/3`. No ordinary Jacobi count has been substituted for the
cost index, and no additional radial sign is claimed.

This review is an internal mathematical audit, not external peer
review or Lean kernel validation.
