# Independent audit of the short-bridge minimum comparisons

Date: 2026-11-07 UTC. Independent internal hand reviews and exact algebra
checks. No Lean, Lake, typechecking, or CI. No general M2 closure claim.

## Scope and results

The three reviewed notes prove:

1. [Equal-centre exclusion](MIXED_GLOBAL_SHORT_BRIDGE_EQUAL_CENTRES.md):
   a positive two-short-bridge window in an actual finite normal closed
   period cannot have all three reverse centres equal. The bridge turn
   sizes may differ. The result uses no Casimir cap.
2. [General central comparison](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL.md):
   along the unique exact two-secant path from equal centres to the
   actual incoming bridge, the central residual F0 decreases strictly.
   Its strict equal-centre upper bound therefore holds for either sign
   of the bridge diagonal.
3. [Positive-diagonal scale comparison](MIXED_GLOBAL_SHORT_BRIDGE_SCALE.md):
   the actual transported outer reverse-root maximum increases strictly
   with the scalar scale rho on its genuine root domain, when the bridge
   diagonal is positive.

The outer-root boundary signs for unequal centres and the nonpositive
diagonal outer comparison are not proved by these results. Nor do they
place a whole-period reverse minimum next to a long forward run. F and
M2 remain open.

## Equal-centre proof

An independent reviewer reran all 35 exact checks and reviewed the
central primitive, same-lift Gram recurrence, incident reverse derivative,
and required root interval. Interchanging left and right data justifies
x<=y. The strict centre-minimum theorem supplies the necessary outer
turn inequality P>a; it is not an assumption on arbitrary local data.

The stronger H bound has the correct derivative sign and the displayed
diagonal polynomial identity is exact. Its strictness handles unequal
turns, the zero bridge diagonal, and the zero-factor comparison face.
For positive diagonal, increasing rho reaches one of the two stated
upper faces: w>v>3/4 throughout, and w must reach f'(T)<1 before leaving
the Legendre domain. The two endpoint estimates are negative, including
their intersection. Additional star constraints may be discarded on
this auxiliary scalar comparison; no physical deformation is asserted.

## General central comparison

A separate reviewer checked the continuation directly. For beta>=x,
the derivative of `(beta-1)eta` is
`-(beta-1)g'(beta/x)/x<0` away from its initial endpoint. Thus positivity
of eta at the actual bridge persists back to beta=x. The left integral
average decreases strictly with alpha and brackets the right average at
alpha=1 and alpha=x. This proves existence and uniqueness of the entire
continuation used by the proof. Independent differentiation of both
secants and their homogeneity reproduces the two derivatives.

The Padé logarithm bound is an upper bound in the required direction.
The ratio estimate eta/xi>=2/7 treats both the convex and concave
quadratic cases, including their boundary. The norm bound u<13/16
correctly implies beta/x<3 through the actual forward derivative.
The B0<0 case uses the upper bound on u with the required reversal of
the multiplication inequality. Positivity at rho=0 and rho=1/S^2 then
controls the affine derivative for every intermediate scale.

All 19 exact checks were rerun. Independently parsing the manuscript's
44 coefficient rows reconstructs exactly 362 strictly positive nonzero
coefficients. The four separately displayed polynomial pieces have the
stated discriminant, endpoint values and concavity. The certificate
therefore covers every point of the fixed domain, not a sample. The
strict j>0 term retains strictness at the equal-centre endpoint.

## Positive-diagonal scale comparison

The second reviewer reconstructed the physical transport independently:
lambda=K_a/K_A, d=D_phys/K_A,
`E_L=2du-lambda E` and `w=d^2u+lambda^2v-d lambda E`.
The same multiplier is used on every arc. The genuine outer reverse
root has 2<tau<T and w=U(1/tau) at its maximum; the incident norm
upper bounds in the proof have the correct physical directions.

Holding dimensionless ratios and the actual turn norms fixed is a
scalar comparison. Direct differentiation gives equation (5), including
the scale derivative of the outer primitive h(P/alpha^2). The affine
norm substitutions hold tau and w=U(1/tau) fixed only while bounding
that derivative. Both clipping cases and all denominator signs are
correct. No comparison point is asserted to be a full PMP trajectory.

All 17 checks passed. Independent parsing of the actual manuscript
tables recovers 53 rows and 33+33+76=142 positive coefficients. The
compact decomposition reconstructs the original rational expression.
The strict x>alpha condition supplies strictness even at alpha=1.

The scale comparison explicitly retains a possible upper exit at
w=3/4, including simultaneous T=2. Unlike equal centres, lambda is
not identically one; silently omitting this face would be invalid.
Central zero factor, outer derivative, lower norm, and nonpositive
diagonal outer signs remain separate open obligations.

These reviews are independent internal hand audits. They are not Lean
kernel validation, external peer review, or a complete Reinhardt proof.
