# Independent audit of the uniform forward angle count

Date: 2026-11-07 UTC. Independent internal hand review. No Lean, Lake,
typechecking, or CI. This audit does not close case F.

The proof in [GLOBAL_STRUCTURE_FORWARD_ANGLE_COUNT](GLOBAL_STRUCTURE_FORWARD_ANGLE_COUNT.md)
has been reviewed independently of its author. The eight exact rational
checks were rerun successfully.

The whole-period minimum argument is valid: on the periodic active-margin
sequence a smallest entry has the four forward switches required by the
small-forward-minimum theorem. The three interior arcs are distinct even
for N=4; the already excluded N=1 alternative is not used. Hence every
active square is strictly above 4/3. The switch norm floor is 3/32, so
the exact Wronskian/Gram formula gives sin(theta_i)<2 gamma=kappa/sqrt3.
The normalization includes the factor sqrt12 between gamma and kappa.

The actual complete-period budget supplies kappa<205/138. The rational
sine comparison has the correct directions: cos(epsilon) is bounded
below, sin(epsilon) above, and its negative coefficient uses the upper
bound sqrt3<26/15. At epsilon<11/672 the displayed rational lower bound
exceeds 205/138 by 21871/207728640. Both angles are acute, so inversion
by sine is legitimate.

Finally the actual geometric winding, not central monodromy alone, gives
sum theta=(N-1)pi/3. Summing the strict angle deficits gives N<64, and
N=1 modulo3 gives N<=61. This covers every competitive pure-forward
period without a length catalogue or an endpoint-rank assumption.

**Result:** the count is proved with its stated scope. The remaining
cost/index comparison for F and every unresolved M2 obligation remain
open. This is an internal hand audit, not kernel validation or external
peer review.
