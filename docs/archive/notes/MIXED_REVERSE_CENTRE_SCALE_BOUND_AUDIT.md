# Independent audit of the reverse-centre scale bound

Date: 2026-11-07 UTC. Reviewer: root agent, independently of the author.

I read the reverse-centre scale proof and its supplementary checker.
All twenty-two exact checks pass. The inequalities and actual-period
interface pass an independent hand audit without correction.

The exact stationarity and determinant expressions use the conserved
primary multiplier of the actual normal period. The strict turn bounds
and positive reverse factor give r,t<1/2 and rho<rt; the whole-period
budget, rather than conservation alone, supplies gamma^2<23/125.

The upper estimate E<3r/2, and its reflected form, make both incident
norm derivatives of the determinant expression strictly positive on
the whole comparison rectangle. Lowering the norms to 3/4 therefore
has the required direction, including when E is negative. Under the
contradictory assumption rho>=3/20, the lower-corner value E0 is positive:
the boundary reduction to rt=rho is valid, its one-variable expression
is concave, and its equal endpoint values give at least 19/60. Thus
raising r,t to 1/2 decreases the determinant, as claimed.

For the final one-variable estimate, the logarithm upper bound has the
correct direction for 0<x<1. The derivative numerator decreases in the
positive value B; replacing it by Bhat gives the exact strictly positive
rational remainder. At rho=3/20, B lies between 0 and 7/20. The final
rational separation is exactly 851/4624−23/125=23/578000>0.

Hence every competitive reverse centre has rho<3/20 and a^2<12/17,
without a restriction on adjacent forward-run lengths. This improves a
necessary scale bound; it excludes neither F nor the smaller-scale M2
domain. The proof uses no deformation of a path, endpoint rank, uniform
dwell-time claim, Lean, Lake, typechecking, CI, or numerical sign premise.
