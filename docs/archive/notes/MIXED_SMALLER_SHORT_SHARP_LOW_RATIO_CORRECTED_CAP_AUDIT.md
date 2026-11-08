# Independent review of the sharp low-ratio corrected cap

Date: 2026-11-08 UTC. **Accepted as an analytic scalar reduction.**
This review concerns the complete argument in
[the sharp low-ratio corrected-cap note](MIXED_SMALLER_SHORT_SHARP_LOW_RATIO_CORRECTED_CAP.md).
Its terminal face signs and the final whole-period assembly are
separate theorems.

## 1. The original root supplies the retained incident deficit

The incoming ceiling at the original outer root gives
\(J_A=[U(r_A)-u]/r_A\ge0\). Restoring the original incoming
norm after putting both incident norms at their ceilings subtracts
exactly \(J_A\) from the ceiling pairing. Restoring the outgoing
norm subtracts another nonnegative term. This proves
\(E_{L,\mathrm{actual}}\le3q-J_A\).

The comparison with the ceiling endpoint uses
\(q<r_A/\tau<1/4\); hence the derivative \(1/q-4\) remains
positive on the entire intervening interval, including any part
above \(1/7\). The endpoint difference is exactly
\(-(1-2r_A)(1-2/\tau)\le0\).

The original envelope raises the central pairing \(E\), so it
lowers \(E_L=2du-\lambda E\). The retained inequality therefore
persists along both scalar envelope segments. Neither segment is
assumed to carry a new physical root or outgoing incident ceiling.

The derivative ratio in equation (4) of the source has a positive
denominator. Its increase with \(b\) follows from
\(2u-\tau(3q-J_A)>0\). The bound \(D\le4\alpha^2\), the
range \(0<K\le9/2\), and \(b_0\ge-2/7\) follow with the
stated comparison directions. The two cases \(b_0\le0\) and
\(b_0>0\) therefore reduce the ratio to equation (9).
Its derivative is strictly negative on \([0,1/7]\). At the final
scale, increasing the incoming norm to \(u_0\) is justified by
the explicitly negative derivative in equation (10).

## 2. The ten polynomial signs are complete

The clearing identity (12) follows directly from

\[
J_A=\frac{H_N}{12S^2\alpha(\alpha+\beta)},\qquad
2u_0-6/7=\frac{17x^2+20x+17}{21S^2}.
\]

Every cleared factor is positive. The enlarged strip (13) contains
the actual strip: \(8x/(9x+8)\ge8/17\), and the upper bound
is equivalent to the convex quadratic inequality
\(19x^2-39x-4\le0\) on \([1,2]\).

Independent reconstruction of the polynomial in (11), with
substitution (14), gives exactly the ten printed polynomials in
(15). Their printed endpoint values are correct. Each row has one
coefficient sign change, so the termwise inequality
\(H(z)\ge z^mH(1)>0\) applies on \(0<z\le1\); the value
at zero is 432. The binomial weights are nonnegative and sum to
one. This proves the required sign over the complete enlarged
strip, including its closed boundary.

Thus the ratio bound \(d\Gamma/dR_\tau\le7/96\) is established
throughout the original envelope. Integrating it from the original
root, where \(R_\tau=0\), gives the lower bound on the original
actual-period Casimir stated in (16).

## 3. The scale comparisons retain their required hypotheses

At fixed normalized duration \(p\), lowering \(\beta\) to its
explicit lower endpoint decreases the affine scale slope \(L(p)\),
while the admissible inequality for \(p\) persists. This step uses
only the central incoming ceiling \(u\le U(1/S)\); it does not
assume that the lowered shape retains \(u\le U(r_A)\).

The difference in the stronger slope inequality is affine in \(u\).
At its upper endpoint the accepted positive-slope argument applies.
At \(u=3/4\), direct collection of the product (19) gives exactly
the printed \(P_1,P_0\) and the positive leading \(k^2\) term
in (18). All coefficients are nonnegative, and the displayed
quadratic part of \(P_0\) is strictly positive because \(x>1\).
The resulting constant in (20) is exactly \(7/96\), so the
corrected expression strictly decreases at fixed \(p\).

For the tau-two face, the square completion (22) is valid for every
diagonal parameter. Its lower bound is concave in
\(a=\alpha^{-2}\), with precisely the stated quadratic
coefficient. Both endpoint arguments are correct. At \(a=1\),
the quadratic in \(q\) has positive leading coefficient, its
derivative at \(q=1/7\) is negative, and the dependence on \(u\)
at that scale is concave. The two complete endpoint polynomials in
(25) match direct substitution and have positive coefficients.

Consequently \(q(R_2^*)'>1/7\ge q\), so \((R_2^*)'>1\).
The Casimir derivative is at most \(245/3456\), giving the strict
corrected derivative bound \(-7/3456\) in (26).

## 4. Scope of the accepted reduction

The original incoming norm, equal-secant short shape, and common
covector are retained during both scale comparisons. The remaining
terminal scales are exactly \(q=\min\{q_c,1/7\}\). The bound
\(r_A\ge1/(1+x)\ge1/3\) ensures \(T\ge7/3>2\) throughout
the tau-two continuation.

The corrected scalar remains a lower bound for the original
\(\Gamma_{\mathrm{actual}}\). No competitive cap is assigned
to the artificial endpoint Casimir, and no physical completion
cost is transported through the comparison. The result is a uniform
conditional reduction for an actual short bridge with \(1<x\le2\),
suitable for the separate terminal sign theorems.

The review used the explicit identities and elementary inequalities
described above. No Lean compilation, Lake, typechecking, CI,
parameter-box computation, or executable cover is a proof input.
