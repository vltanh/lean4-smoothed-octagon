# Independent review of the low-ratio forward hand exclusion

Date: 2026-11-08 UTC.

**Acceptance:** the [low-ratio theorem](MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION.md)
proves \(t>1/3\) for every remaining actual smaller-nonshort window
whose actual successor is forward. This closes the ratio sign that
was left open in the earlier reduction. It does not prove the separate
gap bound \(j\le1/30\) or close the entire H-N-forward gate.

The review checks the complete domain, both scalar substitutions,
the shape comparison, the positive denominator, the first three
gap coefficients, all derivative losses, the positive discriminant,
the complete higher-order loss and the actual-boundary interface.
No Lean compilation, Lake, typechecking, CI or interval cover was run.

## 1. The original scalar comparison is preserved

The common strict t>1/4 and order bounds place a hypothetical
t<=1/3 point in the previously accepted reduction domain. At those
unchanged coordinates, the incoming floor lies below the original v,
and the positive-integral ceiling V lies strictly above v. The
logarithm ceiling and the two negative scalar coefficients therefore
give the stated strict negative comparison.

The exact identity
\[
v_3-V=\frac{(1-t)x^6(31x^2+82x+46)}
 {60(1+x)^2(x+2)^5(x^2+10x+15)}>0
\]
is correct. Because rho>0, replacing v_3 by V lowers the effective
norm by \((1+\rho)(v_3-V)\). It thus preserves the earlier proved
ceiling below U(t). The proof of positive shape derivative uses just
this ceiling, independence of k and the established mixed-derivative
signs. It applies without any new condition at an intermediate shape.
Hence lowering k to one preserves the required negative scalar sign.

Only after this lowering is the q interval enlarged. The proof does
not apply shape monotonicity on that enlargement: it proves an
independent polynomial sign there. This order avoids an otherwise
unjustified use of the original floor at enlarged points.

## 2. The compact defining identity and normalization

The original residual gives exactly equation (23) of the theorem.
With E_0=q^2B+W^2-2pqW, the residual/transport combination gives
the bracket in its equation (24) as \(4qW^2\widehat G\).
Multiplication by \(48(q+1)WR\) therefore gives precisely
\(P=192q(q+1)W^3R\widehat G\). All factors are positive.
Substitution of the effective norm and the logarithm bound cancels
their denominators; P is a polynomial, of degree ten in j.

The first three coefficients have exactly the factors printed in
equation (12). They are positive factors on the full h interval.
The proof's variable beta=j/[h(h+1)] is nonnegative and gives
the identity in equation (15), including its factor h+1 in front
of beta squared. This factor is at least 4/3.

## 3. Derivatives of the quadratic coefficients

Each displayed base derivative has degree at most seven in z.
Its coefficients in the stated basis are compared with the
coefficients of \((z+(1-z))^7=1\), including the binomial
factors. The three resulting lower bounds are respectively
5705, 15034 and 72896/9.

The negative coefficient sums R_0,R_1,R_2 include all terms with
a positive power of u=h-1/3 and omit only the already retained
u=0 polynomial. At u<=1/6,z<=1, the complete losses are bounded
by their evaluations at 1/6. These equal
\[
2024155555/10077696<201,
\quad7862531755/13436928<586,
\quad68094787741/40310784<1690.
\]
Each is strictly below its corresponding base lower bound. Thus
all three coefficient derivatives are positive, with strictness
also at h=1/3 and h=1/2. Since beta>=0, even a negative value
of the middle base coefficient causes no problem in lowering the
quadratic coefficientwise.

## 4. The base quadratic and its higher-order remainder

The three base polynomials and the fifteen coefficients of the
displayed discriminant identity agree with the compact definition.
The normalization factor 4/31381059609 is positive. Every term
in its expansion in \(z^m(1-z)^{14-m}\) is nonnegative on the
closed interval, and the surviving coefficient at either endpoint
is positive. Hence the discriminant is strictly positive everywhere.

It follows that a_0 a_2>0, so neither can vanish. Their positive
values at z=0 and continuity prove that both remain positive.
The resulting quadratic in beta has positive leading coefficient
and negative ordinary discriminant, proving its strict positivity
for all real beta, in particular for the needed nonnegative beta.

For the higher powers j^3 through j^10, all eight negative coefficient
sums in Section 5 are complete. The retained constant 370816/81
belongs to C_3 and is not included in any negative sum. Keeping it
and discarding the other positive monomials therefore gives a valid
lower bound. Using j<=1/2 bounds the entire negative contribution
after factoring out j^3 by
\[
80+270/2+1145/4+3341/8+2972/16+940/32+134/64+6/128
=72713/64.
\]
The difference is exactly 17842471/5184>0. This proves the stated
remainder inequality also at j=0, where the remainder vanishes.
The quadratic part is still strictly positive there. Consequently
P>0 on every boundary as well as in the interior.

## 5. Actual-period implication and scope

An actual nonshort forward point satisfies the incident-upper
residual N<0. The accepted boundary comparison places the solved
boundary outgoing norm below the actual one. The transported next
norm decreases along that same stationary line, so the actual next
norm floor gives the required boundary next-norm floor. These are
the precise eligibility conditions used in the earlier ratio
reduction. No actual norm floor is assigned to a different outgoing
switch, and no Casimir cap is needed in this proof.

Thus every such hypothetical point with t<=1/3 forces a negative
value at k=1, while the proved polynomial sign forces a positive
value at those same t,x,q. This contradiction establishes the claimed
strict bound. The common normal covector, actual positive durations
and the twisted seam are unchanged throughout the interface.

As a transcription safeguard, this review independently reconstructed
P from the residual and transported-norm formulas, rather than loading
the author's polynomial. The reconstruction checks the three base
polynomials, all twenty-four base derivative coefficients, the three
complete derivative loss polynomials and their sums, all fifteen
discriminant coefficients, and all eight complete remainder loss
polynomials, weighted sums and constants. These supplementary checks
match the displayed hand identities; no executable sign verdict is
a premise of the accepted proof.
