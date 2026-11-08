# Independent audit of the small-forward-minimum hand replacement

Date: 2026-11-07 UTC. Two independent internal mathematical readings.

The complete replacement in
[SMALL_FORWARD_MINIMUM_HAND_PROOF](SMALL_FORWARD_MINIMUM_HAND_PROOF.md)
and its final
[integral rational bound](HAND_H5_INTEGRAL_RATIONAL_BOUND.md)
is accepted. It replaces the hard symmetric face H5 in the current
hand-only dependency chain. It does not claim the later forward or
mixed exclusions are complete.

## Actual interface and normalization

The original common-lift stationarity identities, both genuine exterior
missing-control inequalities, larger-neighbor monotonicity and the two
easy faces are unchanged. Dividing their scalar residual by a gives
exactly the displayed normalized coefficients. In particular, the
opposite floor remains F_x(H); it is not weakened to its value at one
without retaining the positive difference Delta.

The change of variables has the correct directions: the hard face
gives 0<lambda<1, 0<s<=lambda, and z>=(3-lambda)/(1+lambda).
The cubic theorem proves its sign on the full larger closed domain,
so none of the actual weak minimum or switch ties is lost.

## Integral comparison

The two initial-value identities are the old easy-face identities with
the exact opposite-floor difference restored. The second derivative
and the facts P(1)=-zZ(H-1), P'>=Z give the claimed upper bound
without assuming concavity of the original residual. Both integrations
have the displayed exact values.

The central logarithmic expression first decreases and then increases
as a function of q. Its two permissible upper endpoints are correctly
chosen from U>=3 and U>=z. Their derivatives and starting values prove
the required nonpositive sign throughout both ranges.

The Padé remainder derivative is nonnegative, and the floor identity
Delta=x(x-1/2)d+xHf(H)/d gives the stronger rational floor with the
correct inequality direction. Its multiplier is strictly negative.
After dropping only the nonpositive central term, the resulting upper
bound is exactly the rational expression B in the second note.

## Cubic sign, including boundaries

Both further weakenings increase B: the floor is multiplied by a
negative coefficient, while the logarithmic remainder is subtracted.
The resulting denominator is positive because z>=1 and S-v>=z>0.
The displayed cubic P and its expansion in p=U-3 agree directly by
multiplication.

The three nonconstant coefficients in that expansion are nonnegative
by v^2<=v and the explicit bounds in the note. The constant coefficient
is strictly positive for v>0. For m<=1/5 this follows from the completed
square with positive residual 251m^2/92. For m>=1/5 the four-term cubic
identity is exact, and all four coefficient functions have displayed
positive signs. In particular, both concavity claims, the substitution
n=1-m, the completed square for the lower range of Q, and its final
four-positive-term identity were checked independently. The endpoint
m=1 forces v=1 and has value 15; m=0 and v=0 are handled explicitly.

Thus B<0 whenever h>1 on the complete required domain. No table of
hundreds of coefficients, interval cover or numerical optimizer is
needed for this implication. Supplementary symbolic checks of the
identities do not supply any of its mathematical signs.

## Whole-period consequence and remaining gates

Combining this accepted hard-face sign with the original hand arguments
excludes every small forward minimum in the stated actual normal-period
setting. The consequences a_min^2>4/3 in F and a reverse global minimum
in the mixed case therefore have a hand-only proof under the same
upstream normality/geometric premises.

The forward neighbor and norm-sum exclusions, the smaller-short
cost/root exclusion, and the smaller-nonshort successor exclusions
remain open. This audit removes one shared prerequisite; it does not
turn the completed computational baseline into a completed hand proof.
