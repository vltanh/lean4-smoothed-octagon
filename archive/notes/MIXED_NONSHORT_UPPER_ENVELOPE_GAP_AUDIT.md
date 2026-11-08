# Independent review of the nonshort upper envelope and duration gap

Date: 2026-11-07. Internal mathematical review of the displayed hand
proof. No interval cover, runtime exclusion, Lean, Lake, typechecking or
CI is a premise of this result.

**Verdict:** I accept the upper-envelope comparison, the inequality
d^2+2cd>4, the resulting delta1>1/10 gap under a^2<2/3, and the two
secant restrictions in
[MIXED_NONSHORT_UPPER_ENVELOPE_GAP](MIXED_NONSHORT_UPPER_ENVELOPE_GAP.md).
These are necessary conditions on actual same-lift nonshort data. They
do not close either successor branch on their own.

## 1. Which upper envelope is used

The source first replaces the incident norm u by U(a/S) in the central
stationarity expression. The resulting outgoing envelope w_U has
positive derivative in b and is strictly above the actual outgoing
norm. The coefficient w_u=K(aK+SY)/(aQ^2) is positive because Y>0.
Differentiation gives exactly the two derivatives displayed in Lemma 1.

Consequently w_U(b*)>w_actual>g_d(r). This does not assert that the
solved boundary root w* satisfies the actual outgoing floor. That
distinction is necessary: the existing root comparison gives
w*<w_actual. The new proof consistently uses the upper envelope instead.

## 2. Chord estimate and the five-term identity

The incoming same-edge secant has endpoints a<d and intermediate turn c.
Strict turn log-concavity gives ad<c^2. The pointwise chord difference
has the explicit factor

\[
\frac{c(s-a)(d-s)
 [c^2(a+d+s+2c)-ad\,s]}
 {(a+c)^2(c+d)^2(c+s)^2}>0
\quad(a<s<d).
\]

Thus integrating gives the strict trapezoid upper bound on v, without
requiring the entire interval to lie below 2c. This handles the case in
which the ordinary second derivative of g_c changes sign within the
interval.

At b*, the coefficient of v in w_U is positive. The substitutions
C_a=4/T+4c/K and u=U(aT/K) therefore justify replacing v by its chord
upper bound. I independently reconstructed the rational difference
Q^2(w_U,ch-g_d(r0)) and its denominator, with
r0=Q/W-d. The numerator becomes exactly the displayed P0+e Pe after
d=a+x and 4=d^2+2cd+e. Every coefficient is explicitly factored into
positive quantities in the theorem.

Under the contrary hypothesis e>=0, q>1 gives r>r0>=d.
Since g_d is increasing on [d,infinity), the sign identity contradicts
w_U(b*)>g_d(r). No condition at an artificial outgoing switch is used.
This proves d^2+2cd>4 for either successor alternative.

## 3. The scale gap and its zero-duration scope

The sharpened scale a^2<2/3 and the smaller-turn inequality T^2<=K
give G=4-a^2-2ac>1 by the displayed positive squared difference
9-10z-3z^2, z=a^2. The new centre inequality is precisely
T^2 delta1(delta1+2)>G. Since T^2<14/3 and 3/14>21/100, it follows
that delta1>1/10.

All quantities a,c,d and delta1 are unchanged by the b-to-b* root
comparison. Thus the new maximum max(delta1,delta2) is also >1/10,
regardless of which parameter maximized the original three-variable
chart. The entire former epsilon<=1/32 corner is consequently absent
for actual nonshort data. Its coefficient-table proof can be removed
from this refined route.

## 4. The turn-length and reverse-only restrictions

Extending the incoming secant interval [a,d] to [0,d] raises its
average, because the added values exceed g_c(a)>v. Combining this
with v>g_c(d) gives the logarithmic inequality in Lemma 3. Its
difference has derivative t(t-1)/(1+t)^3. The two-term positive
atanh lower bound at t=5/2 exceeds 60/49 by the stated exact integer
comparison. Hence d<5c/2.

For the reverse successor, w<=Sec(a,r,d) and the actual strict outgoing
floor give Sec(a,r,d)>g_r(d). Minimality and r^2>=ad also give a<r.
The values of g_r in the interior of [a,d] lie strictly below g_r(a):
use its decrease up to r, its increase afterwards, and
g_r(d)<=g_r(a) when ad<=r^2. Thus the extended secant has the strict
upper endpoint inequality needed for the same argument, proving
d<5r/2. The preserved missing-control inequality uses only unchanged
a,d,r,q, and is legitimate after the comparison.

## Scope

The new facts are elementary uniform restrictions, including arbitrary
positive durations and the original chart0-maximal configurations.
They preserve the actual PMP interface and do not assume that an
upper-envelope point is physical. The remaining forward and reverse
exclusions still need separate hand arguments; this review does not
replace their completed interval covers.
