# A conditional nonshort scale bound below 4/5

Date: 2026-11-07 UTC. Hand proof.

**Theorem.** At an actual smaller-turn minimum reverse centre satisfying

\[
t:=\frac a{a+c}\le\frac25,
\]

the competitive whole-period premises imply

\[
\boxed{a<\frac45.}
\tag{1}
\]

The bound `t<=2/5` is an explicit hypothesis of this lemma.
[The high-ratio hand exclusion](MIXED_NONSHORT_HIGH_T_HAND_EXCLUSION.md)
proves the stronger strict bound for every actual smaller-nonshort
continuation. Combining the two notes therefore gives `a<4/5` throughout
that actual nonshort case. The [independent audit](NONSHORT_HAND_SCALE_AUDIT.md)
checks both implications. The retained central Casimir
argument is in
[MIXED_NONSHORT_RETAINED_CENTRAL_CASIMIR](MIXED_NONSHORT_RETAINED_CENTRAL_CASIMIR.md).

**Proof.** Suppose `a>=4/5`. The already proved
[hand scale and cap](HAND_PROOF_REFINEMENTS.md) give

\[
\frac4{29}\le\rho:=\frac{a^2}{a^2+4}<\frac17,
\qquad \gamma^2<\frac{9193}{50000}.
\tag{2}
\]

The [explicit turn floor](EXPLICIT_TURN_NORM_FLOOR.md) and t<=2/5 show
that both actual incident norms exceed

\[
\Phi(3/5)=-\frac4{25}+\frac25\sqrt{26/5}
 >\frac{94}{125}=:\mu.
\tag{3}
\]

The last comparison is just `sqrt(26/5)>57/25`; its two squares differ
by `1/625`.

Write z=a/(a+b), so `z<=t<=2/5` and `rho<zt`. The Casimir numerator
increases with each incident norm on the actual norm rectangle, as
proved in the retained-central-bound note. Lower both norms to the
constant mu. With these norms fixed, the diagonal expression is

\[
E(z,t)=1+z+t-\rho+\log\frac{\rho}{zt}
 -(1-\mu)(1/z+1/t).
\]

It is positive. To see the lower estimate explicitly, lower mu further
to 3/4; both ratio derivatives then equal `(2s-1)^2/(4s^2)>0`.
Decrease one ratio until the product is rho. At that boundary the sum
of the two ratios is at most `1/2+2rho`, by expanding the product of
their distances from 1/2. The coefficient of this sum is
`1-1/(4rho)<0`. Thus the boundary value, and hence the original value,
satisfy

\[
E(z,t)>1+\rho-\frac1{8\rho}
 \ge\frac{33}{29}-\frac{29}{32}
 =\frac{215}{928}>0.
\tag{4}
\]

Moreover its two ratio derivatives are positive for ratios at most 2/5:

\[
\partial_z E=\frac{U(z)-\mu}{z^2}>0,
\qquad \partial_t E=\frac{U(t)-\mu}{t^2}>0,
\]

because U decreases up to 1/2 and
`U(2/5)=19/25>94/125`. Raise both ratios to 2/5. This increases the
positive E, hence decreases the Casimir expression with the norms fixed.
The original strict lowering of the actual norms proves

\[
\gamma^2>\mathcal H(\rho):=
\frac{4\mu^2-B(\rho)^2}{16(1-\rho)^2},
\quad B(\rho)=\frac{14}{25}-\rho+\log(25\rho/4).
\tag{5}
\]

On the rho interval (2), B is positive by (4) and increasing because
`B'=1/rho-1>0`. At its upper endpoint, use
`log(25/28)<-3/28` to obtain

\[
0<B(\rho)<\frac{14}{25}-\frac17-\frac3{28}
 =\frac{31}{100}<\frac13.
\tag{6}
\]

Differentiating (5) shows that its derivative has the sign of

\[
4\mu^2-B^2-B(1-\rho)^2/\rho.
\]

The factor `(1-rho)^2/rho` decreases for rho<1. Using (2), (6) and
mu>3/4, this expression is strictly greater than

\[
\frac94-\frac19-\frac13\frac{625}{116}
 =\frac{179}{522}>0.
\]

Thus H is increasing on (2), and its value at rho=4/29 supplies a
uniform lower bound. There,

\[
B(4/29)=\frac{306}{725}-\log(29/25)
 <\frac{306}{725}-\frac4{27}
 =\frac{5362}{19575}.
\]

The strict logarithm inequality is the first positive term in
`log(29/25)=2 atanh(2/27)>4/27`; it also follows by integrating
`1/(1-s^2)>1` from zero to 2/27. Substitution in (5) gives the exact
rational contradiction

\[
\gamma^2>
\frac{4(94/125)^2-(5362/19575)^2}{16(25/29)^2}
=\frac{5237560379}{28476562500}
=\frac{9193}{50000}+\frac{7438391}{113906250000}
>\frac{9193}{50000}.
\]

This contradicts (2), proving (1). All logarithm estimates, derivative
signs and rational comparisons used in the proof are displayed.
