# Scope and arithmetic audit of the conditional small-shape cost theorem

Date: 2026-11-08 UTC. Review of
[MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION](MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION.md)
and its
[analytic shape bounds](MIXED_SMALLER_SHORT_CENTRAL_COST_SHAPE_BOUNDS.md).
The conclusion is conditional on the actual shape domain and original
Casimir lower floor stated in the theorem. This record does not close
those caller obligations.

## 1. Original period, covector and score

The starting bridge is the actual smaller-short bridge, with its
original equal-turn secants, incoming norm u, physical cost and common
PMP covector. The inequality Gamma_actual>1829/10000 lowers the
original kappa to 40/27 by the already proved monotonicity of the
relaxed score. It is not a ceiling and is not reapplied at another
scale.

The root-to-shear theorem applies on exactly the shape domain used
here. It supplies h<0 and -hR>5A/2. The existing scale-angle theorem
then gives the initial strictly negative scale derivative, with all
its actual-point caps satisfied. The subsequent continuation uses the
exact critical-angle classification. Its upper angle is excluded by
omega_c<13/175<5/48<theta1. This comparison remains valid if the
central scalar endpoint passes the original outer q=1/7 cap: no
continued root, outgoing norm floor, competitive Casimir cap or
physical admissibility is asserted there.

The lower-row angle is fixed by shape, and both that angle and the
entire continued shear angle remain below pi/6. Thus the completion
term is on the active branch throughout. The resulting central score
is a valid lower bound for the original full-period cost, rather than
a substituted cost for an unproved competitor.

## 2. Independent checks of the analytic helper

The simplification of the scale-independent shear term is exact:
\[
H_0=\frac{(R+T)(3+RT)}{3+T^2}=R+(1+A)T.
\]
This proves the Z formula directly from the existing physical shear
formula. The upper A bound retains its correlation between x and
T; the larger independent interval for T alone would not prove
A<1/100. Its endpoint 25233/2692699 and derivative sign are correct.

The positive integral for V(x)-3/4 can be obtained by integrating
its stated rational kernel. Pairing t and 1-t gives the exact
symmetric denominator a^2-R^2(t-1/2)^2. The first two positive
terms have moments 1/6 and 1/120, giving precisely
R^2/(12a)+R^4/(240a^3). The later inequality
1/(1+z)>=1-z+(19/21)z^2 uses z<=2/19 and is in the lower-bound
direction. Consequently the final uq is below the original incoming
secant; it is not an incoming ceiling. Its R-form and the rational
N_u/D_u in the cost theorem agree term by term.

For the shear second derivative, the derivative formulas for
T and g are exact. The bracket in (11) exceeds 4/5, with the
rational upper comparison 144039/731555<1/5. The factor outside
that bracket exceeds 5 after taking the monotone endpoint in G.
The two contributions give Z_dd<-1163/375<-3. The derivative in
eta of Z_d(0) is positive; the upper initial-slope comparison has
complete numerator 12-69h+80h^2+159h^3+93h^4+26h^5+3h^6.
Its only adverse term leaves at least 1/2.

The lower-shear proof correctly uses two concavities: at fixed
x,beta the alpha curvature of H0 is positive, so Z is concave in
eta; at each eta endpoint the proved d curvature gives the chord
bound. Both printed quintics are the exact numerators of
Z-Z0(1+11d/2) at d=1/19. They decrease, and their positive right
endpoint values prove the required signs. The upper and lower Z
bounds therefore hold on the entire closed rectangle, including d=0.

## 3. Cancellation and all lower-bound directions

At central scale, the cost identity gives
\[
C_c=\frac{\sqrt3}{2}\{(1+a_1)R+(1+a_2)T\}+JH,
\quad a_i=u/U_i,
\quad H=Z/\sqrt3.
\]
The exact cancellation
\[
JK=2c-3(b_1+b_2)/2
\]
was rederived from J=3a1/2, a2=a1(1+A), and
K=A+2+2kappa0/J. This is essential: bounding K by 4 before this
cancellation would lose the available cost margin.

The half-angle estimate uses a positive H, and the central-shape
lemma supplies H>0 throughout. The denominator correction is less
than 150001/150000. Its entire extra contribution is bounded by
1/800000 using the explicit rational comparison in (10).
After cancellation the two remaining shear terms have negative
coefficients. Therefore K>=4, Z<=ZU in the term multiplied by
b1+b2>=0, and Z>=ZL in A^2/Z all give lower bounds. The arctangent
polynomial is an upper bound, so its use with the negative completion
coefficient also gives a lower bound.

Only after these comparisons is u lowered to uq. This is justified
by the displayed strictly positive derivative of mathcal B with
respect to u. No norm floor, root or Casimir statement is transferred
along that change. The eventual multiplication by ell<sqrt(3) is
made only after mathcal B>b*>0 has been established.

## 4. Analytic eta reduction

At fixed R and d, uq,ZL,ZU do not depend on eta. The variable T
therefore ranges over the interval bounded by its two eta endpoints.
The decomposition (16) is exact.

The second derivative of f divided by z is exactly the difference
in (17); u>=3/4 and z^2<1/7 give the strict negative sign. The
second derivative of g is also negative. Finally the displayed
formula for (A^2)'' is correct, with positive numerator because
T^2>1/12 and R^2,T^2<1/7. Its coefficient in mathcal B is negative.
Thus concavity in T is proved analytically, without a coefficient
certificate or an assertion about the second secant at an endpoint.
The resulting eta endpoint reduction retains all interior shapes.

## 5. Reconstruction of the two polynomial numerators

Starting from (15), substitute uq=N_u/D_u and T=N/B. Then
\[
b_1=N_1/(K_1D_u),\quad b_2=N_2/(K_2D_u),
\quad A=N_A/K_2.
\]
The two Z formulas reduce respectively to
N_Z/[6(3-R)(1-R)] and R^2(1+R)(2+11d)/(3-R).
Multiplication by the positive denominator (22) gives exactly the
products in (24). In particular the b*ZU term has factor 1/48;
the A^2/ZL term has factor 161/432. These factors were checked
from the original scalar expression rather than inferred from a
cleared numerator.

The ratio coordinate is t=R-1/3, not x-2. Its endpoint is 2/57.
Both polynomials have degree at most (24,14), and their common
normalization is the positive rational number specified by (25).
The three stated coefficientwise inequalities were reconstructed from
these products with exact rational coefficients:

- the full second derivative is bounded above by -250+M;
- the common d=0 polynomial is bounded below by 1-E0;
- both d=1/19 polynomials are bounded below by 89/100-E1.

The two factors defining M give its complete binomial coefficient
formula for every t,d degree. The two E polynomials display every
adverse endpoint term, including those above degree fifteen. There
is no omitted tail, hidden coefficient minimum, subdivision or
external executable input. Exact symbolic arithmetic was used to
cross-check the printed identities during discovery; the proof
premises are the finite formulas and inequalities printed in the
paper, which can be checked by rational multiplication.

The sign argument itself uses only four short integer power
comparisons and the two exact endpoint evaluations in (31).
In particular M<5 proves strict displacement concavity with a margin
exceeding 245. The endpoint lower bounds are at least 4/5 and
89/100-3/4=7/50, respectively. Thus all equality boundaries in
t, d and eta are covered.

## 6. Rational constants and final strictness

A separate mathematical reading accepts the conditional theorem and
its analytic helper. It checked the original-period score comparison,
the continuation on the decreasing angle branch without retaining
the outer scale cap, the positive-integral incoming lower bound, both
central shear bounds, and the cancellation before using K>=4. It
also checked the concavity in the angle coordinate, the complete
adverse-term majorants, the three univariate endpoint signs, and all
directions of the final rational-constant comparisons. The actual
shape and original Casimir hypotheses remain explicit caller inputs.

The elementary square checks are
\[
3\cdot571^2-989^2=2,
\]
\[
173205081^2-3\cdot10^{16}=84216561,
\quad
2\cdot10^{18}-1414213562^2=1055272156.
\]
The stated Machin lower expression exceeds 314159265/10^8 by
\[
17666710543624273/6755115084786337500000000>0.
\]
The rational octagon upper expression obtained from the stated square
root and log bounds is below 3126055/10^6 by
\[
182619963490373213/325671709936905028125000>0.
\]
These checks establish the directions of all constants in (20).
The octagon fraction is positive and decreases with both sqrt(2)
and log(2), so those substitutions have the required upper-bound
direction.

The final chain uses the actual period inequality, the justified
central scalar comparison, the strict lower bound for mathcal B,
and the strict octagon upper bound. It proves the claimed strict
physical-cost contradiction. The theorem remains conditional on
its actual shape and original Casimir hypotheses; it does not
independently close their ratio, displacement or Casimir gates.
