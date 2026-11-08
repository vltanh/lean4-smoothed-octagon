# A strict physical-cost contradiction on the small short-shape domain

Date: 2026-11-08 UTC. Conditional hand theorem, with a separate
[scope and arithmetic audit](MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_AUDIT.md).
This proves the completion-cost step on its stated domain. It does not
supply the actual ratio, displacement or Casimir lower bound.

## 1. Statement and original physical quantities

Suppose an actual smaller-short bridge retained by the
common-covector six-variable reduction satisfies
\[
2\le x\le13/6,\quad0\le d:=\beta/x-1\le1/19,
\quad\alpha=1+\eta d,\quad13/5\le\eta\le3,
\]
\[
\Gamma_{\rm actual}>1829/10000,
\tag{1}
\]
and has its required actual outer descending root. Then its original
period satisfies
\[
\boxed{C_{\rm period}>A_{\rm oct}.}\tag{2}
\]
The actual setup includes the same common PMP covector, the two
original turn secants, the physical bridge cost, and the original
whole-period completion inequality. All comparisons below retain
those physical inputs until an explicitly justified scalar comparison
is made. No Casimir cap, root or closure is assigned to a comparison
point.

Write
\[
R=\frac{x-1}{x+1},\quad T=\frac{\beta-\alpha}{\beta+\alpha},
\quad U_1=\frac{3+R^2}{4},\quad U_2=\frac{3+T^2}{4},
\quad A=U_1/U_2-1.
\]
Here T is an angle coordinate. Let u be the original incoming secant
and h the actual physical shear. The
[root-to-shear theorem](MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR.md)
gives
\[
h<0,\qquad-hR>5A/2.
\tag{3}
\]

## 2. Justified continuation of the relaxed score

Set
\[
\kappa_0=40/27,\qquad c=\kappa_0+3/2=161/54.
\]
The original Casimir bound gives kappa_actual>kappa0 because
\[
12(1829/10000)-(40/27)^2=23/1822500>0.
\]
The relaxed completion score is nondecreasing in kappa by the
[angle-circle comparison](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md).
We therefore lower kappa to kappa0, keeping the actual shape and norm
u fixed.

The original central-duration cap is rho<=1/(1+x)^2, or
rho/(1-rho)<=1/[x(x+2)]. Increase this scalar scale to the latter
endpoint, continuing the exact shear and physical-cost formulas. At
the original point, (3) and Section 5 of the
[scale-angle theorem](MIXED_SMALLER_SHORT_SCALE_ANGLE_BARRIER.md)
give a strictly negative scale derivative of the fixed-kappa score.

The continuation remains on that decreasing branch. To check this
without transporting an original scale cap, use the exact
[critical-angle classification](MIXED_SMALLER_SHORT_SHEAR_COST_REDUCTION.md).
Its two possible critical angles are |theta1-theta2| and
theta1+theta2; they depend only on the fixed shape, u and kappa.
The shear decreases with scale, so its angle omega increases.
At central scale put H=-h_c=Z/sqrt(3). The
[analytic central shape bounds](MIXED_SMALLER_SHORT_CENTRAL_COST_SHAPE_BOUNDS.md)
give 0<Z<1/5 and 0<=A<1/100. In particular H<1/8. In the
half-angle formula below, K+sqrt(K^2-A^2)>=7, hence
\[
\omega_c<2(2/8+1/100)/7=13/175.
\tag{4}
\]
On the other hand, the incoming bound u<=3/4+R^2/12 gives
\[
\theta_1\ge R/\sqrt{12U_1}>5R/16\ge5/48>13/175.
\]
Thus the increasing angle cannot reach the upper critical angle
before central scale. Its initial strictly negative derivative places
it after the lower critical angle, and it remains there. This also
covers A=0 on its h<0 angle branch.

Clipping is absent: the fixed lower-row angle is
\[
\psi=\arctan(R/\sqrt3)+\arctan(T/\sqrt3)<\pi/6,
\]
and (4) gives omega<pi/6. For an explicit bound on the fixed angle,
psi<=2R/sqrt(3)<=14/(19sqrt(3))<1/2<pi/6.
At the central scalar scale the resulting
lower bound for the original period is therefore
\[
\mathcal F_c=C_c+c(\pi/3-\psi-\omega_c),
\quad
C_c=\sqrt3\left\{\frac{uQ}{x(x+2)}+\frac{R+T}{2}\right\},
\]
\[
Q=2\beta x-x-\alpha\beta,\qquad
C_{\rm period}\ge\mathcal F_c.
\tag{5}
\]
This is a scalar comparison of the exact original physical score.
It asserts neither a physical continued trajectory nor a continued
Casimir bound.

## 3. Cancel the leading shear term before bounding its denominator

Let
\[
a_i=u/U_i,\quad b_i=1-a_i\ge0,\quad b=b_1+b_2,
\quad J=3a_1/2,\quad K=A+2+2\kappa_0/J.
\]
The original norm bounds give b_i>=0. Also K>4: indeed
\[
\frac{80}{81}U_1-u
\ge\frac{53R^2}{324}-\frac1{108}
\ge\frac{26}{2916}>0.
\tag{6}
\]
By the exact central shear identity,
\[
Z=\frac{2U_1Q}{x(x+2)}-R-(1+A)T,
\]
so the physical cost in (5) is exactly
\[
C_c=\frac{\sqrt3}{2}\{(1+a_1)R+(1+a_2)T\}+JH,
\qquad H=Z/\sqrt3.
\tag{7}
\]
Moreover
\[
\boxed{JK=2c-3b/2.}\tag{8}
\]
This cancellation is why a simple denominator bound suffices below.

The exact shear half-angle formula is
\[
\omega_c=2\arctan
 \frac{\sqrt{H^2+A^2}+H}{K+\sqrt{K^2-A^2}}.
\]
Using sqrt(H^2+A^2)<=H+A^2/(2H),
sqrt(K^2-A^2)>=K-A^2/K, and arctan(y)<=y gives
\[
\omega_c\le\frac{150001}{150000K}
                  \left(2H+\frac{A^2}{2H}\right).
\tag{9}
\]
The correction factor is valid because A<1/100 and K>4 imply
1/[1-A^2/(2K^2)]<320000/319999<150001/150000.
Its contribution to c*omega is less than 1/800000: using
Z<1/5, Z>=1/9, 17/10<sqrt(3)<7/4 and c<3,
\[
\frac{c}{150000K}
 \left(\frac{2Z}{\sqrt3}+\frac{\sqrt3 A^2}{2Z}\right)
<\frac1{200000}\left(\frac4{17}+\frac{63}{80000}\right)
<\frac1{800000}.
\tag{10}
\]
Combining (8)--(10), and only now using K>=4, gives
\[
JH-c\omega_c>
-\frac{\sqrt3}{8}\left(bZ+\frac{cA^2}{Z}\right)
-\frac1{800000}.
\tag{11}
\]

Use the explicit bounds ZL<=Z<=ZU from the central shape lemma:
\[
Z_L=\frac{2R^2(1+R)}{3-R}(1+11d/2),
\]
\[
Z_U=\frac{2R^2(1+R)}{3-R}
       +\frac{1+2R}{3(1-R)}d-\frac32d^2.
\tag{12}
\]
Since b>=0, (11) remains a lower bound when bZ is raised to bZU
and A^2/Z to A^2/ZL.

The alternating integral identity for arctan gives
\[
\arctan(z/\sqrt3)\le
\frac z{\sqrt3}-\frac{z^3}{9\sqrt3}
                         +\frac{z^5}{45\sqrt3}.
\]
Define the small polynomial
\[
L(z)=z/162+161z^3/1458-161z^5/7290.
\tag{13}
\]
Equations (5), (7) and (11) now imply
\[
\mathcal F_c>
 c\pi/3+\sqrt3\,\mathcal B(u;R,T,d)-1/800000,
\tag{14}
\]
\[
\boxed{\mathcal B
=L(R)+L(T)-\frac{b_1R+b_2T}{2}
 -\frac{(b_1+b_2)Z_U}{8}-\frac{cA^2}{8Z_L}.}
\tag{15}
\]
At fixed R,T,d this expression increases with u, since
\[
\mathcal B_u=\frac{R}{2U_1}+\frac{T}{2U_2}
 +\frac{Z_U}{8}(U_1^{-1}+U_2^{-1})>0.
\]
We may replace the original u by the proved quadratic lower bound uq
from (6) of the central shape lemma. Only this displayed scalar
expression is changed; no other physical constraint is transported.
All occurrences of u below mean uq.

## 4. Concavity removes eta analytically

At fixed R and d, the values u,ZL,ZU are independent of eta.
The variable T ranges between its values for eta=3 and eta=13/5.
We prove that (15) is strictly concave in T on that entire interval.

Put
\[
f(z)=-40z/81+161z^3/1458-161z^5/7290
                  +\frac{2uz}{3+z^2},
\quad g(z)=\frac{u}{2(3+z^2)}.
\]
Then
\[
\mathcal B=f(R)+f(T)+Z_U\{g(R)+g(T)-1/4\}
          -\frac{c}{8Z_L}
                  \left(\frac{R^2-T^2}{3+T^2}\right)^2.
\tag{16}
\]
For 9/31<=z<=7/19 and u>=3/4,
\[
\frac{f''(z)}z
=\frac{161(3-2z^2)}{729}
    -\frac{4u(9-z^2)}{(3+z^2)^3}<2/3-5/6<0,
\]
\[
g''(z)=-\frac{3u(1-z^2)}{(3+z^2)^3}<0.
\tag{17}
\]
For the first comparison, z^2<1/7 gives the lower bound
4557/5324>5/6 for the second term.
Finally, direct differentiation gives
\[
\left[\left(\frac{R^2-T^2}{3+T^2}\right)^2\right]''
=\frac{4(3+R^2)
 (9T^2+5R^2T^2-3R^2-3T^4)}{(3+T^2)^4}>0.
\tag{18}
\]
Its numerator parenthesis exceeds
3/4-3/7-3/49>0, using T^2>1/12 and R^2,T^2<1/7.
Thus every T-dependent term in (16) is concave, with a strict first
term. It suffices to prove the desired bound at
\[
\boxed{\eta=13/5\quad\hbox{or}\quad\eta=3.}\tag{19}
\]

## 5. Two completely specified polynomials

Use the rational constants
\[
\ell=989/571<\sqrt3,\quad
\pi_0=314159265/10^8<\pi,\quad
A_0=3126055/10^6>A_{\rm oct}.
\]
Their elementary rational justifications are given in Section 7.
Set
\[
b_*:=\frac{A_0-c\pi_0/3+1/800000}{\ell}
     =\frac{792669623}{356040000000}>0.
\tag{20}
\]
It remains to prove mathcal B(uq;R,T,d)>b*.

The following factored definitions specify every coefficient used in
the rest of the proof. Put
\[
t=R-1/3,\qquad0\le t\le2/57,
\qquad e\in\{13/5,3\},
\]
\[
B=2+[e+1-(e-1)R]d,
\quad N=2R+[(e+1)R-(e-1)]d,
\quad T=N/B,
\]
\[
K_1=3+R^2,\quad K_2=3B^2+N^2,
\quad H_R=3R^2+10R+10,
\]
\[
D_u=1260(2+R)^3,
\]
\[
N_u=945(2+R)^3+84H_RR^2
        -42H_RR(1+R)d+19H_R(1+R)^2d^2,
\]
\[
N_1=K_1D_u-4N_u,\quad N_2=K_2D_u-4B^2N_u,
\quad N_A=K_1B^2-K_2,
\]
\[
N_Z=12R^2(1+R)(1-R)+2(1+2R)(3-R)d
                                      -9(3-R)(1-R)d^2.
\tag{21}
\]
These give exactly
\[
u_q=N_u/D_u,\quad b_1=N_1/(K_1D_u),\quad
b_2=N_2/(K_2D_u),\quad A=N_A/K_2,
\]
\[
Z_U=N_Z/[6(3-R)(1-R)],\quad
Z_L=R^2(1+R)(2+11d)/(3-R).
\]
All factors of the following denominator are positive:
\[
\mathcal D=B^5K_1K_2^2D_u(3-R)(1-R)R^2(1+R)(2+11d).
\tag{22}
\]
Define
\[
W_e=\mathcal D(\mathcal B-b_*),\qquad
P_e=W_e/W_e(0,0).
\tag{23}
\]
This is a polynomial of degree at most (24,14) in t,d. If desired,
it can be formed without rational-function manipulation by adding
the following polynomial products:
\[
\begin{aligned}
W_e={}&\mathcal D\{L(R)-b_*\}\\
&+\frac{\mathcal D}{B^5}
 \left(\frac{NB^4}{162}+\frac{161N^3B^2}{1458}
                                -\frac{161N^5}{7290}\right)\\
&-\frac{\mathcal D}{K_1D_u}\frac{N_1R}{2}
 -\frac{\mathcal D}{BK_2D_u}\frac{N_2N}{2}\\
&-\frac{\mathcal D}{(3-R)(1-R)D_uK_1K_2}
                      \frac{N_Z(N_1K_2+N_2K_1)}{48}\\
&-\frac{\mathcal D}{K_2^2R^2(1+R)(2+11d)}
                            \frac{161(3-R)N_A^2}{432}.
\end{aligned}
\tag{24}
\]
Every quotient in this display is an exact polynomial quotient.
The normalization is independent of e and positive; explicitly
\[
\frac{W_e(0,0)}{\mathcal D(0,0)}
=\frac{11606203670488891}{16826052703320000000}>1/1500.
\tag{25}
\]

## 6. One displacement concavity bound and three univariate signs

Write F \preceq G for coefficientwise domination in the ordinary
t,d monomial basis: every coefficient of G-F is nonnegative.
The finite product definitions (21)--(24) give the following common
bound for both e values:
\[
\boxed{\partial_d^2P_e\preceq-250+M(t,d),}\tag{26}
\]
\[
M=60000000t^6(1+t)^{18}(1+2d)^4
             +2000000d^5(1+t)^{24}(1+2d)^7.
\tag{27}
\]
This is a small factored polynomial bound, not a list of minima over
an undisplayed positive basis. To make its complete coefficient
content explicit, for d degrees j<=4 the adverse coefficients start
at t degree six and are bounded by
\[
60000000\binom{18}{i-6}\binom4j2^j.
\]
For 5<=j<=12 they are bounded by
\[
2000000\binom{24}i\binom7{j-5}2^{j-5}.
\]
A binomial coefficient outside its usual range means zero. The
constant second derivative is below -250; all other coefficients
below the first stated ranges are nonpositive. These are precisely
the coefficient inequalities obtained by substituting the two rational
e values in (24), differentiating twice, and collecting powers. No
higher degree is omitted.

Here is the entire subsequent derivative sign arithmetic. For
0<=t<=2/57 and 0<=d<=1/19,
\[
(1+t)^6\le(59/57)^6<5/4,
\quad(1+2d)^4\le(21/19)^4<3/2,
\]
\[
(1+2d)^7\le(21/19)^7<21/10.
\]
The first strict inequality is 5*57^6-4*59^6=2760101681>0;
the others are 388962<390963 and 857661210<893871739.
Thus (1+t)^18<2 and (1+t)^24<5/2. Consequently
\[
M<180000000(2/57)^6+10500000/19^5
=\frac{1280000000}{3810716361}
   +\frac{10500000}{2476099}<1/2+9/2=5.
\tag{28}
\]
Equations (26)--(28) show P_e is strictly concave in d. Its minimum
on [0,1/19] is therefore at one of those endpoints.

For those endpoints, the complete adverse parts have the following
explicit common majorants:
\[
\begin{aligned}
E_0(t)={}&101t^2+872t^3+2779t^4+4060t^5+1618t^6\\
        &+26t^{16}+22t^{17}+6t^{18}+t^{19},\\
E_1(t)={}&6t+336t^2+2505t^3+7434t^4+9510t^5+2195t^6\\
        &+83t^{16}+49t^{17}+12t^{18}+t^{19}
                        +t^{21}/50+t^{23}/10000.
\end{aligned}
\tag{29}
\]
Direct collection in (24) gives, for both e values,
\[
\boxed{P_e(t,0)\succeq1-E_0(t),\qquad
 P_e(t,1/19)\succeq89/100-E_1(t).}\tag{30}
\]
The d=0 polynomial is the same for both e values, so these are only
three univariate signs. Every negative term is bounded in (29),
including the high-degree terms. The remaining coefficients are
nonnegative.

For an especially short sign check, the terms of degree at least
sixteen in each E_i are at most t^7: their coefficient sums are below
146 and 146t^9<=146/6^9<1. The two resulting degree-seven majorants,
evaluated at t=2/57, are exactly
\[
\frac{325384688228}{1954897493193}<1/5,
\qquad
\frac{1454798090996}{1954897493193}<3/4.
\tag{31}
\]
Their coefficients are nonnegative, so these bounds hold on the whole
interval. Thus (30) is strictly positive at both d endpoints, and
concavity proves P_e>0 everywhere. The positive denominator and
normalization in (22)--(25) prove mathcal B>b* at the two eta
endpoints. Section 4 extends this strict bound to every eta in (1).

The coefficientwise bounds (26) and (30) are the only finite
polynomial arithmetic used in this section. Their input consists of
two explicit bivariate polynomials; their outputs are the displayed
two-factor majorant and two short univariate polynomials. There is no
subdivision, executable sign cover, or 192-entry basis certificate.

## 7. Rational constants and strict physical conclusion

The square-root comparison ell<sqrt(3) follows from
989^2<3*571^2. Machin's tangent identity and the alternating
arctangent integral give
\[
\pi>
16\sum_{j=0}^5\frac{(-1)^j}{(2j+1)5^{2j+1}}
-4\left(\frac1{239}-\frac1{3\cdot239^3}
                         +\frac1{5\cdot239^5}\right)
>\frac{314159265}{10^8}.
\]
For the octagon, use its exact formula
\[
A_{\rm oct}=2\sqrt3\,
 \frac{8-4\sqrt2-\log2}{2\sqrt2-1}.
\]
The positive fraction decreases with sqrt(2) and log(2). Substituting
\[
\sqrt3<173205081/10^8,\quad
\sqrt2>1414213562/10^9,\quad
\log2>2\sum_{j=0}^7\frac1{(2j+1)3^{2j+1}}
\]
and clearing positive denominators gives A_oct<3126055/10^6.
These are finite rational comparisons; none is a decimal assumption.

We have proved mathcal B(uq)>b*>0. Therefore (14), monotonicity in u,
and sqrt(3)>ell give
\[
C_{\rm period}\ge\mathcal F_c
>c\pi_0/3+\ell\mathcal B(u_q)-1/800000
>A_0>A_{\rm oct}.
\]
This is the strict contradiction (2), for the original physical period
and its original common covector. The actual shape restrictions and
original Casimir floor in (1) remain explicit caller obligations.
