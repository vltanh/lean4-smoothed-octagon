# Reciprocal-shape reduction of the S1 outer large-shape branch

This replaces the dimension-three sign step in row A of
[the original outer-face note](../../archive/notes/MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN.md).
It uses its original rational tests \(F_0,F_1\), with the same domain
\[
 3/2\le x\le2,\qquad 6/5\le a\le x,\qquad
 24/43\le C\le10/13,\qquad \beta=x+C(a-1),
\tag{A1}
\]
and incoming interval \(u_f\le u\le u_v\). The conclusion is
\(F_0>0,F_1>0\). In particular it includes both original norm endpoints.
The upper and lower norm comparisons below slightly enlarge the incoming
interval; no condition on the actual incoming norm is removed.

The terminal signs are supplied by
[the shared upper-shape face](SHORT_OUTER_UPPER_SHAPE_TERMINAL.md),
[the A-branch \(F_0\) face](SHORT_OUTER_A_F0_TERMINAL.md), and
[the A-branch \(F_1\) face](SHORT_OUTER_LARGE_SHAPE_F1_TERMINAL.md).
The proof in this note is independent of their scalar endpoint calculations.
It reduces a norm variable, then beta for \(F_1\), then reciprocal shape.
Every polynomial sign check is univariate. This closes row A only;
the other rows and the other S1 notes are separate claims.

## 1. One logarithm majorant and the unchanged source functions

Use the definitions of \(\Gamma_*,w,E_L,F_0,F_1\) in
[the beta reduction](SHORT_OUTER_BETA.md), equations (1)--(2), with
\(c=7/96\), \(g=9193/50000\), and
\[
 \ell(Y)=2\frac{Y-1}{Y+1}+\frac23\left(\frac{Y-1}{Y+1}\right)^3,
 \qquad \log Y\le\ell(Y)\quad(0<Y\le1).
\tag{A2}
\]
This is the sole logarithm bound. Its two derivative comparisons are
\[
 \ell'(Y)-1/Y=-\frac{(Y-1)^4}{Y(Y+1)^4},
 \qquad
 \ell''(Y)+1/Y^2=
 \frac{(1-Y)^3(1+8Y-Y^2)}{Y^2(1+Y)^5}\ge0.
\tag{A3}
\]
The complete numerators are
\(-Y^4+4Y^3-6Y^2+4Y-1\), and
\(1+5Y-22Y^2+26Y^3-11Y^4+Y^5\).
They have respectively five and six monomials, degrees four and five.
These are derivatives of (A2), not additional analytic bounds.

Write \(S=x+1\). Since both residuals are affine in \(u\) apart from
\(\Gamma_*\), they satisfy
\[
 (F_i)_{uu}=-\frac{(6a^2+1)^2S^2}{288a^4}<0
 \qquad(i=0,1).
\tag{A4}
\]
The numerator remains a product of two squares. Its expanded positive
polynomial is
\[
 36a^4x^2+72a^4x+36a^4+12a^2x^2+24a^2x+12a^2+x^2+2x+1,
\]
nine monomials, degree six in two variables.

## 2. An affine incoming interval

The original incoming endpoints and the beta-concavity ceiling are
\[
 u_f=\frac34+\frac{(x-1)^2}{28S^2},\qquad
 u_v=\frac34+\frac{2(x-1)^2}{S(35x+13)},\qquad
 u_0=\frac34+\frac{(x-1)^2}{12S^2}.
\]
Use instead
\[
 u_-=(8x+1303)/1750,\qquad u_+=(6x+443)/600.
\tag{A5}
\]
The three exact comparisons are
\[
 u_f-u_- =\frac{(4-x)(2x-3)^2}{875S^2}\ge0,
\tag{A6}
\]
\[
 u_+-u_v=\frac{210x^3-1157x^2+2142x-1291}{600S(35x+13)}>0,
\tag{A7}
\]
\[
 u_0-u_+=\frac{(2x-3)(-3x^2+18x-19)}{600S^2}\ge0.
\tag{A8}
\]
Each cleared identity has at most four monomials and degree three.
For (A7), call its numerator \(P_3\). Then
\[
 P_3(3/2)=55/2,\qquad
 P_3'=630(x-11/6)^2-4(x-11/6)+103/6\ge33/2,
\]
since \(x-11/6\le1/6\). The derivative is the three-term
quadratic \(630x^2-2314x+2142\). In (A8), the quadratic increases on
\([3/2,2]\), and equals \(5/4\) at the left endpoint.
Also
\[
 \frac34<u_-\le u_+\le91/120<19/25.
\tag{A9}
\]
The affine difference \(u_+-u_-\) is positive at both interval endpoints.
Thus (A4) reduces \(F_1\) to the two affine norms in (A5).
For \(F_0\), the wider constant interval \([3/4,19/25]\) will suffice.

## 3. The reciprocal-shape circuit

Put
\[
 r=1/a,\quad d=1+C,\quad e=x-C,\quad Z=(a+\beta)/a=d+er,
\]
\[
 A_0=S-1+1/S,\quad E_0=S(u-1)+1/S,\quad J_2=Su+A_0,
\]
\[
 d_0=1+2C,\quad d_1=2[(1-C)x-C],\quad
 d_2=1+2x-2x^2+2Cx.
\tag{A10}
\]
For \(D_r=d_0+d_1r+d_2r^2\), the complete source quartics are
\[
\begin{aligned}
 49w={}&36+(12-6S)r^2+(S^2-S+1)r^4
             +uD_r^2-D_r(6E_0+J_2r^2),\\
 7E_L={}&2uD_r-6E_0-J_2r^2,\\
 576\Gamma_*={}&4u[36+(12-6S)r^2+(S^2-S+1)r^4]
                     -(6E_0+J_2r^2)^2.
\end{aligned}
\tag{A11}
\]
Keep these as polynomials in \(r\) with opaque coefficient expressions.
Their coefficients are compared separately; a polynomial in \(x,r,u\)
is never expanded. The three coefficients of \(49w\) needed for curvature are
\[
\begin{aligned}
 W_2={}&12-6S+u(d_1^2+2d_0d_2)-6d_2E_0-d_0J_2,\\
 W_3={}&d_1(2ud_2-J_2),\\
 W_4={}&(S-d_2)(A_0-ud_2).
\end{aligned}
\tag{A12}
\]
The two lower coefficients, printed to make the circuit complete, are
\(W_0=36+ud_0^2-6d_0E_0\) and
\(W_1=2ud_0d_1-6d_1E_0\).

Define
\[
 \gamma_2=\frac{u(2-S)}{24}-\frac{E_0J_2}{48},\qquad
 \gamma_4=-\frac{(Su-A_0)^2}{576},
\]
\[
\begin{aligned}
 p_2&=\gamma_2-W_2/336+(2ud_2-J_2)/96,\\
 p_3&=-W_3/336,\qquad p_4=\gamma_4-W_4/336,\\
 b_2&=\gamma_2+(2ud_2-J_2)/96-W_3/(96e)+dW_4/(96e^2),\\
 b_3&=-W_4/(96e),\qquad b_4=\gamma_4.
\end{aligned}
\tag{A13}
\]
Then the nonlinear polynomial parts of the two residuals are
\[
\begin{aligned}
 F_0+c\ell(2Z/7)&=p_4r^4+p_3r^3+p_2r^2+\text{an affine function of }r-c/Z,\\
 F_1+c\ell(2Z/7)&=b_4r^4+b_3r^3+b_2r^2+\text{an affine function of }r+Q/Z.
\end{aligned}
\tag{A14}
\]
No sign depends on the omitted affine coefficients; their second derivatives
are zero. The residue \(Q<0\), for either endpoint of the C interval and
all \(3/4\le u\le19/25\), is proved separately in
[the complete reciprocal-residue lemma](SHORT_OUTER_RECIPROCAL_RESIDUE.md).
Division by \(d+er\) gives the coefficients \(W_4/e\) and
\(W_3/e-dW_4/e^2\); this accounts for every term in (A13).

## 4. Shape curvature reduces to two scalar functions

On (A1) and \(3/4\le u\le19/25\), put
\(H=A_0-uS\), \(L=S-d_2=x(2e-1)\). Then
\[
 H\ge\frac{(2x-3)(3x-2)}{25S}\ge0,\qquad L>0,
\]
\[
 W_4=L(H+uL)>0,\qquad W_3=-d_1(H+2uL).
\]
The factor identities
\[
 4L/x-2d_1=4(1+C)(x-1)>0,
\]
\[
 4L/x-d_1=2[(3+C)x-3C-2]\ge5-3C>0
\tag{A15}
\]
give
\[
 4W_4/x+W_3=H(4L/x-d_1)+uL(4L/x-2d_1)>0.
\]
The expanded polynomials in (A15) have at most four monomials and degree two.
In particular \(4p_4/x+p_3<0\). Since \(p_4<0\), the quadratic
\(12p_4r^2+6p_3r+2p_2\) decreases for \(r\ge1/x\). Define
\[
 M_0=12p_4/x^2+6p_3/x+2p_2,\qquad
 M_1=6b_3/x+2b_2.
\tag{A16}
\]
The polynomial curvature of \(F_0\) is at most \(M_0\). Since
\(b_4\le0,b_3<0\), that of \(F_1\) is at most \(M_1\).

Moreover \(2<Z<3\) and \(e/Z\le2/3\). For the latter, \(e\le d\)
and \(r\ge1/2\) imply \(Z\ge3e/2\). Thus \(0<2Z/7<1\), and (A3) yields
\[
 [-c/Z-c\ell(2Z/7)]_{rr}
 \le c(e/Z)^2(1-2/Z)\le7/648,
\tag{A17}
\]
\[
 [-c\ell(2Z/7)]_{rr}\le c(e/Z)^2\le7/216.
\tag{A18}
\]
The negative residue in (A14) contributes \(2Qe^2/Z^3<0\).

## 5. Eight small univariate signs

Differentiating (A16) before substituting any norm gives
\[
 (M_0)_{uu}=-\frac{S^2(2x^2+1)}{24x^2}<0,
 \qquad (M_1)_{uu}=-S^2/12<0.
\tag{A19}
\]
The two expanded numerators are respectively
\(2x^4+4x^3+3x^2+2x+1\), five monomials of degree four, and
\(x^2+2x+1\), three monomials of degree two.
It suffices to control the first norm derivatives at \(u=3/4\).
For \(C=24/43\), the exact normalizations are
\[
\begin{aligned}
 -[(M_0)_u+1/5]_{u=3/4}&=A_-/[6212640x^2],\\
 -(M_1)_u|_{u=3/4}&=B_-/[2064(43x-24)^2],\\
 -[M_0+1/75]_{u=3/4}&=D_-/[248505600x^2S^2],\\
 -[M_1+1/30]_{u=3/4}&=E_-/[82560S^2(43x-24)^2].
\end{aligned}
\tag{A20}
\]
For \(C=10/13\), they are
\[
\begin{aligned}
 -[(M_0)_u+1/5]_{u=3/4}&=A_+/[567840x^2],\\
 -(M_1)_u|_{u=3/4}&=B_+/[624(13x-10)^2],\\
 -[M_0+1/75]_{u=3/4}&=D_+/[22713600x^2S^2],\\
 -[M_1+1/30]_{u=3/4}&=E_+/[24960S^2(13x-10)^2].
\end{aligned}
\tag{A21}
\]
Here are all eight numerator polynomials, with \(z=2x-3\in[0,1]\)
used for their complete shifts. The signs follow immediately from the
printed shifts: only \(D_-,D_+\) have negative terms, and their negative
coefficients sum in absolute value to less than their positive constants.

\[
 A_-(x)=443760 x^{5} + 869530 x^{4} - 1532230 x^{3} - 935223 x^{2} + 475150 x - 64715.
\]
This has 6 monomials and degree 5. Its shift is
\[
 8A_-((3+z)/2)=110940 z^{5} + 2098865 z^{4} + 13669550 z^{3} + 37770594 z^{2} + 41193034 z + 9154241.
\]

\[
 B_-(x)=734053 x^{4} - 1253923 x^{3} + 1050230 x^{2} - 169330 x - 232200.
\]
This has 5 monomials and degree 4. Its shift is
\[
 16B_-((3+z)/2)=734053 z^{4} + 6300790 z^{3} + 21269168 z^{2} + 35416762 z + 21775611.
\]

\[
 D_-(x)=- 4437600 x^{7} + 10939150 x^{6} + 28504700 x^{5} - 32698433 x^{4} - 34482216 x^{3} + 21800692 x^{2} - 4751500 x + 323575.
\]
This has 8 monomials and degree 7. Its shift is
\[
 32D_-((3+z)/2)=- 1109400 z^{7} - 17827825 z^{6} - 82719550 z^{5} + 52183259 z^{4} + 1451153244 z^{3} + 4082149421 z^{2} + 4041244010 z + 818411225.
\]

\[
 E_-(x)=12083215 x^{6} - 6332610 x^{5} - 32868228 x^{4} + 15436742 x^{3} + 25560541 x^{2} - 19157756 x + 613008.
\]
This has 7 monomials and degree 6. Its shift is
\[
 64E_-((3+z)/2)=12083215 z^{6} + 204832650 z^{5} + 1309782813 z^{4} + 3930885292 z^{3} + 5682373657 z^{2} + 3463938890 z + 296851515.
\]

\[
 A_+(x)=40560 x^{5} + 80410 x^{4} - 177590 x^{3} - 71703 x^{2} + 47710 x - 5915.
\]
This has 6 monomials and degree 5. Its shift is
\[
 8A_+((3+z)/2)=10140 z^{5} + 192305 z^{4} + 1217470 z^{3} + 3167154 z^{2} + 2984314 z + 160241.
\]

\[
 B_+(x)=22139 x^{4} - 49777 x^{3} + 48434 x^{2} - 14396 x - 10270.
\]
This has 5 monomials and degree 4. Its shift is
\[
 16B_+((3+z)/2)=22139 z^{4} + 166114 z^{3} + 493256 z^{2} + 750302 z + 339101.
\]

\[
 D_+(x)=- 405600 x^{7} + 1370350 x^{6} + 2676700 x^{5} - 4057873 x^{4} - 3437096 x^{3} + 2434452 x^{2} - 477100 x + 29575.
\]
This has 8 monomials and degree 7. Its shift is
\[
 32D_+((3+z)/2)=- 101400 z^{7} - 1444225 z^{6} - 4154750 z^{5} + 28710379 z^{4} + 212291164 z^{3} + 495242301 z^{2} + 427117610 z + 52913225.
\]

\[
 E_+(x)=389545 x^{6} - 401570 x^{5} - 995088 x^{4} + 1038934 x^{3} + 768647 x^{2} - 1011420 x + 13000.
\]
This has 7 monomials and degree 6. Its shift is
\[
 64E_+((3+z)/2)=389545 z^{6} + 6208670 z^{5} + 36561123 z^{4} + 98618948 z^{3} + 128611967 z^{2} + 78641310 z + 5237365.
\]

For the two \(D\) shifts, the strict constant remainders after discarding
positive nonconstant terms and using \(z^k\le1\) are respectively
\(716754450\) and \(47212850\). Thus all eight numerators are positive.
The shifts are expanded separately; they have at most eight monomials and
degree seven. Their largest printed coefficient is \(5682373657\).

By (A19)--(A21), for either endpoint C and all \(u\ge3/4\),
\[
 (M_0)_u<-1/5,\quad (M_1)_u<0,\qquad
 M_0<-1/75,\quad M_1<-1/30.
\tag{A22}
\]

## 6. F0 curvature throughout the C interval

To use reciprocal concavity for \(F_0\), C must remain free. It cannot
be reduced by an unproved beta-concavity assertion. The exact coefficient
identities needed here are
\[
 (M_0)_{CC}=-u(x-1)^2/21,\qquad
 (M_0)_{uCC}=-(x-1)^2/21.
\tag{A23}
\]
For an expanded check the common polynomial is \(x^2-2x+1\), three
monomials of degree two; \(u\) is kept as a scalar factor.

If a twice differentiable function has second derivative at least \(-K\)
on an interval of length \(\Delta\), its value is at most its endpoint
linear interpolation plus \(K\Delta^2/8\). This follows by adding
\(Kz^2/2\), applying convexity, then completing the quadratic.
Here \(\Delta=118/559<1/4\), and (A23) permits \(K=1/21\).
Apply this first to \((M_0)_u(x,3/4,C)\): the endpoint bounds (A22) give
\[
 (M_0)_u(x,3/4,C)<-1/5+1/2688<0.
\]
Together with (A19), this makes \(M_0\) decreasing in \(u\).
Apply the same interpolation estimate to \(M_0(x,3/4,C)\). It gives
\[
 M_0(x,u,C)<-1/75+1/2688
 \quad(3/4\le u\le19/25).
\tag{A24}
\]
Consequently, by (A17),
\[
 \boxed{(F_0)_{rr}<-1/75+1/2688+7/648<-1/500}
\tag{A25}
\]
for every C in the original A interval. For \(F_1\), at either C
endpoint, (A18), (A22), and the negative residue give
\[
 \boxed{(F_1)_{rr}<-1/30+7/216=-1/1080.}
\tag{A26}
\]
Thus the shape signs reduce to \(a=6/5\) and \(a=x\).

## 7. Closing the F0 caller

For fixed \(x,a,C\), (A4) reduces \(F_0\) to the constant norm interval
endpoints \(3/4,19/25\). Concavity (A25) reduces reciprocal shape to
\(a=6/5,x\).

At \(a=6/5\), the fixed-norm beta estimate in
[the small-shape beta note](SHORT_OUTER_BETA_LOW_SHAPE.md), Sections 1--2,
applies to every \(u\ge3/4\): its upper bound \(u\le u_0\) is not used
in those sections. In detail, \((E_L)_u<0\), so \(E_L<1/2\) follows
by lowering u to \(3/4\); then \(u-E_L\ge1/4\). The displayed formula
for \((\overline R_2)_\beta\) gives the same strict bound
\((F_0)_\beta<-7/5120\). Thus raise C to \(10/13\).
The shared upper-shape terminal proves this face positive at both
constant norm endpoints.

At \(a=x\), \((F_0)_u\) decreases in both u and C. The C derivative is
\(-7(x-1)/(96x)<0\). Its value at \(u=19/25,C=10/13\) is
\[
 (F_0)_u=\frac{P_u(x)}{655200x^4},
\]
\[
 P_u=19656x^6+10062x^5-45642x^4+31329x^3+6123x^2-3133x+546.
\tag{A27}
\]
This has seven monomials and degree six. It is positive because
\[
 P_u=x^4(19656x^2+10062x-45642)
       +x(31329x^2-3133)+6123x^2+546,
\]
and the two parentheses are positive at \(x=3/2\) and increase.
The first equals \(13677\) there. Hence lower u to \(3/4\).

At this norm, w and \(E_L\) are independent of beta when \(a=x\).
The only beta-dependent part of \(F_0\) is
\(-c[-Z/4+1/Z+\ell(2Z/7)]\). By (A3), the bracket has Z derivative
at most
\[
 -1/4-1/Z^2+1/Z=-\frac{(Z-2)^2}{4Z^2}\le0.
\]
Thus \(F_0\) increases with C; lower C to \(24/43\).
The separate A \(F_0\) terminal proves this last curve positive.
Both shape endpoints close, so \(F_0>0\) on all of (A1), in fact for
the larger constant norm interval.

## 8. Closing the F1 caller and the expansion boundary

By (A5)--(A9) and (A4), it suffices to use the two affine norms.
They satisfy \(u\le u_0\). The fixed-norm beta concavity theorem in
[SHORT_OUTER_BETA](SHORT_OUTER_BETA.md) therefore reduces C to its two
endpoints: \(x\le\beta\le ax\) follows from \(0<C<1<x\) and \(a\ge1\).
At either C endpoint, (A26) reduces shape to \(a=6/5\) and \(a=x\).
The shared upper-shape terminal covers the first, throughout the larger
constant norm interval and all \(1/2\le C\le10/13\). The A \(F_1\)
terminal covers the second at each affine norm. This proves \(F_1>0\).
The original caller, which only needs positivity at \(u_f,u_v\), closes.

The source identities (A11)--(A16) must be checked coefficient by
coefficient in r and then in u; their coefficient expressions remain
opaque while differentiating in r. The C interpolation identities are
checked coefficient by coefficient in C. With C fixed, each expanded
coefficient identity is univariate in x, of degree at most eight.
The norm- and C-derivative sign numerators are printed in (A19)--(A23).
The eight scalar source identities (A20)--(A21) have respectively
6,5,8,7 monomials for each C endpoint. The eight shifts have the same
counts and degrees; even before collection the largest has 36 summands
and coefficient \(17617327470\). No substitution \(u=u_\pm(x)\) is
expanded into a joint shape/scale polynomial. The affine-norm terminal
note uses a separate Laurent decomposition for that purpose.
