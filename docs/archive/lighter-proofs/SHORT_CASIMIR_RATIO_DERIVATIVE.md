# Extended Casimir: the ratio derivative after the shape comparison

This replaces the third derivative-sign dependency of the
[extended floor caller](../../archive/notes/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md).
It proves
\[
 -\Psi_x>11/14000\qquad
 (2\le x\le13/6,\ 0\le d\le1/19,\ e=13/5).               \tag{1}
\]
The wider old sign for arbitrary e is not claimed. The actual caller first
lowers e to 13/5 using the second sign in
[the first-derivative proof](SHORT_CASIMIR_FIRST_DERIVATIVES.md).
It then needs precisely (1) to increase x to 13/6. This explicitly
preserves the original caller while removing an unused e interval.
All logarithmic derivatives remain exact.

Use the source definitions in that note: Ψ=Γ−r1/7, with r1=R1+log y.
On this comparison a=1+(13/5)d and b=x(1+d). For an x derivative d
is held fixed, so a is also fixed. Write S=x+1, X=x(x+2), and
\[
 u(x,d)=3/4+\frac{2(x-1)^3}{S(35x+13)((1+d)x-1)}
       +\frac{d^3x}{48((1+d)x-1)}.
\]

## 1. Keep a lower norm curve and its x derivative

We first establish
\[
 9/1000<u_x<1/100,\qquad
 u>v(x,d):=379/500+(9/1000)(x-2)-(9/500)d.                 \tag{2}
\]
These two estimates hold on the full x,d rectangle.
Put B0=(1+d)x−1 and H0=2(x−1)^3/[S(35x+13)]. Directly differentiating
u=3/4+H0/B0+d³x/(48B0) gives
\[
 u_{xd}=
 \frac{-xH_0'B_0+H_0((1+d)x+1)}{B_0^3}
 -\frac{d^2(3(x-1)+xd)}{48B_0^3}<0.                     \tag{3}
\]
For its sign, use B0≥1 and
\[
 \frac{H_0'}{H_0}=\frac3{x-1}-\frac1{x+1}-\frac{35}{35x+13}
 \ge18/7-1/3-35/83>3/2.
\]
Thus xH0'/H0>3≥1+2/B0, which proves the negative sign of the first
term of (3); the last term is nonpositive. This uses no multivariate
expanded numerator.

The lower bound in (2) follows by increasing d to 1/19 and applying
Section 1 of [the boundary-derivative proof](SHORT_CASIMIR_BOUNDARY_DERIVATIVES.md).
For the upper bound decrease d to zero. There
\[
 U_0(x)=u(x,0)=3/4+2(x-1)^2/[S(35x+13)],
\]
\[
 1/100-U_0'=I(h)/[100S^2(35x+13)^2],\qquad h=x-2,
\]
\[
\begin{aligned}
I={}&1225 h^{4} + 13160 h^{3} + 29174 h^{2} + 8024 h\\
&{} + 1
\end{aligned}
\]

All coefficients are positive. Finally U0(2)>379/500, and U0'>9/1000.
The first-derivative note proves u_d>−9/500. Integrating these two
bounds in x and then in d yields the affine lower norm v in (2).
In particular 757/1000<u<19/25, since u decreases with d and its
value at x=2,d=1/19 exceeds 757/1000.

The Γ monotonicities established in the boundary-derivative note now
give a simple uniform total derivative bound, without a split:
\[
 \frac d{dx}\Gamma(x,u(x,d))
 <\Gamma_x(2,19/25)+(1/100)\Gamma_u(13/6,757/1000)
 <-171/20000+41/20000=-13/2000.                            \tag{4}
\]
Γu>0 justifies using the upper bound on u_x here.

## 2. The cost derivative increases with the incoming norm

Write K=X+a², B=a+b, D=a²+2ab+1+2x−2bx. On this curve the source
bounds give 0<D/K<1/3. Also D<aB: indeed
\[
 D-aB=b(a-2x)+1+2x\le x(a-2x)+1+2x\le-13/19<0,
\]
using a≤22/19, x≥2, and b≥x. The norm coefficient is therefore positive:
\[
 (r_1)_u=B/a+S^3/K-2D/K+D(D-S^3)/(aBK)>B/a-2D/K>0.        \tag{5}
\]
To see the first comparison, group the S³ terms as
(S³/K)(1−D/(aB)) and retain the positive D²/(aBK) term.

Let \(r_{1,x}^{\flat}\) hold u fixed while following b=x(1+d).
We also need \(\partial_u r_{1,x}^{\flat}>0\). Remove e before any
expansion by putting
\[
 A=13d+5=5a,\quad C=5dx+13d+5x+5=5B,
\]
\[
 H=169d^2+130d+25x^2+50x+25=25K.
\]
The complete norm-coefficient source is
\[
 T_u=B^2K+aB(S^3-2D)+D(D-S^3),
\]
\[
 Q=78125\{(T_u)_xBK-T_u(B_xK+BK_x)\},\qquad
 \partial_u r_{1,x}^{\flat}=Q/(AC^2H^2).                 \tag{6}
\]
The degree-nine source Q is not expanded. Differentiate it once in x
first; the resulting degree-eight identity is Qx=J(d,h):
\[
\begin{aligned}
J={}&7140250 d^{7} h + 32845150 d^{7} - 32955000 d^{6} h^{2} - 185097250 d^{6} h\\
&{} - 165543950 d^{6} + 13097500 d^{5} h^{3} - 20660250 d^{5} h^{2} - 460863000 d^{5} h\\
&{} - 562609450 d^{5} + 21125000 d^{4} h^{4} + 306507500 d^{4} h^{3} + 1320647250 d^{4} h^{2}\\
&{} + 1973614500 d^{4} h + 1000723750 d^{4} + 1125000 d^{3} h^{5} + 78375000 d^{3} h^{4}\\
&{} + 851722500 d^{3} h^{3} + 3396397500 d^{3} h^{2} + 5513992500 d^{3} h + 3177307500 d^{3}\\
&{} + 2187500 d^{2} h^{6} + 46125000 d^{2} h^{5} + 453187500 d^{2} h^{4} + 2373937500 d^{2} h^{3}\\
&{} + 6553162500 d^{2} h^{2} + 8809037500 d^{2} h + 4522462500 d^{2} + 4375000 d h^{6}\\
&{} + 83437500 d h^{5} + 674687500 d h^{4} + 2863000000 d h^{3} + 6580875000 d h^{2}\\
&{} + 7674562500 d h + 3529062500 d + 2187500 h^{6} + 38437500 h^{5}\\
&{} + 281250000 h^{4} + 1076875000 h^{3} + 2250937500 h^{2} + 2419687500 h\\
&{} + 1040625000
\end{aligned}
\]

Discard positive d terms and replace d by 1/19 in negative terms.
Rounding the resulting h coefficients downward to multiples of 1000
leaves the following strictly positive lower polynomial:
\[
\begin{aligned}
J_{\mathrm{low}}={}&2187000 h^{6} + 38437000 h^{5} + 281250000 h^{4} + 1076875000 h^{3}\\
&{} + 2250937000 h^{2} + 2419687000 h + 1040624000
\end{aligned}
\]

The remaining boundary source, now of degree seven in one variable, is
\[
\begin{aligned}
Q(2,d)={}&51409800 d^{7} - 48773400 d^{6} - 288842125 d^{5} + 529878375 d^{4}\\
&{} + 1501150625 d^{3} + 1867559375 d^{2} + 1316312500 d + 367031250
\end{aligned}
\]

Discarding its positive nonconstant terms and inserting d=1/19 in the
two adverse powers leaves more than 366000000. Thus Q>0 by integration
in x, and (6) has the required sign. Since r1 is affine in u, (2), (5)
and (6) now imply
\[
 \frac d{dx}r_1(x,a,b,u(x,d))
 \ge f(x,d):=\frac d{dx}r_1(x,a,b,v(x,d)).                 \tag{7}
\]
This is a comparison along the norm curves, not a fixed-norm substitution
inside a total derivative.

## 3. Increase the normalized cost numerator in d before taking endpoints

Use a=A/5, B=C/5, K=H/25 as above and the affine norm v from (2).
Set E=S³(v−1)+3S−1, M=S²(S²−S+1), W=M+vD²−DE, and
\[
 T=(v-1)B^2K+a^2K+aBK-a^3B-aB(2vD-E)+W-3K^2/4.
\]
These are the exact rational source pieces: R1=T/(aBK), y=2aB/K.
Directly differentiating, with d fixed, gives the unexpanded numerator
\[
 N=(10/3)AC^2H^2(f+1/25)
\]
\[
 =(781250/3)\{T_xBK-T(B_xK+BK_x)\}
   +(10/3)ACH^2C_x-(10/3)AC^2HH_x+(2/15)AC^2H^2.                  \tag{8}
\]
Its source degree is ten. Differentiate the printed products twice in d
before expanding. The complete degree-eight result is Ndd=P(d,h):
\[
\begin{aligned}
P={}&- 11995620 d^{6} h^{2} - 110359704 d^{6} h - 172736928 d^{6} + 36678915 d^{5} h^{3}\\
&{} + \frac{488636967 d^{5} h^{2}}{2} + 1247667512 d^{5} h + \frac{6590962651 d^{5}}{5} - 20723625 d^{4} h^{4}\\
&{} - 941376475 d^{4} h^{3} - \frac{16599016915 d^{4} h^{2}}{2} - 20487166960 d^{4} h - 16335523100 d^{4}\\
&{} - 2028000 d^{3} h^{5} + 281242000 d^{3} h^{4} + \frac{5588014250 d^{3} h^{3}}{3} - \frac{3324019790 d^{3} h^{2}}{3}\\
&{} - 13790558990 d^{3} h - 14241417060 d^{3} + 1473750 d^{2} h^{6} - 20020700 d^{2} h^{5}\\
&{} + 118598600 d^{2} h^{4} + 2389233430 d^{2} h^{3} + 6414761770 d^{2} h^{2} + 6307847210 d^{2} h\\
&{} + 2694185780 d^{2} - 45000 d h^{7} + \frac{12419625 d h^{6}}{2} + 69698425 d h^{5}\\
&{} + 488800325 d h^{4} + 2339505200 d h^{3} + \frac{11181177325 d h^{2}}{2} + 6979205375 d h\\
&{} + 4131923600 d + 28125 h^{8} + \frac{433750 h^{7}}{3} + \frac{4070875 h^{6}}{6}\\
&{} + \frac{49876625 h^{5}}{3} + \frac{477120125 h^{4}}{3} + \frac{1984816000 h^{3}}{3} + \frac{7777127875 h^{2}}{6}\\
&{} + \frac{3847984625 h}{3} + 611261375
\end{aligned}
\]

Discard positive d terms and insert d=1/19 in negative terms.
Rounding each resulting h coefficient downward to a multiple of 1000
produces the following positive lower polynomial:
\[
\begin{aligned}
P_{\mathrm{low}}={}&28000 h^{8} + 142000 h^{7} + 678000 h^{6} + 16569000 h^{5}\\
&{} + 159039000 h^{4} + 661598000 h^{3} + 1295962000 h^{2} + 1280493000 h\\
&{} + 609059000
\end{aligned}
\]

The first boundary jet has degree eight in one variable:
\[
\begin{aligned}
N_d(2+h,0)={}&28125 h^{8} + \frac{383125 h^{7}}{3} - 1931875 h^{6} - 16751875 h^{5}\\
&{} - \frac{86249375 h^{4}}{2} - 18388125 h^{3} + 78990000 h^{2} + \frac{344264375 h}{3}\\
&{} + \frac{311725625}{6}
\end{aligned}
\]

After discarding its positive nonconstant terms and substituting h=1/6
in the adverse terms, this exceeds 51000000. Since Ndd>0, Nd>0
throughout the rectangle. Consequently N(x,d)≥N(x,0).
Only now expand the reduced one-variable source:
\[
\begin{aligned}
N(2+h,0)={}&\frac{28125 h^{8}}{2} + \frac{143750 h^{7}}{3} - \frac{4009375 h^{6}}{3} - \frac{36331250 h^{5}}{3}\\
&{} - \frac{126812500 h^{4}}{3} - \frac{214831250 h^{3}}{3} - 56421875 h^{2} - 12618750 h\\
&{} + \frac{8746875}{2}
\end{aligned}
\]

Its second derivative is negative on 0≤h≤1/6: discard the nonconstant
negative terms, bound its two positive terms at h=1/6, and compare
their sum with the negative constant −112843750. Thus this source is
concave, so its minimum is at an endpoint. Direct substitution gives
\[
 N(2,0)>4000000,\qquad N(13/6,0)>300000.
\]
This proves N>0 and hence f>−1/25. Equations (4) and (7) yield
\[
 \Psi_x<-13/2000+(1/25)/7=-11/14000,
\]
which is (1).

## 4. Caller and size audit

The second original derivative sign first lowers e to 13/5 while x,d
remain fixed. This note then increases x to 13/6. The remaining delta
concavity step and two endpoint values are exactly those in Section 4
of the original floor caller. No conclusion for unused e values is
needed, and no physical period or covector is changed by these scalar
comparisons. The d=0 edge is included without division by d.

Every polynomial needed for the signs is printed. The degree-nine norm
source is differentiated once, and the degree-ten cost source twice,
before any expansion. Their resulting bivariate identities have degree
at most eight and fewer than fifty monomials. Each individual expanded
product contribution to these derivatives, before the shift x=2+h,
also has degree at most eight, at most 150 monomials, and coefficients
within twelve digits. All printed shifted and boundary polynomials
satisfy the same coefficient limit. The only bounds on parameter powers
use d≤1/19 and h≤1/6; there is no subdivision or coefficient-table
certificate. Exact source and directed-rounding checks support the
transcription. No numerical sample, Lean, Lake, typechecking or CI run
is a proof premise.
