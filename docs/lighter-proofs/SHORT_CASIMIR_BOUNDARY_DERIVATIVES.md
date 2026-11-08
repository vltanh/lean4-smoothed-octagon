# Extended Casimir: the two boundary derivatives

This proves the fourth and fifth signs in
[the original six-sign list](../../archive/notes/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md):
\[
 -\Phi_x\big|_{d=1/19}>1/1750,
 \qquad -\Phi_e\big|_{x=13/6,d=1/19}>0,
 \quad 2\le x\le13/6,\quad13/5\le e\le3.                 \tag{1}
\]
The domain and the two comparisons used by Section 4 of
[the actual floor caller](../../archive/notes/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md)
are unchanged. All derivatives include the exact logarithm.
Use the definitions and independent-variable bounds of
[the first-derivative note](SHORT_CASIMIR_FIRST_DERIVATIVES.md).
In particular \(\Phi=\Gamma-r_0/7\), where
\[
 r_0=2w-1/2+(u-1)(a+b)/a+a/(a+b)-a^2/K-E_L+\log(2a(a+b)/K).
\]
At the boundary d=1/19, a=1+e/19 is constant during the x comparison,
b=20x/19, and 108/95≤a≤22/19.

## 1. The incoming curve and a uniform Casimir slope

Write S=x+1, X=x(x+2), K=X+a², h=x−2. The exact incoming curve is
\[
 U(x)=\frac{9755699x^3+1858476x^2-6497987x-3868476}
 {17328(x+1)(20x-19)(35x+13)}.
\]
It obeys
\[
 9/1000<U'<1/100,\qquad
 U(x)>v(x):=757/1000+(9/1000)(x-2).                         \tag{2}
\]
Here are both complete derivative numerators:
\[
 U'-9/1000=I_-(h)/[114000S^2(20x-19)^2(35x+13)^2],
\]
\[
 1/100-U'=I_+(h)/[22800S^2(20x-19)^2(35x+13)^2].
\]
\[
\begin{aligned}
I_-={}&- 502740000 h^{6} - 6456618000 h^{5} - 23179547975 h^{4} - 30704339320 h^{3}\\
&{} - 13549003994 h^{2} + 1159166376 h + 1218893409
\end{aligned}
\]
\[
\begin{aligned}
I_+={}&111720000 h^{6} + 1434804000 h^{5} + 5381565925 h^{4} + 8137767560 h^{3}\\
&{} + 5598968782 h^{2} + 1896980472 h + 379628973
\end{aligned}
\]

Every coefficient of I+ is positive. For I−, discard its positive h term
and put h=1/6 in its negative terms; what remains exceeds 600000000.
Also U(2)=1270649/1677928>757/1000, which proves the second assertion
of (2) by integration. The first-derivative note gives U<19/25.

We next prove
\[
 \frac{d}{dx}\Gamma(x,U(x))<-7/1000.                       \tag{3}
\]
This uses only one split, x=25/12. The required monotonicities of the
original source
\(\Gamma=(4Mu-E^2)/(16X^2)\), with
\(M=S^2(S^2-S+1)\), \(E=S^3(u-1)+3S-1\), are
\[
 \Gamma_{xu}>0,\quad \Gamma_{xx}<0,\quad \Gamma_{uu}<0
 \qquad(2\le x\le13/6,\ 757/1000\le u\le19/25).
\]
For completeness,
\[
 \Gamma_{uu}=-S^6/(8X^2),\quad
 \Gamma_{xuu}=-S^5(X-2)/(4X^3),
\]
\[
 \Gamma_{xxuu}=-\frac{S^4(x^4+4x^3+2x^2-4x+12)}{4X^4}<0.
\]
The last quartic is positive for x≥2. Thus Γxu is minimized at u=19/25,
and Γxxu is also minimized there. The following positive polynomial
numerators at that endpoint prove Γxu>0, Γxxu>0, and Γxx<0 throughout
the interval. In the last step Γxx increases in u, so its maximum is
its negative value at u=19/25.

\[
\Gamma_{xu}\big|_{u=19/25}=G_1(h)/(200 x^{3} \left(x + 2\right)^{3}).
\]
\[
\begin{aligned}
G_1={}&12 h^{7} + 252 h^{6} + 2232 h^{5} + 10825 h^{4}\\
&{} + 31080 h^{3} + 52941 h^{2} + 49706 h + 19896
\end{aligned}
\]

\[
\Gamma_{xxu}\big|_{u=19/25}=G_2(h)/(100 x^{4} \left(x + 2\right)^{4}).
\]
\[
\begin{aligned}
G_2={}&6 h^{8} + 144 h^{7} + 1488 h^{6} + 8615 h^{5}\\
&{} + 30495 h^{4} + 67318 h^{3} + 89872 h^{2} + 65604 h\\
&{} + 19760
\end{aligned}
\]

\[
-\Gamma_{xx}\big|_{u=19/25}=G_3(h)/(5000 x^{4} \left(x + 2\right)^{4}).
\]
\[
\begin{aligned}
G_3={}&36 h^{8} + 864 h^{7} + 8928 h^{6} + 54040 h^{5}\\
&{} + 212595 h^{4} + 544208 h^{3} + 854432 h^{2} + 729024 h\\
&{} + 252160
\end{aligned}
\]

All coefficients are positive. The following scalar bounds are direct
substitutions in Γ and U and have the stated rational directions:
\[
 U(25/12)<7581/10000,
\]
\[
 \Gamma_x(2,7581/10000)<-89/10000,\quad
 \Gamma_u(25/12,757/1000)<187/1000,
\]
\[
 \Gamma_x(25/12,19/25)<-19/2000,\quad
 \Gamma_u(13/6,757/1000)<41/200.
\]
Γu is positive on this rectangle, since it increases in x, decreases
in u, and Γu(2,19/25)>0. By (2) and the proved monotonicities,
the total derivative is less than
\(-89/10000+187/100000=-703/100000<-7/1000\) on the first half,
and less than \(-19/2000+41/20000=-149/20000<-7/1000\) on the second.
This proves (3).

## 2. Keep the norm motion in the cost derivative

Let \(r_{0,x}^{\flat}\) mean the x derivative with a,u fixed and b=20x/19.
The first-derivative note gives 0<D/K<1/3 on the required domain. Hence
\[
 (r_0)_u=(a+b)/a+(S^3/K)(1-2D/K)+2(D/K)(D/K-1)>0.
\]
The coefficient \(\partial_u r_{0,x}^{\flat}\) is also positive. Its
complete source identity is
\[
 \partial_u r_{0,x}^{\flat}
 =C(c,h)/[361aK^3],\qquad c=a-1.
\]
\[
\begin{aligned}
C={}&1900 c^{6} - 1083 c^{5} h^{2} - 4582 c^{5} h + 5485 c^{5}\\
&{} - 6080 c^{4} h^{3} - 82755 c^{4} h^{2} - 263110 c^{4} h - 219235 c^{4}\\
&{} + 9766 c^{3} h^{4} + 91900 c^{3} h^{3} + 140808 c^{3} h^{2} - 256460 c^{3} h\\
&{} - 466846 c^{3} + 36838 c^{2} h^{4} + 355140 c^{2} h^{3} + 984924 c^{2} h^{2}\\
&{} + 793380 c^{2} h - 83098 c^{2} + 1881 c h^{6} + 33858 c h^{5}\\
&{} + 310391 c h^{4} + 1493972 c h^{3} + 3601311 c h^{2} + 4007850 c h\\
&{} + 1562449 c + 2261 h^{6} + 40698 h^{5} + 333479 h^{4}\\
&{} + 1428332 h^{3} + 3240147 h^{2} + 3654298 h + 1596081
\end{aligned}
\]

For every c∈[1/8,1/6], replace c by 1/8 in positive terms and by 1/6
in negative terms. After rounding each resulting h coefficient downward
to a multiple of 1000, this gives the explicit positive lower polynomial
\[
\begin{aligned}
C_{\mathrm{low}}={}&2000 h^{6} + 44000 h^{5} + 372000 h^{4} + 1620000 h^{3}\\
&{} + 3705000 h^{2} + 4166000 h + 1786000
\end{aligned}
\]

The required range 13/95≤c≤3/19 lies inside this rectangle. Since r0
is affine in u, (2) and these two positive coefficients give
\[
 \frac{d}{dx}r_0(x,a,20x/19,U(x))
 \ge f(x,a):=\frac{d}{dx}r_0(x,a,20x/19,v(x)).              \tag{4}
\]
In particular the norm is not frozen during either comparison.

## 3. A separately concave numerator proves f>−9/200

This step uses the original boundary range
\(2\le x\le13/6\), \(108/95\le a\le22/19\).
Define the unexpanded polynomial source
\[
 N=45125aC_*^2K^3(f+9/200),\qquad C_*=19a+20x,
 \quad B=C_*/19,\quad v'=9/1000,\quad B'=20/19,
\]
\[
 D=a^2+40ax/19+1+2x-40x^2/19,\quad
 E=S^3(v-1)+3S-1,
\]
\[
 W=M+vD^2-DE,\qquad Q=2vD-E.
\]
Primes in the next identity denote x differentiation with a fixed.
Cancel only the displayed denominators after differentiating the source
r0. This gives the following eight-term product source for N:
\[
\begin{aligned}
N={}&90250aC_*^2(W'K-2WK')
 +45125C_*^2K^3\{v'B+(v-1)B'\}\\
&-45125\cdot361a^2B'K^3+45125a^3C_*^2K'K\\
&-45125aC_*^2(Q'K-QK')K+45125\cdot19aC_*B'K^3\\
&-45125aC_*^2K'K^2+(9/200)45125aC_*^2K^3.
\end{aligned}                                                        \tag{5}
\]
Each product has degree at most ten. Differentiate twice before expanding.
The two complete resulting degree-eight identities are
\(-N_{aa}=P_A(c,h)\) and \(-N_{xx}=P_X(c,h)\):
\[
\begin{aligned}
P_A={}&- 63336006 c^{7} - 190131480 c^{6} h - 3411515702 c^{6} + 24630669 c^{5} h^{3}\\
&{} - \frac{1339539957 c^{5} h^{2}}{2} - 12899389902 c^{5} h - 38269433832 c^{5} + 129635100 c^{4} h^{4}\\
&{} - 1384476705 c^{4} h^{3} + \frac{1869625365 c^{4} h^{2}}{2} - 13147630260 c^{4} h - 76129292340 c^{4}\\
&{} + 51285465 c^{3} h^{5} + 411975225 c^{3} h^{4} + 13232985800 c^{3} h^{3} + 128959957955 c^{3} h^{2}\\
&{} + 307044832385 c^{3} h + 161763249920 c^{3} - 67346640 c^{2} h^{6} + 1058631255 c^{2} h^{5}\\
&{} + 10418692425 c^{2} h^{4} + 75222577320 c^{2} h^{3} + 380210764425 c^{2} h^{2} + 804919769895 c^{2} h\\
&{} + 538404182004 c^{2} - \frac{63683307 c h^{7}}{2} + \frac{285274251 c h^{6}}{2} + 2457318186 c h^{5}\\
&{} - 1814606481 c h^{4} - \frac{60062007819 c h^{3}}{2} + \frac{96658382163 c h^{2}}{2} + 317958337773 c h\\
&{} + 288505318770 c - 5065020 h^{8} - \frac{119973087 h^{7}}{2} + \frac{808687201 h^{6}}{2}\\
&{} + 3884414146 h^{5} - 833702501 h^{4} - \frac{121026207631 h^{3}}{2} - \frac{304669396099 h^{2}}{2}\\
&{} - 126156559259 h - 22982058630
\end{aligned}
\]

The same endpoint replacements c=1/8 in positive terms and c=1/6 in
negative terms, now with h coefficients rounded downward to multiples
of one million, give
\[
\begin{aligned}
L_A={}&- 6000000 h^{8} - 66000000 h^{7} + 420000000 h^{6} + 4208000000 h^{5}\\
&{} - 973000000 h^{4} - 64319000000 h^{3} - 140101000000 h^{2} - 73248000000 h\\
&{} + 21745000000
\end{aligned}
\]

Thus P_A≥L_A. Discard positive nonconstant terms and insert h=1/6
in the remaining negative terms. The result is greater than 5000000000.
\[
\begin{aligned}
P_X={}&3518667 c^{7} h - \frac{63787617 c^{7}}{2} + 51854040 c^{6} h^{2} - 276895341 c^{6} h\\
&{} + \frac{124641691 c^{6}}{2} + 51285465 c^{5} h^{3} + 247185135 c^{5} h^{2} + 3969895740 c^{5} h\\
&{} + \frac{25791991591 c^{5}}{2} - 168366600 c^{4} h^{4} + 1764385425 c^{4} h^{3} + 10418692425 c^{4} h^{2}\\
&{} + 37611288660 c^{4} h + \frac{126736921475 c^{4}}{2} - \frac{445783149 c^{3} h^{5}}{2} + \frac{1426371255 c^{3} h^{4}}{2}\\
&{} + 8191060620 c^{3} h^{3} - 3629212962 c^{3} h^{2} - \frac{60062007819 c^{3} h}{2} + \frac{32219460721 c^{3}}{2}\\
&{} - 141820560 c^{2} h^{6} - \frac{2519434827 c^{2} h^{5}}{2} + \frac{12130308015 c^{2} h^{4}}{2} + 38844141460 c^{2} h^{3}\\
&{} - 5002215006 c^{2} h^{2} - \frac{363078622893 c^{2} h}{2} - \frac{304669396099 c^{2}}{2} - 121888800 c h^{7}\\
&{} - 1328584320 c h^{6} + \frac{3371204193 c h^{5}}{2} + \frac{129290985465 c h^{4}}{2} + 262820081435 c h^{3}\\
&{} + 384548364339 c h^{2} + \frac{269070634521 c h}{2} - \frac{150855982151 c}{2} - 146512800 h^{7}\\
&{} - 1368707760 h^{6} + \frac{7369631871 h^{5}}{2} + \frac{149621701905 h^{4}}{2} + 300221900635 h^{3}\\
&{} + 530041237053 h^{2} + \frac{846227115771 h}{2} + \frac{235576507477}{2}
\end{aligned}
\]

The same endpoint replacements c=1/8 in positive terms and c=1/6 in
negative terms, now with h coefficients rounded downward to multiples
of one million, give
\[
\begin{aligned}
L_X={}&- 167000000 h^{7} - 1595000000 h^{6} + 3859000000 h^{5} + 82987000000 h^{4}\\
&{} + 333697000000 h^{3} + 577956000000 h^{2} + 434757000000 h + 101032000000
\end{aligned}
\]

Thus P_X≥L_X. Discard positive nonconstant terms and insert h=1/6
in the remaining negative terms. The result is greater than 100000000000.

Consequently N is concave in a and in x separately. Apply the elementary
endpoint bound in one variable and then the other: its minimum is bounded
below by the minimum of its four corners. Direct rational substitution
in the small products (5) gives

| x | a | Strict lower bound for N |
|---|---|---|
| 2 | 108/95 | 3700000000 |
| 2 | 22/19 | 4400000000 |
| 13/6 | 108/95 | 230000000 |
| 13/6 | 22/19 | 1200000000 |

The denominators in the definition of N are positive. Hence f>−9/200.
Combining (3) and (4) proves
\[
 \Phi_x<-7/1000+(9/200)/7=-1/1750,
\]
which is the fourth original derivative sign on its full domain.

## 4. The final shape derivative follows from the first note's curvature

At x=13/6,d=1/19, only a=1+e/19 depends on e. The first-derivative note
proves that Φa increases with u. It is therefore enough to use u=19/25.
Retain its normalized source, named N0 here to distinguish it from (5):
\[
 N_0=3325a^2(19a+20x)^2K^3\Phi_a(x,a,20x/19,19/25).
\]
That note gives N0(2,a)=V(a), (N0)x(2,a)=W(a), and the explicit bound
\[
 -(N_0)_{xx}\ge2200000000+10600000000(x-2).
\]
Two integrations to x=13/6 give
\[
 N_0(13/6,a)\le T(a)-2200000000/72-10600000000/1296,
 \qquad T=V+W/6.                                         \tag{6}
\]
No high-degree source has been expanded. Its remaining shape comparison
is the following full univariate derivative:
\[
\begin{aligned}
T\prime(1+c)={}&\frac{26280800 c^{7}}{3} + 126272993 c^{6} + 86255878 c^{5} - 2639689505 c^{4}\\
&{} - \frac{25060398500 c^{3}}{3} - 5949572785 c^{2} + \frac{7043503634 c}{3} + \frac{4993595059}{3}
\end{aligned}
\]

On 0≤c≤3/19, discard positive nonconstant terms and bound every adverse
power at 3/19. The result exceeds 1400000000, so T increases. The direct
scalar value obeys T(22/19)<34000000. The right side of (6) is therefore
less than −4000000 throughout the required shape interval. Its positive
normalizing factor proves Φa<0. Since Φe=Φa/19, the fifth original sign
follows, with the same actual endpoint e=3.

## 5. Caller and expansion audit

The fourth sign increases x at d=1/19, for every e in its original interval.
The fifth then increases e at x=13/6,d=1/19. Thus these two signs supply
exactly the two boundary comparisons in the original Phi chain; no
physical hypotheses or competitive cap are moved to a different shape.

Every polynomial used for a sign is fully printed. The largest bivariate
polynomials have 42 and 43 monomials and degree eight; the norm-coefficient
polynomial has degree seven. The first stage fixes d before expansion;
the numerator (5) is differentiated twice before expansion. Each separate
expanded derivative contribution in (5), in a,x, also has degree at most
eight and coefficients with at most twelve digits. Collecting them before
the simple shift c=a−1,h=x−2 keeps the displayed shift identities within
the same budget. The largest printed coefficient is 804919769895.
Only the single rational split x=25/12 is used. Scalar substitutions and
rational rounding directions were checked exactly from the displayed
sources. This note uses no coefficient-table certificate, no numerical
sampling premise, and no Lean, Lake, typechecking or CI run.
