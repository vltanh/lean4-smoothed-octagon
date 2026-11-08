# Central-ratio comparison in x by two small Taylor bounds

This supplies the strict x comparison for the central-ratio duration
tangent tests. It preserves the incoming-norm curve and upper beta
endpoint from [the central-ratio source](../../archive/notes/MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_SIGN.md).
The conclusion holds on the full rectangle used by the new tangent
reduction, including its extra scalar comparison points.

The [algebra appendix](SHORT_RATIO_CENTRAL_X_ALGEBRA.md) prints every
primitive source polynomial, both complete degree-eight upper
polynomials, and all coefficient and remainder bounds. The proof uses
no high-degree cleared numerator as a premise.

## 1. The two derivatives and their duration caller

Throughout this note,
\[
 13/6\le x\le12/5,\qquad1\le a\le4/3,\qquad
 c=\frac{24x+51}{128},\qquad b=x+c(a-1).
\tag{1}
\]
Put
\[
\begin{gathered}
 S=x+1,\quad K=x(x+2)+a^2,\quad B=a+b,\quad
 k=\frac{aB}{K},\quad T=1/k,\quad q=a^2/K,\\
 u=\frac34+\frac{680(x-1)^3+3S^2(b-x)}{9600S^2(b-1)},\\
 D=a^2+2ab+1+2x-2bx,\quad E=S^3(u-1)+3S-1,\\
 M=S^2(S^2-S+1),\quad
 w=\frac{M+D^2u-DE}{K^2},\quad E_L=\frac{2Du-E}{K},\quad h=w-3/4,\\
 \mathcal B=(u-1)B/a+a/B+1-q-E_L.
\end{gathered}
\tag{2}
\]
The two exact-log tests needed here are
\[
 G=\mathcal B+(4-7k/2)h+\log(2k),\qquad
 H=\mathcal B+(T+1/4)h+\log(2k).
\tag{3}
\]
Every x derivative below is total along both curves in (1)--(2),
with a fixed. We prove the uniform estimates
\[
 \boxed{G_x<-1/250,\qquad H_x<-1/2000,\qquad T_x>0.}
\tag{4}
\]
In particular both functions are bounded above by their values at \(x=13/6\).

For the smaller-shape duration tangent, take
\(t(a)=20/3-4a\) on \(1\le a\le7/6\). Its two tests are exactly
\[
 F_0=G+4/t-2/t^2-3/2+\log(t/2),
\]
\[
 F_1=H+T\phi(t)+2/t-1+\log(t/2),\qquad
 \phi(t)=\frac{t-1}{t^2}-\frac14=-\frac{(t-2)^2}{4t^2}\le0.
\tag{5}
\]
As t depends only on a,
\[
 (F_0)_x=G_x<0,\qquad (F_1)_x=H_x+T_x\phi(t)\le H_x<0.
\tag{6}
\]
On \(7/6\le a\le4/3\), the choice \(t=2\) gives the tests G,H
in (3) themselves. Thus (4) proves all four x comparisons required by
the duration tangent assembly. The original central cap need not hold
at each point of this scalar rectangle; no physical cost, outgoing
floor or upper Casimir cap is assigned to those additional points.

## 2. Incoming norm and incoming-speed bounds

Define the following two elementary majorants:
\[
 U=\frac34+\frac{x-1}{96}-\frac1{400}-\frac{a-1}{200},\qquad
 V=\frac1{96}-\frac{a-1}{400}.
\tag{7}
\]
We will use, separately,
\[
 \boxed{u<U,\qquad u_x<V.}
\tag{8}
\]
The second comparison is proved directly, rather than obtained by
differentiating the first inequality.

Put
\[
 v=\frac{17(x-1)^2}{240S^2},\qquad L_\beta=b-1=x-1+c(a-1),
 \qquad W=\frac{c(v-1/3200)}{L_\beta}.
\]
The original curve (2) has the exact representation
\[
 u=3/4+v-(a-1)W.
\tag{9}
\]
Here \(v\ge833/86640>1/3200\), and
\[
 W_x=\frac{cv_xL_\beta-(75/128)(v-1/3200)}{L_\beta^2}.
\tag{10}
\]
We claim \(W_x>1/400\). At fixed x, the numerator of the difference
is the concave quadratic in L
\[
 \Phi(L)=cv_xL-\frac{75}{128}(v-1/3200)-\frac{L^2}{400}.
\tag{11}
\]
Since \(L\) ranges from \(x-1\) to \(x-1+c/3\), it suffices to
check the two endpoints. With \(Y=x-2\), the exact identities are
\[
 \Phi(x-1)=\frac{p_0(Y)}{409600S^3},\qquad
 \Phi(x-1+c/3)=\frac{p_1(Y)}{6553600S^3},
\]
\[
\begin{aligned}
 p_0(Y)={}&13137+1361Y-43205Y^2-42269Y^3-11264Y^4-1024Y^5,\\
 p_1(Y)={}&322953+16409Y-930505Y^2-820321Y^3-210256Y^4-18496Y^5.
\end{aligned}
\tag{12}
\]
Each has six monomials and degree five. On \(0\le Y\le2/5\),
discard the positive linear term and evaluate every negative term at
\(2/5\). The lower bounds are respectively
\(10062937/3125>0\) and \(362499073/3125>0\).
Thus (11) is positive throughout the interval, proving the claim.

Moreover \(W_a=-c^2(v-1/3200)/L_\beta^2<0\). Its minimum on
(1) is therefore at \((x,a)=(13/6,4/3)\), where
\[
 W=\frac{3320411}{636515200}
   =\frac1{200}+\frac{27567}{127303040}>\frac1{200}.
\tag{13}
\]
Finally
\[
 v_x=\frac{17(x-1)}{60S^3},\quad
 v_{xx}=\frac{17(2-x)}{30S^4}<0,\quad
 v_x(13/6)=\frac{357}{34295}<\frac1{96}.
\]
At \(x=13/6\), the difference between \((x-1)/96-1/400\) and v
is \(199/5198400>0\), and that difference increases with x.
Consequently \(v<(x-1)/96-1/400\). Equations (9)--(13) now give
both comparisons in (8), including a=1.

## 3. Signs of the two norm coefficients

The chain-rule comparison using (8) needs two positive coefficients.
The following short shape bounds establish their signs:
\[
 0<d:=D/K\le2/7,\quad d_x<-12/25,\quad
 Td\le5/8,\quad 2/7\le k<1/2,\quad 0<T_x\le1,
\tag{14}
\]
\[
 \frac{29}{10}<\Lambda:=S^3/K\le17/5,\qquad\Lambda_x>0.
\tag{15}
\]
Here is a complete verification. Set
\[
 X=x-13/6,\qquad A=4/3-a,\qquad
 0\le X\le7/30,\quad0\le A\le1/3,
\tag{16}
\]
and write \(\ell=B_x=(3a+13)/16\),
\(Z=2SB-\ell K\). Direct differentiation gives
\[
 D_x=2+2\ell(a-x)-2b<0,\qquad
 D_a=2a+2b+2c(a-x)\ge(15a+x)/4>0.
\]
Thus \(D\ge D(12/5,1)=2/25>0\), while
\(D\le a^2+1+2x\le341/45\). Also
\[
 D_aK-2aD\ge\frac{103}{24}\frac{361}{36}
                    -\frac83\frac{341}{45}
             =\frac{32873}{1440}>0.
\tag{17}
\]
So d increases with a.

The four small polynomials below complete (14):
\[
\begin{aligned}
 Q_v={}&2321581-3759243A+481464A^2+650268A^3-147744A^4\\
 &-2361876X-2698236AX+931176A^2X-129600A^3X\\
 &-3595788X^2-3132AX^2-101088A^2X^2-1050624X^3-82944X^4,\\
 Q_r={}&268+7177A-4551A^2+16976X-1896AX-792A^2X\\
 &+6528X^2-1152AX^2,\\
 Q_T={}&2896708-2706975A+507897A^2+1389120X-873648AX\\
 &+99792A^2X+195840X^2-63936AX^2+5184A^2X^2,\\
 Q_k={}&15620-43647A+12249A^2-3168X-10584AX+1512A^2X-2304X^2.
\end{aligned}
\tag{18}
\]
Their exact source identities are
\[
\begin{aligned}
 Q_v/6912&=-25(D_xK-2SD)-12K^2,\\
 Q_r/384&=5aB-8D,\\
 (a-1)Q_T/147456&=aB^2-Z,\\
 Q_k/1152&=7aB-2K.
\end{aligned}
\tag{19}
\]
The counts in (18) are 14,8,9,7 monomials, of degrees 4,3,4,3;
all coefficients have at most seven digits. For \(Q_v,Q_T\),
discard every positive nonconstant term and bound each negative
monomial at the upper limits in (16). This gives, respectively,
\[
 Q_v\ge59098176/625>0,\qquad Q_T\ge48131807/25>0.
\tag{20}
\]
For \(Q_r\), use \(A^2\le A/3\) and \(X\le7/30\) only on
negative terms. It follows that
\[
 Q_r\ge268+\frac{127332}{25}A+16976X+6528X^2>0.
\tag{21}
\]
Finally \((Q_k)_A\le-35481-9576X<0\); at \(A=1/3\),
\(Q_k=2432-6528X-2304X^2\ge19584/25>0\).
This proves the four signs in (19).

The first of (19) gives \(d_x<-12/25\). Combining it with (17),
d has its maximum at \((13/6,4/3)\), where
\(d=3517/12448<2/7\). The second gives \(Td\le5/8\).
The third proves \(T_x=Z/(aB^2)\le1\), and positivity follows from
\[
 Z=\ell(x^2-a^2)+\frac{179a-51}{64}S>0.
\tag{22}
\]
The fourth gives \(k\ge2/7\). For the remaining upper bound,
\(c<7/8\) and \(a\le4/3\) imply the elementary inequality
\[
 K-2aB\ge x^2-2x/3-23/9\ge25/36>0,
\]
which is the enlarged-domain comparison in Section 2 of the source.
It proves \(k<1/2\). Finally (15) follows from
\[
 \Lambda\ge\frac{(19/6)^3}{(19/6)^2+7/9}
     =\frac{6859}{2334}>29/10,\qquad
 \Lambda\le S,\qquad
 \Lambda_x=\frac{S^2\{S^2+3(a^2-1)\}}{K^2}>0.
\]

For either test in (3), let \(g=4-7k/2\) or \(g=T+1/4\).
Its incoming coefficient is exactly
\[
 C=\frac Ba+\Lambda(1-gd)+gd^2-2d.
\tag{23}
\]
For G, \(9/4<g\le3\), \(gd\le6/7\), and
\(0<g_x=(7/2)k^2T_x<7/8\). For H, \(g>9/4\),
\(gd=Td+d/4\le39/56\), and \(0<g_x=T_x\le1\).
Consequently \(C>B/a-2d>3/7>0\). Differentiating (23) gives
\[
 C_x=\ell/a+\Lambda_x(1-gd)
       +(-d_x)\{2+g(\Lambda-2d)\}
       +g_xd(d-\Lambda).
\]
All bounds needed for its sign are now explicit:
\[
 C_x>\frac{12}{25}\left\{2+2\left(\frac{29}{10}-\frac47\right)\right\}
            -\frac27\frac{17}{5}
       =\frac{1946}{875}>0.
\tag{24}
\]

Both tests are affine in the independent norm argument u. If their
rational part at u=3/4 is denoted by \(F_*\), the exact total derivative
is therefore
\[
 (F_*)_x+(\log k)_x+(u-3/4)C_x+u_xC.
\tag{25}
\]
In view of (8), (23),(24), replacing u and \(u_x\) by U,V in (25)
is an upper comparison. This compares the two chain-rule terms with
proved positive coefficients and leaves the original norm curve as
the object whose derivative is being estimated.

## 4. Six natural rational contributions

This section specifies that upper comparison without forming its
large common-denominator numerator. All the following quantities use
U,V from (7), at the fixed beta curve (1). Define
\[
\begin{gathered}
 E_0=S^3(U-1)+3S-1,\qquad
 E_1=3S^2(U-1)+S^3V+3,\\
 J_0=2DU-E_0,\qquad J_1=2D_xU+2DV-E_1,\\
 H_0=M+D^2U-DE_0-\frac34K^2,\\
 H_1=4S^3-3S^2+2S+2DD_xU+D^2V-D_xE_0-DE_1-3SK.
\end{gathered}
\tag{26}
\]
Here \(E_1,J_1,H_1\) use the independently bounded incoming speed V;
they are not asserted to be derivatives of \(E_0,J_0,H_0\) after
substitution of the affine majorant U. Put
\[
\begin{aligned}
 P_a&=VB+(U-1)\ell,& P_b&=\ell b,\\
 P_1&=J_1+2S,&P_2&=2S(a^2+J_0),\\
 G_0&=4K-7aB/2,&C_0&=21aSB-(7a\ell/2+16S)K,\\
 G_1&=K+aB/4,&C_1&=-2SBK-\ell K^2-SaB^2.
\end{aligned}
\tag{27}
\]
The ten primitive polynomials
\(P_a,P_b,P_1,P_2,G_0,C_0,G_1,C_1,H_0,H_1\) are expanded in full
in the appendix using the coordinates (16). Their largest identity
has 32 monomials and degree seven. Numerators and denominators of
all printed coefficients have at most twelve digits.

The two exact rational upper derivatives from (25) are
\[
\begin{aligned}
 \mathcal R_0={}&\frac{P_a}{a}+\frac{P_b}{B^2}-\frac{P_1}{K}
 +\frac{P_2}{K^2}+\frac{G_0H_1}{K^3}+\frac{C_0H_0}{K^4},\\
 \mathcal R_1={}&\frac{P_a}{a}+\frac{P_b}{B^2}-\frac{P_1}{K}
 +\frac{P_2}{K^2}+\frac{G_1H_1}{aBK^2}
 +\frac{C_1H_0}{aB^2K^3}.
\end{aligned}
\tag{28}
\]
Thus \(G_x\le\mathcal R_0\), \(H_x\le\mathcal R_1\).
Identity (28) follows by differentiating (3) before clearing any
denominators, using \(K_x=2S\), \(B_x=\ell\), and the two
independent substitutions U,V. Every source factor needed for this
calculation is printed in (26)--(27) and the appendix. Products such
as \(G_0H_1\) are kept factored.

## 5. Direct finite coefficient comparisons

In the coordinates (16), the three denominators have the short forms
\[
\begin{aligned}
 a&=a_0-A,&a_0&=4/3,\\
 B&=B_0+17X/16-231A/128-3AX/16,&B_0&=1447/384,\\
 K&=K_0+19X/3-8A/3+X^2+A^2,&K_0&=389/36.
\end{aligned}
\tag{29}
\]
Their expansions have respectively 2,4,5 monomials and degree at most two.

Here is the finite scalar recurrence for the coefficients used in the
comparison. For any of the three displayed denominator polynomials
\(D=\sum d_{jk}X^jA^k\), let \(v^D_{00}=1/d_{00}\), and, in
increasing total degree, set
\[
 v^D_{jk}=-\frac1{d_{00}}
    \sum_{\substack{r\le j,\ s\le k\\r+s>0}}
          d_{rs}v^D_{j-r,k-s},\qquad1\le j+k\le8.
\tag{30}
\]
Only the at most four nonconstant entries in (29) occur in this sum.
Negative indices mean zero. For coefficient arrays use the ordinary
finite convolution
\[
 (p*v)_{jk}=\sum_{r=0}^j\sum_{s=0}^k p_{rs}v_{j-r,k-s}.
\tag{31}
\]
Write \(\alpha=v^a,\beta=v^B,\kappa=v^K\), and use the printed
primitive coefficients for the other arrays. The required scalars are
exactly
\[
\begin{aligned}
 r^{(0)}={}&P_a*\alpha+P_b*\beta^{*2}-P_1*\kappa
       +P_2*\kappa^{*2}+G_0*H_1*\kappa^{*3}+C_0*H_0*\kappa^{*4},\\
 r^{(1)}={}&P_a*\alpha+P_b*\beta^{*2}-P_1*\kappa
       +P_2*\kappa^{*2}+G_1*H_1*\alpha*\beta*\kappa^{*2}
       +C_1*H_0*\alpha*\beta^{*2}*\kappa^{*3},
\end{aligned}
\tag{32}
\]
only for \(j+k\le8\). The notation \(v^{*m}\) means m successive
convolutions. Every arithmetic operation in (30)--(32) is scalar;
products of primitive polynomials are never expanded beyond total
degree eight, and no exact Taylor polynomial with large cleared
coefficients is a sign premise.

The appendix prints two complete integer polynomials \(Z_0,Z_1\),
each with 45 monomials and degree eight. If \(z^{(i)}_{jk}\) is the
printed coefficient, the complete set of coefficient comparisons is
\[
 z^{(i)}_{jk}-1<10^7r^{(i)}_{jk}\le z^{(i)}_{jk}
 \quad(0\le j+k\le8,\ i=0,1).
\tag{33}
\]
These are finite rational inequalities, reconstructed solely by
(29)--(32) and the printed primitive coefficients. They are upward
roundings, not coefficients obtained from an unknown minimum.
For example, (30) gives
\[
 \alpha_{00}=3/4,\quad\beta_{00}=384/1447,\quad\kappa_{00}=36/389,
 \qquad\beta_{10}=-156672/2093809,\quad\kappa_{10}=-8208/151321.
\]
For the constant coefficient of \(\mathcal R_0\), substitution in
(32) gives the directly checkable comparison
\[
\begin{gathered}
 -\frac{58182}{10^7}
 <\frac{(P_a)_{00}}{a_0}+\frac{(P_b)_{00}}{B_0^2}
  -\frac{(P_1)_{00}}{K_0}+\frac{(P_2)_{00}}{K_0^2}
  +\frac{(G_0)_{00}(H_1)_{00}}{K_0^3}
  +\frac{(C_0)_{00}(H_0)_{00}}{K_0^4}
 < -\frac{58181}{10^7}.
\end{gathered}
\tag{34}
\]
Every number on its middle line is printed in the appendix. The other
44 comparisons in that row and the 45 in the second row use the same
recurrence and convolution; their individual upper integers are all
printed as coefficients of \(Z_i\).

There is a short sign check for those upper polynomials. Discard
negative terms of total degree at least three. Bound each remaining
positive monomial \(cX^jA^k\) of those degrees as follows:
\[
 cX^jA^k\le
 \begin{cases}
 c(7/30)^j(1/3)^{k-2}A^2,&k\ge2,\\
 c(7/30)^{j-2}(1/3)^kX^2,&k\le1.
 \end{cases}
\tag{35}
\]
In the second case \(j\ge2\), so there is no negative exponent.
Addition of the explicitly printed coefficients then gives
\[
\begin{aligned}
 Z_0/10^7\le{}&-58181/10^7-63X/1250-9A/2500
                 -7X^2/100-31XA/100-19A^2/100,\\
 Z_1/10^7\le{}&-114863/10^7-599X/10000-163A/10000
                 -19X^2/250-9XA/50-11A^2/250.
\end{aligned}
\tag{36}
\]
These are six-monomial quadratic upper bounds. In particular their
maxima on the rectangle (16) are their negative constant terms.

## 6. An explicit geometric remainder

It remains to bound what the degree-eight coefficient comparisons omit.
For a fixed point \((X,A)\) in (16), insert \((zX,zA)\) into each
factor. For a printed primitive \(P=\sum p_{jk}X^jA^k\), its coefficient
of \(z^n\) has absolute value at most
\[
 \sum_{j+k=n}|p_{jk}|(7/30)^j(1/3)^k.
\tag{37}
\]
The appendix prints all eight coefficients of a degree-at-most-seven
polynomial \(m_P(z)\) dominating (37), for each of the ten primitives.
Every entry is a displayed rational sum rounded upward to a multiple
of \(10^{-6}\).

The denominator coefficients admit sharper directional bounds than
adding their two linear absolute contributions. In (29), the linear
terms in X and A have opposite signs. Hence their absolute difference
is at most the larger of their two individual upper limits. The exact
bounds are
\[
 \left|\frac{a-a_0}{a_0}\right|\preceq z/4,
\]
\[
 \left|\frac{B-B_0}{B_0}\right|\preceq
       \frac{231}{1447}z+\frac{28}{7235}z^2,
 \qquad
 \left|\frac{K-K_0}{K_0}\right|\preceq
       \frac{266}{1945}z+\frac{149}{9725}z^2.
\tag{38}
\]
Here \(\preceq\) compares the absolute value of each scalar z
coefficient at the fixed direction \((X,A)\); it does not assert an
ordering of bivariate polynomial coefficients. For example, the
linear coefficient for K is
\((19X/3-8A/3)/K_0\), whose absolute value is at most \(266/1945\),
and its quadratic coefficient is bounded by
\(((7/30)^2+(1/3)^2)/K_0=149/9725\).

Define three positive-series rational functions
\[
 I_a(z)=\frac1{a_0(1-z/4)},\quad
 I_B(z)=\frac1{B_0(1-231z/1447-28z^2/7235)},
\]
\[
 I_K(z)=\frac1{K_0(1-266z/1945-149z^2/9725)}.
\tag{39}
\]
Each denominator perturbation at z=1 is less than one. The geometric
series identity, followed by the triangle inequality, therefore
bounds all coefficients of the inverse factors by these positive
series, including their entire tails. Products are treated by
convolution, which preserves the bounds.

The two explicit majorants for (28) are consequently
\[
\begin{aligned}
 \mathcal M_0={}&m_{P_a}I_a+m_{P_b}I_B^2+m_{P_1}I_K+m_{P_2}I_K^2
             +m_{G_0}m_{H_1}I_K^3+m_{C_0}m_{H_0}I_K^4,\\
 \mathcal M_1={}&m_{P_a}I_a+m_{P_b}I_B^2+m_{P_1}I_K+m_{P_2}I_K^2
             +m_{G_1}m_{H_1}I_aI_BI_K^2
             +m_{C_1}m_{H_0}I_aI_B^2I_K^3.
\end{aligned}
\tag{40}
\]
Every factor is printed in (39) or in the appendix; no combined
high-degree product needs to be expanded.

For completeness, the scalar coefficients of each inverse factor in
(39) are generated by
\[
 v_0=1/d_0,\qquad v_1=pv_0,\qquad
 v_n=pv_{n-1}+qv_{n-2}\quad(n\ge2)
\tag{41}
\]
for \(1/[d_0(1-pz-qz^2)]\); take \(q=0\) for \(I_a\).
Use ordinary scalar convolution for the six products in (40).
The appendix lists lower bounds for every one of the nine
coefficients of degrees zero through eight, as well as an upper
bound for \(\mathcal M_i(1)\). Subtraction gives exactly
\[
 \sum_{n=9}^{\infty}[z^n]\mathcal M_0(z)<\frac{1741}{10^6},
 \qquad
 \sum_{n=9}^{\infty}[z^n]\mathcal M_1(z)<\frac{10839}{10^6}.
\tag{42}
\]
Thus the coefficient comparisons (33) and the analytic remainder
bound, directly together, establish
\[
 \mathcal R_0\le Z_0/10^7+1741/10^6,\qquad
 \mathcal R_1\le Z_1/10^7+10839/10^6.
\tag{43}
\]
There is no separate unprinted exact polynomial whose sign is needed.
Using (36), the right sides are at most
\[
 -40771/10^7<-1/250,\qquad -6473/10^7<-1/2000,
\]
respectively. Equations (25),(28) prove (4), and (5)--(6) supply the
four duration-tangent derivatives with the original norm curve.

## 7. Arithmetic and domain audit

The two expanded upper polynomials have 45 monomials, two variables,
and total degree eight. The ten expanded primitive identities have
at most 32 monomials and degree seven; all coefficient numerators and
denominators have at most twelve digits. Their natural source
contributions in (26)--(27), expanded individually before addition,
also satisfy the budget: degree at most seven, at most 30 monomials,
and coefficient numerators of at most eleven digits. The additional
shape identities have at most fourteen monomials and degree four;
the two norm-endpoint polynomials have six monomials and degree five.

The recurrence arithmetic in (30)--(33),(41) is scalar. Its exact
rational intermediate values do not require expanded polynomial
identities with large coefficients. The printed coefficient bounds,
majorants and remainder arithmetic are the complete finite data used
in the comparison. Symbolic arithmetic can check their transcription;
the sign proof uses only these printed rational inequalities,
convolution, geometric series and elementary monotonicity.

The full rectangle (1) is retained throughout. No additional domain
subdivision, logarithm majorant, numerical sample, Lean compilation
or generated high-degree certificate is required for this x comparison.
