# The high-D all-forward sum residual is negative by hand

Date: 2026-11-07 UTC. Complete hand proof of the high-D region.
Together with [HAND_FORWARD_SYMMETRIC_SUM_REDUCTION](HAND_FORWARD_SYMMETRIC_SUM_REDUCTION.md),
this closes the scalar sum target in
[HAND_FORWARD_CONDITIONAL_NORM_BOUNDS](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md):
\(\delta u+\delta v<1/35\).

All sign arguments below use the displayed rational inequalities.
The six coefficient polynomials needed in the final calculation are
displayed in full in Section 5, and their signs are proved by coarse
bounds and a single quartic. No interval execution or omitted
coefficient-count assertion is a premise.

## 1. Coordinates and the exact initial-value cancellation

Continue on the symmetric domain
\[
1\le z\le4/3,\qquad 1+6z/5\le U<3,\qquad
I=\frac{(1+z)^2}{z^2+U}\le h\le h_c
 =\frac{(1+z)(5U-2-3z)}{3(z^2+U)}.
\]
Put
\[
a=\frac{z-1}{z+1},\quad t=I-1,\quad A=1-a,\quad B=1+a,
\quad S=\frac2A,\quad z=\frac BA,\quad b=1-aI.
\]
Then
\[
0\le a\le\frac17,\qquad
0\le t\le\frac14,\qquad b>0,
\tag{1}
\]
and
\[
D=BI-1,\qquad n_1=\frac{2(1-D)}{A^2},\qquad
H_c=h_c-1=\frac{2(1-a^2)-t(5+3a+2a^2)}{3A}>0.
\tag{2}
\]
The lower bound for the numerator of \(H_c\) on (1) is \(29/49>0\).

The condition \(U\le3\) is equivalent to
\[
t\ge\frac{a(1-a)}{1-a+a^2}\ge\frac{39}{40}a.
\tag{3}
\]
For the second inequality it suffices to check
\(1-a-39a^2\ge0\); on \(0\le a\le1/7\) its minimum is \(3/49\).

Use the exact decomposition
\[
\frac{\mathcal E_\Sigma}{H}
 =\frac{A_0}{H}+A_1+zg(H),\qquad H=h-1,
\]
from the linked sum-reduction note. Let
\[
\Delta=L(z,I)-a^2/4,\qquad J=A_0/b.
\]
Cancellation of the common logarithmic term in \(A_1-SA_0\) gives
\[
\boxed{
A_1=SA_0-n_1(1/35-a^2/2)
 +\frac{D(I-zb)}I\left(\frac B2-S\Delta\right).
}
\tag{4}
\]
This can also be checked directly from the exact centered row:
\(n=n_1H,\ m=m_0+m_1H\), with
\[
m_0=\frac{SbD}{I},\qquad
m_1-n_1=\frac{SD(I+b)}I,
\]
so that
\[
m_1-n_1-Sm_0=\frac{SD(I-zb)}I.
\]
Writing the residual as \(r=r_0+Hr_1+zH g(H)\), its rational
terms also give
\[
r_1-Sr_0=\frac{n_1a^2}{2}+\frac{SD(I-zb)}{4I}.
\]
Subtracting \(SA_0\) from the definition of \(A_1\), then using
\(S(1-a^2)/4=B/2\), proves (4).
In (4), \(I-zb\ge0\), since \(q=I/b\ge z\) when \(U\le3\).
All replacements of \(\Delta\) below therefore have the stated direction.

## 2. A quantitative initial-value lemma

The exact \(J\) from Section 1 of the linked sum-reduction note can be
written without separate logarithms of the two original edge ratios:
\[
\boxed{
J=\frac{D}{Sb}-\frac{zBD}{2}
 +\frac{a[(3+a)I-2]}{At}\log I+\log b.
}
\tag{5}
\]
At \(t=0\), this uses the continuous extension.

**Lemma.** On the entire rectangle (1),
\[
\boxed{
J\le J_*:=-\frac{at^2}{2}-a^2t-\frac{a^3}{3}.
}
\tag{6}
\]

The coefficient of \(\log I\) in (5) is nonnegative. Use
\[
\log I\le
 \frac{t(I+1)}{2I}-\frac{t^3}{3I(I+1)},
\tag{7}
\]
which is the lower bound
\(f(I)\ge t^3/[3I(I+1)]\) proved directly by differentiation in Section 2 of the linked
sum-reduction note.
Also, for \(0\le y<1\),
\[
\log(1-y)\le-y-y^2/2-y^3/3.
\tag{8}
\]
Indeed \(1/(1-s)\ge1+s+s^2\), and integration from 0 to \(y\)
proves (8). Apply it with \(y=aI<1\).

Substitute (7)--(8) in (5), and add
\(at^2/2+a^2t+a^3/3\). After multiplication by the positive denominator
\(6AbI(I+1)\), the resulting numerator is
\[
\begin{aligned}
&at^2(-2+6t+6t^2)\\
&-a^2t^2(6+9t+6t^2+3t^3)\\
&+a^3t(-18-19t+12t^2+17t^3+4t^4)\\
&+a^4t(30+81t+83t^2+43t^3+13t^4+2t^5)\\
&-a^5t(12+42t+58t^2+40t^3+14t^4+2t^5).
\end{aligned}
\tag{9}
\]
This is an ordinary polynomial identity.

For \(0\le t\le1/4\), the first parenthesis is at most \(-1/8\).
The third parenthesis is at most
\[
-18+\frac{12}{16}+\frac{17}{64}+\frac4{256}
 =-\frac{543}{32}.
\]
The fourth parenthesis is at most
\[
30+\frac{81}{4}+\frac{83}{16}+\frac{43}{64}
 +\frac{13}{256}+\frac2{1024}
 =\frac{28755}{512}<57.
\]
Since \(a\le1/7\), the third and fourth lines of (9) together are at most
\[
-\left(\frac{543}{32}-\frac{57}{7}\right)a^3t
 =-\frac{1977}{224}a^3t\le0.
\]
The other lines are nonpositive. Thus (9) is nonpositive and proves (6),
including the continuous boundary \(t=0\).

## 3. Replace the remaining factors by elementary tangents

We now assume
\[
D\ge\frac{38}{243}.
\tag{10}
\]
The high-D envelope in Section 4 of the linked sum-reduction note,
followed by (4), is
\[
\frac{\mathcal E_\Sigma}{H}
\le
(S+H_c^{-1})A_0-n_1(1/35-a^2/2)
 +\frac{D(I-zb)}I\left(\frac B2-S\Delta\right)
 +z\left\{\frac2{243}
       +\left(\frac D2-\frac{19}{243}\right)
           \frac{H_c}{1+H_c}\right\}.
\tag{11}
\]
The coefficient \(D/2-19/243\) is nonnegative by (10).

From the rational exterior floor and \(I+1\le9/4\),
\[
\Delta\ge
 B\left\{\frac{at}{4}+\frac{t^2}{6(I+1)}\right\}
 \ge\Delta_*:=B\left(\frac{at}{4}+\frac{2t^2}{27}\right).
\tag{12}
\]

For every \(X>0\), two tangent inequalities at \(X=2/7\) are
\[
\frac1X\ge7-\frac{49X}{4},\qquad
\frac X{1+X}\le\frac{4+49X}{81}.
\tag{13}
\]
Their errors are the explicit nonnegative quantities
\[
\frac{(7X-2)^2}{4X},\qquad
\frac{(7X-2)^2}{81(1+X)},
\]
respectively.

Since \(A_0=bJ\le bJ_*\le0\), equations (6), (10)--(13) imply
\[
\frac{\mathcal E_\Sigma}{H}\le\mathcal B(a,t),
\tag{14}
\]
where
\[
\begin{aligned}
\mathcal B={}&
 \left(S+7-\frac{49H_c}{4}\right)bJ_*
 -n_1(1/35-a^2/2)\\
&+\frac{D(I-zb)}I\left(\frac B2-S\Delta_*\right)\\
&+z\left\{\frac2{243}
 +\left(\frac D2-\frac{19}{243}\right)
          \frac{4+49H_c}{81}\right\}.
\end{aligned}
\tag{15}
\]
The first replacement in (13) is multiplied by a nonpositive quantity.
The second is multiplied by a nonnegative one. No sign of
\(S+7-49H_c/4\) is needed.

It remains to prove the rational inequality \(\mathcal B<0\) on
(1), (3). The proof in Sections 4--6 does so on that entire domain,
without using (10) again.

## 4. A factored numerator and its six coefficients

For compactness define
\[
C=5+3a+2a^2,\quad N=2(1-a^2)-Ct,\quad
L=(1+a^2)I-B,\quad Q_0=3t^2+6at+2a^2.
\]
Thus \(H_c=N/(3A)\) and \(I-zb=L/A\).
Multiplication of (15) by its positive denominator gives the identity
\[
16533720\,A^2I\,\mathcal B=P(a,t),
\tag{16}
\]
where the numerator has the following factored form:
\[
\begin{aligned}
P={}&-229635\,aQ_0b(24+84A-49N)AI\\
&-472392(1-D)(2-35a^2)I\\
&+306180\,DLB(27b-8t^2)\\
&+140\,BI\{972A+(243D-38)(12A+49N)\}.
\end{aligned}
\tag{17}
\]

Put \(u=1-4t\). By (1), (3),
\[
0\le u\le1-\frac{39}{10}a\le1.
\tag{18}
\]
Define \(g_0,\ldots,g_5\) by the identity
\[
\frac{4^5}{10^6}P\left(a,\frac{1-u}{4}\right)
 =\sum_{j=0}^5g_j(a)u^j.
\tag{19}
\]
The following coefficient estimates will be proved in Section 5:
\[
\begin{aligned}
g_0&\le-14+620a-12200a^2,\\
g_1&\le18000a-1400,\\
g_3&\ge0,\qquad g_4,g_5\le0,\\
g_2+(1-39a/10)g_3&\le100-9800a-33000a^2.
\end{aligned}
\tag{20}
\]
Using (18) and the signs in (20), equation (19) is therefore at most
\[
-F(a)+B_1(a)u-C_1(a)u^2,
\tag{21}
\]
where
\[
F(a)=14-620a+12200a^2,\quad
B_1(a)=18000a-1400,\quad
C_1(a)=33000a^2+9800a-100.
\tag{22}
\]
Notice \(F\ge747/122>0\) by completing the square.

## 5. All coefficient estimates are elementary

Here are the six polynomials in (19). For readability, write
\(G_j=10^6g_j\):
\[
\begin{aligned}
G_0={}&-14784960+615669660a-13567399195a^2
 +10286718050a^3+14075775a^4\\
&-64277132850a^5+129238578000a^6-90016920000a^7,\\
G_1={}&-1495492672+13498937120a+43281673855a^2
 -62722455110a^3\\
&+60189451245a^4-102384601830a^5
 +38321488800a^6+54010152000a^7,\\
G_2={}&-79831744-15222909064a-12452663230a^2
 +45598836500a^3\\
&-4865761530a^4+24669228780a^5
 -44339762880a^6-10802030400a^7,\\
G_3={}&17010\{10144+356768a-424801a^2-589414a^3
 -70115a^4\\
&\hspace{28mm}+298458a^5+529200a^6+42336a^7\},\\
G_4={}&76545\{-128-9076a+32297a^2+4298a^3
 -2837a^4-18522a^5-7056a^6\},\\
G_5={}&33756345\,a^2(-5+2a+a^2+2a^3).
\end{aligned}
\tag{23}
\]
Both (17) and (23) are displayed so that the change of variables can be
checked without relying on an external coefficient list.

### 5.1. Bound for g0

Rounding coefficients in the indicated upper direction gives
\[
g_0\le-14+620a+
 a^2\{-13567+R(a)\},
\]
where
\[
R(a)=10287a+15a^2-64277a^3+129239a^4.
\]
For \(0\le a\le1/7\),
\[
R'(a)\ge10287-\frac{3\cdot64277}{49}>0.
\]
Moreover
\[
1367-R(1/7)=\frac{73691}{2401}>0.
\]
Thus \(R(a)<1367\), proving the first line of (20).

### 5.2. Bound for g1

The second derivative of \(g_1\) is positive throughout the interval:
discarding its positive higher terms gives the lower bound
\[
g_1''\ge86562-\frac{376338}{7}
                 -\frac{2047700}{343}>26000.
\]
Hence \(g_1\) is convex. Its endpoint values satisfy
\[
g_1(0)<-1400,\qquad
g_1(1/7)=\frac{345963121821}{300125000}<1153<\frac{8200}{7}.
\]
The line \(18000a-1400\) lies above both endpoint values.
Convexity places \(g_1\) below the endpoint chord, proving its bound
in (20).

### 5.3. Signs of g3, g4, g5

From (23), dropping positive higher terms and rounding downward gives
\[
g_3\ge172+
 a\left(6068-\frac{7226}{7}
             -\frac{10026}{49}
             -\frac{1193}{343}\right)>0.
\]
Likewise,
\[
g_4\le-9+a(-694+2473a+329a^2)
 \le-9-334a<0.
\]
Finally \(G_5\le0\), because its final parenthesis is at most
\[
-5+\frac27+\frac1{49}+\frac2{343}<0.
\]

### 5.4. The combined g2 and g3 bound

Expanding only this combination, discarding its negative terms of
degrees 6, 7, 8, and rounding its remaining coefficients upward gives
\[
\begin{aligned}
g_2+(1-39a/10)g_3
\le{}&100-9800a\\
&+a^2\{-43346+63754a+33043a^2+34398a^3\}.
\end{aligned}
\]
The last brace is less than \(-33000\), since
\[
-43346+\frac{63754}{7}+\frac{33043}{49}
       +\frac{34398}{343}
 =-33000-\frac{22719}{49}.
\]
This proves the last line of (20). The derivation has used only
the six explicitly displayed polynomials and \(0\le a\le1/7\).

## 6. A single quartic proves strict negativity

We finish the sign of (21).

If \(a\le7/90\), then \(B_1(a)\le0\). If \(C_1(a)\ge0\), both terms
involving \(u\) in (21) are nonpositive. If \(C_1(a)<0\), its
monotonicity and \(C_1(1/100)=13/10>0\) imply \(a<1/100\).
In that case \(B_1\le-1220\), while \(-C_1\le100\), so
\[
B_1u-C_1u^2\le-1220u+100u^2\le0.
\]
Thus (21) is at most \(-F<0\) throughout this first region.

Now suppose \(7/90\le a\le1/7\). Here \(C_1>0\), and completing the
square in \(u\) gives
\[
B_1u-C_1u^2\le\frac{B_1^2}{4C_1}.
\]
The needed strict inequality \(B_1^2<4C_1F\) is equivalent to
\(Q(a)>0\), by the exact identity
\[
4C_1F-B_1^2=800Q(a),
\]
where
\[
\boxed{
Q(a)=2013000a^4+495500a^3-439170a^2+63996a-2457.
}
\tag{24}
\]

There is a short derivative proof of this final sign. We have
\[
Q'''(a)=2973000+48312000a>0.
\]
On \([7/90,1/10]\), \(Q''\) is increasing and
\(Q''(1/10)=-339480<0\); hence \(Q\) is concave there.
Its two endpoint values are positive:
\[
Q(7/90)=\frac{3730181}{21870},\qquad
Q(1/10)=\frac{2477}{10}.
\]
A concave function lies above its endpoint chord, so it is positive on
this interval.

On \([1/10,1/7]\), the function \(Q'\) is convex because \(Q'''>0\).
Its endpoint values are
\[
Q'(1/10)=-921,\qquad
Q'(1/7)=-\frac{2630532}{343}.
\]
Therefore \(Q'<0\) throughout this interval: it lies below its negative
endpoint chord. Thus \(Q\) decreases there, and
\[
Q(a)\ge Q(1/7)=\frac{13541}{2401}>0.
\]
This proves (24)'s sign on the whole remaining interval.

Consequently (21), (19), (16), and (14) give
\(\mathcal E_\Sigma<0\) throughout the high-D region.
The low-D proposition in
[HAND_FORWARD_SYMMETRIC_SUM_REDUCTION](HAND_FORWARD_SYMMETRIC_SUM_REDUCTION.md)
covers the complementary region. The exact monotonic reduction in
[HAND_FORWARD_CONDITIONAL_NORM_BOUNDS](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md)
then proves \(\delta u+\delta v<1/35\) on the full ordered all-forward
domain. The separate larger-neighbor norm target \(\delta v<1/64\)
is not proved in this note.
