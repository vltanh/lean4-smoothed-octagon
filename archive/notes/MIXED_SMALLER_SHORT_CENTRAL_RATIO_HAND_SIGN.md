# A hand sign for the central face of the short upper-ratio reduction

Date: 2026-11-08 UTC. **Result:** the central scale face cannot carry
the positive variable-floor test when \(13/6\le x\le12/5\).
This is a complete scalar proof, accepted after a separate reading
recorded in the
[reconstruction audit](MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_AUDIT.md).
The outer scale face remains a separate S2 obligation.

The argument removes duration by integrating its exact derivative,
removes beta by two strict monotonicities, and removes x by two global
rational derivative signs. Only two one-variable signs remain. Their
quadratic and remainder estimates are given explicitly. The arithmetic
appendices specify six finite polynomials and print their complete
coefficient bounds; they contain no minimum over a hidden coefficient
family, parameter subdivision or executable premise.

## 1. Domain, scalar statement and actual interface

Assume

\[
\frac{13}{6}\le x\le\frac{12}{5},\qquad
1\le a,\qquad a^2\le\frac{x(x+2)}6,
\tag{1}
\]
\[
x+\frac{8x(a-1)}{9x+8}\le b
\le x+\frac{x(7x+1)(a-1)}{4x^2+11x+1}.
\tag{2}
\]

Here \(a=\alpha\), \(b=\beta\). In the actual application (1) is
exactly the central cap \(q_c\le1/7\), and (2) follows from the
[global upper order](MIXED_SMALLER_SHORT_GLOBAL_UPPER_ORDER.md) and
[strong lower order](MIXED_SMALLER_SHORT_STRONG_ORDER.md). Set

\[
S=1+x,\quad K=x(x+2)+a^2,\quad B=a+b,\quad
q=\frac{a^2}{K},\quad k=\frac{aB}{K}=\frac1T,
\]
\[
u=\frac34+
 \frac{680(x-1)^3+3S^2(b-x)}{9600S^2(b-1)},
\quad D=a^2+2ab+1+2x-2bx,
\]
\[
E=S^3(u-1)+3S-1,
\quad w=\frac{S^2(S^2-S+1)+D^2u-DE}{K^2},
\quad E_L=\frac{2Du-E}{K},\quad h=w-\frac34.
\tag{3}
\]

For \(2\le\tau\le T\), define the exact logarithmic scalar

\[
\begin{aligned}
G_\tau={}&(w-1)\tau+\tau^{-1}+(u-1)B/a+a/B+1-q-E_L
             +\log(\tau k)\\
 &+\left(2-\frac{7\tau k}{4}\right)h.
\end{aligned}
\tag{4}
\]

We prove

\[
\boxed{G_\tau<0\quad\text{throughout (1)--(2), }2\le\tau\le T.}
\tag{5}
\]

All transport quantities in (3) are the central upper-envelope
formulas, with just the displayed rational incoming-norm replacement.
For an actual equal-secant shape this replacement is legitimate:
the [variable-floor theorem](MIXED_SMALLER_SHORT_VARIABLE_FLOOR_REDUCTION.md)
proves strict increase in the incoming norm before the replacement.
The required ceiling \(u_{\rm actual}\le u\) is proved in the central
part of [RATIO_SIGN_HAND_GAP](MIXED_SMALLER_SHORT_RATIO_SIGN_HAND_GAP.md).
For clarity, its ingredients are the
[Gauss incoming bound](MIXED_SMALLER_SHORT_GAUSS_INCOMING_CEILING.md),
which gives

\[
V(x)-3/4<\frac{17(x-1)^2}{240S^2},
\]

and the central order estimate \((b-x)/x<3/25\). Splitting the
positive incoming integral at its minimum gives

\[
u_{\rm actual}-\frac34\le
\frac{(x-1)[V(x)-3/4]+(b-x)^3/(48x^2)}{b-1}
\le u-\frac34.
\]

The two scalar comparisons use no physical cost or upper Casimir cap
at a changed scale. Consequently (5) rules out exactly the central
positive endpoint in the accepted variable-floor reduction.

## 2. Simpler beta endpoints and a common enlarged domain

Put

\[
b_-(x,a)=x+\frac58(a-1),\qquad
b_+(x,a)=x+\frac{24x+51}{128}(a-1).
\tag{6}
\]

The original beta interval is contained in \([b_-,b_+]\).
The lower assertion is \(8x/(9x+8)\ge5/8\), equivalent to
\(19x\ge40\). For the upper assertion, clearing its positive
denominator leaves

\[
96x^3-428x^2+457x+51
 =6-11v+(220+96v)v^2>0,
\quad v=x-9/4\ge-1/12.
\]

Indeed \(220+96v\ge212\), and
\(6-11v+212v^2>0\) by its negative discriminant.
Also \((24x+51)/128<7/8\) on the entire x interval.
The central cap gives \(a<4/3\). We will prove all further
comparisons on the larger simple set

\[
\frac{13}{6}\le x\le\frac{12}{5},\quad
1\le a\le\frac43,\quad b=x+c(a-1),\quad
\frac58\le c\le\frac78.
\tag{7}
\]

No equal-secants or central-cap assertion is made at extra points
of this enlarged set. Its denominators are positive. Moreover

\[
K-2aB\ge x^2-\frac23x-\frac{23}{9}\ge\frac{25}{36}>0.
\tag{8}
\]

To obtain the first inequality, maximize \(b\) at
\(x+7(a-1)/8\), and then maximize a at \(4/3\); the resulting
expression decreases in a. Thus \(0<k<1/2\), and \(T>2\), even
on the enlarged set.

## 3. Eliminate duration with a cubic loss

At fixed shape and scale, differentiation of (4) gives the exact
identity

\[
G_\tau'=A-\frac{(\tau-2)^2}{4\tau^2},
\qquad A=\left(1-\frac{7k}{4}\right)h.
\tag{9}
\]

For \(s=\tau-2\ge0\), using \(\tau\le T\) and integrating gives

\[
G_\tau\le G_2+As-\frac{s^3}{12T^2}.
\tag{10}
\]

If \(A\le0\), this is at most \(G_2\). If \(A>0\), the cubic
on the right is maximized on \(s\ge0\) at \(s=2T\sqrt A\),
with value \(4TA^{3/2}/3\). The elementary square
\((\sqrt A-1/12)^2\ge0\) gives
\(\sqrt A\le6A+1/24\). Therefore

\[
G_\tau\le G_2+C,\qquad
C=8TA^2+\frac{TA}{18}\quad(A\ge0).
\tag{11}
\]

Using the cubic loss is necessary here: the tangent bound obtained by
replacing its last term by zero need not be negative on the central
face. No claim is made that the maximizing duration is an endpoint.

## 4. Eliminate beta using opposite endpoint comparisons

The following two signs hold throughout the enlarged domain (7):

\[
\boxed{\partial_b G_2>\frac1{16},\qquad \partial_b w<0.}
\tag{12}
\]

Appendix A proves both from two displayed finite polynomial
specifications and their explicit coefficient-norm lower bounds.
There is no implicit root differentiation: \(G_2\) is (4) evaluated
at the fixed duration two, and u is the explicit rational function (3).
In particular, \(\partial_b\log(2k)=1/B\) exactly.

Put \(e=1-7k/4>0\), so

\[
C(k,h)=\frac{8e^2h^2}{k}+\frac{eh}{18k}.
\]

For \(h\ge0\), this is increasing in h and decreasing in k:

\[
C_h=\frac{16e^2h}{k}+\frac e{18k}>0,
\quad
C_k=-\frac{8(1-49k^2/16)h^2+h/18}{k^2}\le0.
\tag{13}
\]

Here \(k<1/2\) makes \(1-49k^2/16>0\). As b increases,
\(k_b=a/K>0\) while \(h_b=w_b<0\), by (12). Consequently,
whenever the original h is nonnegative, its correction C is at most
the value at \(b_-\); that lower beta endpoint also has nonnegative h.
The value \(G_2\) is at most the value at \(b_+\).

Define the following two explicit functions, allowing their scalar
arguments to range over the rectangle in x and a in (7):

\[
F_0(x,a)=G_2(x,a,b_+(x,a)),
\]
\[
F_1(x,a)=F_0(x,a)+C(x,a,b_-(x,a)).
\tag{14}
\]

The correction in the second line uses its polynomial formula even
when its h is negative. In that case it is not required as a duration
bound: (10) and \(F_0\) suffice. Equations (10)--(13) show that for
every original point of (1)--(2),

\[
G_\tau\le\max\{F_0(x,a),F_1(x,a)\}.
\tag{15}
\]

Thus two scalar signs will finish the central face.

## 5. Eliminate x by exact logarithmic differentiation

Both functions in (14) decrease strictly in x on the full rectangle

\[
13/6\le x\le12/5,\qquad1\le a\le4/3:
\qquad \boxed{\partial_xF_0<0,\quad\partial_xF_1<0.}
\tag{16}
\]

Appendix B supplies the two explicit rational derivative polynomials,
all the coefficients of their global lower polynomials, and the short
sign argument. The logarithm is differentiated exactly; a logarithm
majorant has not been used to obtain (16).

It follows that

\[
F_j(x,a)\le F_j(13/6,a)\quad(j=0,1).
\tag{17}
\]

The extra points on the right may violate the original central cap,
which causes no issue: (16) was proved on the enlarged scalar
rectangle, without transporting physical hypotheses to it.

## 6. The two one-variable signs

Only in this section replace the logarithm. At \(x_0=13/6\), set
\(y=2k(x_0,a,b_+(x_0,a))\). By (8), \(0<y<1\). The identity

\[
\log y\le2z+\frac23z^3,\qquad z=\frac{y-1}{y+1}<0,
\tag{18}
\]

follows by integrating the nonnegative remainder of the geometric
series for \((1-z^2)^{-1}\), with reversed integration limits.
Let \(\overline F_j(a)\) be \(F_j(x_0,a)\) with (18) inserted.
Define

\[
\begin{aligned}
\Delta_0(a)={}&681364684800\,a(309a+139)(693a+523)\\
 &\cdot(36a^2+325)^3(2655a^2+1569a+5200)^3,\\
\Delta_1(a)={}&6641261582745600\,a(15a+13)^2(39a+37)\\
 &\cdot(309a+139)(693a+523)(36a^2+325)^5
 (2655a^2+1569a+5200)^3,
\end{aligned}
\tag{19}
\]
\[
P_j(a)=-\Delta_j(a)\overline F_j(a).
\tag{20}
\]

All factors in (19) are positive. The degrees of \(P_0,P_1\) are
15 and 22. Their complete coefficients, the coefficient translation
identity and the elementary remainder bounds used next are printed
in Appendix C.

### 6.1. First polynomial: one completed quadratic

Expand \(P_0(7/6+t)=\sum c_it^i\), with \(|t|\le1/6\).
Appendix C gives

\[
c_0>0,\quad |c_1|<24c_0,\quad c_2>780c_0,
\quad \sum_{i=3}^{15}|c_i|(1/6)^{i-2}<280c_0.
\]

Consequently

\[
\frac{P_0}{c_0}\ge1-24|t|+500t^2
\ge1-\frac{24^2}{2000}=\frac{89}{125}>0.
\tag{21}
\]

### 6.2. Second polynomial: a small initial interval and a quadratic

On \(1\le a\le11/10\), expand about \(21/20\), so
\(|t|\le1/20\). The full coefficient norm in Appendix C gives

\[
P_1(21/20)>0,\quad
\sum_{i=1}^{22}|c_i|(1/20)^i<\frac{17}{20}c_0.
\]

Therefore \(P_1>3c_0/20>0\) on this initial interval.

On \(11/10\le a\le4/3\), write \(t=a-11/10\in[0,7/30]\).
For this expansion Appendix C gives

\[
c_0>0,\quad c_1>-6c_0,\quad c_2>330c_0,
\quad \sum_{i=3}^{22}(-c_i)_+(7/30)^{i-2}<54c_0.
\]

Discarding the nonnegative higher terms is legitimate because t is
nonnegative. Hence

\[
\frac{P_1}{c_0}\ge1-6t+276t^2
\ge1-\frac{36}{1104}=\frac{89}{92}>0.
\tag{22}
\]

The shared endpoint \(a=11/10\) is included in both estimates.
Equations (19)--(22) prove \(\overline F_0,\overline F_1<0\), hence
\(F_0,F_1<0\). Combining (15), (17) and (18) proves (5).

## Appendix A. Two beta derivative polynomials

The specifications in this appendix use only sums and products of the
following low-degree factors:

\[
z=b-1,\quad v=x-a,\quad
C_0=(x-1)(677x^2-1366x+677),
\]
\[
V=9600S^2z,\quad U=7203S^2z+C_0,\quad u=U/V,
\]
\[
E_N=S^3(U-V)+(3S-1)V,\quad L=2DU-E_N,
\]
\[
W=S^2(S^2-S+1)V+D^2U-DE_N,\quad H=4W-3K^2V,
\]
\[
P_w=2vLz+D(D-S^3)C_0.
\tag{A1}
\]

Quotient differentiation gives the exact identity

\[
-w_b=\frac{P_w}{K^2Vz}.
\tag{A2}
\]

For the other derivative define

\[
\begin{aligned}
N={}&8B^2K^3z(U-V)-8C_0B^3K^3+8abK^3Vz\\
 &+8aB^2K^2\{4vUz+(2D-S^3)C_0\}\\
 &-4aB^2(8K-7aB)P_w-7a^2B^2Hz,
\end{aligned}
\]
\[
P_b=\frac N4-\frac{aB^2K^3Vz}{8}.
\tag{A3}
\]

All apparent constant denominators cancel. Direct differentiation of
(3)--(4), including \(\partial_b\log(2k)=1/B\), gives

\[
P_b=19200aB^2z^2S^2K^3\left(\partial_bG_2-\frac1{16}\right).
\tag{A4}
\]

These identities specify both derivative polynomials completely.
The denominators in (A2),(A4) are strictly positive.

### A.1. The elementary coefficient-norm rule

If \(Q(X,s,t)=\sum q_{ijk}X^is^jt^k\), \(X\ge0\),
\(|s|\le r\), \(|t|\le R\), then

\[
Q\ge\sum_i\left(q_{i00}-
 \sum_{j+k>0}|q_{ijk}|r^jR^k\right)X^i.
\tag{A5}
\]

This is the triangle inequality for the finitely many terms at each
power of X. The following coefficient arrays are the complete exact
lower polynomials from (A5), not extrema found by optimization.
Their entries are obtained from the displayed products (A1),(A3) by
the binomial formula \((c+s)^m=\sum_j\binom mjc^{m-j}s^j\).
Every lower-polynomial coefficient is printed, including all negative
ones, and all are used in the estimates below.

### A.2. The incoming scalar increases with beta

In (A3), substitute

\[
x=13/6+X,\quad a=7/6+s,\quad
b=x+(3/4+t)(a-1),
\quad |s|\le1/6,\ |t|\le1/8.
\]

Apply (A5). If \(L_b(X)=\sum_{i=0}^{12}\ell_iX^i\), the exact
result is

\[
P_b\ge\frac{L_b(X)}{17832200896512}.
\tag{A6}
\]

The complete coefficient vector is:

| Degree | \(\ell_i\) |
| ---: | ---: |
| 0 | 3108447502363285626596 |
| 1 | 34615892363229886969595 |
| 2 | 98017286840108285133999 |
| 3 | 157920924283368194613852 |
| 4 | 160395974049129439632192 |
| 5 | 106761783370800754439712 |
| 6 | 46335222327768124500864 |
| 7 | 12118113641652753088512 |
| 8 | 1323762396476069265408 |
| 9 | -285796051617907998720 |
| 10 | -148007014838842687488 |
| 11 | -20629861212119629824 |
| 12 | -1058079584261505024 |

The coefficients through degree eight are positive. The constant
coefficient exceeds \(3\cdot10^{21}\), while the sum of the absolute
values of the four negative coefficients is less than
\(5\cdot10^{20}\). Since \(0\le X\le7/30<1\),
\(L_b(X)>0\). Equations (A4),(A6) prove the first sign in (12).

### A.3. The comparison norm decreases with beta

In (A1), substitute

\[
x=137/60+s,\quad a=1+A,\quad b=x+(3/4+t)A,
\quad |s|\le7/60,\ |t|\le1/8,\quad0\le A\le1/3.
\]

Apply (A5), with A in place of the nonnegative variable X. The exact
result is

\[
P_w\ge\frac{L_w(A)}{18662400000000},
\qquad L_w(A)=\sum_{i=0}^5v_iA^i,
\tag{A7}
\]

with the complete vector:

| Degree | \(v_i\) |
| ---: | ---: |
| 0 | 3029338903125972892 |
| 1 | 31253831540474267200 |
| 2 | 11321934280043335375 |
| 3 | -35150336733635248500 |
| 4 | -44771087349676800000 |
| 5 | -13087223935632000000 |

Here \(v_0,v_1,v_2>0\). Since \(A\le1/3\),

\[
L_w(A)\ge v_0+A\left(v_1-
 \frac{|v_3|}{9}-\frac{|v_4|}{27}-\frac{|v_5|}{81}\right)+v_2A^2.
\]

The bracket is positive: \(v_1>3\cdot10^{19}\), while its three
subtracted terms have sum less than \(6\cdot10^{18}\), by the
printed integers. Thus \(L_w>0\). Equation (A2) proves the second
sign in (12), including all boundaries of (7).

## Appendix B. The two x derivative signs

Let \(F_0,F_1\) be the exact logarithmic functions (14), and put

\[
Z_+=24ax+51a+104x-179=128(b_+-1),
\]
\[
B_+=24ax+179a+104x-51=128(a+b_+),
\]
\[
Z_-=5a+8x-13=8(b_--1),\quad
B_-=13a+8x-5=8(a+b_-).
\]

Define the two explicit positive denominators

\[
D_0=5033164800\,aS^3K^4Z_+^2B_+^2,
\]
\[
D_1=45298483200\,aS^5Z_-^3B_-^2K^6Z_+^2B_+^2,
\tag{B1}
\]

and the finite derivative polynomials

\[
Q_j=-D_j\partial_xF_j\quad(j=0,1).
\tag{B2}
\]

Equations (3),(6),(11),(14),(B1) specify these polynomials by finite
products and quotient differentiation. Their degrees in \((x,a)\)
are respectively \((15,13)\) and \((28,22)\). No logarithm remains:
its derivative is \(\partial_x k/k\), with \(k=a(a+b_+)/K\).
Every denominator divides the indicated positive product (B1).

Here is a direct coefficient lower bound for their signs. Substitute
\(x=13/6+X\), \(a=7/6+s\), and write
\(Q_j=\sum q^{(j)}_{ik}X^is^k\). For \(|s|\le1/6\), the
nonnegative even terms may be dropped, and the remaining terms give

\[
Q_j\ge\sum_i\left[q^{(j)}_{i0}-
 \sum_{\substack{k\ge1:\ k\text{ odd or }q^{(j)}_{ik}<0}}
 |q^{(j)}_{ik}|6^{-k}\right]X^i.
\tag{B3}
\]

The complete lower polynomials from (B3) are

\[
Q_0\ge\frac{J_0(X)}{1410554953728},
\qquad
Q_1\ge\frac{J_1(X)}{170581728179578208256}.
\tag{B4}
\]

The following two arrays print every coefficient of \(J_0,J_1\).
They are exact coefficient sums in (B3), with no unlisted sign or
numerical extremum.

### B.1. First derivative lower polynomial

| Degree | \([X^i]J_0\) |
| ---: | ---: |
| 0 | 43766291587338682771672321682883019 |
| 1 | 2448144914634415056535668369010588620 |
| 2 | 15418727902730131055513878315645373040 |
| 3 | 39972381838729629770606574275885120256 |
| 4 | 61400164261486015749893659809360027840 |
| 5 | 66573843880722712066853566838068657824 |
| 6 | 52326177753350537264122404407975678976 |
| 7 | 30965828409559823708708415804284573184 |
| 8 | 13885226928894490909475449923055300608 |
| 9 | 4726431079894958051831012371829735424 |
| 10 | 1209960360095818558237204181615640576 |
| 11 | 228228253866589408478091120381788160 |
| 12 | 30579240170575198614793769636069376 |
| 13 | 2728994617272346968500712945745920 |
| 14 | 143379008005763867517682936971264 |
| 15 | 3271105611777392527743714852864 |

All coefficients are positive, so \(J_0(X)>0\) for \(X\ge0\).
This proves \(\partial_xF_0<0\).

### B.2. Second derivative lower polynomial

| Degree | \([X^i]J_1\) |
| ---: | ---: |
| 0 | 127244044898077633426718084509983225651621469644086857 |
| 1 | 2244404588736878011730685887196960032320416826887859146 |
| 2 | 15111737013630866539093918613109001190376158157702138696 |
| 3 | 66361205393307415286279693408288618376433638166700163360 |
| 4 | 207549038915223929959766945895619908748083643581375270768 |
| 5 | 451529185291162832692774923168429009988782902495054372736 |
| 6 | 792222975248997937300863220758362544449595263301430500288 |
| 7 | 1143007981372015354802592488279058181784426338903925223552 |
| 8 | 1349415792923497966372815215986971090260216379741548590080 |
| 9 | 1337007320043753453219483296787929900559838525649046862848 |
| 10 | 1123856329714274169223770752533180235783948677220970961920 |
| 11 | 799489859741036950767654586773173795992272931685484337152 |
| 12 | 478121798649886181023824242647675684405723466737710612480 |
| 13 | 237337600305676151369378548858656720915805466891031035904 |
| 14 | 95389362813958570274517062080010368362758190748233498624 |
| 15 | 29320497096206061847723094772155751412450502096093970432 |
| 16 | 5715880067273255442160743508715060431560614807404019712 |
| 17 | -653433164169413901629691467108053406961538525802004480 |
| 18 | -1210088751462315089524270836331218851685496896714964992 |
| 19 | -550528792981210468677957209295842784961825331239452672 |
| 20 | -167934691751611497000092543557402432114701635162210304 |
| 21 | -38781640219968853120102734842841973202619764563771392 |
| 22 | -6986687107707328784503588714542117717341638854967296 |
| 23 | -981986287687637841051634021190526873480458259136512 |
| 24 | -105894870458680694268653591190602266687523178676224 |
| 25 | -8469474227709342520485717469823584616940520341504 |
| 26 | -473026846867277356472481154119599080914882134016 |
| 27 | -16440032848791423852591898079388765561261391872 |
| 28 | -266936154244205709562464579896393285693865984 |

The coefficients through degree sixteen are positive. The constant
coefficient is larger than \(10^{53}\). There are twelve negative
coefficients, each of absolute value less than \(2\cdot10^{54}\),
and each multiplies \(X^i\) with \(i\ge17\). Thus, for
\(0\le X\le7/30<1/4\),

\[
J_1(X)>10^{53}-\frac{24\cdot10^{54}}{4^{17}}>0,
\]

where the last inequality is just \(240<4^{17}\).
This proves \(\partial_xF_1<0\). All denominators in (B1) are
positive throughout the full enlarged rectangle, so both derivative
signs have exactly the scope required in (16).

## Appendix C. Complete terminal polynomials and remainder arithmetic

The polynomials \(P_0,P_1\) are defined by the finite product identity
(20). For independent checking of the final arithmetic, their complete
coefficients \(P_j(a)=\sum_i p_{ji}a^i\) follow.

### C.1. Degree-fifteen polynomial

| Degree | \(p_{0i}\) |
| ---: | ---: |
| 0 | 71543553927246005456384000000000000 |
| 1 | 548876164961914900951356672000000000 |
| 2 | 895199242469792752555330463040000000 |
| 3 | -311798160382607976864137078426400000 |
| 4 | -1060684336414361934471034573978230000 |
| 5 | -660691601659731967773021820876177665 |
| 6 | -5096329481326818535181628277763772 |
| 7 | 314123654725740666617016262886766144 |
| 8 | 330283244354997150391199291321390856 |
| 9 | 139169941024706427989243615308675434 |
| 10 | -36925115552746747906610932933458816 |
| 11 | -64048387494951132243231701857452948 |
| 12 | -25752173731858985873589213006741048 |
| 13 | -2679336544111556569340909797641105 |
| 14 | 6463428286020010084541543711291100 |
| 15 | 1612345887705733634425715300072700 |

### C.2. Degree-twenty-two polynomial

| Degree | \(p_{1i}\) |
| ---: | ---: |
| 0 | -4331102522090019698408818359151244800000000000000 |
| 1 | -23456692584050199303161077009483139232000000000000 |
| 2 | -38591746871951521751350291382280863930760000000000 |
| 3 | 865671470454465363877443655367593685260500000000 |
| 4 | 71416998220728690223160868899786562729997785750000 |
| 5 | 84034470761791942817400417444980457158539648100625 |
| 6 | 25360491525542794119251638599492518984929255696125 |
| 7 | -49668218299206395089311230252243066368942484162121 |
| 8 | -81420348325529723706248947043944571364571934617809 |
| 9 | -45020870763463696883082160625303304606124336092270 |
| 10 | 11030804204964105396138695951199261541938651099438 |
| 11 | 34208306161500299775178207828125987909884580866334 |
| 12 | 24120223011050507548825169872469796853602891663774 |
| 13 | 3936194540515292418233756146213249054951087916517 |
| 14 | -6455559570124692588076646044791965335913373417303 |
| 15 | -5256093790066597705327153932923240790619396974261 |
| 16 | -1412381552275936571665884447149950874504416799229 |
| 17 | 502513097544648200443335528077020360596305888424 |
| 18 | 571723489042443410890725322545123020347195508316 |
| 19 | 139543309272256859629622058302378992000883001264 |
| 20 | -29209297308752935050862932134586075980753670960 |
| 21 | -17511335551257421054598661037384989732145075200 |
| 22 | -2014886717726705536829931900089042739278328000 |

### C.3. Translation and the three small norm estimates

For either polynomial and any rational centre t, its coefficients
about that centre are specified by the complete finite identity

\[
P(t+s)=\sum_{j=0}^n c_j(t)s^j,
\qquad
c_j(t)=\sum_{i=j}^n\binom ij p_i t^{i-j}.
\tag{C1}
\]

For \(P_0\) at \(t=7/6\), the first three coefficients are

\[
c_0=\frac{69651718624097211716655923475326148473}{6144},
\]
\[
c_1=\frac{33656401532688150409803374101112334639}{128},
\quad
c_2=\frac{18295709218713357403911276510149647289535}{2048}.
\]

They give \(c_0>0\), \(|c_1|<24c_0\), \(c_2>780c_0\) by
cross multiplication.

For \(P_1\) at \(t=21/20\), the positive constant is

\[
c_0=\frac{3590377528836827123115530964481083183093978902707785204142728488284493677}
 {5242880000000000000000000}>0.
\]

For \(P_1\) at \(t=11/10\), the first three coefficients are

\[
c_0=\frac{4306531516908451755727589714141905593259629513206910365582563247}
 {9765625000000000},
\]
\[
c_1=-\frac{4348800529975136826926843385162244275674816436115042180008089001}
 {1953125000000000},
\]
\[
c_2=\frac{455274498737238160286154888311688593115855910158688837738410562443}
 {3125000000000000}.
\]

These give \(c_0>0\), \(-6c_0<c_1<0\), and \(c_2>330c_0\).

The next table is a convenient small collection of integer bounds for
the remaining displayed coefficients. In column A the entry bounds

\[
100\,\frac{|c_j(7/6)|}{c_0(7/6)}6^{-(j-2)}
\quad\text{for }P_0,
\]

in column B it bounds

\[
100000\,\frac{|c_j(21/20)|}{c_0(21/20)}20^{-j}
\quad\text{for }P_1,
\]

and in column C it bounds

\[
1000\,\frac{(-c_j(11/10))_+}{c_0(11/10)}(7/30)^{j-2}
\quad\text{for }P_1.
\]

A dash means that the degree is outside the sum in question. Each
entry is an ordinary rational comparison using the fully printed
coefficients and (C1); there is no omitted coefficient family.

| Degree j | A | B | C |
| ---: | ---: | ---: | ---: |
| 1 | — | 26094 | — |
| 2 | — | 33647 | — |
| 3 | 25467 | 19679 | 0 |
| 4 | 549 | 4192 | 0 |
| 5 | 899 | 269 | 0 |
| 6 | 131 | 2 | 29686 |
| 7 | 11 | 2 | 20609 |
| 8 | 6 | 1 | 3113 |
| 9 | 1 | 1 | 0 |
| 10 | 1 | 1 | 0 |
| 11 | 1 | 1 | 0 |
| 12 | 1 | 1 | 0 |
| 13 | 1 | 1 | 0 |
| 14 | 1 | 1 | 1 |
| 15 | 1 | 1 | 1 |
| 16 | — | 1 | 1 |
| 17 | — | 1 | 1 |
| 18 | — | 1 | 1 |
| 19 | — | 1 | 1 |
| 20 | — | 1 | 1 |
| 21 | — | 1 | 1 |
| 22 | — | 1 | 1 |

The exact column sums of the printed integer bounds are respectively

\[
27070<28000,\qquad 83900<85000,\qquad 53417<54000.
\tag{C2}
\]

Dividing by the indicated normalizations proves all three remainder
bounds used in Section 6. This completes the central terminal sign
with every duration, shape endpoint and equality boundary included.
