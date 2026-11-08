# A hand sign for the central low-ratio corrected cap

**Replacement status, 2026-11-08:** the [new central proof](../../docs/lighter-proofs/SHORT_CENTRAL_COMPLETE.md)
replaces equations (20)--(25) and Appendices A--C under the requested
small-identity standard. It preserves the two original strict signs,
the actual domain and the duration caller. The old certificate-style
arguments below are retained as historical source material.

Date: 2026-11-08 UTC. **Result:** at the central scale cap, every
actual short shape with \(1<x\le2\) has corrected Casimir strictly
above \(9193/50000\), with correction coefficient \(7/96\).
The [separate reconstruction review](MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_AUDIT.md)
records the domain, signs and endpoints. This is the central scalar
face of S1; the outer faces and the actual-period comparison belong
to the [lower-ratio assembly](MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_EXCLUSION.md).

The proof removes duration by a tangent bound, the incoming norm by
strict decrease, beta by strict decrease, and alpha by monotonicity
or concavity. It ends in three one-variable signs. Five derivative
lower polynomials and three terminal polynomials are specified below,
with every coefficient used in their sign arguments displayed. Each
sign follows from one coefficient sign change and one positive
endpoint, or from positive coefficients alone. There is no parameter
cover, numerical extremum, or executable premise.

## 1. Actual face and scalar statement

Write \(a=\alpha\), \(b=\beta\), and assume the actual equal-secants
and orders from the [six-variable reduction](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md),
[strong order](MIXED_SMALLER_SHORT_STRONG_ORDER.md), and
[global upper order](MIXED_SMALLER_SHORT_GLOBAL_UPPER_ORDER.md):

\[
1\le a<x\le b\le ax,\qquad 1<x\le2,
\qquad a^2\le\frac{x(x+2)}6,
\tag{1}
\]
\[
x+\frac{8x(a-1)}{9x+8}\le b
\le x+\frac{x(7x+1)(a-1)}{4x^2+11x+1}.
\tag{2}
\]

The last inequality in (1) is exactly the central-cap condition
\(q_c\le1/7\). Put

\[
c_*=\frac7{96},\qquad g_* =\frac{9193}{50000},\qquad
S=x+1,\quad X=x(x+2),\quad Z=35x+13,
\]
\[
K=X+a^2,\quad B=a+b,\quad q=\frac{a^2}{K},\quad
k=\frac{aB}{K}=\frac1T,\quad
D=a^2+2ab+1+2x-2bx.
\tag{3}
\]

For an incoming norm u, the central upper-envelope quantities are

\[
E=S^3(u-1)+3S-1,
\qquad w=\frac{S^2(S^2-S+1)+D^2u-DE}{K^2},
\]
\[
E_L=\frac{2Du-E}{K},\qquad
\Gamma=\frac{4S^2(S^2-S+1)u-E^2}{16X^2},\qquad
J=(u-1)B/a+a/B+1-q-E_L,
\quad h=w-\frac34.
\tag{4}
\]

These are algebraic comparison quantities at the central scale.
No competitive cap is asserted for a different physical trajectory.
Define the exact logarithmic tests

\[
F_0(x,a,b,u)=\Gamma-c_*\{J+2h+\log(2k)\}-g_*,
\]
\[
F_1(x,a,b,u)=\Gamma-c_*\{J+Th+\log(2k)\}-g_*.
\tag{5}
\]

We prove that both are strictly positive at the original incoming
norm, throughout (1)--(2). Consequently, for every \(2\le\tau\le T\),

\[
\boxed{\Gamma-c_*R_\tau>g_*.}
\tag{6}
\]

Indeed \(R_2=J+2h+\log(2k)\), and the exact duration derivative is
\(R_\tau'=w-U(1/\tau)\le h\), where \(U(r)=1-r+r^2\).
Integrating from two gives

\[
R_\tau\le R_2+(\tau-2)h
\le\max\{R_2,R_2+(T-2)h\}.
\tag{7}
\]

Thus the left side of (6), minus g, is at least
\(\min(F_0,F_1)>0\), regardless of the sign of h. The endpoints
\(\tau=2,T\) are included.

## 2. A simple containing shape domain

Set

\[
a_U(x)=\frac{1013x+676}{2340}.
\tag{8}
\]

The central cap and \(a\ge1\) give
\(x\ge\sqrt7-1>23/14>8/5\), since
\(7>(37/14)^2\). Also

\[
a_U(x)^2-\frac{x(x+2)}6
 =\frac{(337x-676)^2}{2340^2}\ge0.
\]

Hence \(1\le a\le a_U(x)\le1351/1170<6/5\).
At \(x=23/14\), \(a_U=1+1/10920\), so the entire alpha interval
is nonempty on the enlarged actual x range. The useful cone inclusion
is the explicit inequality

\[
\frac{x+5}6-a_U(x)=\frac{1274-623x}{2340}
\ge\frac{28}{2340}>0\qquad(x\le2).
\tag{9}
\]

The beta interval (2) is contained in

\[
x+\frac47(a-1)\le b\le x+\frac{10}{13}(a-1).
\tag{10}
\]

For the lower endpoint, \(8x/(9x+8)\ge4/7\) is exactly
\(x\ge8/5\). For the upper endpoint, clearing positive factors gives

\[
13x(7x+1)-10(4x^2+11x+1)=(x-2)(51x+5)\le0.
\]

All u and beta derivative signs will be proved on the larger set

\[
\frac85\le x\le2,\qquad 1\le a\le\frac76,
\qquad b=x+c(a-1),\qquad\frac12\le c\le\frac45.
\tag{11}
\]

All alpha derivative signs will be proved on the simple cone

\[
\frac85\le x\le2,\qquad
1\le a\le\frac{x+5}6,\qquad
b=b_+(x,a):=x+\frac{10}{13}(a-1).
\tag{12}
\]

No equal-secant or actual-cap property is claimed at additional scalar
points in (11)--(12). Their denominators are positive. More explicitly,
\(b>1\), \(B,K,X>0\), and

\[
K-2aB\ge x^2-\frac x3-\frac{301}{180}
\ge\frac{319}{900}>0.
\tag{13}
\]

The first inequality follows by increasing b to
\(x+4(a-1)/5\) and then a to \(7/6\); the resulting expression
is decreasing in a. The last quadratic increases for \(x\ge8/5\).
Thus \(T>2\) on all of (11), including (12).

We also have \(0\le x-a\le1\), \(b\le32/15\), and therefore

\[
\frac{14}{15}\le
 a^2+1+2x-2b(x-a)=D
 \le\frac{229}{36}<7<S^3.
\tag{14}
\]

The lower bound uses \(a^2+1\ge2\), \(2x\ge16/5\), and
\(2b(x-a)\le64/15\). Consequently

\[
w_u=\frac{D(D-S^3)}{K^2}<0.
\tag{15}
\]

## 3. Replace the incoming norm, then beta

The rational incoming ceiling used here is

\[
u_\ell=\frac34+
 \frac{(x-1)^2(b+15x-16)}{8SZ(b-1)}
 =\frac34+\frac{2(x-1)^2}{SZ}
       \frac{x-1+(b-x)/16}{b-1}.
\tag{16}
\]

For the actual shapes (1)--(2), \(3/4<u\le u_\ell\). To prove the
upper inequality, use the [incoming norm estimate](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md):

\[
u-\frac34\le
\frac{2(x-1)^3/(SZ)+(b-x)^3/(48x^2)}{b-1}.
\]

It suffices that \((b-x)^2SZ\le6x^2(x-1)^2\). Write
\(R=4x^2+11x+1\). Since \(a<6/5\), the strong order gives
\(b-x\le x(7x+1)/(5R)\). The needed inequality follows from

\[
150R^2(x-1)^2-(7x+1)^2SZ>0.
\]

For \(v=x-3/2\ge0\), this last polynomial is exactly

\[
2400v^6+30000v^5+137635v^4+287768v^3
 +\frac{557379}{2}v^2+104452v+\frac{74855}{16},
\tag{17}
\]

which is positive. The strict lower norm bound follows directly
from the positive integral in the same incoming-norm note. The
ceiling (16) is asserted only for the original incoming norm.

Both functions in (5) have second u derivative

\[
(F_j)_{uu}=-\frac{S^6}{8X^2}<0.
\]

Also \((F_1)_u=(F_0)_u-c_*(T-2)w_u>(F_0)_u\).
Appendix A proves the uniform strict sign

\[
(F_1)_u\big|_{u=3/4}<0\qquad\text{on (11)}.
\tag{18}
\]

It follows that both functions strictly decrease for every
\(u\ge3/4\). Hence, for the actual incoming norm,

\[
F_j(x,a,b,u)\ge\widehat F_j(x,a,b),\qquad
\widehat F_j(x,a,b):=F_j(x,a,b,u_\ell).
\tag{19}
\]

Appendix A also proves, using the exact logarithm derivative,

\[
\partial_b\widehat F_0<0,\qquad
\partial_b\widehat F_1<0\qquad\text{on (11)}.
\tag{20}
\]

Therefore increasing beta to the endpoint in (10) gives

\[
\widehat F_j(x,a,b)\ge f_j(x,a),\qquad
f_j(x,a):=\widehat F_j(x,a,b_+(x,a)).
\tag{21}
\]

This is an inequality between scalar functions. No transported incident
norm ceiling, root equation, physical cost or competitive Casimir cap
is used on the beta segment.

## 4. Eliminate alpha and prove the terminal signs

Appendix B proves on the whole cone (12)

\[
\partial_a f_0<0,\qquad \partial_a^2 f_1<0.
\tag{22}
\]

The first inequality gives
\(f_0(x,a)\ge f_0(x,a_U(x))\). The second says that f1 is strictly
concave as a function of alpha, so on \([1,a_U(x)]\),

\[
f_1(x,a)\ge\min\{f_1(x,1),f_1(x,a_U(x))\}.
\tag{23}
\]

The interval inclusion needed in both comparisons is exactly (9).
It is not enough to use the larger rectangle for (22), and we do not
do so.

For \(0<y\le1\), set \(z=(y-1)/(y+1)\). The integrated
geometric identity gives

\[
\log y=2z+\frac23z^3+2\int_0^z\frac{t^4}{1-t^2}\,dt
\le \ell(y):=2z+\frac23z^3.
\tag{24}
\]

Because \(2k<1\) by (13), substituting \(\ell(2k)\) for the
logarithm lowers both f's. Let \(\overline f_j\) denote these
rational lower functions. Appendix C proves

\[
\overline f_0(x,a_U(x))>0,\qquad
\overline f_1(x,a_U(x))>0,\qquad
\overline f_1(x,1)>0
\tag{25}
\]

for \(23/14\le x\le2\), including x=2. Equations (19)--(25)
prove both tests (5) positive and therefore prove (6).

The logarithm is differentiated exactly in the monotonicity arguments;
its majorant is introduced only in these final one-variable tests.

## Appendix A. Three explicit derivative lower polynomials

All polynomials below are specified by the low-degree sums and
products (3)--(5),(16), together with quotient differentiation. For
clarity one can perform all rational differentiations using

\[
U=6SZ(b-1)+(x-1)^2(b+15x-16),\qquad
V=8SZ(b-1),\qquad u_\ell=U/V,
\]
\[
E_N=S^3(U-V)+(3S-1)V,\quad
W=S^2(S^2-S+1)V+D^2U-DE_N,
\]
\[
L=2DU-E_N,\quad
G_N=4S^2(S^2-S+1)UV-E_N^2.
\tag{A1}
\]

Then \(w=W/(K^2V)\), \(E_L=L/(KV)\), and
\(\Gamma=G_N/(16X^2V^2)\). The derivatives of the logarithm
are rational; in particular \(\partial_b\log(2k)=1/B\).
There is no implicit root derivative.

Define the positive clearing factors

\[
\Delta_u=96aX^2KB,
\]
\[
\Delta_{b0}=1536aX^2SZ^2K^2B^2(b-1)^3,
\qquad
\Delta_{b1}=1536aX^2SZ^2KB^2(b-1)^3.
\tag{A2}
\]

The following identities specify three polynomials completely:

\[
P_u=-\Delta_u(F_1)_u\big|_{u=3/4},\qquad
P_{b0}=-\Delta_{b0}\partial_b\widehat F_0,
\qquad
P_{b1}=-\Delta_{b1}\partial_b\widehat F_1.
\tag{A3}
\]

For Pu, a direct formula free of differentiation is

\[
\frac{P_u}{\Delta_u}=
 -\frac{4S^2(S^2-S+1)-2S^3(-S^3/4+3S-1)}{16X^2}
 +c_*\left\{\frac Ba-\frac{2D-S^3}{K}
                   +\frac{D(D-S^3)}{aBK}\right\}.
\tag{A4}
\]

Every denominator divides the clearing product in (A2). After
\(b=x+c(a-1)\), the degrees in \((x,a,c)\) are respectively
\((9,4,2)\), \((17,9,6)\), and \((15,7,5)\).
The coefficientwise lower bounds are small enough to print in full.

### A.1. Finite norm rule

Substitute

\[
x=8/5+z,\quad a=1+A,\quad
c=13/20+t,\quad0\le z\le2/5,
\quad0\le A\le1/6,\quad |t|\le3/20.
\tag{A5}
\]

For any of the three polynomials, write
\(P=\sum p_{ijk}z^iA^jt^k\), and define the exact rational numbers

\[
d_{ij}=p_{ij0}-\sum_{k\ge1}|p_{ijk}|(3/20)^k,
\qquad
l_i=d_{i0}+\sum_{j\ge1}\min(d_{ij},0)6^{-j}.
\tag{A6}
\]

The triangle inequality first bounds the t terms, and then each
negative coefficient of \(A^j\) is bounded at \(A=1/6\), while
positive higher terms are discarded. Thus
\(P\ge\sum_i l_i z^i\). This is a finite coefficient identity and
inequality, not an extremum assertion. The coefficients are obtained
from (A1)--(A4) by the binomial formula.

The complete resulting lower polynomials are

\[
P_u\ge\frac{H_u(z)}{20250000000},\qquad
P_{b0}\ge2430z^{17}+\frac{H_{b0}(z)}{393660000000000000000},
\]
\[
P_{b1}\ge\frac{H_{b1}(z)}{87480000000000000}.
\tag{A7}
\]

The displayed positive degree-seventeen term is discarded below.
The following tables give every coefficient of the three H's in
ascending powers of z.

### A.2. Incoming-norm derivative

| Degree | Coefficient |
| ---: | ---: |
| 0 | 27473889096 |
| 1 | 83935985320800 |
| 2 | 459662517751900 |
| 3 | 919263007944500 |
| 4 | 945383470035625 |
| 5 | 562270347225000 |
| 6 | 200222502187500 |
| 7 | 41813358750000 |
| 8 | 4673700000000 |
| 9 | 212625000000 |

All ten coefficients are positive, so Pu is strictly positive on
(A5). The denominator in (A3) is positive, proving (18).

### A.3. First beta derivative

| Degree | Coefficient |
| ---: | ---: |
| 0 | 103044300994856354355034220304 |
| 1 | 1475594942261419206268725024000 |
| 2 | 9207162939727384766998060450500 |
| 3 | 33453184691508377363128050033000 |
| 4 | 79544581153930054041299137773125 |
| 5 | 131537287321187434026965422878125 |
| 6 | 156595768145456242131969263546875 |
| 7 | 136583497952581973971852605859375 |
| 8 | 87795108419369521836964275000000 |
| 9 | 41693059822821878400428812500000 |
| 10 | 14342321618773554834700312500000 |
| 11 | 3413063879419855635000000000000 |
| 12 | 500389896949641891000000000000 |
| 13 | 27012255548451840000000000000 |
| 14 | -4421970803256721875000000000 |
| 15 | -896501089242000000000000000 |
| 16 | -37403309655000000000000000 |

### A.4. Second beta derivative

| Degree | Coefficient |
| ---: | ---: |
| 0 | 2689852893976657502396352 |
| 1 | 35158746768562938883563072 |
| 2 | 201383881695310966909437060 |
| 3 | 672709453128458886574062600 |
| 4 | 1473986438566256876492445625 |
| 5 | 2248451201926217212742180625 |
| 6 | 2462445655901449993312396875 |
| 7 | 1965984555533141448959359375 |
| 8 | 1148415221447597710240312500 |
| 9 | 487030647605983515000000000 |
| 10 | 146636432182818432000000000 |
| 11 | 29913954626448000000000000 |
| 12 | 3728331500112000000000000 |
| 13 | 203235810480000000000000 |
| 14 | -7043714640000000000000 |
| 15 | -1073379600000000000000 |

Here is the elementary sign argument used for these and the remaining
tables. If \(H(z)=\sum h_i z^i\), with positive coefficients through
m and negative coefficients thereafter, and \(0<z\le r\), then

\[
H(z)\ge(z/r)^mH(r).
\tag{A8}
\]

This follows term by term: for i at most m, \((z/r)^i\ge(z/r)^m\);
for i greater than m the inequality reverses and its coefficient is
negative. At z=0 the positive constant treats the endpoint.
For the two beta polynomials m=13, r=2/5, and direct substitution
of the printed coefficients gives

\[
H_{b0}(2/5)=8626032544594062064501772782992>0,
\]
\[
H_{b1}(2/5)=166990609393267037338303616>0.
\tag{A9}
\]

Thus both are strictly positive. Equations (A2)--(A3),(A7) prove
both signs (20), including a=1; the apparent factor a−1 that arises
if one differentiates the c parametrization cancels identically
before the derivative polynomial is defined.

## Appendix B. The alpha monotonicity and concavity

Here substitute \(b=b_+(x,a)\), \(u=u_\ell(x,b_+)\), and retain
the exact logarithm in \(f_0,f_1\). Put

\[
Y=10a+13x-23=13(b_+-1),\qquad
H=23a+13x-10=13(a+b_+).
\]

Define the two positive clearing factors

\[
\Delta_{a0}=64896a^2X^2SZ^2Y^3H^2K^3,
\qquad
\Delta_{a1}=4992a^3X^2SZ^2Y^4H^3K^3,
\tag{B1}
\]

and the complete finite derivative polynomials

\[
P_{a0}=-\Delta_{a0}\partial_a f_0,
\qquad
P_{a1}=-\Delta_{a1}\partial_a^2 f_1.
\tag{B2}
\]

The definitions (3)--(5),(16),(21),(B1) specify these by rational
products and quotient differentiation. No logarithm remains, since
its first derivative is \(k_a/k\) and its second derivative is
\((k_{aa}k-k_a^2)/k^2\). Their degrees in \((x,a)\) are
\((19,11)\) and \((22,13)\).

Parametrize exactly the cone (12) by

\[
x=8/5+z,\qquad a=1+A(x-1)/6,
\qquad0\le z\le2/5,\quad0\le A\le1.
\tag{B3}
\]

Writing either polynomial after substitution as
\(P=\sum p_{ij}z^iA^j\), the elementary lower polynomial is

\[
P\ge\sum_i\left[p_{i0}+\sum_{j\ge1}\min(p_{ij},0)\right]z^i.
\tag{B4}
\]

Every coefficient of these two exact lower polynomials is printed
next, with the normalization

\[
P_{a0}\ge\frac{H_{a0}(z)}{6919804687500000000000},\qquad
P_{a1}\ge\frac{H_{a1}(z)}{3113912109375000000000000}.
\tag{B5}
\]

### B.1. Monotonicity of f0

| Degree | Coefficient |
| ---: | ---: |
| 0 | 169962826552074851227040131884173424384 |
| 1 | 2475636156310674554681097701448039893760 |
| 2 | 16630558290473529975830497060813035763200 |
| 3 | 68319317859833017213031898761942312640000 |
| 4 | 192914245521879214800775992266175933600000 |
| 5 | 371759049200317748686946094393192412800000 |
| 6 | 517515635553870686052614715736515018000000 |
| 7 | 558098845223223439116254401451072100000000 |
| 8 | 476417045043189040609987471714875750000000 |
| 9 | 327723310690152430303245160931805000000000 |
| 10 | 184447010064630320087776572417401250000000 |
| 11 | 85961908205779578562525185407137500000000 |
| 12 | 33401898024268548477890791966640625000000 |
| 13 | 9224382391101240287721956874184570312500 |
| 14 | 2014626203598839565950168137976074218750 |
| 15 | 362132412533996014241220519836425781250 |
| 16 | 41306604948366677516432088470458984375 |
| 17 | 3080598319476060186487712860107421875 |
| 18 | 141171506633966220849151611328125000 |
| 19 | 3075190990323851953125000000000000 |
| 20 | -87055700550037193298339843750 |

The coefficients through degree nineteen are positive, and the last
is negative. Its endpoint value is

\[
H_{a0}(2/5)=20394803157477269554899422258867302173952>0.
\tag{B6}
\]

Equation (A8), with m=19, proves positivity throughout the cone.
Therefore \(\partial_a f_0<0\).

### B.2. Concavity of f1

| Degree | Coefficient |
| ---: | ---: |
| 0 | 2121739182669444601359680412256987126995717 |
| 1 | 31886215800156564385961968098215691533209875 |
| 2 | 220651377848247766100649899859383339498528925 |
| 3 | 929977314851871229573249377878544130611421875 |
| 4 | 2624195031801827866392703428994519330757296875 |
| 5 | 4976797264365039283910388926253946612209328125 |
| 6 | 6642263084541393226565249707742946610199296875 |
| 7 | 5719363009482909708071758873896238942583203125 |
| 8 | 1628832826905850432932774797602762528394531250 |
| 9 | -4832113859933428359093612632326171593925781250 |
| 10 | -10507012524312045123543048327208201762324218750 |
| 11 | -12051559512658998317232215496847323953613281250 |
| 12 | -9795669870717101386420179729517036885253906250 |
| 13 | -6067655058391742871122261516042358142089843750 |
| 14 | -2940170252550586522468806113061732971191406250 |
| 15 | -1123755839629679243692144625851124450683593750 |
| 16 | -338082807725286154125728685191036224365234375 |
| 17 | -79210498358668493011266826175823211669921875 |
| 18 | -14160097956157679758409464967327117919921875 |
| 19 | -1865837604858152161543895640850067138671875 |
| 20 | -170795184581063624691209900379180908203125 |
| 21 | -9699267731706021453156950473785400390625 |
| 22 | -257496068370314295792925357818603515625 |
| 23 | -20424933928092528641223907470703125 |

The coefficients through degree eight are positive, and all later
ones are negative. The endpoint value is

\[
H_{a1}(2/5)=262397325589616003343306935335175654646853007>0.
\tag{B7}
\]

Equation (A8), now with m=8, proves positivity. Thus
\(\partial_a^2f_1<0\), completing (22).

## Appendix C. Three terminal one-variable polynomials

This appendix applies only the rational logarithm bound (24).
Define the five low-degree factors

\[
M=1013x+676,\quad N=4055x-4706,\quad P=53719x-7852,
\]
\[
K_U=6501769x^2+12320776x+456976,
\]
\[
L_U=193357691x^2+216890024x-4675216.
\tag{C1}
\]

All are positive for \(x\ge8/5\). The positive clearing factors are

\[
D_{0U}=1622400000\,X^2SZ^2MN^2PK_U^2L_U^3,
\]
\[
D_{1U}=124800000\,X^2SZ^2MN^2PK_UL_U^3,
\qquad
D_{1b}=7200000\,X^2S^4(x+3)^3Z^2.
\tag{C2}
\]

Let z=x−8/5. The following exact identities, with the rational
functions defined in (3)--(5),(16),(21),(24), fix every normalization:

\[
\overline f_0(x,a_U)=
 \frac{Q_{0U}(z)}{762939453125\,D_{0U}},\qquad
\overline f_1(x,a_U)=
 \frac{Q_{1U}(z)}{30517578125\,D_{1U}},
\]
\[
\overline f_1(x,1)=
 \frac{Q_{1b}(z)}{48828125\,D_{1b}}.
\tag{C3}
\]

The coefficients below are the full polynomial products in (C3),
not bounds on an unprinted coefficient family. All signs follow by
(A8) on the single interval \(0\le z\le2/5\). This polynomial
interval is slightly larger than the actual terminal x interval;
no trajectory is asserted at its extra points.

### C.1. First test at aU

| Degree | Coefficient |
| ---: | ---: |
| 0 | 770414544197719807001923229582095986115461724912247634860393216177066318971797504 |
| 1 | 8798772642581888682201147833652084470903480944788051873259558608669689400703057920 |
| 2 | 41862166645616081019288504387340816473735643809150735821863442326457170322364825600 |
| 3 | 98377201365176397617302944492506487434362367786535027249187025609611261432037376000 |
| 4 | 59264848629426296915458123439420501692039035927286025650892399860636996095836160000 |
| 5 | -362201120285027409918568441183896557127188449240904696776602274695487900768665600000 |
| 6 | -1409220131077910893030845222676812523633016721773077921707871646305525901952000000000 |
| 7 | -2897655498625520133786041196357228134908216233398960365055539539987771512939520000000 |
| 8 | -4151539153823878002439087939500776917466647919191300197803034330159644465803200000000 |
| 9 | -4495681459385183266215092393918996202251153490065984679863594142970127001192000000000 |
| 10 | -3818558510916911898331242798180920747841534400420545890363866103325017185057500000000 |
| 11 | -2595256213193031663442904645823977605436629648317520462153332425783646656887500000000 |
| 12 | -1427376915144649113651132056627946634056832640259315677562218414680391532292968750000 |
| 13 | -639231326106242018572898474849064853858132671871184002465041992122387217753906250000 |
| 14 | -233798201272535935427224745632749037400136018078529338061465133988541716082763671875 |
| 15 | -69924360857329581514777479126512143380433190962785895152082768238106716766357421875 |
| 16 | -17115736224791838817296837251647957085171728543176673506773354686892583618164062500 |
| 17 | -3434793666500899696133969519568176605878385956664815996414539285686605834960937500 |
| 18 | -566608965207093498602432938045721654113159391682247422170300432309440612792968750 |
| 19 | -76768503243916616566725178678370725824664642501654022372304734791984558105468750 |
| 20 | -8398971623181244045223837061059897855533496189673475291268848847198486328125000 |
| 21 | -702296572940922538546677124078860027742401322448513780873610778808593750000000 |
| 22 | -39542092179778629880861120388604006954937185600770352167373454570770263671875 |
| 23 | -1102241630632933318939110846380528158639465116121736809862315654754638671875 |

There is exactly one sign change, after degree four. Its endpoint is

\[
Q_{0U}(2/5)=
135093062839526513389575368426290648980427879579036289202776648487500000000000000>0.
\tag{C4}
\]

Therefore \(Q_{0U}>0\) by (A8), including z=0 and z=2/5.

### C.2. Second test at aU

| Degree | Coefficient |
| ---: | ---: |
| 0 | 48311002800954145671717868149328060730405574444739844860808556359712768 |
| 1 | 540244915848808852604271282435204432800160150864145845622359642215546880 |
| 2 | 2504520409962585914777667121896939115286335690714250229440314626854092800 |
| 3 | 5734507356466835991285976397638500592049486781495031766719370186784768000 |
| 4 | 3692634284788956689003559767873801574267594548203102323634518648545280000 |
| 5 | -17221059939427919324065199213002343277382540443834206459965566058905600000 |
| 6 | -64407972932219767363081619926582870454566685105618189996906428824576000000 |
| 7 | -122554380803305441648031271609553474949727167921688679859201349908160000000 |
| 8 | -159477682514246328461282217389990161891042295068548609649682489225100000000 |
| 9 | -154281362700001156221164728837867335998212425482293990250976127329750000000 |
| 10 | -115143982797135159513001757866866459263071757262664400252606537131875000000 |
| 11 | -67590619682483020659845706741960720085416076272092515018463544957421875000 |
| 12 | -31540027259110669080547655817224408740712544865451141592618070193115234375 |
| 13 | -11766885054460856279873971899309201043799273864007672428085207308349609375 |
| 14 | -3520532562724229267975948475777811330118802776275536017596264672851562500 |
| 15 | -846199071065465786085356514781493768589173756224789225289173461914062500 |
| 16 | -163521952732557393774693804321506286233949047978916753263696594238281250 |
| 17 | -25324209681978833961457540969765929650580348473813954782893371582031250 |
| 18 | -3091330503265430835865078300046821140574902439655527882492065429687500 |
| 19 | -283125008784493055599129960552097893923623091427860729141235351562500 |
| 20 | -17293748719023930871603588589815570044836419034116368770599365234375 |
| 21 | -521629222699206143359592820108131356790136116977365016937255859375 |

Again there is exactly one sign change, after degree four, and

\[
Q_{1U}(2/5)=
325233875669988611221652359259540287328583122634199583810375000000000000>0.
\tag{C5}
\]

Equation (A8) proves \(Q_{1U}>0\) on the entire interval.

### C.3. Second test at a=1

| Degree | Coefficient |
| ---: | ---: |
| 0 | 623158425047746827981 |
| 1 | 2039129125615240677765 |
| 2 | 739060420676079647025 |
| 3 | -6951728241514390818375 |
| 4 | -16364338190066057653125 |
| 5 | -18225196035243720721875 |
| 6 | -11330571778885589578125 |
| 7 | -3054057903675850859375 |
| 8 | 1034235481469698046875 |
| 9 | 1418512549226240234375 |
| 10 | 698752625966787109375 |
| 11 | 207650241310888671875 |
| 12 | 40002544010986328125 |
| 13 | 4910339193115234375 |
| 14 | 350565948486328125 |
| 15 | 11111297607421875 |

The terms of degrees eight through fifteen are all positive.
Discard them, obtaining a degree-seven polynomial \(Q^-_{1b}\).
It has positive coefficients through degree two and negative
coefficients thereafter. Its exact endpoint is

\[
Q^-_{1b}(2/5)=455182279602810165163>0.
\tag{C6}
\]

Thus \(Q_{1b}\ge Q^-_{1b}>0\) by (A8) with m=2.
The denominators in (C3) are positive, so all three inequalities
(25) follow. In particular the x=2 boundary is strictly excluded;
none of these steps merely proves a nonnegative limiting test.
