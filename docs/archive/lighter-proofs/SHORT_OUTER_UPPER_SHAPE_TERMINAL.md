# The shared outer S1 face a=6/5

This note supplies the upper shape boundary for the A and B branches in
the original [outer low-ratio sign](../../archive/notes/MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN.md).
On
\[
 3/2\le x\le2,\qquad a=6/5,\qquad \beta=x+C/5,
 \qquad3/4\le u\le19/25,
\]
we prove
\[
 F_0>1/2000\quad(C=10/13),\qquad
 F_1>1/2000\quad(1/2\le C\le10/13).
 \tag{1}
\]
The exact rational functions and the single cubic logarithm majorant are
those printed in [the S-branch source](SHORT_OUTER_S_BETA.md), Section 1.
In particular, \(c=7/96\), \(g=9193/50000\),
\(\ell(y)=8(y^3-1)/(3(y+1)^3)\), \(S=x+1\), and
\(y=2(a+\beta)/(7a)\). Here \(2/3\le y<4/5\), so
\(\log y\le\ell(y)\), \(\ell''(y)\ge-1/y^2\).

Norm concavity reduces u to the two constant endpoints. For F1,
[wide-norm beta concavity](SHORT_OUTER_BETA_WIDE_NORM.md) then reduces C
to 1/2 and 10/13. Thus every remaining sign is univariate in x. We first
print its source identity, then its separate curvature bound, then its
scalar endpoints. The F1 curvature uses one split at x=5/3.

## 1. The two F0 source identities

The following small source inputs make the substitutions explicit. In
this note \(a=6/5\) and \(K=241/25\). Set \(J_n=SJ\), where
\(J=K[S(u-1)+1/S]+2S-1\). The complete polynomials needed are
\[
 M=x^2-191x/25+52681/625,
\]
\[
 J_{n,f}=(-41x^2-182x+823)/100,\qquad
 J_{n,v}=(-196x^2-1017x+5204)/625,
\]
\[
 D_h=-2x^2+21x/5+67/25,\qquad
 D_t=-2x^2+266x/65+913/325.
\]
Here h,t denote C=1/2,10/13. Each polynomial has three monomials and
degree two. The original source functions are now the short circuit
\[
 \Gamma=\frac{4uS^2M-J_n^2}{576a^4S^2},\quad
 w=\frac{SM+uSD^2-DJ_n}{49a^4S},\quad
 E_L=\frac{2uDS-J_n}{7a^2S}.
\]
Collect these degree-two inputs before expanding any products. When a
linear pole L is used below, cancel L/B=10 or 65 before expansion.
The source-to-N checks then have at most 99 raw summands for F0 and
141 for F1, all of degree at most six. Their largest individual integer
coefficient is 400639005000. The collected numerators each have seven
monomials. This staging supplies the original-source link for (2) and
Section 3 without a larger hidden identity.

Here C=10/13. Set \(L=65x+88\) and
\[
 \widetilde Q_u=F_0+c\ell(y)+g+\frac{91}{16L}.
\]
The added last term is exactly \(ca/(a+\beta)\). It is separated before
any denominator clearing. At the two norm endpoints the complete source is
\[
 \widetilde Q_f=\frac{N_f}{14129676288S^2},\qquad
 \widetilde Q_v=\frac{N_v}{551940480000S^2}.
 \tag{2}
\]
The subscripts f and v throughout this note denote u=3/4 and u=19/25.
\[
\begin{aligned}
N_f={}&- 60840000 x^{6} + 143925600 x^{5} + 116313857 x^{4}\\
{}&- 569512532 x^{3} + 3262396038 x^{2} + 6214844620 x\\
{}&+ 1372030625
\end{aligned}
\]
This source numerator has seven monomials and degree six.

\[
\begin{aligned}
N_v={}&- 2408250000 x^{6} + 5535660000 x^{5} + 4472851872 x^{4}\\
{}&- 22291588512 x^{3} + 127729904657 x^{2} + 243446913588 x\\
{}&+ 53952839172
\end{aligned}
\]
This source numerator has seven monomials and degree six.


Polynomial division, with S left as a factor, gives
\[
 \widetilde Q_u=P_u(x)-\frac{A}{S}-\frac{K_2}{S^2},\qquad
 A=\frac{3363155}{33965568},\qquad K_2=\frac{58081}{746496}.
 \tag{3}
\]
The complete quartics are:
\[
\begin{aligned}
P_f={}&- \frac{625 x^{4}}{145152} + \frac{212825 x^{3}}{11321856}\\
{}&- \frac{354057343 x^{2}}{14129676288} -  \frac{7055747 x}{784982016}\\
{}&+ \frac{3870460273}{14129676288}
\end{aligned}
\]
\[
\begin{aligned}
P_v={}&- \frac{475 x^{4}}{108864} + \frac{79 x^{3}}{4212}\\
{}&- \frac{287983711 x^{2}}{11498760000} -  \frac{6506917 x}{718672500}\\
{}&+ \frac{151547747297}{551940480000}
\end{aligned}
\]

Each identity (3), cleared only by the denominator in (2), has seven
monomials and degree six. The largest individual expanded coefficient
in this division is 303095494594. The pole L and the logarithm remain
outside this identity.

## 2. A separate F0 curvature bound

The complete normalized second derivatives of the two quartics are
\[
\begin{aligned}
14129676288P_f''={}&- 730080000 x^{2} + 1593633600 x - 708114686
\end{aligned}
\]
At x=3/2, the second and third derivatives are respectively \(\frac{2832551}{1009262592}\) and \(- \frac{79675}{1886976}\).

\[
\begin{aligned}
551940480000P_v''={}&- 28899000000 x^{2} + 62112960000 x - 27646436256
\end{aligned}
\]
At x=3/2, the second and third derivatives are respectively \(\frac{10421953}{11498760000}\) and \(- \frac{1751}{39312}\).


Both second-derivative polynomials have three monomials and degree two.
Their leading coefficients are negative, so their first derivatives
decrease. The displayed endpoint values prove
\(P_u''<3/1000\) on the whole interval.

Since y is affine in x, the logarithm curvature bound gives
\[
 F_0''\le P_u''-\frac{2A}{S^3}-\frac{6K_2}{S^4}
 -\frac{2\cdot91\cdot65^2}{16L^3}+\frac{c}{(a+\beta)^2}.
\]
Discard the negative L-pole. The remaining bounds use only S<=3 and
\(a+\beta\ge371/130\):
\[
 \frac{c}{(a+\beta)^2}\le\frac{118300}{13213536}<\frac9{1000},
 \qquad \frac{2A}{27}+\frac{6K_2}{81}>\frac{13}{1000}.
\]
Thus \(F_0''<-1/1000\). Concavity reduces each fixed-norm F0 sign to
x=3/2 and x=2. The endpoint bounds are supplied in Section 5.

## 3. Four F1 source identities with staged division

Put \(Q=F_1+c\ell(y)+g\). For C=1/2 let L=10x+13, and for C=10/13
let L=65x+88. The four complete source identities are
\(Q=N/(dS^2L)\). The positive scalar d is stated with each polynomial.

For \(C=\frac{1}{2},\ u=\frac{3}{4}\), \(d=11943936\):
\[
\begin{aligned}
N_{hf}={}&- 2160000 x^{6} + 3033590 x^{5} + 11083707 x^{4}\\
{}&+ 11063704 x^{3} + 58674394 x^{2} + 64719690 x\\
{}&+ 8430995
\end{aligned}
\]
This source numerator has seven monomials and degree six.

For \(C=\frac{1}{2},\ u=\frac{19}{25}\), \(d=466560000\):
\[
\begin{aligned}
N_{hv}={}&- 85500000 x^{6} + 114630840 x^{5} + 428266452 x^{4}\\
{}&+ 439934258 x^{3} + 2319301187 x^{2} + 2553333708 x\\
{}&+ 336929292
\end{aligned}
\]
This source numerator has seven monomials and degree six.

For \(C=\frac{10}{13},\ u=\frac{3}{4}\), \(d=155271168\):
\[
\begin{aligned}
N_{tf}={}&- 182520000 x^{6} + 236682355 x^{5} + 941984476 x^{4}\\
{}&+ 1018884514 x^{3} + 5070712676 x^{2} + 5672017379 x\\
{}&+ 819547592
\end{aligned}
\]
This source numerator has seven monomials and degree six.

For \(C=\frac{10}{13},\ u=\frac{19}{25}\), \(d=6065280000\):
\[
\begin{aligned}
N_{tv}={}&- 7224750000 x^{6} + 8908255980 x^{5} + 36377918016 x^{4}\\
{}&+ 40407862639 x^{3} + 200326991396 x^{2} + 223686640164 x\\
{}&+ 32668712496
\end{aligned}
\]
This source numerator has seven monomials and degree six.

The partial fractions must be verified in two stages. First divide by
the cubic S²L, keeping the proper numerator primitive:
\[
 Q=P(x)+H\frac{V(x)}{S^2L}.
 \tag{4}
\]
The complete P,H,V for the four cases follow. This stage uses polynomials
of degree six with at most seven monomials. It never multiplies by the
additional constant 23 occurring in the later pole separation.

For case \(hf\):
\[
\begin{aligned}
P_{hf}={}&- \frac{125 x^{3}}{6912} + \frac{1016159 x^{2}}{11943936}\\
{}&- \frac{244559 x}{1990656} + \frac{12856331}{59719680}
\end{aligned}
\]
\[H_{hf}=\frac{1}{3732480}.\]
\[
\begin{aligned}
V_{hf}={}&4199152 x^{2} -  2740716 x - 7811083
\end{aligned}
\]

For case \(hv\):
\[
\begin{aligned}
P_{hv}={}&- \frac{95 x^{3}}{5184} + \frac{1102169 x^{2}}{12960000}\\
{}&- \frac{2388793 x}{19440000} + \frac{101459729}{466560000}
\end{aligned}
\]
\[H_{hv}=\frac{1}{93312000}.\]
\[
\begin{aligned}
V_{hv}={}&103846438 x^{2} -  70782624 x - 196409437
\end{aligned}
\]

For case \(tf\):
\[
\begin{aligned}
P_{tf}={}&- \frac{125 x^{3}}{6912} + \frac{13058867 x^{2}}{155271168}\\
{}&- \frac{3149027 x}{25878528} + \frac{172132991}{776355840}
\end{aligned}
\]
\[H_{tf}=\frac{1}{48522240}.\]
\[
\begin{aligned}
V_{tf}={}&303133442 x^{2} -  300658291 x - 690622828
\end{aligned}
\]

For case \(tv\):
\[
\begin{aligned}
P_{tv}={}&- \frac{95 x^{3}}{5184} + \frac{4720649 x^{2}}{56160000}\\
{}&- \frac{30755059 x}{252720000} + \frac{1357391987}{6065280000}
\end{aligned}
\]
\[H_{tv}=\frac{1}{93312000}.\]
\[
\begin{aligned}
V_{tv}={}&575965406 x^{2} -  592156063 x - 1335104344
\end{aligned}
\]

Now separate only the primitive quadratic V. The complete identities are
\[
\begin{aligned}
\frac{V_{hf}}{S^2L}={}&- \frac{2744990}{x + 1} + \frac{31649052}{10 x + 13}\\
{}&- \frac{290405}{x^{2} + 2 x + 1}
\end{aligned}
\]
\[
\begin{aligned}
\frac{V_{hv}}{S^2L}={}&- \frac{68624750}{x + 1} + \frac{790093938}{10 x + 13}\\
{}&- \frac{7260125}{x^{2} + 2 x + 1}
\end{aligned}
\]
\[
\begin{aligned}
\frac{V_{tf}}{S^2L}={}&- \frac{661532950}{23 x + 23} + \frac{49971710916}{1495 x + 2024}\\
{}&- \frac{3775265}{x^{2} + 2 x + 1}
\end{aligned}
\]
\[
\begin{aligned}
\frac{V_{tv}}{S^2L}={}&- \frac{1272178750}{23 x + 23} + \frac{95938823088}{1495 x + 2024}\\
{}&- \frac{7260125}{x^{2} + 2 x + 1}
\end{aligned}
\]

These four identities clear to quadratics, with three monomials. For the
last two identities clear the scalar 23 only at this quadratic stage.
The largest individual coefficient is 194643348750. In the preceding
cubic division the largest individual coefficient is 327131468867.
Combining the two proved identities is rational addition; a global
coefficient expansion of all their denominators is not required.

## 4. A separate F1 curvature bound

In each of the four cases, the preceding identities have the form
\[
 Q=d_3x^3+d_2x^2+d_1x+d_0+
 \frac{A}{S+\delta}-\frac{B_0}{S}-\frac{K_2}{S^2},
 \quad\delta=(1+C)/5,\quad K_2=58081/746496.
\]
Thus \(A,B_0>0\). The printed fractions give, by direct scalar comparison,
\[
 d_3\le-125/6912,\quad 2d_2<171/1000,\quad
 B_0>59/100,\quad A/B_0<7/6,\quad K_2>7/90,
 \quad 3/10\le\delta\le23/65.
 \tag{5}
\]
For clarity the A/B comparisons cancel H first. Their four remaining
fractions, in the order hf,hv,tf,tv, are
\[
 \frac{31649052}{10\cdot2744990},\quad
 \frac{790093938}{10\cdot68624750},\quad
 \frac{49971710916}{65\cdot661532950},\quad
 \frac{95938823088}{65\cdot1272178750}.
\]
Comparing each with 7/6 requires integer products of at most twelve digits.
The other comparisons in (5) have smaller products.

The logarithm correction is at most \(c/(S+\delta)^2\), because y is
affine in x. Therefore
\[
 F_1''\le-\frac{125x}{1152}+\frac{171}{1000}
 -\frac{2B_0}{S^3}\left[1-\frac{A}{B_0}
                  \left(\frac S{S+\delta}\right)^3\right]
 -\frac{6K_2}{S^4}+\frac{c}{(S+\delta)^2}.
 \tag{6}
\]
The bracket is positive on the whole interval: S<=3 and delta>=3/10
give its subtracted term at most \((7/6)(10/11)^3<1\).
Also \(c/(S+\delta)^2\le25/2688\), using \(S+\delta\ge14/5\).

For x>=5/3, discard both negative reciprocal terms in (6). This gives
\[
 F_1''<\frac{171}{1000}-\frac{625}{3456}+\frac{25}{2688}
 =-\frac{823}{1512000}<-\frac1{2000}.
\]
For x<=5/3, use S<=8/3 and
\[
 1-\frac76\left(\frac{80}{89}\right)^3>\frac3{20},
 \qquad20(6\cdot89^3-7\cdot80^3)-18\cdot89^3=226838>0.
\]
Substitution in (6) yields the entirely scalar upper bound
\[
 \frac{171}{1000}-\frac{125}{768}+\frac{25}{2688}
 -2\frac{59}{100}\frac3{20}\left(\frac38\right)^3
 -6\frac7{90}\left(\frac38\right)^4
 =-\frac{229}{224000}<-\frac1{1000}.
\]
Thus all four F1 functions are strictly concave in x. Their minima
are attained at x=3/2 or x=2; no endpoint at the curvature split is needed.

## 5. Scalar endpoints with small cross-products

The following displays give exact source values
\((\Gamma,w,E_L,\ell)\), followed by directed rational bounds
\((G,W,E,l)\) with \(\Gamma\ge G,w\le W,E_L\ge E,\ell\le l\).
Set \(p=a/(a+\beta)\) and \(r=(u-1)(a+\beta)/a\); their exact values
are also printed. Then the two lower bounds are obtained without a
large common source denominator:
\[
\begin{aligned}
 F_0&\ge G-c[2W-1/2+r+p-1/7-E+l]-g=:L_0,\\
 F_1&\ge G-c[6/7+r-E+l+p(7W-17/4)]-g=:L_1.
\end{aligned}
\tag{7}
\]
Every required lower bound below is greater than 1/2000.

At \((C,x,u)=(\frac{1}{2},\frac{3}{2},\frac{3}{4})\):
\[
(\Gamma,w,E_L,\ell)=\left(\frac{221886239}{1194393600},\ \frac{113791}{141120},\ \frac{4889}{10080},\ - \frac{152}{375}\right),
\]
\[
(G,W,E,l)=\left(\frac{371}{2000},\ \frac{807}{1000},\ \frac{97}{200},\ - \frac{81}{200}\right),
\quad(p,r)=\left(\frac{3}{7},- \frac{7}{12}\right).
\]
\[L_1=\frac{20533}{7200000}>\frac1{2000}.\]

At \((C,x,u)=(\frac{1}{2},\frac{3}{2},\frac{19}{25})\):
\[
(\Gamma,w,E_L,\ell)=\left(\frac{3}{16},\ \frac{62539}{78400},\ \frac{47}{100},\ - \frac{152}{375}\right),
\]
\[
(G,W,E,l)=\left(\frac{3}{16},\ \frac{399}{500},\ \frac{47}{100},\ - \frac{81}{200}\right),
\quad(p,r)=\left(\frac{3}{7},- \frac{14}{25}\right).
\]
\[L_1=\frac{9661}{2400000}>\frac1{2000}.\]

At \((C,x,u)=(\frac{1}{2},2,\frac{3}{4})\):
\[
(\Gamma,w,E_L,\ell)=\left(\frac{19625567}{107495424},\ \frac{289109}{381024},\ \frac{1091}{3024},\ - \frac{3768}{15625}\right),
\]
\[
(G,W,E,l)=\left(\frac{73}{400},\ \frac{759}{1000},\ \frac{9}{25},\ - \frac{241}{1000}\right),
\quad(p,r)=\left(\frac{4}{11},- \frac{11}{16}\right).
\]
\[L_1=\frac{100717}{52800000}>\frac1{2000}.\]

At \((C,x,u)=(\frac{1}{2},2,\frac{19}{25})\):
\[
(\Gamma,w,E_L,\ell)=\left(\frac{48412319}{262440000},\ \frac{894139}{1190700},\ \frac{1598}{4725},\ - \frac{3768}{15625}\right),
\]
\[
(G,W,E,l)=\left(\frac{23}{125},\ \frac{751}{1000},\ \frac{169}{500},\ - \frac{241}{1000}\right),
\quad(p,r)=\left(\frac{4}{11},- \frac{33}{50}\right).
\]
\[L_1=\frac{33871}{26400000}>\frac1{2000}.\]

At \((C,x,u)=(\frac{10}{13},\frac{3}{2},\frac{3}{4})\):
\[
(\Gamma,w,E_L,\ell)=\left(\frac{221886239}{1194393600},\ \frac{115162727}{143095680},\ \frac{62927}{131040},\ - \frac{2605400}{6744273}\right),
\]
\[
(G,W,E,l)=\left(\frac{371}{2000},\ \frac{161}{200},\ \frac{12}{25},\ - \frac{193}{500}\right),
\quad(p,r)=\left(\frac{156}{371},- \frac{371}{624}\right).
\]
\[(L_0,L_1)=\left(\frac{69027749}{9921600000},\frac{31490249}{9921600000}\right),\quad L_0,L_1>\frac1{2000}.\]

At \((C,x,u)=(\frac{10}{13},\frac{3}{2},\frac{19}{25})\):
\[
(\Gamma,w,E_L,\ell)=\left(\frac{3}{16},\ \frac{23735779}{29811600},\ \frac{907}{1950},\ - \frac{2605400}{6744273}\right),
\]
\[
(G,W,E,l)=\left(\frac{3}{16},\ \frac{797}{1000},\ \frac{93}{200},\ - \frac{193}{500}\right),
\quad(p,r)=\left(\frac{156}{371},- \frac{371}{650}\right).
\]
\[(L_0,L_1)=\left(\frac{12064879}{1653600000},\frac{2239543}{551200000}\right),\quad L_0,L_1>\frac1{2000}.\]

At \((C,x,u)=(\frac{10}{13},2,\frac{3}{4})\):
\[
(\Gamma,w,E_L,\ell)=\left(\frac{19625567}{107495424},\ \frac{48664387}{64393056},\ \frac{13679}{39312},\ - \frac{79889480}{355112313}\right),
\]
\[
(G,W,E,l)=\left(\frac{73}{400},\ \frac{189}{250},\ \frac{347}{1000},\ - \frac{28}{125}\right),
\quad(p,r)=\left(\frac{39}{109},- \frac{109}{156}\right).
\]
\[(L_0,L_1)=\left(\frac{17947561}{10202400000},\frac{15695311}{10202400000}\right),\quad L_0,L_1>\frac1{2000}.\]

At \((C,x,u)=(\frac{10}{13},2,\frac{19}{25})\):
\[
(\Gamma,w,E_L,\ell)=\left(\frac{48412319}{262440000},\ \frac{150538991}{201228300},\ \frac{19976}{61425},\ - \frac{79889480}{355112313}\right),
\]
\[
(G,W,E,l)=\left(\frac{23}{125},\ \frac{749}{1000},\ \frac{13}{40},\ - \frac{28}{125}\right),
\quad(p,r)=\left(\frac{39}{109},- \frac{218}{325}\right).
\]
\[(L_0,L_1)=\left(\frac{2169337}{3400800000},\frac{1147231}{1700400000}\right),\quad L_0,L_1>\frac1{2000}.\]

Each scalar comparison is a single cross multiplication of printed
fractions. The largest integer product is 443772478000, from the first
Gamma lower bound. The small sums in (7) likewise use at most twelve-digit
integer coefficients. The proof does not use the much larger fully
collected rational value of any endpoint.

## 6. Result and expansion boundary

Concavity in x proves the endpoint-norm signs. Beta concavity extends
the F1 result to the whole stated C interval; norm concavity extends both
results to the full uniform norm interval. This proves (1).

The immediate callers are the A reduction's a=6/5 endpoints in
[the large-shape reduction](SHORT_OUTER_LARGE_SHAPE_REDUCTION.md) and
the B branch's upper shape boundary. This note supplies only those
boundaries. The separate a=x and lower-chord terminal proofs are needed
to close the corresponding full branches.

Every source or division polynomial printed here has at most seven
monomials and degree six in x; the derivative polynomials have degree two.
The generic logarithm derivative inequalities are those of the same
cubic majorant, valid for 0<y<=1. No new transcendental bound is used.
Keep the primitive proper numerator V separate during the two division
stages in Section 3: multiplying all stages by 23 in one operation would
create unnecessarily large coefficients. All stated scalar and expanded
polynomial checks stay within twelve digits. This is a hand-proof
boundary lemma, with no claim of Lean integration or measured resource use.
