# The actual S1 small-shape outer F0 sign

This closes the \(F_0\) part of the actual small-shape branch B in
[MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN](../../archive/notes/MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN.md),
using the [beta](SHORT_OUTER_BETA_LOW_SHAPE.md) and
[shape](SHORT_OUTER_ALPHA_LOW_SHAPE.md) reductions. The companion \(F_1\) sign and the S and A branches are assembled in
the [completed outer replacement](SHORT_OUTER_COMPLETE.md).

The conclusion is
\[
 F_0(x,a,\beta,u)>0
\tag{1}
\]
on the original caller's actual domain
\[
 \frac32\le x\le2,\quad 1\le a\le\frac65,\quad
 6a^2\ge x(x+2),\quad
 x\le\beta\le x+\frac{x(7x+1)}{4x^2+11x+1}(a-1),
 \quad u_f(x)\le u\le u_\ell(x,\beta).
\tag{2}
\]
The old generated row B also included extraneous points with
\(a<1\) and without the actual cap. We do not assert (1) there.
The caller is the actual outer-face split in Section 2 of the old
note: every point assigned to its small-shape branch satisfies (2),
and only (1) is used for its \(F_0\) alternative.

All functions and the cubic logarithm majorant \(\ell\) are as
printed in the preceding two notes. The proof retains this single
bound for the logarithm. Its critical endpoint is replaced by a
slightly more conservative rational comparison point. The exact
residual there is approximately \(2.89124\cdot10^{-6}\); the
staged proof below certifies the smaller explicit margin
\(167/144000000\). This is a reduction in algebraic cost, not an
increase in the old thin margin.

## 1. Use a constant beta slope before moving the shape

Let \(C_*=10/13\), \(p=45/97\), and define
\[
 a_*(x)=
 \begin{cases}1,&3/2\le x\le5/3,\\
 px+22/97,&5/3\le x\le2,
 \end{cases}
 \qquad
 \beta_*(x)=x+C_*(a_*(x)-1).
\tag{3}
\]
The shape note proved \(a_*(x)\le a\) on (2).
The comparison
\[
 \frac{10}{13}-\frac{x(7x+1)}{4x^2+11x+1}
 =\frac{(2-x)(51x+5)}{13(4x^2+11x+1)}\ge0
\tag{4}
\]
has a three-monomial quadratic numerator. Also \(C_*\le x\).
Thus, at the original shape, the beta theorem permits increasing
beta to \(x+C_*(a-1)\), separately along \(u_f\) and \(u_\ell\).
The original cap remains valid during this first motion.

The shape theorem's proof applies to every fixed
\(C\in[1/2,4/5]\), including \(C_*\). Decrease \(a\) to \(a_*(x)\)
along those same expressly specified norm curves. This second
motion is valid on the full rectangle and does not need to preserve
the cap. Concavity in \(u\) at the original point therefore reduces
(1) to the two norm endpoints at (3).

## 2. The first interval has an ample margin

Here \(a_*=1,\ \beta_*=x\). Set
\[
 Q(x,u)=F_0(x,1,x,u)+\frac7{96}\ell(2(x+1)/7).
\]
The actual comparison norms lie in
\([3/4,19/25]\), since they are at most
\[
 u_0=\frac34+\frac{(x-1)^2}{12(x+1)^2}
 \le\frac34+\frac1{108}<\frac{19}{25}.
\]
The function \(Q\) is concave in \(u\). At the two fixed norm
endpoints its complete formulas are
\[
\begin{aligned}
Q(x,3/4)&=
\frac{-1800000x^6+3300000x^5+4028125x^4-12512500x^3
+9452574x^2+3955148x-34088051}{201600000(x+1)^2},\\
Q(x,19/25)&=
\frac{-114000x^6+204000x^5+248760x^4-788460x^3
+594424x^2+264018x-2121501}{12600000(x+1)^2}.
\end{aligned}
\tag{5}
\]
Each numerator has seven monomials and degree six.
Both functions increase on \(3/2\le x\le5/3\).
For an explicit derivative proof, put \(t=5/3-x\in[0,1/6]\).
Their derivative numerators, with denominators
\(32256(x+1)^3\) and \(1260000(x+1)^3\), respectively, are
\[
\begin{aligned}
D_f(t)={}&-1152t^6+11664t^5-45271t^4
+\frac{251692}{3}t^3-\frac{232928}{3}t^2
+\frac{931856}{27}t+\frac{142672}{27},\\
D_v(t)={}&-45600t^6+463200t^5-1808248t^4
+\frac{30508958}{9}t^3-\frac{28936432}{9}t^2
+\frac{40767329}{27}t+\frac{35088301}{243}.
\end{aligned}
\tag{6}
\]
These are seven-monomial degree-six polynomials. Discard their
positive nonconstant terms and use \(t\le1/6\) in their three
negative terms. This gives
\[
 D_f\ge445313/144>0,\qquad
 D_v\ge13046693/243>0.
\tag{7}
\]
Thus concavity in \(u\), followed by monotonicity in \(x\), gives
\[
 Q(x,u)\ge Q(3/2,19/25)=-82087/4200000.
\tag{8}
\]
The other endpoint value is
\(Q(3/2,3/4)=-15467579/806400000\), which is larger.

Since \(\ell\) increases on this range and
\(\ell(16/21)=-41320/151959\), we obtain
\[
 \boxed{F_0(x,1,x,u)\ge
 -\frac{82087}{4200000}
 +\frac7{96}\frac{41320}{151959}
 =\frac{180391567}{638227800000}>0.}
\tag{9}
\]
The largest cleared coefficient in the polynomial identities
(5)--(7) is \(823741866\), nine digits.

## 3. A uniform norm interval on the second piece

For \(5/3\le x\le2\), (3) becomes
\[
 a_*=\frac{45x+22}{97},\qquad
 \beta_*=\frac{1711x-750}{1261},\qquad
 1\le a_*\le112/97<7/6.
\tag{10}
\]
Along it the upper norm has the explicit low-degree formula
\[
 u_\ell(x,\beta_*)=
 \frac{47492x^3+1035x^2-47904x-22223}
 {(x+1)(35x+13)(1711x-2011)}.
\tag{11}
\]
Its derivative is
\[
 \frac{(x-1)J(x)}
 {(x+1)^2(35x+13)^2(1711x-2011)^2},
\quad
 J(x)=495717581x^3-822706779x^2-69332085x+398481283.
\]
For \(z=x-5/3\ge0\),
\[
 J=495717581z^3+1655881126z^2
 +\frac{3957875480}{3}z+\frac{7900740016}{27}>0.
\tag{12}
\]
The formula (11) has four numerator monomials and degree three;
the derivative numerator has five monomials and degree four.
The shift identity for \(J\) has four monomials and degree three,
with largest cleared coefficient \(44708790402\).
Consequently
\[
 \frac34\le u_\ell(x,\beta_*)\le\frac{266045}{351339}
 <u_*:=\frac{340}{449},\qquad
 u_*-\frac{266045}{351339}=\frac{1055}{157751211}.
\tag{13}
\]
Also \(u_f\le3/4+1/252<u_*\). By concavity in \(u\), it suffices
to prove the two fixed-norm functions \(F_0(x,a_*,\beta_*,3/4)\)
and \(F_0(x,a_*,\beta_*,u_*)\) positive.

## 4. Both fixed-norm functions decrease in x

This is another dimension reduction, done before a terminal sign.
Use the polynomial part \(\mathcal P\) in equation (4) of the shape
note. At fixed \(u\), let
\[
 H=\mathcal P_x+p\mathcal P_a+(1+C_*p)\mathcal P_\beta,
 \qquad \beta=x+C_*(a-1).
\tag{14}
\]
We prove, on the larger rectangle
\[
 5/3\le x\le2,\quad1\le a\le7/6,\quad u\ge3/4,
 \qquad H\le1/156.
\tag{15}
\]

### 4.1. The polynomial derivative decreases with the norm

The coefficient of \(u^2\) in \(H\) is
\[
 -\frac{(6a^2+1)(x+1)(582a^3+97a-90x-90)}{27936a^5}<0.
\tag{16}
\]
The last factor is at least \(582+97-270>0\).
The numerator, if expanded, has 12 monomials and degree six.
Its complete polynomial is
\[
3492a^5x+3492a^5+1164a^3x+1164a^3
-540a^2x^2-1080a^2x-540a^2
+97ax+97a-90x^2-180x-90.
\]

Put \(c=a-1\in[0,1/6]\), \(z=x-5/3\in[0,1/3]\).
The other needed norm coefficient is
\[
 -H_u\big|_{u=3/4}=\frac{J_u(c,z)}{66096576a^5},
\tag{17}
\]
where the complete 20-monomial, degree-six polynomial is
\[
\begin{aligned}
J_u={}&-4131036c^5z-9881196c^5
-21744684c^4z-45305790c^4\\
&+7334496c^3z^2-21868242c^3z-63787900c^3\\
&-2190240c^2z^3+8990244c^2z^2+3137430c^2z-27907528c^2\\
&-727584cz^3+4616232cz^2+8978199cz+\frac{30456674}{9}c\\
&-1460160z^4-3835104z^3-1634646z^2
+2237495z+\frac{32620952}{9}.
\end{aligned}
\tag{18}
\]
Discard each positive nonconstant term and use
\(c^i z^j\le6^{-i}3^{-j}\) in every negative term. The remaining
constant is \(153348569/72>0\).
This proves \(H_u<0\) for all \(u\ge3/4\), so it remains to
bound \(H\) at \(u=3/4\).

### 4.2. Retain the reciprocal powers of S as separate factors

At \(u=3/4\), polynomial division gives
\[
 H=\frac{P(a,x)}{528772608a^5}
       +\frac{R_1(a)}{S}+\frac{R_2(a)}{S^2}+\frac{R_3(a)}{S^3},
\tag{19}
\]
where all three \(R_i\) are positive:
\[
\begin{aligned}
 R_1&=\frac{2340a^3+8265a^2+1170a+2630}{141232a^5},\\
 R_2&=\frac{43650a^5+90792a^4+160341a^3+64272a^2+25511a+8190}
 {2542176a^5},\\
 R_3&=\frac{36a^4+12a^2+1}{288a^4}.
\end{aligned}
\tag{20}
\]
Their numerator counts are four, six, and three, and their degrees
are three, five, and four. The polynomial part is
\[
\begin{aligned}
P={}&-4131036a^5x-1861236a^5-2179008a^4x+13228860a^4\\
&+14668992a^3x^2-13343424a^3x-21382008a^3\\
&-4380480a^2x^3+9880164a^2x^2+1399680a^2x-29879652a^2\\
&-21917376ax^3+47298240ax^2-19837135ax-9337419a\\
&+8760960x^4-20779200x^3+7986150x^2+10761660x-11443770.
\end{aligned}
\tag{21}
\]
It has 20 monomials and degree six.

The differentiation in (19) is staged; one must not multiply all
its terms by \(a^5S^3\) and expand a degree-nine polynomial.
Here is a size-compliant identity before differentiating that
justifies the separation:
\[
 \mathcal P\big|_{u=3/4}
 =\frac{A(a,x)}{10902528a^4}
 -\frac{(6a^2+1)(75a^2+156a+263)}{26208a^4S}
 -\frac{(6a^2+1)^2}{576a^4S^2},
\tag{22}
\]
\[
\begin{aligned}
A={}&-97344x^4+(97344a^2+44928a+230880)x^3\\
&-(42588a^4+22464a^3+74292a^2+203040a+88735)x^2\\
&-(38376a^4-272760a^3+468768a^2-166368a+119574)x\\
&+2359308a^4-60144a^3+843300a^2+52416a+127153.
\end{aligned}
\tag{23}
\]
The displayed \(A\) has 19 monomials and degree six.
Clearing (22) requires 29 monomials and degree eight, with largest
coefficient \(4493040\). Differentiate its three terms separately.
The product rule gives (19), requiring only the 20-term polynomial
(21) and the one-variable numerators (20).

For \(8/3\le S\le3\), convexity of \(S^{-j}\) gives the secant bounds
\[
 S^{-1}\le\frac{14-3x}{24},\qquad
 S^{-2}\le\frac{166-51x}{576},\qquad
 S^{-3}\le\frac{1814-651x}{13824}.
\tag{24}
\]
Their direct positive remainders are
\[
\begin{aligned}
 \frac{14-3x}{24}-S^{-1}
 &=\frac{(3x-5)(2-x)}{24S},\\
 \frac{166-51x}{576}-S^{-2}
 &=\frac{(3x-5)(2-x)(17x+41)}{576S^2},\\
 \frac{1814-651x}{13824}-S^{-3}
 &=\frac{(3x-5)(2-x)(217x^2+842x+1201)}{13824S^3}.
\end{aligned}
\tag{25}
\]
These have respectively three, four, and five monomials after
expansion, and degrees two, three, and four.

Let \(\overline H\) be (19) with the three secants in (24).
Since every \(R_i\) is positive, \(H\le\overline H\).
With \(c,z\) as above,
\[
 \frac1{156}-\overline H
 =\frac{P_H(c,z)}{456859533312a^5},
\tag{26}
\]
where
\[
\begin{aligned}
P_H={}&6953078340c^5z+6370738452c^5
+38092736916c^4z+21267233316c^4\\
&-12674009088c^3z^2+56516150124c^3z+15950022876c^3\\
&+3784734720c^2z^3-27634815360c^2z^2
+16762737780c^2z-10086130044c^2\\
&+26506082304cz^3+36569781504cz^2
+21261767565cz-6167998287c\\
&-7569469440z^4-9788553216z^3
+8238874176z^2+8205980133z+1508611689.
\end{aligned}
\tag{27}
\]
There are 20 monomials of degree six. All coefficients have at
most 12 digits. Bound the negative \(c,c^2\) constant terms using
\(c\le1/6\). Absorb the four negative terms involving \(z^2,z^3,z^4\)
into the displayed positive \(z^2\) term using
\(c\le1/6,\ z\le1/3\). After discarding all other positive
nonconstant terms, this gives
\[
 P_H\ge \frac{400883391}{2}+3308661216z^2>0.
\tag{28}
\]
Thus (15) is proved.

### 4.3. Restore the reciprocal and logarithm terms

On the line (10), set
\[
 m=\frac{22}{97}+pC_*=\frac{736}{1261},
 \qquad y=\frac{2(a+\beta)}{7a}.
\]
As in the shape proof, write
\(\varepsilon(y)=((1-y)/(1+y))^4\).
Here \(9/14\le y\le6/7\) and
\(0\le\varepsilon<1/400\). Direct differentiation gives
\[
 \frac{dF_0}{dx}
 =H-\frac7{96}\frac{m\beta}{a(a+\beta)^2}
       +\frac7{96}\frac{m}{a(a+\beta)}\varepsilon.
\tag{29}
\]
Since \(a\le7/6\) and \(1\le\beta/a\le2\),
\[
 \frac7{96}\frac{m\beta}{a(a+\beta)^2}
 \ge\frac7{96}m\frac{36}{49}\frac29
 =\frac{184}{26481}.
\]
Also \(m/[a(a+\beta)]<1\). Therefore, for every fixed
\(u\ge3/4\),
\[
 \boxed{\frac{dF_0}{dx}<
 \frac1{156}-\frac{184}{26481}+\frac7{38400}
 =-\frac{120611}{338956800}<0.}
\tag{30}
\]
The two terminal functions in Section 3 attain their minima at \(x=2\).

## 5. The final scalar sign, using only small integer products

At \(x=2\), the comparison point is
\[
 a=\frac{112}{97},\quad \beta=\frac{2672}{1261},\quad
 a+\beta=\frac{4128}{1261},\quad K=\frac{84673}{9409}
 =9-\frac8{9409}.
\tag{31}
\]
First, \(F_0\) decreases in \(u\ge3/4\) at this fixed point.
Indeed \(\delta<3/10,\ \lambda>24/25,\ B/a>14/5\),
\(v\le7/9,\ E\ge5/36\), and \(K^2/a^4\le49\).
The factor formula for \((\overline R_2)_u\) used in the shape note
then gives
\[
 (\overline R_2)_u\ge \frac{14}{5}-\frac{21}{50}
       +\frac25\frac{72}{25}=\frac{883}{250},\qquad
 (\Gamma_*)_u\le\frac{2009}{10368}.
\]
Hence \((F_0)_u\le-82649/1296000<0\).
It suffices to check \(u=u_*=340/449\).

Put \(M=10^6\). The following enclosures are proved by individual
small integer comparisons:
\[
\begin{gathered}
 \frac{964297}{M}\le\lambda=\frac{84673}{87808}
       \le\frac{964298}{M},\qquad
 \frac{294741}{M}\le\delta=\frac{336449}{1141504}
       \le\frac{294742}{M},\\
 \frac{757238}{M}\le u_*=\frac{340}{449}
       \le\frac{757239}{M},\qquad
 \frac{777767}{M}\le v\le\frac{777768}{M},\\
 \frac{160656}{M}\le E\le\frac{160658}{M}.
\end{gathered}
\tag{32}
\]
For clarity, the two enclosures not obtained from a single
linear-fraction comparison have these short proofs. Set
\(d=8/254019\), so
\[
 S/K=1/3+d,\qquad v=7/9-d/3+d^2.
\]
Thus \(v\ge592703/762057\ge777767/M\).
On the other side \(31/M\le d<1/10000\), giving
\[
 v\le7/9-\frac{31}{3M}+\frac1{10^8}<777768/M.
\]
This is one three-term quadratic identity.
The pairing has the decomposition
\[
 E=\frac5{36}+\frac{39}{1796}+\frac{40}{762057}.
\tag{33}
\]
Use
\[
 \frac{217149}{10^7}\le\frac{39}{1796}\le\frac{21715}{M},
 \qquad
 \frac{52489}{10^9}\le\frac{40}{762057}\le\frac{53}{M}.
\]
Their sums with \(5/36\) imply (32). The displayed comparisons
require integers of at most 12 digits after clearing denominators.

Now multiply the factor bounds one step at a time, rounding only
to multiples of \(1/M\). For the Casimir:
\[
 \lambda^2\ge929868/M,\quad
 u_*v\ge588954/M,\quad (E/2)^2\le6453/M,
\]
\[
 \lambda^2\{u_*v-(E/2)^2\}
 \ge \frac{929868}{M}\frac{582501}{M}
 \ge\frac{541649}{M}.
\]
Since \(\Gamma_*=(49/144)\lambda^2\{u_*v-(E/2)^2\}\),
\[
 \Gamma_*\ge\frac{26540801}{144000000}.
\tag{34}
\]

For the transported norm and pairing, the same enclosures give
\[
\begin{gathered}
 \lambda^2\le929871/M,\quad \delta^2\le86873/M,\quad
 \lambda E\ge154920/M,\quad \delta\lambda E\ge45661/M,\\
 \lambda^2v\le723224/M,\quad \delta^2u_*\le65784/M,\quad
 \delta u_*\ge223189/M,\quad \lambda E\le154923/M.
\end{gathered}
\]
Consequently
\[
 w=\lambda^2v+\delta^2u_*-\delta\lambda E\le743347/M,
 \qquad E_L=2\delta u_*-\lambda E\ge291455/M.
\tag{35}
\]
For example the only product in the last Casimir step is
\(929868\cdot582501=541649039868>541649M\).
Every other product comparison in (34)--(35) has the same form;
the largest evaluated integer is \(929871000000\), 12 digits.
They are scalar comparisons, so every identity has one constant
monomial and degree zero.

The remaining rational factors satisfy
\[
 r_A=91/258\le352714/M,\qquad
 (u_*-1)/r_A=-28122/40859\le-688269/M.
\tag{36}
\]
For the single logarithm bound, \(y=516/637\) and
\(-z_y=q=121/1153\ge104943/M\). The two staged products give
\[
 q^2\ge11013/M,\qquad q^3\ge1155/M,
 \qquad \ell(y)=-2q-\frac23q^3\le-210656/M.
\tag{37}
\]
Again these are products of integers of at most six digits before
multiplication, with at most 12 digits afterward.

Substitution of (35)--(37) into the original factored residual,
without forming a common huge numerator, yields
\[
\begin{aligned}
 \overline R_2
 &\le\frac{2(743347)-688269+352714-291455-210656}{M}
      -\frac12-\frac17\\
 &=\frac{10799}{1750000}.
\end{aligned}
\]
Finally,
\[
 \boxed{
 F_0\ge
 \frac{26540801}{144000000}
 -\frac7{96}\frac{10799}{1750000}
 -\frac{9193}{50000}
 =\frac{167}{144000000}>0.}
\tag{38}
\]
All integers used in this final subtraction have at most 12 digits.
This proves both fixed-norm endpoints on the second interval.
Together with (9) and the caller-preserving reductions in Section 1,
it proves (1) on (2).

The proof uses only the split \(x=5/3\), the original cubic
logarithm bound on \(0<y\le1\), and the rational lower shape (3).
No coefficient table is a premise. Exact rational computation was
used to check the displayed identities and transcription; no Lean
compilation or CI was run.
