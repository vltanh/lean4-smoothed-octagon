# Shape monotonicity on the S1 small-shape strip

This continues [the beta reduction](SHORT_OUTER_BETA_LOW_SHAPE.md) of
the old low-ratio outer-face note's domain B. It removes the shape
variable from its two remaining \(F_0\) signs. The
[completed actual small-shape proof](SHORT_OUTER_LOW_SHAPE_TERMINAL.md)
uses this monotonicity after a constant-slope beta comparison. The
\(F_1\) sign, other branches, and S1 as a whole remain open.

Use \(S=x+1,\ B=a+\beta,\ K=6a^2+1\) and the functions
\(D,w,E_L,\Gamma_*,\overline R_2,F_0\) printed in
[SHORT_OUTER_BETA](SHORT_OUTER_BETA.md), (1)--(2). The norms \(u_f\)
and \(u_\ell\) are those in
[SHORT_OUTER_BETA_LOW_SHAPE](SHORT_OUTER_BETA_LOW_SHAPE.md), (3).
Put
\[
 C(x)=\frac{x(7x+1)}{4x^2+11x+1},\qquad
 \beta(x,a)=x+C(x)(a-1).
\tag{1}
\]
On the full rectangle
\[
 \frac32\le x\le2,\qquad 1\le a\le\frac65,
\tag{2}
\]
we prove that both
\[
 a\longmapsto F_0(x,a,\beta(x,a),u_f(x)),\qquad
 a\longmapsto F_0(x,a,\beta(x,a),u_\ell(x,\beta(x,a)))
\tag{3}
\]
are strictly increasing. In particular, the outer-cap inequality
\(6a^2\ge x(x+2)\) is not required along this motion.

The proof also applies when the old cubic logarithm majorant is
replaced everywhere by the single Padé bound in
[LOG_BOUND](LOG_BOUND.md): only its first-derivative error bound
is used below, and the Padé error is smaller.

## 1. A polynomial part with two elementary parameter reductions

Temporarily allow \(1/2\le C\le4/5\), set
\(\beta=x+C(a-1)\), and keep \(x,C,u\) fixed while differentiating
with respect to \(a\). Define
\[
 \mathcal P=
 \Gamma_*-\frac7{96}
 \left(2w-\frac12+(u-1)\frac{B}{a}-\frac17-E_L\right),
 \qquad H=\frac{d\mathcal P}{da}.
\tag{4}
\]
The omitted terms are \(a/B\), the logarithm bound, and a constant;
they are handled without clearing their denominators in Section 2.

### 1.1. Concavity in C

The coefficient of \(C^2\) in \(\mathcal P\) is
\[
 -\frac{u(a-1)^2(a-x)^2}{84a^4}.
\]
Only the term \(uD^2\) in \(w\) contributes. Consequently the
coefficient of \(C^2\) in \(H\) is
\[
 -\frac{u(a-1)(a-x)\{a(x+1)-2x\}}{42a^5}\le0.
\tag{5}
\]
Indeed \(a\le x\), while \(a(x+1)\le(6/5)(x+1)\le2x\)
for \(x\ge3/2\). The expanded two-variable numerator factor in
(5) is
\[
 a^3x+a^3-a^2x^2-4a^2x-a^2+3ax^2+3ax-2x^2,
\]
eight monomials of degree four. The earlier square product has
nine monomials of degree four. The scalar \(u>0\) is factored out;
no four-variable expansion is used.

Thus a lower bound for \(H\) follows from its values at
\(C=1/2,4/5\).

### 1.2. Increase the norm from three quarters

For either of these fixed values of \(C\), \(H\) is quadratic in
\(u\), with positive quadratic coefficient
\[
 \frac{KS^2}{144a^5}.
\tag{6}
\]
This follows by differentiating the \(u^2\) coefficient
\(-K^2S^2/(576a^4)\) of \(\Gamma_*\). The numerator in (6) is
\[
 6a^2x^2+12a^2x+6a^2+x^2+2x+1,
\]
six monomials of degree four.

The following explicit identities show that
\[
 H(C,3/4)>-\frac1{144},\qquad H_u(C,3/4)>0
 \quad(C=1/2,\ 4/5).
\tag{7}
\]
It follows from (6) that the same lower bound holds for every
\(u\ge3/4\). Together with (5), this proves
\[
 \boxed{H>-\frac1{144}\quad
 (1/2\le C\le4/5,\ u\ge3/4).}
\tag{8}
\]

Here are all four sign polynomials used for (7). Put
\(c=6/5-a\in[0,1/5]\) and \(z=x-3/2\in[0,1/2]\).
The identities are
\[
\begin{aligned}
 H(1/2,3/4)+1/144&=\frac{P_{1/2}(c,z)}{16128a^5S^2},&
 H_u(1/2,3/4)&=\frac{Q_{1/2}(c,z)}{4032a^5},\\
 H(4/5,3/4)+1/144&=\frac{P_{4/5}(c,z)}{403200a^5S^2},&
 H_u(4/5,3/4)&=\frac{Q_{4/5}(c,z)}{50400a^5}.
\end{aligned}
\tag{9}
\]
The complete expansions, with the last two powers of \(c\) grouped
as a positive product, are
\[
\begin{aligned}
P_{1/2}={}&
576z^6+\frac{108672}{25}z^5+\frac{1448267}{125}z^4
+\frac{1696774}{125}z^3+\frac{49391649}{6250}z^2
+\frac{2591359}{1250}z+\frac{518123}{2000}\\
&+c\left(\frac{5616}{5}z^5+\frac{217044}{25}z^4
+\frac{577728}{25}z^3+\frac{3264138}{125}z^2
+\frac{67329}{5}z+\frac{9621}{20}\right)\\
&+c^2\left(-288z^5-\frac{10614}{5}z^4
-\frac{27828}{5}z^3-\frac{168831}{25}z^2
-\frac{9933}{5}z+\frac{45981}{8}\right)\\
&-c^3\left(72z^4+174z^3+\frac{2934}{5}z^2
+\frac{9495}{2}z+\frac{16215}{2}\right)
+112c^4(6-c)(z+5/2)^2,\\[2mm]
P_{4/5}={}&
14400z^6+107808z^5+\frac{7142767}{25}z^4
+\frac{42170662}{125}z^3+\frac{51553449}{250}z^2
+\frac{3397219}{50}z+\frac{2502083}{80}\\
&+c\left(21600z^5+\frac{835632}{5}z^4
+\frac{11022624}{25}z^3+\frac{2459592}{5}z^2
+226026z-79605\right)\\
&+c^2\left(-7200z^5-60630z^4-\frac{972684}{5}z^3
-298989z^2-127065z+\frac{1547325}{8}\right)\\
&+c^3\left(-720z^4+4398z^3+6075z^2
-\frac{222975}{2}z-\frac{879375}{4}\right)
+2800c^4(6-c)(z+5/2)^2.
\end{aligned}
\tag{10}
\]
Each has 30 monomials and total degree seven after expansion.
Discard nonnegative terms involving \(c\), and bound each adverse
term using \(c^j\le5^{-j}\); the last product is nonnegative.
This gives the fully printed positive lower bounds
\[
\begin{aligned}
P_{1/2}\ge{}&
576z^6+\frac{108384}{25}z^5+\frac{1437581}{125}z^4
+\frac{1668772}{125}z^3+\frac{47673999}{6250}z^2
+\frac{1222277}{625}z+\frac{388403}{2000}>0,\\
P_{4/5}\ge{}&
14400z^6+107520z^5+\frac{7081993}{25}z^4
+\frac{41197978}{125}z^3+\frac{48563559}{250}z^2
+\frac{1549247}{25}z+\frac{1087703}{80}>0.
\end{aligned}
\tag{11}
\]
These have seven monomials each and degree six.

The norm-derivative polynomials are
\[
\begin{aligned}
Q_{1/2}={}&
192z^4+\frac{22848}{25}z^3+\frac{295058}{125}z^2
+\frac{463922}{125}z+\frac{535057}{250}\\
&-c\left(\frac{2736}{5}z^3+\frac{78444}{25}z^2
+\frac{159336}{25}z+\frac{99243}{25}\right)\\
&+c^2\left(288z^3+\frac{6564}{5}z^2
+\frac{13956}{5}z+\frac{9963}{5}\right)
+c^3(72z^2-42z-186),\\
Q_{4/5}={}&
2400z^4+11280z^3+\frac{719681}{25}z^2
+\frac{5578777}{125}z+\frac{496933}{20}\\
&-c\left(7920z^3+41436z^2+\frac{2049696}{25}z
+\frac{252711}{5}\right)\\
&+c^2\left(3600z^3+16302z^2+\frac{196986}{5}z
+\frac{60939}{2}\right)
+c^3\left(360z^2-3567z-\frac{10185}{2}\right).
\end{aligned}
\tag{12}
\]
Each has 16 monomials and degree five. The same elementary bounds give
\[
\begin{aligned}
Q_{1/2}&\ge192z^4+\frac{20112}{25}z^3
+\frac{216614}{125}z^2+\frac{304544}{125}z
+\frac{336199}{250}>0,\\
Q_{4/5}&\ge2400z^4+9696z^3+\frac{512501}{25}z^2
+\frac{3525514}{125}z+\frac{1469747}{100}>0.
\end{aligned}
\tag{13}
\]
Each lower polynomial has five monomials and degree four. After
clearing their coefficient denominators, the largest coefficient in
(9)--(13) is \(1305655200\), ten digits.

## 2. The reciprocal and logarithm terms supply a positive derivative

Let \(y=2B/(7a)\) and
\(\varepsilon(y)=1-y\ell'(y)\). For the old cubic majorant,
\[
 \varepsilon(y)=\left(\frac{1-y}{1+y}\right)^4;
\]
for the Padé bound it is nonnegative and no larger. In (2),
\(x\le\beta\le ax\), hence
\[
 \frac94\le\frac Ba\le3,\qquad
 \frac9{14}\le y\le\frac67,\qquad
 0\le\varepsilon(y)\le(5/23)^4<1/400.
\tag{14}
\]
Differentiation without expanding the rational functions gives
\[
 \frac{dF_0}{da}
 =H+\frac7{96}\frac{(x-C)\beta}{aB^2}
   -\frac7{96}\frac{x-C}{aB}\varepsilon(y)
 \quad\text{when \(u\) is held fixed.}
\tag{15}
\]
Indeed \(d(a/B)/da=(x-C)/B^2\) and
\(y'/y=-(x-C)/(aB)\).

For \(r=\beta/a\in[5/4,2]\), the function
\(r/(1+r)^2\) decreases and is at least \(2/9\).
Moreover \(a^{-2}\ge25/36\), \(x-C\ge7/10\), and
\((x-C)/(aB)\le1\). Therefore (8) and (15) give
\[
 \frac{dF_0}{da}>
 -\frac1{144}+\frac7{96}\frac{25}{36}\frac29\frac7{10}
 -\frac7{38400}
 =\frac{2333}{3110400}>0.
\tag{16}
\]
This already proves the first monotonicity in (3).

## 3. The changing upper norm costs less than this margin

We need only an upper bound for \((F_0)_u\):
\[
 \boxed{(F_0)_u\le245/2304<1/9.}
\tag{17}
\]
Here is a proof using the transport factors themselves.
Since \(a-x<0\), \(D\) decreases with \(\beta\). At \(\beta=x\),
\[
 \frac72a^2-D
 =(a-1)\left(\frac52(a+1)-2x\right)
   +2(x-3/2)(x-1/2)\ge0.
\tag{18}
\]
The expanded polynomial has five monomials and degree two.
Thus \(\delta=D/(7a^2)\le1/2\), while
\(\lambda S\ge(6/7)(5/2)=15/7\). The identity
\[
 (\overline R_2)_u
 =2\delta^2-2\delta(\lambda S+1)+B/a+\lambda S
\tag{19}
\]
has five monomials of degree two when \(\lambda S\) and \(B/a\)
are left as scalar factors. Its right side decreases as a function
of \(\delta\le1/2\), so
\[
 (\overline R_2)_u\ge B/a-1/2\ge7/4.
\tag{20}
\]

For the central norm \(v=U(S/K)\), the bounds
\(1/4\le S/K\le3/7<1/2\) imply \(v\le13/16\).
The central pairing satisfies
\[
 E=S(u-1)+1/S+(2S-1)/K
 \ge-S/4+1/S+\frac{25(2S-1)}{241}
 \ge\frac{295}{2892}>\frac1{10}.
\tag{21}
\]
The middle function decreases for \(5/2\le S\le3\), since
its derivative is \(-1/4-S^{-2}+50/241<0\).
Using \(K^2/a^4=(6+a^{-2})^2\le49\), we obtain
\[
 (\Gamma_*)_u=\frac{K^2(4v-2ES)}{576a^4}
 \le\frac{539}{2304}.
\]
Subtracting \((7/96)(7/4)\) proves (17).

The beta note proved
\[
 0\le-(u_\ell)_\beta\le5/664.
\tag{22}
\]
Along (1), \(du_\ell/da=C(u_\ell)_\beta\).
Combining (16), (17), and (22) gives
\[
\begin{aligned}
 \frac{d}{da}F_0(x,a,\beta(x,a),u_\ell(x,\beta(x,a)))
 &>\frac{2333}{3110400}-\frac19\frac45\frac5{664}\\
 &=\frac{20839}{258163200}>0.
\end{aligned}
\tag{23}
\]
This proves the second monotonicity in (3).

The actual \(C(x)\) is in the interval used throughout, because
\[
\begin{aligned}
 2(4x^2+11x+1)(C-1/2)&=(x-1)(10x+1),\\
 5(4x^2+11x+1)(4/5-C)&=6+(2-x)(19x-1).
\end{aligned}
\tag{24}
\]
The expanded numerators have three monomials each and degree two.

## 4. Exact terminal obligations

After the previous beta reduction, the actual outer cap gives
\(a\ge\sqrt{x(x+2)/6}\). Define a simpler lower shape
\[
 a_*(x)=
 \begin{cases}
 1,&3/2\le x\le5/3,\\
 (45x+22)/97,&5/3\le x\le2.
 \end{cases}
\tag{25}
\]
For the second piece, a direct square comparison gives
\[
 \frac{x(x+2)}6-\left(\frac{45x+22}{97}\right)^2
 =\frac{-2741x^2+6938x-2904}{56454}>0.
\tag{26}
\]
The numerator is a concave quadratic, with endpoint values
\(9409/9\) at \(x=5/3\) and \(8\) at \(x=2\); hence it is
positive on the whole interval. This identity has three monomials
and degree two. No square-root approximation is used in a sign
polynomial.

The original B-domain \(F_0\) task is therefore reduced to the four
univariate signs
\[
\begin{aligned}
 F_0(x,a_*(x),\beta(x,a_*(x)),u_f(x))&>0,\\
 F_0(x,a_*(x),\beta(x,a_*(x)),
              u_\ell(x,\beta(x,a_*(x))))&>0
\end{aligned}
\tag{27}
\]
on the two intervals in (25). These particular terminal functions are
not asserted positive here. The completed companion route first increases
beta to the constant slope \(C=10/13\) at the original shape, and only
then applies the monotonicity proved here. Its slightly different terminal
functions are proved positive in
[SHORT_OUTER_LOW_SHAPE_TERMINAL](SHORT_OUTER_LOW_SHAPE_TERMINAL.md).
The alpha motion is valid even where the rational chord lies below
the original cap, because the monotonicity theorem was proved on
the full rectangle (2).

All identities were checked with exact rational symbolic arithmetic
as transcription checks. No Lean compilation or CI was run.
