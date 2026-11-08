# Beta monotonicity retains the sharp norm bound on the S1 small-shape strip

This removes beta from the \(F_0\) test in domain B of
[the low-ratio outer-face note](../../archive/notes/MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN.md),
including its beta-dependent upper norm \(u_\ell\). This reduction now
feeds the completed [actual small-shape \(F_0\) proof](SHORT_OUTER_LOW_SHAPE_TERMINAL.md).
The \(F_1\) test, other branches, and S1 as a whole remain open under
the requested size budget.

Use the fixed-scale functions \(w,E_L,\overline R_2,\Gamma_*\) and cubic
logarithm bound from [SHORT_OUTER_BETA](SHORT_OUTER_BETA.md), (1)--(2).
Put \(F_0=\Gamma_*-(7/96)\overline R_2-9193/50000\).
We prove
\[
\frac{d}{d\beta}F_0(x,a,\beta,u_f(x))<0,\qquad
\frac{d}{d\beta}F_0(x,a,\beta,u_\ell(x,\beta))<0
\tag{1}
\]
on
\[
\frac32\le x\le2,\quad1\le a\le\frac65,\quad
6a^2\ge x(x+2),\quad x\le\beta\le ax.
\tag{2}
\]
Here
\[
\begin{aligned}
u_f&=\frac34+\frac{(x-1)^2}{28(x+1)^2},\\
u_v&=\frac34+\frac{2(x-1)^2}{(x+1)(35x+13)},\\
u_\ell&=\frac34+\frac{2(x-1)^2}{(x+1)(35x+13)}
 \frac{x-1+(\beta-x)/16}{\beta-1},\\
u_0&=\frac34+\frac{(x-1)^2}{12(x+1)^2}.
\end{aligned}
\tag{3}
\]
Both \(u_f,u_\ell\) lie in \([3/4,u_0]\); the extra ratio in
\(u_\ell\) is at most one, so \(u_\ell\le u_v\le u_0\).
The proof that the actual norm is at most \(u_\ell\) remains
Section 1 of the old outer-face note.

The largest polynomial below has 19 monomials and degree six in two
variables. The only split is at \(x=7/4\).

## 1. The transported pairing is at most one half

Write \(S=x+1,\ K=6a^2+1,\ \lambda=K/(7a^2)\) and
\(\delta=D/(7a^2)\). Since \(a\le x,\ \beta\ge x\),
\[
4a^2-D\ge3a^2-2ax-1-2x+2x^2
=(a-1)(3a+3-2x)+2(x-1)^2\ge0.
\]
The expanded polynomial has six monomials and degree two. Therefore
\[
(E_L)_u=2\delta-\lambda S
 \le8/7-(6/7)(5/2)=-1<0,\qquad
(E_L)_\beta=\frac{4u(a-x)}{7a^2}\le0.
\]
For \(3/4\le u\le u_0\), the maximum is bounded by setting
\(u=3/4,\ \beta=x\). There
\[
\frac12-E_L=\frac{P_E(a,x)}{28a^2(x+1)},
\]
\[
P_E=-6a^2x^2-4a^2x+26a^2-12ax^2-12ax
       +12x^3+7x^2-8x+1.
\tag{4}
\]
This has nine monomials and degree four. Put
\(c=6/5-a\in[0,1/5]\), \(z=x-3/2\in[0,1/2]\).
Its complete ten-monomial expansion, grouped into positive factors, is
\[
\begin{aligned}
P_E={}&13c^2/2+cz(504/5-22c)+cz^2(132/5-6c)+147c/5\\
 &+12z^3+949z^2/25+118z/25+61/100>0.
\end{aligned}
\tag{5}
\]
Thus \(E_L<1/2\).

## 2. A quantitative fixed-norm beta derivative

Set \(r=a/(a+\beta),\ B=a+\beta,\ y=2B/(7a)\). The existing
logarithm majorant has
\[
\ell'(y)-1/y=-\frac{(y-1)^4}{y(y+1)^4}.
\]
Its numerator is \(-y^4+4y^3-6y^2+4y-1\), five monomials of degree
four. Differentiating the transport before substituting a norm gives
\[
(\overline R_2)_\beta
=\frac{4(x-a)(u-E_L)}{7a^2}
 +\frac{u-U(r)}a
 -\frac1B\left(\frac{y-1}{y+1}\right)^4,
\quad U(r)=1-r+r^2.
\tag{6}
\]
Here \(u-E_L\ge1/4\), and \(r\ge1/(x+1)\) gives
\((u-U(r))/a\ge-(x-1)^2/[4(x+1)^2]\).
Also \(B\ge5/2,\ y\ge9/14\), so
\[
\frac1B\left(\frac{y-1}{y+1}\right)^4
\le\frac25\left(\frac5{23}\right)^4
=\frac{250}{279841}<\frac1{1000}.
\]
Since \(a\le6/5\),
\[
(\overline R_2)_\beta>
\frac{25(x-6/5)}{252}-\frac{(x-1)^2}{4(x+1)^2}-\frac1{1000}.
\]
The first two terms increase with \(x\), because their derivative is
\[
\frac{25}{252}-\frac{x-1}{(x+1)^3}
\ge\frac{25}{252}-\frac8{125}>0.
\]
Their value at \(x=3/2\) is \(83/4200\). Hence
\[
\boxed{(\overline R_2)_\beta>
 83/4200-1/1000>3/160,\qquad (F_0)_\beta<-7/5120.}
\tag{7}
\]

## 3. The norm derivative is bounded below by minus one sixth

We prove
\[
\boxed{(F_0)_u\ge-1/6.}
\tag{8}
\]
First \((F_0)_u\) decreases with \(u\), since
\[
(F_0)_{uu}=-\frac{K^2S^2}{288a^4}<0.
\]
Its positive numerator has nine monomials and degree six:
\[
36a^4x^2+72a^4x+36a^4
+12a^2x^2+24a^2x+12a^2+x^2+2x+1.
\]
Thus raise \(u\) to \(u_0\) for a lower bound. At fixed \(u_0\),
\((F_0)_u\) is concave in beta: its beta-squared coefficient is
\(- (x-a)^2/(84a^4)\le0\). This is the quadratic term
\(2D^2/(49a^4)\) in \((\overline R_2)_u\), multiplied by \(-7/96\).
It suffices to check \(\beta=x\) and \(\beta=ax\).

Let \(E_x,E_{ax}\) denote these two values of \((F_0)_u\). Their full
numerator identities are
\[
E_x+1/6=\frac{P_x}{12096a^4},\qquad
E_{ax}+1/6=\frac{P_{ax}}{12096a^4},
\tag{9}
\]
\[
\begin{aligned}
P_x={}&a^4(252x^2+468x+2574)+a^3(432x^2-90x)\\
&+a^2(-432x^3-924x^2-6x+138)+a(288x^3-216x^2-72x)\\
&-144x^4+216x^3+7x^2-50x+7,\\
P_{ax}={}&a^4(540x^2+378x+2574)-a^3(144x^3+792x^2)\\
&+a^2(-144x^4-204x^2-78x+138)
 +a(216x^3+72x^2)-65x^2-50x+7.
\end{aligned}
\tag{10}
\]
These have 17 and 14 monomials, respectively, and degree six.

### 3.1. Both endpoint functions increase with a

Use \(c=6/5-a,\ z=x-3/2\) again. Differentiation gives
\[
6048a^5\partial_aE_x=\Phi_x(c,z),\qquad
3024a^5\partial_aE_{ax}=\Phi_{ax}(c,z),
\tag{11}
\]
with the complete polynomials
\[
\begin{aligned}
\Phi_x={}&c^3(216z^2+603z+837/2)\\
&+c^2(432z^3+10452z^2/5+17616z/5+9507/5)\\
&-c(3024z^3/5+108252z^2/25+230616z/25+145107/25)\\
&+288z^4+34992z^3/25+467834z^2/125
 +748022z/125+902113/250,\\
\Phi_{ax}={}&-c^3(36z^3+360z^2+837z+567)\\
&+c^2(72z^4+2808z^3/5+2370z^2+21651z/5+26247/10)\\
&-c(864z^4/5+25758z^3/25+16749z^2/5
 +276057z/50+318159/100)\\
&+2592z^4/25+61236z^3/125+32351z^2/25
 +260152z/125+616183/500.
\end{aligned}
\tag{12}
\]
There are 16 and 19 monomials, with degrees five and six.
Use \(c\le1/5\) only on the negative groups, and discard the
nonnegative groups containing \(c^2,c^3\). The resulting bounds are
\[
\begin{aligned}
\Phi_x&\ge288z^4+31968z^3/25+359582z^2/125
 +517406z/125+611899/250>0,\\
\Phi_{ax}&\ge1728z^4/25+35442z^3/125+3106z^2/5
 +242573z/250+73939/125>0.
\end{aligned}
\tag{13}
\]
Each lower polynomial has five monomials and degree four.

### 3.2. The outer cap supplies a rational lower endpoint

The cap in (2) implies \(a\ge4x/7\), since
\[
\frac{x(x+2)}6-\frac{16x^2}{49}
=\frac{x(98-47x)}{294}>0\quad(x\le2).
\]
By (13), lower \(a\) to 1 for \(x\le7/4\), and to \(4x/7\) for
\(x\ge7/4\).

At \(a=1\), both expressions in (9) are
\[
\frac{2719+250x-449x^2+72x^3-144x^4}{12096}.
\tag{14}
\]
The five-term numerator decreases for \(x\ge3/2\), because its
derivative is \(250-898x-72x^2(8x-3)<0\).
The expression's value at \(x=7/4\) is \(121/1792>0\).

At \(a=4x/7\), put \(v=x-7/4\in[0,1/4]\). The two expressions
in (9) are \(R_x(v)/(3096576x^4)\) and
\(R_{ax}(v)/(3096576x^4)\), where
\[
\begin{aligned}
R_x={}&64512v^6+652032v^5+2685360v^4+5961480v^3\\
&+7849555v^2+5926011v+7844067/4,\\
R_{ax}={}&-39168v^6-669312v^5-3261840v^4-6495888v^3\\
&-4575620v^2+1150422v+7844067/4.
\end{aligned}
\tag{15}
\]
Both have seven monomials and degree six. The first is positive
termwise. For the second, all adverse terms at \(v=1/4\) sum to
\[
39168/4^6+669312/4^5+3261840/4^4
 +6495888/4^3+4575620/4^2=1603517/4.
\]
Discarding its positive linear term gives
\(R_{ax}\ge3120275/2>0\). This proves (8).

## 4. Keep the beta-dependent upper norm throughout the motion

Differentiating (3) gives
\[
(u_\ell)_\beta
=-\frac{15(x-1)^3}{8(x+1)(35x+13)(\beta-1)^2}.
\]
Using \(\beta\ge x\),
\[
0\le-(u_\ell)_\beta
\le\frac{15(x-1)}{8(x+1)(35x+13)}\le\frac5{664}.
\tag{16}
\]
The last inequality follows from the three-term quadratic
\[
(x+1)(35x+13)-249(x-1)
=35x^2-201x+262=(2-x)(131-35x)\ge0.
\]
Combining (7), (8), and (16) yields
\[
\begin{aligned}
\frac{d}{d\beta}F_0(x,a,\beta,u_\ell(x,\beta))
&=(F_0)_\beta+(F_0)_u(u_\ell)_\beta\\
&<-7/5120+5/3984=-143/1274880<0.
\end{aligned}
\tag{17}
\]
For \(u_f\) the second term vanishes. This proves (1).

## 5. Exact remaining caller obligations

At the actual norm, first use concavity of \(F_0\) in \(u\) on
\([u_f(x),u_\ell(x,\beta)]\), supplied by the original note.
Then increase beta on each expressly specified norm curve to
\[
\beta_+=x+\frac{x(7x+1)}{4x^2+11x+1}(a-1).
\]
The order theorem gives \(\beta\le\beta_+\le ax\); all other
conditions in (2) are independent of beta. The old B-domain \(F_0\)
task is therefore reduced to
\[
F_0(x,a,\beta_+,u_f(x))>0,\qquad
F_0(x,a,\beta_+,u_\ell(x,\beta_+))>0.
\tag{18}
\]
These two bivariate signs remain unproved here. The reduction makes
no assertion about beta monotonicity in the old S or A domains.
It never replaces the original \(u_\ell\) by a new beta endpoint's
value without the total derivative (17).

All sign polynomials are printed. After clearing their small rational
coefficient denominators, they remain within the stated monomial,
degree and coefficient budgets. Exact rational symbolic checks
verified the identities as a transcription check. No Lean compilation
or CI was run.

