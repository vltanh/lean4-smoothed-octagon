# Reciprocal-shape reduction of the actual outer B residual F1

## Scope and caller

This is the shape reduction for the actual B part of
MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN, using the \(F_1\) source
printed in [the beta note](SHORT_OUTER_BETA.md). It applies on
\[
 3/2\le x\le2,\quad 1\le a\le6/5,\quad 6a^2\ge x(x+2),
\]
with the original beta interval and original incoming-norm interval.
The actual B \(F_0\) sign has a separate completed proof in
[the low-shape terminal note](SHORT_OUTER_LOW_SHAPE_TERMINAL.md).
No \(F_0\) inequality is used below.

The conclusion here is a reduction to four curves on each shape boundary.
Their terminal signs are separate dependencies.

## 1. Freeze beta slope and incoming norm

Write \(\beta=x+C(a-1)\). On the original B domain, its two slope
bounds lie in
\[
 1/2\le C\le10/13.
\]
Indeed the original lower slope is at least \(24/43>1/2\), and the
original upper slope is at most \(10/13\), as in the beta note.
All the enlarged beta values still satisfy \(x\le\beta\le ax\), since
\(C\le x\).

The original norm bounds imply
\[
 3/4\le u\le19/25.
 \tag{1}
\]
For clarity, the original upper endpoint satisfies \(u_\ell\le u_v\), where
\[
 u_v=3/4+\frac{2(x-1)^2}{(x+1)(35x+13)}.
\]
The beta-dependent factor multiplying \(u_v-3/4\) in \(u_\ell\) is
at most one, because its denominator minus numerator is
\(15(\beta-x)/16\ge0\).
Also
\[
 \frac{19}{25}-u_v
 =\frac{-165x^2+448x-187}{100(x+1)(35x+13)}>0.
 \tag{2}
\]
The three-monomial quadratic numerator is concave and has endpoint values
\(455/4\) and \(49\) on \([3/2,2]\). This proves (1).

By [the constant-norm beta lemma](SHORT_OUTER_BETA_WIDE_NORM.md),
\(F_1\) is concave in beta throughout the enlarged rectangle with the
same fixed norm \(u\). Reduce first to \(C=1/2,10/13\).
At fixed \(x,a,\beta\), it is also concave in \(u\):
\[
 \partial_u^2F_1=-\frac{(6a^2+1)^2(x+1)^2}{288a^4}<0.
 \tag{3}
\]
Only \(\Gamma\) contributes a quadratic term in \(u\); all the other
source terms are affine. Thus it suffices to use the four constant pairs
\[
 (C,u)\in\{1/2,10/13\}\times\{3/4,19/25\}.
 \tag{4}
\]
In particular, the beta-dependent upper endpoint is not moved along a
shape comparison: the norm is now one of two constants.

## 2. The reciprocal-shape curvature formula

Put
\[
 r=1/a,\quad S=x+1,\quad e=x-C,\quad d=1+C,\quad z=d+er,
\]
\[
 A_0=S-1+1/S,\quad E_0=S(u-1)+1/S,\quad J_2=Su+A_0,
\]
\[
 d_1=2[x-C(1+x)],\qquad d_2=1+2x-2x^2+2Cx,
\]
\[
 W_4=(S-d_2)(A_0-ud_2),\qquad W_3=d_1(2ud_2-J_2).
 \tag{5}
\]
These are the quartic and cubic coefficients of \(W=49w\) in the
factored source quartic printed in
[the residue proof](SHORT_OUTER_RECIPROCAL_RESIDUE.md).
Polynomial division of that quartic by \(z=d+er\) writes
\[
 F_1+\frac7{96}\ell(2z/7)
   =b_4r^4+b_3r^3+b_2r^2+b_1r+b_0+\frac{Q}{z}.
 \tag{6}
\]
The coefficients needed for a second derivative are
\[
 b_4=-\frac{(Su-A_0)^2}{576},\qquad
 b_3=-\frac{W_4}{96e},
\]
\[
 96b_2=2(4-2S)u-2E_0J_2+(2ud_2-J_2)
                   -W_3/e+dW_4/e^2.
 \tag{7}
\]
The unused \(b_0,b_1\) vanish after two derivatives and need no sign claim.
The division is performed in \(r\) with the coefficient expressions
opaque; it is a quartic identity, not a global expansion in \(r,x,u\).
The source-to-sign identities needed from (7) are printed fully in Section 3.

We have \(b_4\le0\), \(b_3<0\), and \(Q<0\). The last claim is the
separate residue theorem for the two slopes in (4).
For \(b_3\), note first that
\[
 A_0-\frac{19}{25}S=\frac{(2x-3)(3x-2)}{25S}\ge0,
 \tag{8}
\]
a three-monomial quadratic identity after clearing \(25S\).
Also \(S-d_2=x(2e-1)>0\). Therefore
\[
 A_0-ud_2=(A_0-uS)+u(S-d_2)>0,
\]
and \(W_4>0\).

Set \(M_1=5b_3+2b_2\). Section 3 proves
\[
 M_1<-1/25.
 \tag{9}
\]
Since \(5/6\le r\le1\), the polynomial contribution to the second
\(r\) derivative is at most \(M_1\). The pole term contributes
\(2Qe^2/z^3<0\).

The fixed rational logarithm majorant obeys
\(\ell''(y)\ge-1/y^2\) for \(0<y\le1\).
Here \(0<2z/7\le6/7\). Moreover
\[
 \frac e z\le\frac e{3/2+(5/6)e}\le\frac6{11}<\frac35,
\]
using \(d\ge3/2\), \(e\le3/2\), and positivity.
Its possible positive contribution is thus at most
\[
 \frac7{96}\frac{e^2}{z^2}\le\frac{21}{800}.
\]
Consequently
\[
 \boxed{\partial_r^2F_1<-1/25+21/800=-11/800<0.}
 \tag{10}
\]

## 3. Four complete small curvature polynomials

For each pair in (4), write
\[
 -96e^2S^2(M_1+1/25)=cP(x),
 \tag{11}
\]
where \(c>0\) is specified below. Each identity has eight monomials
and degree seven in \(x\). With \(v=x-3/2\ge0\), each printed shift
has positive coefficients, which proves (9).

For \(C=1/2,u=3/4\), \(c=1/400\) and
\[
 P=6000x^7-6300x^6-13200x^5+16189x^4+1914x^3-8348x^2+2718x-509.
\]
\[
\begin{aligned}
 4P(3/2+v)={}&24000v^7+226800v^6+854400v^5+1653256v^4\\
             &+1759692v^3+1006891v^2+265530v+14875.
\end{aligned}
\]

For \(C=1/2,u=19/25\), \(c=1/1250\) and
\[
 P=19000x^7-20012x^6-41536x^5+51598x^4+6212x^3-26657x^2+8425x-1578.
\]
\[
\begin{aligned}
 8P(3/2+v)={}&152000v^7+1435904v^6+5408848v^5+10472384v^4\\
             &+11175940v^3+6450200v^2+1749875v+116250.
\end{aligned}
\]

For \(C=10/13,u=3/4\), \(c=1/219700\) and
\[
\begin{aligned}
 P={}&3295500x^7-5767125x^6-5926050x^5+14610677x^4\\
     &-1693376x^3-7338358x^2+2416620x-661700.
\end{aligned}
\]
\[
\begin{aligned}
 64P(3/2+v)={}&210912000v^7+1845480000v^6+6264460800v^5
                  +10547569328v^4\\
              &+9425601904v^3+4471655228v^2+1037584440v+20348125.
\end{aligned}
\]

For \(C=10/13,u=19/25\), \(c=1/1373125\) and
\[
\begin{aligned}
 P={}&20871500x^7-36593232x^6-37204973x^5+92791653x^4\\
     &-10781048x^3-46928962x^2+15088680x-4102800.
\end{aligned}
\]
\[
\begin{aligned}
 8P(3/2+v)={}&166972000v^7+1460460144v^6+4957074512v^5
                 +8353429704v^4\\
             &+7495861790v^3+3609034075v^2+874904250v+28606875.
\end{aligned}
\]
Every shift identity has eight monomials and degree seven.
The largest displayed coefficient is \(10547569328\), eleven digits.

## 4. The two shape boundaries

Define the lower comparison shape by
\[
 a_*(x)=
 \begin{cases}
 1,&3/2\le x\le5/3,\\
 (6x+3)/13,&5/3\le x\le2.
 \end{cases}
 \tag{12}
\]
It satisfies \(a_*(x)\le a\) at every original point. For the second
piece, the exact three-monomial identity is
\[
 \frac{x(x+2)}6-\left(\frac{6x+3}{13}\right)^2
   =\frac{-47x^2+122x-54}{1014}>0.
 \tag{13}
\]
The quadratic numerator is concave and has endpoint values \(169/9\)
and \(2\). Thus its sign is strict throughout that interval.
The first piece uses the original \(a\ge1\).

For fixed \(x,C,u\) in (4), (10) applies on the entire enlarged shape
interval \(a_*(x)\le a\le6/5\), even where the original outer cap would
fail at a comparison point. Concavity in \(r\) reduces \(F_1\) to the
two values at \(a=6/5\) and \(a=a_*(x)\).
Together with Section 1, this is the exact four-curve reduction of the
actual B \(F_1\) sign.

The rational lower chord is slightly below the sharper 97-denominator
chord used for \(F_0\). Its endpoint retains a positive \(F_1\) margin,
while making the source fractions in the remaining terminal proof much
smaller. No improvement of the original numerical margin is claimed.
