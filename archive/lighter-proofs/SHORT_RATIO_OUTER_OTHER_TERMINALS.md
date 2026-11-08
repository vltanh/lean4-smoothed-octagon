# Outer upper-ratio tests: middle and upper terminals

This note proves both exact-log tests \(H_0,H_1\) strictly negative
on the two larger-shape terminal families

\[
\frac{13}{6}\le x\le\frac{12}{5},\quad
\frac58\le c\le\frac78,\quad
b=x+c(a-1),\quad a\in\{3/2,x\},
\tag{1}
\]

at the incoming norm

\[
u=u_v=\frac34+\frac{2(x-1)^2}{(x+1)(35x+13)}.
\tag{2}
\]

The tests and transport are exactly (3),(6) of
[the source outer-ratio note](../../archive/notes/MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_SIGN.md).
The [beta lemma](SHORT_RATIO_OUTER_BETA.md) proves
\(3/4<u_v<4/5\), and shows that this middle terminal also bounds
the smaller-shape norm \(u_s\) at \(a=3/2\).

Write \(S=x+1\), \(Z=(a+b)/a\), \(y=2Z/7\), and
\(h=x-2\). Since \(b\le ax\), all these points have
\(0<y\le34/35<1\). We use the elementary bounds

\[
\log y\le y-1,\qquad
\log y\le q(y):=(y-1)-\frac12(y-1)^2.
\tag{3}
\]

For the second inequality, integrate \((1-v)^{-1}\ge1+v\)
from zero to \(1-y\). These two coarse logarithm bounds suffice
at the present terminals.

## 1. The shared shape \(a=3/2\)

Let \(J_j\) be \(H_j\) on this face with \(y-1\) replacing
\(\log y\), at the norm (2). Set \(t=c-5/8\), so

\[
1/6\le h\le2/5,\qquad0\le t\le1/4.
\]

The positive-denominator source identities are

\[
P_0=-47628S(35x+13)(c+2x+3)J_0,
\]
\[
P_1=-31752S(35x+13)(c+2x+3)J_1.
\tag{4}
\]

After specializing \(a=3/2,u=u_v,b=x+c/2\) and only then
expanding, the complete polynomials are

\[
\begin{aligned}
P_0(h,t)=\frac1{2048}\big[&(29622272)h^{8}\\
 &{}+(59244544 t + 115212288)h^{7}\\
 &{}+(44433408 t^{2} + 263651328 t - 1504835584)h^{6}\\
 &{}+(14811136 t^{3} + 222658560 t^{2} - 1498626048 t - 11746991104)h^{5}\\
 &{}+(1851392 t^{4} + 82526208 t^{3} - 280657408 t^{2} - 11527271936 t - 30345562348)h^{4}\\
 &{}+(11354112 t^{4} + 90894336 t^{3} - 3195671552 t^{2} - 25752693184 t - 27186736708)h^{3}\\
 &{}+(22335488 t^{4} - 154900480 t^{3} - 6179157120 t^{2} - 22281431136 t + 14420692653)h^{2}\\
 &{}+(14745600 t^{4} - 278351872 t^{3} - 4590814720 t^{2} - 1399708608 t + 35831008232)h\\
 &{}+(3092480 t^{4} - 93784064 t^{3} - 1136097152 t^{2} + 8441036000 t + 5522142723)\big].
\end{aligned}
\]

\[
\begin{aligned}
P_1(h,t)=\frac1{256}\big[&(-1851392)h^{7}\\
 &{}+(- 2777088 t - 100117504)h^{6}\\
 &{}+(- 1388544 t^{2} - 105794560 t - 848275648)h^{5}\\
 &{}+(- 231424 t^{3} - 30706432 t^{2} - 767762016 t - 2631801700)h^{4}\\
 &{}+(- 1419264 t^{3} - 177395968 t^{2} - 2110288736 t - 2736950236)h^{3}\\
 &{}+(- 2791936 t^{3} - 430245056 t^{2} - 2276207224 t + 1436109239)h^{2}\\
 &{}+(- 1843200 t^{3} - 448134656 t^{2} - 247508736 t + 3486400264)h\\
 &{}+(- 386560 t^{3} - 154005312 t^{2} + 887736184 t + 261744249)\big].
\end{aligned}
\]

Discard positive terms with a positive power of \(t\), and replace
\(t^k\) by \(4^{-k}\) in negative terms. The resulting complete
lower polynomials are

\[
\begin{aligned}
\ell_0(h)=\frac1{2048}\big[&(29622272)h^{8}\\
 &{}+(115212288)h^{7}\\
 &{}+(-1504835584)h^{6}\\
 &{}+(-12121647616)h^{5}\\
 &{}+(-33244921420)h^{4}\\
 &{}+(-33824639476)h^{3}\\
 &{}+(8461717229)h^{2}\\
 &{}+(35189805912)h\\
 &{}+(5449671275)\big].
\end{aligned}
\]

\[
\begin{aligned}
\ell_1(h)=\frac1{256}\big[&(-1851392)h^{7}\\
 &{}+(-100811776)h^{6}\\
 &{}+(-874811072)h^{5}\\
 &{}+(-2825664972)h^{4}\\
 &{}+(-3275631844)h^{3}\\
 &{}+(840123493)h^{2}\\
 &{}+(3396485864)h\\
 &{}+(252112877)\big].
\end{aligned}
\]

Putting \(h=1/6\) in positive terms and \(h=2/5\) in negative
terms gives

\[
\ell_0>4000000,\qquad\ell_1>2000000.
\tag{5}
\]

Thus \(P_0,P_1>0\), so (3),(4) prove \(H_0,H_1<0\) on
the whole middle family, without a beta subdivision.

## 2. The upper shape \(a=x\)

At this shape \(D=S^2\), so the transport is independent of beta.
The two small source identities, before the norm substitution, are

\[
49x^3w=6x^4+54x^3+5x^2+5x-1
-u(6x^4+17x^3+15x^2+3x-1),
\tag{6}
\]
\[
7x^2SE_L=6x^4+12x^3-x^2-x-1
-u(6x^4+10x^3+x^2-4x-1).
\tag{7}
\]

In particular

\[
w_u=-\frac{S^3(6x-1)}{49x^3}<0.
\]

At the larger scalar norm \(4/5\), the complete quartic is

\[
980x^3\{w(x,4/5)-3/4\}
=24h^4+265h^3+874h^2+1136h+508>0.
\tag{8}
\]

Consequently \(w(x,u_v)>3/4\). This is a derived scalar sign;
no outgoing physical norm condition has been continued to the face.

Now let \(K_j\) be \(H_j\) at \(a=x,u=u_v\), with
\(q(2Z/7)\) in place of the logarithm. Since
\(Z=2+c(1-1/x)<8/3\), differentiation with respect to \(Z\)
gives

\[
(K_0)_{ZZ}=\frac2{Z^3}-\frac4{49}
>\frac{27}{256}-\frac4{49}=\frac{299}{12544}>0,
\]
\[
(K_1)_{ZZ}=\frac{2\{1+7(w-3/4)\}}{Z^3}-\frac4{49}>0.
\tag{9}
\]

Both comparison functions are convex in beta. It therefore suffices
to prove their signs at \(c=5/8,7/8\). Define
\(B_5=21x-5\), \(B_7=23x-7\), and

\[
Q_{0,i}=-3136x^4S B_i(35x+13)K_0\big|_{c=i/8},
\]
\[
Q_{1,i}=-1568x^3S B_i(35x+13)K_1\big|_{c=i/8},
\qquad i=5,7.
\tag{10}
\]

All factors are positive. Their complete univariate expansions are

\[
\begin{aligned}
Q_{0,5}(h)=\frac1{1}\big[&(234738)h^{8}\\
 &{}+(3667214)h^{7}\\
 &{}+(24648615)h^{6}\\
 &{}+(92851363)h^{5}\\
 &{}+(213716967)h^{4}\\
 &{}+(306333042)h^{3}\\
 &{}+(264962511)h^{2}\\
 &{}+(124682189)h\\
 &{}+(23749793)\big].
\end{aligned}
\]

\[
\begin{aligned}
Q_{0,7}(h)=\frac1{1}\big[&(264546)h^{8}\\
 &{}+(4135722)h^{7}\\
 &{}+(27918195)h^{6}\\
 &{}+(105942595)h^{5}\\
 &{}+(246387335)h^{4}\\
 &{}+(358167934)h^{3}\\
 &{}+(315902859)h^{2}\\
 &{}+(152970501)h\\
 &{}+(30522633)\big].
\end{aligned}
\]

\[
\begin{aligned}
Q_{1,5}(h)=\frac1{1}\big[&(111132)h^{7}\\
 &{}+(1470458)h^{6}\\
 &{}+(8061427)h^{5}\\
 &{}+(23480036)h^{4}\\
 &{}+(38542410)h^{3}\\
 &{}+(34349390)h^{2}\\
 &{}+(13879207)h\\
 &{}+(1100756)\big].
\end{aligned}
\]

\[
\begin{aligned}
Q_{1,7}(h)=\frac1{1}\big[&(128628)h^{7}\\
 &{}+(1724592)h^{6}\\
 &{}+(9663133)h^{5}\\
 &{}+(29057180)h^{4}\\
 &{}+(50024402)h^{3}\\
 &{}+(48266480)h^{2}\\
 &{}+(23049277)h\\
 &{}+(3623652)\big].
\end{aligned}
\]

Every coefficient is positive, so (10) proves strict negativity at
both beta endpoints. Convexity (9) then proves \(K_0,K_1<0\)
throughout the upper family. The logarithm bound (3) gives the desired
\(H_0,H_1<0\).

## 3. Source identities and size boundary

For (4), substitute the fixed shape and norm before clearing the
displayed denominator. Keep the five original contributions to
\(49a^4w\), the two contributions to \(7a^2E_L\), and the
remaining terms of the test separate. Each source contribution is
a bivariate polynomial of degree at most eight after clearing.

For (10), first simplify to (6),(7); their ten-monomial identities
have degree five in the two variables \(x,u\). Insert (2), then
specialize the beta slope and clear the positive denominator.
This order avoids any larger unused source expansion.

| Polynomial | Monomials | Degree |
|---|---:|---:|
| \(P_0\) | 35 | 8 |
| \(P_1\) | 26 | 7 |
| \(Q_{0,5},Q_{0,7}\) | 9 each | 8 |
| \(Q_{1,5},Q_{1,7}\) | 8 each | 7 |
| (8) | 5 | 4 |

Including (8), there are 58 individual normalized source contributions
for this note. Each has at most 35 monomials and degree at most eight.
Their largest coefficient numerator is \(51,946,975,157\), and the
largest coefficient denominator is 2048. The displayed lower
polynomials and all integer coefficients inside the brackets also
satisfy the twelve-digit bound. The proof uses no subdivision in x
and no coefficient certificate premise.
