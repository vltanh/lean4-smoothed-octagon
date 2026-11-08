# A concave first-event comparison on the reverse order face

Date: 2026-11-07 UTC. Hand exclusion of one shape lower face;
the other two lower faces remain open.

The [reverse order bound](MIXED_NONSHORT_REVERSE_ORDER_BOUND.md) supplies
k>=2t+x. This note treats the lower face k=2t+x when it is the largest
retained lower bound. It reduces the first-event factor to two endpoints
and proves both strictly positive.

## 1. The factor interval on this face

Use

\[
0<t<1/2,\quad x>0,\quad c=1-t,\quad p=t+x,\quad
W=1+x,\quad k=2t+x,\quad Y=x(x+2).
\]

Since this lower face has k>=1, one has p>=c. Keep the exact incoming
secant v=Sec(t,c,p), its actual missing-control floor, and the
k-independent star bound q<W/p:

\[
v\ge F_{p/W}(q),\qquad 1<q<W/p.
\]

The floor can be written

\[
F_{p/W}(q)=\operatorname{Sec}(W/q-p,p,c).
\]

Here 0<W/q-p<c. The swapped-secant order from the cited note gives

\[
\operatorname{Sec}(t,c,p)\le\operatorname{Sec}(t,p,c).
\]

Starting-point monotonicity on the secant with middle p and endpoint c
therefore forces W/q-p>=t. Hence

\[
\boxed{1<q\le W/k.}
\tag{1}
\]

The final inequality is strict when p>c.

## 2. Concavity of the incident-upper residual

On this face,

\[
B=k+2tx+x^2=Wk,\qquad Z=qB/W=qk,\qquad r=Z-p.
\]

Define the central upper envelope and its outgoing norm by

\[
H_0=\frac{k}{t}(v-1+t^2)+t(2-t),\qquad
w_U=\frac{k^2-kt+t^2+H_0Y+vY^2}{B^2}.
\]

The normalized incident-upper residual is

\[
R(q)=c+Z-\frac{p^2}{W}-\frac{p^2}{Z}
 +\frac{p^3}{B}-p\log q-Wv-Zw_U
 +\frac{p(H_0+2vY)}{B}.
\tag{2}
\]

The variables t,x,k,v,B and wU stay fixed as q varies. Thus

\[
R'(q)=k[g_p(r)-w_U],\qquad
R''(q)=k^2\frac{p(r-p)}{(r+p)^3}\le0.
\tag{3}
\]

Indeed (1) gives t<=r<=c<=p throughout the closed comparison
interval. Therefore R is concave there and

\[
R(q)\ge
\min\{R(1),R(W/k)\}.
\tag{4}
\]

The necessary inequality R(q)<0 can only survive if at least one of
these two endpoint values is negative. This is a scalar comparison;
the endpoint q=1 is not called an actual positive-duration switch.

## 3. The endpoint q=1 is strictly positive

Let N=tBqW R, the usual positive multiple of the residual. At q=1,
substitution in (2) and collection give the short exact identity

\[
N(1)=x\{[k+tY](1-v)-2t(1-t)(t+x)\}.
\tag{5}
\]

Use

\[
v=1+\frac{(1-t)^2}{W}
       -\frac{1-t}{x}\log W,\qquad
k+tY=tW^2+t+x.
\]

The first two positive atanh terms give

\[
\log W>
\frac{2x}{x+2}+\frac{2x^3}{3(x+2)^3}.
\]

Substituting this lower bound in (5) gives

\[
N(1)>
\frac{(1-t)x^3}{3W(x+2)^3}\,P(t,x),
\tag{6}
\]
\[
\begin{aligned}
P(t,x)={}&t(3t-1)x^3+(18t^2-15t+5)x^2\\
 &+(36t^2-40t+14)x+(24t^2-32t+12).
\end{aligned}
\tag{7}
\]

For completeness, every sign in this four-term polynomial has a short
proof. The three quadratic coefficients have the exact lower bounds

\[
\begin{aligned}
18t^2-15t+5&=18(t-5/12)^2+15/8,\\
36t^2-40t+14&=36(t-5/9)^2+26/9,\\
24t^2-32t+12&=24(t-2/3)^2+4/3.
\end{aligned}
\]

If t>=1/3, the cubic coefficient is nonnegative and P>0 follows
immediately. If t<1/3, use t(1-3t)<=1/12 and the retained duration
bound x<5/2. Then

\[
t(3t-1)x^3>-\frac5{24}x^2,
\qquad
P(t,x)>
\frac53x^2+\frac{26}{9}x+\frac43>0.
\tag{8}
\]

The duration bound follows already from the hand upper-envelope
lemmas, and the sharper 7/3 duration estimate also implies it.
All factors multiplying P in (6) are positive. Consequently

\[
\boxed{R(1)>0.}
\tag{9}
\]

## 4. The remaining endpoint

Equations (4) and (9) show that the necessary residual inequality on
this entire lower face implies

\[
\boxed{R(W/k)<0.}
\tag{10}
\]

At this endpoint r=c. Its retained domain includes t<2/5,
k=2t+x>=1, k>=(29/4)t^2, the exact incoming secant and its derivative
floor. The next section proves the opposite sign in (10).
The other lower faces k=1 and k=(29/4)t^2 are not excluded by this note.


## 5. Positivity at r=c

**Status:** accepted in independent internal hand review; see
[HAND_ENDPOINT_REDUCTIONS_AUDIT](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).

The accepted high-ratio and scale bounds give t<2/5 and
k>=(29/4)t^2. On the present face they imply x>1/4.
Indeed, if x<=1/4, then k=2t+x>=1 forces t>=3/8. But

\[
f(t)=29t^2/4-2t-1/4
\]

strictly increases for t>=3/8 and satisfies f(3/8)=5/256>0.
Thus (29/4)t^2>2t+1/4>=k, a contradiction.

Put

\[
h=1-2t,\qquad s=k-1,\qquad x=h+s.
\]

The entire remaining domain is contained in

\[
\boxed{1/5<h<1,\qquad 0\le s<4/3,\qquad h+s>1/4.}
\tag{11}
\]

For the s bound, d/c=p/c<7/3 by the sharper duration lemma in
[MIXED_NONSHORT_REVERSE_EXACT_SHAPE_COMPARISON](MIXED_NONSHORT_REVERSE_EXACT_SHAPE_COMPARISON.md).
Here p=c+s, so s<4c/3=2(1+h)/3<4/3.

### Replace only the two logarithms in their justified directions

Set

\[
\bar v=1+\frac{(1-t)^2}{W}
-\frac{2(1-t)}{x+2}\left[1+\frac{x^2}{3(x+2)^2}\right],
\]
\[
L_+(q)=\frac{(q-1)(q^2+10q+1)}{6q(q+1)}.
\]

The first two positive atanh terms give v<bar v. The elementary
logarithm upper bound used in the explicit turn-floor argument gives
log q<Lplus(q) for q>1.

The residual (2) strictly decreases in each of v and log q.
For clarity, its v derivative is

\[
R_v=-\frac{xI}{tWB},
\]
\[
I=k+tx+tW(k-2t)
 +(q-1)\{k(x+2)+tx(x+2)^2\}>0.
\tag{12}
\]

Here k>=1>2t. Its log q coefficient is -p<0.
Thus replacing v and log q by bar v and Lplus gives a strict lower
bound bar R for the exact residual. In the rest of this section q=W/k.

### One explicit algebraic identity

Substitute the two rational bounds into (2), using B=Wk and q=W/k.
Clearing positive denominators gives

\[
\boxed{\bar R(W/k)=
\frac{P(h,s)}
 {24t k^2 W^2(W+k)(x+2)^3},}
\qquad P(h,s)=\sum_{j=0}^7 C_j(h)s^j,
\tag{13}
\]

where the coefficient polynomials, grouped to expose their signs, are

\[
C_0=h^3(1+h)^2
 [-16+24h+120h^2+140h^3+78h^4+23h^5+3h^6],
\]
\[
C_1=h^3(1+h)
 [8+396h+1020h^2+1080h^3+597h^4+179h^5+24h^6],
\]
\[
\begin{aligned}
C_2=h[{}&48+144h+420h^2+1718h^3+3455h^4\\
       &+3498h^5+1946h^6+594h^7+81h^8],\\
C_3={}&16+216h+396h^2+824h^3+2440h^4\\
      &+3562h^5+2558h^6+942h^7+150h^8,\\
C_4={}&40+316h+268h^2+510h^3+1643h^4\\
      &+1833h^5+873h^6+165h^7,\\
C_5={}&40+184h-70h^2+117h^3+638h^4+471h^5+108h^6,\\
C_6={}&18+29h-108h^2+46h^3+136h^4+39h^5,\\
C_7={}&2-4h-20h^2+16h^3+6h^4.
\end{aligned}
\tag{14}
\]

Identity (13) is a single algebraic collection from the rational
expressions displayed above. The proof uses the following short
bounds on its four negative higher-order terms, not a runtime
coefficient-sign test.

### Absorb the four negative terms above the linear part

The only negative monomials among C2,...,C7 are the four explicitly
displayed terms -70h^2, -108h^2, -4h and -20h^2.
First,

\[
184h s^5-70h^2s^5\ge114h s^5\ge0.
\]

Next use h<=1 and s<=4/3 to get

\[
\begin{aligned}
316h s^4-108h^2s^6-4hs^7-20h^2s^7
&\ge hs^4\left[
316-108\frac{16}{9}-24\frac{64}{27}\right]\\
&=\frac{604}{9}hs^4\ge0.
\end{aligned}
\tag{15}
\]

All unused terms of C2s^2+...+C7s^7 are explicitly nonnegative in
(14). Therefore

\[
P(h,s)\ge C_0(h)+C_1(h)s.
\tag{16}
\]

### The remaining constant and linear terms

Let F(h) be the bracket in C0. Its derivative is positive for h>0,
and F(1/4)=63/4096>0. Thus if h>=1/4, both terms on the right
of (16) are nonnegative and C0 is strictly positive.

Suppose 1/5<=h<=1/4. Condition (11) gives s>1/4-h, while C1>0.
Direct subtraction gives

\[
C_0+C_1(1/4-h)=\frac{h^3(1+h)}4\,Q(h),
\tag{17}
\]
\[
Q(h)=-56+396h+12h^2-1960h^3-2851h^4
                      -1805h^5-588h^6-84h^7.
\]

This polynomial is strictly concave on [1/5,1/4], since

\[
Q''(h)=24-11760h-34212h^2-36100h^3-17640h^4-3528h^5
<24-11760/5<0.
\]

Its two endpoint values are

\[
Q(1/5)=220476/78125>0,\qquad Q(1/4)=315/4096>0.
\tag{18}
\]

A concave function is at least the smaller of its endpoint values.
Thus Q>0 on the whole interval. Equations (16)--(18) prove P>0
also in this last case.

All factors in the denominator of (13) are positive. Consequently

\[
\boxed{R(W/k)>\bar R(W/k)>0.}
\tag{19}
\]

This contradicts (10), completing the exclusion of the lower face
k=2t+x. The proof also covers ties in the maximum of the three lower
bounds. The faces where k=1 or k=(29/4)t^2 is the strict maximum
still require separate hand signs.
