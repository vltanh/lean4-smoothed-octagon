# Hand exclusion of the nonshort reverse successor

Date: 2026-11-07 UTC. Complete hand proof, accepted in the
[independent reverse-case audit](MIXED_NONSHORT_REVERSE_HAND_AUDIT.md).

This note completes the reverse-next part of the smaller-nonshort
problem by hand. It combines the
[actual reverse order bound](MIXED_NONSHORT_REVERSE_ORDER_BOUND.md),
the [unit-shape exclusion](MIXED_NONSHORT_UNIT_SHAPE_HAND_EXCLUSION.md),
and the [order-face exclusion](MIXED_NONSHORT_REVERSE_ORDER_FACE_REDUCTION.md)
with one elementary derivative comparison on the remaining scale face.
No interval cover or transported artificial Casimir is used.

## 1. A useful strengthened form of the order-face theorem

The following form of the proved order-face sign will be used.

**Order-face lemma.** Suppose
\[
0<t<2/5,\quad x>1/4,\quad k_o=2t+x\ge1,\quad
x<7/3-(10/3)t.
\]
Keep
\[
v=\operatorname{Sec}(t,1-t,t+x),\qquad
v\ge F_{(t+x)/(1+x)}(q),\qquad
1<q<\frac{1+x}{t+x}.
\]
Then \(N(k_o)>0\).

To check this precise scope, the first part of the cited order-face
proof uses \(k_o\ge1\) to give \(p=t+x\ge c=1-t\).
The incoming floor and the swapped-secant lemma then give
\(q\le(1+x)/k_o\). Its concavity comparison reduces \(R\) to \(q=1\)
and \(q=(1+x)/k_o\). The first endpoint is positive for \(x<5/2\),
which follows from the stated duration bound.

At the second endpoint, the cited proof sets
\[
h=1-2t\in(1/5,1),\qquad s=k_o-1\ge0,\qquad x=h+s.
\]
The duration bound gives \(s<4/3\).
Its displayed rational polynomial sign uses exactly these bounds and
\(x>1/4\). The earlier scale inequality \(k_o\ge29t^2/4\) was used
only to derive \(x>1/4\); it is not used again in the sign argument.
Taking \(x>1/4\) as a hypothesis therefore gives the lemma directly.
No claim is made about a shape with \(x\le1/4\).

## 2. The remaining scale strip

For arbitrary positive \(k\), use
\[
\begin{gathered}
c=1-t,\quad p=t+x,\quad W=1+x,\quad X=x+2,\quad Y=x(x+2),\\
B_k=k+2tx+x^2,\qquad Z_k=qB_k/W,\\
H_{0,k}=\frac{k}{t}(v-1+t^2)+t(2-t),\qquad
w_{U,k}=\frac{k^2-kt+t^2+H_{0,k}Y+vY^2}{B_k^2},
\end{gathered}
\]
\[
\begin{aligned}
R_k={}&c+Z_k-\frac{p^2}{W}-\frac{p^2}{Z_k}
+\frac{p^3}{B_k}-p\log q-Wv-Z_kw_{U,k}
+\frac{p(H_{0,k}+2vY)}{B_k},\\
N_k={}&tB_kqW R_k.
\end{aligned}
\tag{1}
\]
The subscript on \(N_k\) denotes its shape parameter, not a derivative.

Use the same rational quantities as in the unit-shape proof:
\[
\bar v=1+\frac{c^2}{W}
-\frac{2c}{X}\left(1+\frac{x^2}{3X^2}\right),\qquad
L_+=\frac{(q-1)(q^2+10q+1)}{6q(q+1)},
\]
\[
F_\ell=1+\frac{p^2q}{W^2}
-\frac pW\frac{q^2+10q+1}{6(q+1)}.
\]
Let \(\bar N_k\) denote (1) with \(v=\bar v\) and \(\log q=L_+\), and put
\[
P_k=6(q+1)W^2X^3\{\bar N_k-(q-1)(\bar v-F_\ell)\}.
\tag{2}
\]
It is a cubic in \(y=q-1\).

Set
\[
t_0=\frac{13}{35},\qquad \gamma=\frac9{35},\qquad
k_s(t)=\frac{29}{4}t^2.
\]
We first show that each coefficient of \(P_{k_s(t)}\), considered
as a polynomial in \(y\), increases with \(t\) on
\[
t_0\le t\le2/5,\qquad 0<x\le\gamma.
\tag{3}
\]
Write \(P_{k_s(t)}=\sum_{j=0}^3 C_j(t,x)y^j\).
The appendix gives the exact cubic polynomials in \(t\) occurring in
their derivatives. They imply
\[
\begin{aligned}
\partial_t C_0&\ge44x^2,\\
\partial_t C_1&\ge102x-2x^7-x^8\ge99x,\\
\partial_t C_2&\ge48-84x^4-943x^5-847x^6-349x^7-72x^8-6x^9\\
&\ge48-\frac{2301}{81}>0,\\
\partial_t C_3&\ge64-91x^6-61x^7-14x^8-x^9
\ge64-\frac{167}{729}>0.
\end{aligned}
\tag{4}
\]
For the last comparisons, \(x<1/3\); the sums of the listed negative
coefficients are \(2301\) and \(167\).

Here is the complete sign rule behind the derivative table.
For a cubic \(e(t)=\sum_{i=0}^3 a_i t^i\) on
\(13/35\le t\le14/35\),
\[
e(t)\ge
\sum_{a_i\ge0}a_i(13/35)^i+
\sum_{a_i<0}a_i(14/35)^i.
\tag{5}
\]
Applying (5) to each displayed cubic gives its stated integer lower
bound. These are rational substitutions in fixed polynomials; no
minimization procedure is assumed.
For example, the last coefficient of \(\partial_t C_1/x\) satisfies
\[
-16+56t-36t^2
\ge-16+56(13/35)-36(2/5)^2=-24/25>-1.
\]

There is one deliberately sharper entry. For
\[
e(t)=-96+1080t-2376t^2+1392t^3
\]
the derivative has the upper bound
\[
e'(t)\le1080-4752(13/35)+4176(2/5)^2
=-2952/175<0.
\]
Thus \(e(t)\ge e(2/5)=5616/125>44\).
All other table entries use (5) directly. This proves (4), so that
\[
P_{k_s(t)}(t,x,y)\ge P_{k_s(t_0)}(t_0,x,y)
\quad\hbox{for every }y\ge0.
\tag{6}
\]

## 3. Comparison at the bottom of the strip

Assume in addition to (3) that
\[
k_s(t)<2t+2x+x^2.
\tag{7}
\]
The function \(k_s(t)-2t\) is strictly increasing on (3), since
its derivative is at least \(237/70>0\). Therefore
\[
2x+x^2>k_s(t)-2t\ge
k_s(t_0)-2t_0=\frac9{35}+\frac1{4900}.
\]
In particular,
\[
1<2t_0+2x+x^2,\qquad x\le1-2t_0=\gamma.
\tag{8}
\]

The polynomial part of the unit-shape proof establishes
\[
P_1(t_0,x,y)>0\qquad(y\ge0)
\tag{9}
\]
under (8). Its six coefficient signs and cubic comparison use only
the shape inequalities. The incoming floor is used later to infer
\(N_1>0\) from \(P_1>0\); no floor is asserted at this new \(t_0\).
This distinction is necessary because the exact secant changes
when \(t\) changes.

For fixed \(t_0,x,q\), the polynomial \(P_k\) is strictly increasing
in \(k\). To see this directly, the unit-shape proof gives
\(\bar v<U(t_0)\) for \(x\le1-2t_0\), and
\[
L_+<q-1,\qquad
1-\frac{L_+}{q-1}
=\frac{(q-1)(5q+1)}{6q(q+1)}>0.
\]
The exact affine-\(k\) coefficient of the normalized residual then
satisfies
\[
\partial_k\bar N_k
>
q\,t_0x(1-t_0)
\{(q-1)(2x+1)+t_0x\}>0.
\tag{10}
\]
This is the same elementary coefficient calculation as the
[shape monotonicity lemma](MIXED_NONSHORT_SHAPE_MONOTONICITY.md),
with the two explicitly bounded rational quantities in place of
\(v,\log q\). The prefactor in (2) is independent of \(k\), as is
the subtracted floor term, so (10) also gives \(\partial_kP_k>0\).

Since \(k_s(t_0)=4901/4900>1\), equations (6), (9) and (10) give
\[
P_{k_s(t)}(t,x,y)>0.
\tag{11}
\]
If the original exact secant at the original \(t\) satisfies its
incoming floor, then the original logarithm comparison from the
unit-shape proof gives \(N_{k_s(t)}>0\).
Here \(k_s(t)>1\), so the coefficient of \(v\) is negative:
\[
\partial_vN_{k_s}
=-xq\{k_s+tx+tW(k_s-2t)
 +(q-1)[k_sX+txX^2]\}<0.
\]
The log coefficient is also negative, while
\(\bar v>v\ge F_{p/W}(q)>F_\ell\).
Thus this last implication uses the actual floor at the unchanged
original coordinates. It does not transfer that floor to \(t_0\).

## 4. Complete reverse-next exclusion

The retained actual reverse-next window supplies
\[
\begin{gathered}
0<t<2/5,\quad x>0,\quad
k\ge1,\quad k\ge2t+x,\quad k\ge29t^2/4,\\
k<2t+2x+x^2,\qquad
x<7/3-(10/3)t,\qquad
1<q<W/p,\\
v=\operatorname{Sec}(t,1-t,t+x)<U(t),\qquad
v\ge F_{p/W}(q),\qquad N_k<0.
\end{gathered}
\tag{12}
\]
These are hand-derived necessary conditions: \(k\ge2t+x\) is the
reverse order lemma; \(k\ge29t^2/4\) follows from the already proved
physical scale \(a<4/5\); the gap and \(7/3\) duration estimate are
the upper-envelope and exact secant lemmas. The residual negativity
comes from the same-lift \(b\)-boundary comparison. No cap for its
artificial outgoing norm is included.

The strict increase of the exact \(N_k\) in \(k\), with the original
\(t,x,q,v\) fixed, permits the following exhaustive three cases.

1. If \(t\le t_0\) and \(x\le1-2t\), lower \(k\) to one.
   The actual centre gap gives \(1<2t+2x+x^2\), and the actual
   incoming floor is unchanged. The unit-shape theorem gives
   \(N_1>0\), contradicting \(N_1\le N_k<0\).

2. If \(2t+x\ge1\) and \(x>1/4\), lower \(k\) to \(k_o=2t+x\).
   The strengthened order-face lemma of Section 1 gives
   \(N_{k_o}>0\), contradicting \(N_{k_o}\le N_k<0\).

3. Otherwise \(t>t_0\) and \(x\le\gamma\).
   Indeed failure of the first case when \(t\le t_0\) would force
   \(x>1-2t\ge\gamma>1/4\), which is the second case.
   Once \(t>t_0\), an \(x>\gamma\) would also give the second case,
   since \(2t+x>2t_0+\gamma=1\).
   Lower \(k\) to \(k_s=29t^2/4\).
   Its centre-gap inequality (7) follows from (12).
   Sections 2--3 give \(N_{k_s}>0\), contradicting
   \(N_{k_s}\le N_k<0\).

All possibilities contradict (12). Therefore the actual smaller-
nonshort window cannot have a reverse next switch.

This conclusion is uniform in the surrounding period and in the
number of arcs. All comparisons keep the actual incoming covector
data where they are used. The auxiliary scale change appears only
inside a proved polynomial inequality, with no imported switch,
norm-floor, or Casimir assertion.



## 5. Common strict order, without a successor-sign assumption

The scalar contradiction in Section 4 used the next switch being
reverse only to obtain \(k\ge2t+x\). Every other hypothesis in (12)
is already necessary for the common smaller-nonshort window.
Write \(K=a^2+4\) and \(T=a+c\) in the physical coordinates,
so \(k=K/T^2\). Consequently every such common window with \(N_k<0\) satisfies
\[
\boxed{k<2t+x,\qquad d>b_*:=K/T-a\ge c.}
\tag{13}
\]
Indeed the contrary weak inequality is excluded by the scalar theorem.
In particular \(2t+x>1\), so in normalized coordinates
\(p=t+x>c=1-t\).

There is also a useful order on the actual first-event centre \(r\).
Write the incoming missing-control floor as
\[
F_{p/W}(q)=\operatorname{Sec}(W/q-p,p,c).
\]
The actual star bound \(q<W/p\) makes its first argument positive;
\(q>1\) makes it less than \(c\). Since \(t<c<p\), the strict
swapped-secant comparison gives
\[
v=\operatorname{Sec}(t,c,p)
<\operatorname{Sec}(t,p,c).
\]
For middle \(p\) and endpoint \(c\le p\), this secant is strictly
decreasing in its initial argument in \((0,c)\). The retained floor
\(v\ge\operatorname{Sec}(W/q-p,p,c)\) therefore forces
\(W/q-p>t\), and hence
\[
q<\frac{W}{p+t}=\frac{W}{2t+x}.
\tag{14}
\]
This argument is independent of \(k\).

Now \(B_k=k+p^2-t^2<(p+t)W\) by (13). Therefore
\[
r=\frac{qB_k}{W}-p
<\frac{B_k}{p+t}-p<W-p=c.
\tag{15}
\]
Returning to the unnormalized actual coordinates and using the
original global-minimum assignment \(a\le r\), the common necessary
order is
\[
\boxed{a\le r<c\le b_*<d.}
\tag{16}
\]
Only the weak middle inequality is retained to include its closure.
Neither (13) nor (14)--(16) assumes the sign of the actual next switch.
All secants and floors used in their proof are the original incoming
ones.

## Appendix. The derivative coefficients

Write
\[
\partial_t C_0=x^2\sum_{i=0}^5 E_{0i}(t)x^i,\qquad
\partial_t C_1=x\sum_{i=0}^7 E_{1i}(t)x^i,
\]
\[
\partial_t C_j=\sum_{i=0}^9 E_{ji}(t)x^i,\qquad j=2,3.
\]
Here the \(C_j\) are the four coefficients of \(P_{29t^2/4}\) in
\(y=q-1\), not the unit-shape coefficients from the preceding note.
The following are exact polynomial identities obtained from the
displayed definitions of \(R,N,\bar v,L_+,F_\ell\) and \(P_k\).
The last column follows from the single rational power rule in
Section 2, except for \(E_{00}\), whose elementary monotonicity is
proved there.

### The coefficients \(E_{0i}\)

| \(i\) | \(E_{0i}(t)\) | Lower bound |
|---:|---|---:|
| 0 | \(-96+1080t-2376t^{2}+1392t^{3}\) | \(44\) |
| 1 | \(-288+2628t-4992t^{2}+2552t^{3}\) | \(20\) |
| 2 | \(-352+2430t-3372t^{2}+1044t^{3}\) | \(64\) |
| 3 | \(-224+1122t-750t^{2}-348t^{3}\) | \(50\) |
| 4 | \(-76+288t-30t^{2}-232t^{3}\) | \(11\) |
| 5 | \(-12+48t-36t^{2}\) | \(0\) |

### The coefficients \(E_{1i}\)

| \(i\) | \(E_{1i}(t)\) | Lower bound |
|---:|---|---:|
| 0 | \(144-576t+2664t^{2}-2784t^{3}\) | \(102\) |
| 1 | \(-248+1956t+3672t^{2}-7656t^{3}\) | \(495\) |
| 2 | \(-1468+7894t+1686t^{2}-12180t^{3}\) | \(917\) |
| 3 | \(-2292+9861t+2631t^{2}-14094t^{3}\) | \(831\) |
| 4 | \(-1836+6461t+2994t^{2}-9570t^{3}\) | \(364\) |
| 5 | \(-814+2506t+1032t^{2}-3132t^{3}\) | \(58\) |
| 6 | \(-186+576t-45t^{2}-348t^{3}\) | \(-2\) |
| 7 | \(-16+56t-36t^{2}\) | \(-1\) |

### The coefficients \(E_{2i}\)

| \(i\) | \(E_{2i}(t)\) | Lower bound |
|---:|---|---:|
| 0 | \(-48+192t-288t^{2}+1392t^{3}\) | \(48\) |
| 1 | \(144-768t+3744t^{2}+2088t^{3}\) | \(460\) |
| 2 | \(-304-348t+11988t^{2}-2436t^{3}\) | \(1054\) |
| 3 | \(-2144+3810t+17610t^{2}-11774t^{3}\) | \(947\) |
| 4 | \(-3816+6747t+16881t^{2}-17226t^{3}\) | \(-84\) |
| 5 | \(-3514+5388t+9786t^{2}-12180t^{3}\) | \(-943\) |
| 6 | \(-1862+2427t+2739t^{2}-4118t^{3}\) | \(-847\) |
| 7 | \(-564+624t+126t^{2}-522t^{3}\) | \(-349\) |
| 8 | \(-90+72t-54t^{2}\) | \(-72\) |
| 9 | \(-6\) | \(-6\) |

### The coefficients \(E_{3i}\)

| \(i\) | \(E_{3i}(t)\) | Lower bound |
|---:|---|---:|
| 0 | \(-8+96t-144t^{2}+1160t^{3}\) | \(64\) |
| 1 | \(76-240t+1650t^{2}+3828t^{3}\) | \(403\) |
| 2 | \(-66-432t+6777t^{2}+4698t^{3}\) | \(936\) |
| 3 | \(-711+692t+\frac{22845}{2}t^{2}+1131t^{3}\) | \(1179\) |
| 4 | \(-1305+2004t+\frac{43431}{4}t^{2}-3045t^{3}\) | \(742\) |
| 5 | \(-1194+1975t+\frac{23529}{4}t^{2}-3219t^{3}\) | \(145\) |
| 6 | \(-611+1019t+\frac{6429}{4}t^{2}-1247t^{3}\) | \(-91\) |
| 7 | \(-171+282t+\frac{501}{4}t^{2}-174t^{3}\) | \(-61\) |
| 8 | \(-23+34t-18t^{2}\) | \(-14\) |
| 9 | \(-1\) | \(-1\) |
