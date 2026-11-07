# Hand reductions for the remaining pure-forward exclusion

Date: 2026-11-07. These are analytic lemmas, not a closure claim for F.
Every polynomial and sign comparison used below is displayed. Numerical
experiments were used to discover the proposed targets but are not
premises of these proofs. No interval cover or coefficient-count result
is used here.

## 1. Exterior-factor concavity on the whole linear-budget domain

Use the necessary forward-minimum residual

\[
\mathcal E=\alpha A-B-nF_{z/S}(h)-mF_{w/T}(I),
\]

with the notation of the
[forward neighbor reduction](GLOBAL_FORWARD_NEIGHBOR_CONTRACTION.md), where
`S=1+z`, `T=1+w`, `Z=z^2+U`, `I=T^2/(w^2+U)`.
Suppose

\[
11/5\le U\le3,\qquad 1\le z\le w,
\qquad z+w\le5(U-1)/3,
\qquad H:=S^2/Z\le h\le S/z.
\tag{1}
\]

**Lemma.** As a function of the exterior factor `h`, the residual
`E` is concave on the entire interval in (1), and strictly concave
away from the zero-duration circular endpoint.

This does not use the computational neighbor contraction. Indeed, (1)
gives

\[
1\le z\le5/3,\qquad U\ge1+6z/5>z,\qquad H\ge1.
\]

The exact second derivative, also recorded in the
[small-forward-minimum proof](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md), is

\[
\mathcal E_{hh}=-\frac{zP(h)}{Zh^3},
\]
\[
P(h)=(U-z)h^2(2zh-S)+Zh-2zS.
\tag{2}
\]

For `h>=1`,

\[
P'(h)=2(U-z)h(3zh-S)+Z>0.
\tag{3}
\]

At the lower endpoint a direct factorization gives

\[
P(H)=-\frac{S(2z+1-U)}{Z^3}Q(U,z),
\]
\[
\begin{aligned}
Q(U,z)={}&(1-z)U^2
 -z(z^3+7z^2+5z+3)U\\
 &+z^2(z^4+2z^3+6z^2+5z+2).
\end{aligned}
\tag{4}
\]

The polynomial `Q` decreases strictly with `U`. Put `x=z-1`, so
`0<=x<=2/3`. At the permitted lower value `U=1+6z/5`, it is

\[
\begin{aligned}
Q(1+6z/5,z)={}&x^6+\frac{34}{5}x^5+\frac{78}{5}x^4
 +\frac{124}{25}x^3\\
 &-\frac{832}{25}x^2-\frac{1216}{25}x-\frac{96}{5}.
\end{aligned}
\]

Since `x<=2/3`, its four positive terms are at most

\[
\left[(2/3)^4+\frac{34}{5}(2/3)^3
 +\frac{78}{5}(2/3)^2+\frac{124}{25}(2/3)\right]x^2
=\frac{25216}{2025}x^2.
\]

Consequently

\[
Q(U,z)\le-\frac{42176}{2025}x^2
 -\frac{1216}{25}x-\frac{96}{5}<0.
\tag{5}
\]

Also `2z+1-U>=0`, with equality only at `z=1,U=3`.
Equations (3)--(5) prove the lemma. In particular,

\[
\mathcal E(h)\le\mathcal E(H)
 +(h-H)\mathcal E_h(H).
\tag{6}
\]

The larger-neighbor monotonicity already proved in the
[minimum note, Section 3](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md#3-reduce-the-larger-neighboring-margin)
also gives `E_w<=0` and `E_hw<=0`: differentiate
`E_w=alpha(U(a/(a+c))-V)-m V_w`, with respect to `h`.
Both `alpha_h` and `m_h` are positive and both terms retain the stated
nonpositive sign. Thus for proving a weaker neighbor bound `w<4/3`,
one may first lower `w` to `max(z,4/3)` and then bound the tangent in
(6) by its two endpoint values. The remaining comparison has only
the following two planar domains:

\[
\begin{array}{c|c|c}
z&w&U\\\hline
[1,4/3]&4/3&[\,9/5+3z/5,\,3\,]\\
[4/3,5/3]&z&[\,1+6z/5,\,3\,].
\end{array}
\tag{7}
\]

This is a proved reduction of the neighbor task. The final negative
signs on (7) are not asserted proved by this lemma.

## 2. A small norm-sum bound would replace the full Casimir cover

Write

\[
K=1+U,\quad d=3-U,\quad x=z-1,\quad y=w-1,
\quad S=1+z,\quad T=1+w,
\]
\[
f(r)=\frac{r-r^{-1}}2-\log r,\qquad
e_0=1-K/8+K^{-1},
\]
\[
E_0=e_0-f(S/2)-f(T/2)-f(4/K).
\]

The exact centered central stationarity and Casimir formulas from the
[centered system](GLOBAL_FORWARD_CENTERED_SYSTEM.md) are

\[
E=E_0+S\delta u+T\delta v,
\qquad
\gamma^2=\frac{K^2}{16U^2}
 \left[4(3/4+\delta u)(3/4+\delta v)-E^2\right].
\tag{8}
\]

**Lemma.** Suppose

\[
\begin{gathered}
11/5\le U\le3,\qquad 1\le z,w\le4/3,
\qquad z+w\le5(U-1)/3,\\
\delta u,\delta v\ge0,\qquad
\delta u+\delta v\le1/40.
\end{gathered}
\tag{9}
\]

Then the exact expression (8) satisfies

\[
\boxed{\gamma^2>23/125.}
\tag{10}
\]

The norm-sum assumption in (9) is a new unresolved target for the
actual forward stationary equations; it is not supplied by numerical
experiments. The conclusion of this lemma is a complete hand implication
from the explicitly stated assumptions.

### 2.1 Reduce the two norms to their endpoint allocation

For `t>=0`, integration of
`f'(1+t)=t^2/[2(1+t)^2]` gives

\[
\frac{t^3}{6(1+t)^2}\le f(1+t)\le\frac{t^3}{6}.
\tag{11}
\]

Since `x,y<=1/3` and `d/K<=1/4`, this also shows

\[
E_0\ge3/4-1/648-1/384=7733/10368>0.
\]

Fix `t=delta u+delta v`. The bracket in (8), viewed as a function of
`delta u` in `[0,t]`, is a concave quadratic. Its minimum is attained
at an endpoint. By symmetry take `z>=w`, so `S>=T`; the smaller
endpoint value assigns all of `t` to `delta u`, because `E_0>0`.
Thus

\[
\gamma^2\ge\frac{K^2}{16U^2}
 \left[9/4+3t-(E_0+St)^2\right].
\tag{12}
\]

Dropping `f(T/2)>=0` and applying the lower bound in (11) gives

\[
E_0\le\widehat E
:=e_0-\frac{x^3}{12(x+2)^2}-\frac{d^3}{96K}.
\tag{13}
\]

This upper bound is positive. Replacing `E_0` by it in (12) is
therefore valid. The resulting expression is concave in `t`, so on
`0<=t<=1/40` its minimum is again at an endpoint.

At `t=0`, use `widehat E<=e_0` and the exact identity

\[
\frac{K^2}{16U^2}(9/4-e_0^2)
=\frac3{16}-\frac{d^4}{1024U^2}
\ge\frac3{16}-\frac1{12100}>\frac{23}{125}.
\tag{14}
\]

The last gap is `827/242000>0`.

### 2.2 Monotonicity in the scale parameter at the other endpoint

At `t=1/40` define

\[
R(U,x)=\frac{K^2}{16U^2}
 \left[\frac{93}{40}
 -\left(e_0-\frac{x^3}{12(x+2)^2}
             -\frac{d^3}{96K}+\frac{x+2}{40}\right)^2\right].
\tag{15}
\]

For fixed `0<=x<=1/3`, this function increases strictly with `U`
on `[11/5,3]`. Here is an explicit derivative proof. Put

\[
A=\frac32+\frac{x+2}{40}-\frac{x^3}{12(x+2)^2},
\]
\[
F=\frac13+AK-\frac{K^2}{4}+\frac{K^3}{96},
\qquad
G=F-(K-1)F'
=\frac13+A+\frac{9K^2}{32}-\frac K2-\frac{K^3}{48}.
\]

Then

\[
\partial_U R=\frac{FG-(93/40)K}{8U^3}.
\tag{16}
\]

The derivative of `x^3/[12(x+2)^2]` is
`x^2(x+6)/[12(x+2)^3]<=19/2592<1/40`.
Hence `A>=31/20`. At this lower value of `A`, both `F` and `G`
increase with `K` on `[16/5,4]`; their respective lower endpoint
values are `1153/375` and `3721/1500`. They are positive, so
`FG` increases with `A` too.

At `A=31/20`, with `d=4-K`, direct multiplication gives

\[
\begin{aligned}
FG-(93/40)K={}&\frac{23}{50}-\frac{91}{400}d
 -\frac{39}{160}d^2+\frac{61}{480}d^3
 +\frac{11}{3840}d^4\\
 &-\frac3{1024}d^5-\frac1{4608}d^6.
\end{aligned}
\]

Dropping its two positive nonconstant terms and using `d<=4/5`
bounds this below by `68053/562500>0`. This proves (16).

### 2.3 Two rational cases finish the bound

The linear budget and `w>=1` imply `U>=(11+3x)/5`.
By the preceding monotonicity, it suffices to use this lower value
in (15). Direct rational multiplication gives

\[
R((11+3x)/5,x)-\frac{23}{125}
=\frac{-Q(x)}{92160000(x+2)^4(3x+11)^2},
\tag{17}
\]

where the complete polynomial is

\[
\begin{aligned}
Q(x)={}&729x^{10}-51840x^9+810360x^8+6473760x^7\\
 &-44619440x^6-399580544x^5-701870080x^4\\
 &+262379520x^3+1262545920x^2+279633920x-242991104.
\end{aligned}
\]

Let `Q_+` be the sum of the six positive monomials in this display.
It increases for `x>=0`.

For `0<=x<=1/4`, discarding all negative nonconstant terms gives

\[
Q(x)\le Q_+(1/4)-242991104
=-\frac{94448822787495}{1048576}<0.
\]

For `1/4<=x<=1/3`, retain just the negative quartic term:

\[
Q(x)\le Q_+(1/3)-242991104-\frac{701870080}{256}
=-\frac{611814149}{243}<0.
\]

Every denominator in (17) is positive. These two explicit inequalities
prove (10), completing the conditional Casimir lemma.

## 3. The same cost argument retains both exterior factors

For an actual forward minimum window, put

\[
P=p/a=h(z^2+U)/(1+z)-z,
\qquad D=d_{\rm ext}/a=k(w^2+U)/(1+w)-w.
\]

**Lemma.** Under the same whole-period premises as the
[linear budget](GLOBAL_FORWARD_LINEAR_BUDGET.md),

\[
\boxed{P+z+w+D-2<5(U-1)/3,}
\]
\[
\boxed{\frac{h(z^2+U)}{1+z}+\frac{k(w^2+U)}{1+w}
       <\frac{5U+1}{3}.}
\tag{18}
\]

This strengthens the old budget, because `P,D>=1`. It uses the same
univariate inequality already displayed in the linear-budget proof;
no new computer-dependent sign is introduced.

Use the symmetric edge function `G` of the
[whole-period scalar budget](GLOBAL_STRUCTURE_FORWARD_MINIMUM_BUDGET.md).
Its mixed derivative is

\[
G_{ab}=2\left(1-\frac{ab}{(a+b)^2}\right)>0.
\]

Integrating this derivative over a rectangle whose lower corner is
`(a,a)` gives, for `r,t>=1`,

\[
G(ar,at)\ge G(ar,a)+G(a,at)-G(a,a).
\tag{19}
\]

The seven-entry comparison retains `(a,p,b,a,c,d_ext,a)`.
For `N=7`, the five retained consecutive indices are distinct and the
two other indices are lowered to `a`; this gives exactly the seven
cyclic edges displayed, each counted once. For `N>7`, lowering the
remaining indices leaves additional copies of `G(a,a)>0`, which may
be discarded. A cyclic relabeling handles a retained window crossing
the seam. Apply (19) to the two distinct edges `(p,b)` and
`(c,d_ext)`; all other retained edges are unchanged.
Writing `g_U(r)=G(a,ar)/a^2` as in the linear-budget note, the actual
cost therefore satisfies

\[
C\ge\frac{\sqrt3}{U}
 \{2g_U(P)+2g_U(z)+2g_U(w)+2g_U(D)-g_U(1)\}.
\tag{20}
\]

All four ratios lie in `[1,U]`: the global minimum gives their lower
bounds, while the actual strict-star products give `Pz<U`, `wD<U`,
`z<U` and `w<U`.

Suppose (18) failed. Monotonicity allows the four ratios in (20) to
be lowered until their sum is `2+5(U-1)/3`. The function `g_U` is
concave on `[1,U]`. At this fixed sum its four-term sum is minimized
by concentrating all the excess above one into one coordinate.
This follows directly by moving a pair with both coordinates above
one toward an endpoint of its fixed-sum interval, and repeating.
The excess is `(5U-11)/3`, which lies in `[0,U-1]` for
`11/5<=U<=3`. Thus the minimizing four-tuple is a permutation of

\[
\left(1,1,1,\frac{5U-8}{3}\right).
\]

Consequently the right side of (20) is at least

\[
\frac{\sqrt3}{U}\left\{2g_U((5U-8)/3)+5g_U(1)\right\}.
\]

This is exactly the one-variable expression proved strictly larger
than `A_oct` in Section 2 of the linked linear-budget proof. The
contradiction proves (18). These are scalar inequalities; the lowered
arrays are never asserted to close their frames or satisfy PMP.

## 4. What remains to replace the two F covers

The preceding arguments reduce the computational tasks to specific
analytic targets; they do not assume those targets have been proved:

1. Finish the negative residual signs on the two planar domains (7),
   which would give the weaker but sufficient bound `z,w<4/3`.
2. Prove `delta u+delta v<=1/40` for the actual same-covector stationary
   system with its genuine exterior floors. Lemma 2 would then replace
   the five-variable complementary Casimir cover completely, including
   the circular limit, without any separate interval computation.

The scale restriction `U<3` used by the actual forward application
comes from the hard face H5 in the
[small-forward-minimum theorem](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md).
Its large coefficient table remains an open replacement task for the
proof without computer assistance. Neither lemma here proves `U<3`
independently. The displayed
[linear budget](GLOBAL_FORWARD_LINEAR_BUDGET.md) also remains a named
input, with its separate twelve-coefficient univariate identity. These
prerequisites cannot be silently discarded when replacing the two later
covers.
