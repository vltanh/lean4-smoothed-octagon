# Two open moment inequalities for the six-arc word 012102

## Status and scope

This completed boundary investigation is retained from the earlier closed-word
work. Further work on its open interior inequalities is paused under the
uniform-reduction priority in [BOUNDED_REDUCTION.md](BOUNDED_REDUCTION.md).
It supplies no local L1-L5 exclusion.

This note isolates two explicit algebraic inequalities which would complete
the octagon comparison for every positive six-arc word **012102**. Their
implication for the actual cost is proved below, including every needed sign
of the fixed logarithmic constants. Both inequalities are proved on every
finite arc-vanishing boundary face.

**Neither interior moment inequality is proved.** This note does not exclude
the 012102 class, compare arbitrary longer words, establish a finite bound
on the number of arcs, or reduce general measurable controls to finite
vertex words. No numerical sample is a premise of any proof below. No Lean
compilation or kernel validation is claimed.

The complete parameter domain, actual state construction, full-arc strict
star feasibility, and exact cost are proved in
[SIX_ARC_012102.md](SIX_ARC_012102.md). The arguments here operate on that
entire family, without equal-duration or Pontryagin assumptions.

## 1. Definitions and proved starting inequalities

For \(0<s<1\), write
\[
Q(s)=\frac{1+s^2}{1-s^2},\qquad
P(s)=\frac{1+s^2}{2s},\qquad
S(s)=\frac{2s}{1-s^2}.
\]
The full positive six-arc domain is
\[
0<u,v,k<1,\qquad
P(u)P(v)>Q(k),\qquad S(u)S(k)>1,\quad S(v)S(k)>1.
\tag{1}
\]
Its factors and raw active margins are
\[
(q_0,\ldots,q_5)=
\left(Q(u),\frac{P(u)P(v)}{Q(k)},Q(v),
S(v)S(k),Q(k),S(u)S(k)\right),
\]
\[
(a_0,\ldots,a_5)=
\left(\frac{\ell}{u},A,\frac{\ell}{v},B,\frac{\ell}{k},C\right),
\tag{2}
\]
where
\[
\ell=1-uv-k(u+v),\quad A=k+u+v-kuv,\quad
B=k+u-v+kuv,\quad C=k-u+v+kuv.
\]
All these raw active margins are positive, and
\[
N=4Q(k)^2-\bigl(2kQ(k)+A\bigr)^2>0.
\]
The actual active margins are \(2a_i/\sqrt N\). Define
\[
T=\sum_{i=0}^5a_i^2(q_i-q_i^{-1}),\qquad
W=\sum_{i=0}^5a_i^2\frac{q_i-1}{q_i+1},
\]
\[
D=\frac{N}{\ell^2},\qquad t=\frac{T}{\ell^2},\qquad
\omega=\frac{W}{\ell^2}.
\tag{3}
\]
The main reduction note proves
\[
\boxed{D>D_*:=5+4\sqrt2,\qquad \omega>4.}
\tag{4}
\]
It also proves that \(D\) strictly increases in either \(u\) or \(v\)
when \(k\) and the other variable are fixed. This concerns \(D\); it does
not imply analogous monotonicity of the cost or of combinations of the
moments.

The exact normalized cost is
\[
\delta=\frac{\mathrm{cost}}{\sqrt{12}}
=1+\frac{6\ell^2-\sum_{i=0}^5a_i^2\log q_i}{2N}.
\tag{5}
\]
Put
\[
\delta_{\rm oct}=\frac{8-4\sqrt2-\log2}{2\sqrt2-1}.
\]

## 2. The two sufficient interior targets

The proposed inequalities are
\[
\boxed{2t+2\omega\le D+19+8\sqrt2}
\qquad\text{throughout (1),}
\tag{P1}
\]
and
\[
\boxed{D-11(\omega-4)\ge D_*}
\qquad\text{throughout (1).}
\tag{P2}
\]
These are **open interior targets**, not assumptions already verified for
the constructed family.

Multiplying (P1) by \(3\) and (P2) by \(4\), then adding, gives
\[
\boxed{6t+50\omega\le7D+213+8\sqrt2.}
\tag{J}
\]
Equivalently,
\[
6T+50W\le7N+(213+8\sqrt2)\ell^2.
\]
A proof of (J) directly would also suffice; the separate targets are one
possible route.

### 2.1 A sharp logarithm upper bound

The concavity calculation in
[REVERSE_FIVE_MINIMUM.md](REVERSE_FIVE_MINIMUM.md) gives, for \(q\ge1\),
\[
\log q\le m(q-q^{-1})+n\frac{q-1}{q+1},
\tag{6}
\]
where
\[
m=(3+2\sqrt2)(\sqrt2-2\log2)>0,\qquad
n=\frac{3+2\sqrt2}{2}\log2-m\left(2+\frac3{\sqrt2}\right).
\tag{7}
\]
Indeed, the function
\[
G(z)=\frac{q+1}{q-1}\log q
=2\int_0^1\frac{z+2}{(1-s^2)z+2(1+s^2)}\,ds,
\qquad z=q+q^{-1},
\]
is strictly concave. Its tangent at \(q=\sqrt2\) gives (6), using
\[
\frac{q-1}{q+1}(z+2)=q-q^{-1}.
\]
The value at \(q=1\) is interpreted by continuity. Equality in (6) occurs
at \(q=1,\sqrt2\), and the inequality is strict at every other \(q>1\).
Consequently,
\[
\delta\ge1+\frac{6-mt-n\omega}{2D}.
\tag{8}
\]

### 2.2 Exact implication of the joint inequality

The required fixed coefficient signs are
\[
n-\frac{25}{3}m<0,\qquad
\kappa:=2(1-\delta_{\rm oct})-\frac76m>0.
\tag{9}
\]
Section 3 proves both with rational certificates.

Assume that (J) is proved. Since \(m>0\),
\[
mt+n\omega
\le\frac76mD+\frac{213+8\sqrt2}{6}m
+\left(n-\frac{25}{3}m\right)\omega.
\]
Use \(\omega>4\) from (4), together with the negative coefficient in
(9), to get
\[
mt+n\omega
\le\frac76mD+\frac{13+8\sqrt2}{6}m+4n.
\tag{10}
\]
Let \(t_*=8+6\sqrt2\). Direct algebra gives
\[
t_*-\frac76D_*=\frac{13+8\sqrt2}{6},
\qquad
mt_*+4n=2(3+2\sqrt2)\log2
       =6+2(1-\delta_{\rm oct})D_*.
\tag{11}
\]
Hence
\[
6-mt-n\omega+2D(1-\delta_{\rm oct})
\ge\kappa(D-D_*)>0.
\tag{12}
\]
Since \(D>0\), equations (8) and (12) imply
\[
\boxed{\delta>\delta_{\rm oct}.}
\]

This proves the precise dependency: (J), or both (P1) and (P2), would
exclude every positive 012102 trajectory. The implication uses already
proved positivity and normalization bounds, with no hidden symmetry,
minimum-attainment, or regularity hypothesis.

## 3. Exact signs of the fixed coefficients

Put \(r=\sqrt2\) and \(h=\log2\). Expanding (7),
\[
m=4+3r-(6+4r)h,\qquad
n=\left(\frac{51}{2}+18r\right)h-17-12r.
\]
Therefore
\[
6\left(n-\frac{25}{3}m\right)
=(453+308r)h-302-222r,
\tag{13}
\]
\[
6(2r-1)\kappa=37r-164+(82+56r)h.
\tag{14}
\]
The elementary bounds
\[
r>\frac{7071}{5000},\qquad
\frac{69314}{100000}<h<\frac{69315}{100000}
\tag{15}
\]
suffice. The radical bound follows by squaring. For the logarithm, integrate
the geometric series at \(1/3\):
\[
\log2=2\sum_{j=0}^{\infty}\frac1{(2j+1)3^{2j+1}}.
\]
Its first five terms give
\[
\log2>\frac{4297606}{6200145}.
\]
Retain the first four terms for an upper bound. Since \(2j+1\ge9\) for
\(j\ge4\), the remaining tail is strictly below \(1/(4\cdot3^9)\), giving
\[
\log2<
\frac{53056}{76545}+\frac1{78732}
=\frac{1910051}{2755620}.
\]
Cross multiplication proves the two rational bounds for \(h\) in (15).

In (13), first replace \(h\) by its upper bound. The resulting coefficient
\(308(69315/100000)-222\) is negative, so replacing \(r\) by its lower
bound gives
\[
(453+308r)h-302-222r
<-\frac{940229}{25000000}<0.
\]
Both coefficients in (14) increase in the positive quantities \(r,h\).
Their lower bounds give
\[
37r-164+(82+56r)h
>\frac{1757529}{31250000}>0.
\]
Also \(r-2h>7071/5000-2(69315/100000)>0\), proving \(m>0\).
This establishes every coefficient sign used in Section 2 without a
floating-point premise.

## 4. Both targets on the four-arc boundary

Set
\[
u=v=\eta,\qquad k=\frac{1-\eta}{1+\eta},\qquad 0<\eta<1.
\]
Then \(q_3=q_5=1\), and deletion leaves the complete four-arc family. Put
\[
a=\frac1{Q(\eta)}=\frac{1-\eta^2}{1+\eta^2},\qquad
b=\frac1{P(\eta)}=\frac{2\eta}{1+\eta^2},\qquad s=a+b.
\]
Since \(a,b>0\) and \(a^2+b^2=1\), one has \(1<s\le\sqrt2\).
Substitution into (2)–(3) gives
\[
D=\frac{s+3}{s-1},\qquad
\omega=4,\qquad
t=8+2s+\frac{4s}{s^2-1}.
\tag{16}
\]
Thus
\[
2(t+\omega)-D=23+4s+\frac4{s+1}.
\tag{17}
\]
The derivative is \(4-4/(s+1)^2>0\), so
\[
2(t+\omega)-D
\le23+4\sqrt2+\frac4{1+\sqrt2}
=19+8\sqrt2.
\]
This proves (P1), with equality precisely at \(s=\sqrt2\), or
\(\eta=\sqrt2-1\).

For (P2), use \(\omega=4\) and
\[
D=\frac2\eta+\frac4{1-\eta}-1\ge5+4\sqrt2,
\]
with the same equality condition. These are boundary theorems, not
interior comparisons.

## 5. Both targets on the reverse-five boundary

At \(q_1=1\), the remaining positive factors form the reverse word 02102.
Use the notation of [REVERSE_FIVE_ARC.md](REVERSE_FIVE_ARC.md):
\[
S_1=\sum_{i=0}^4Q_i,\qquad
S_{-1}=\sum_{i=0}^4Q_i^{-1},\qquad
\Pi=\prod_{i=0}^4Q_i.
\]
The proved reverse-five identities give
\[
D=2S_1+F+1,\qquad F\ge6,\qquad
S_1\ge5\varphi,\quad \varphi=\frac{1+\sqrt5}{2}.
\tag{18}
\]
The normalizations agree: the first retained factor is \(Q(u)\), its
reverse-five square-root weight is \(1/u\), and its actual active margin
is \(2/(u\sqrt D)\) in either description. Every retained factor has
the same rational weight after normalization. Hence
\[
\omega=5,\qquad t=S_1+S_{-1}+10.
\tag{19}
\]

### 5.1 A reciprocal-square identity

The reverse-five parameterization is
\[
(Q_0,\ldots,Q_4)=
\left(\frac{W_0}{B_0},q,r,\frac{W_0}{A_0},
\frac{qr}{A_0B_0}\right),
\]
\[
A_0^2=q^2-1,\quad B_0^2=r^2-1,\quad W_0^2=q^2+r^2-1.
\]
Therefore
\[
\Pi=\frac{W_0^2q^2r^2}{A_0^2B_0^2}
\]
and
\[
\begin{aligned}
\sum_iQ_i^{-2}
&=\frac{A_0^2+B_0^2}{W_0^2}
 +\frac{q^2+r^2+A_0^2B_0^2}{q^2r^2}\\
&=2-\frac1{W_0^2}+\frac1{q^2r^2}
 =2-\frac1\Pi<2.
\end{aligned}
\tag{20}
\]
Cauchy–Schwarz gives \(S_{-1}^2<10\), hence \(S_{-1}<\sqrt{10}\).

### 5.2 The strict boundary estimates

For (P1),
\[
2(t+\omega)-D=29+2S_{-1}-F
<23+2\sqrt{10}<19+8\sqrt2.
\tag{21}
\]
The last comparison follows already from
\(\sqrt{10}<16/5\) and \(\sqrt2>7/5\).

For (P2),
\[
D-11(\omega-4)=2S_1+F-10
\ge10\varphi-4>12>5+4\sqrt2.
\tag{22}
\]
For example, \(\varphi>8/5\) and \(\sqrt2<3/2\) prove the last strict
comparisons. No symmetry of the five factors is used.

## 6. Both targets on the mixed-five boundaries

Consider \(q_5=1\), or \(u=\eta=(1-k)/(1+k)\). Write
\[
x=\eta,\qquad y=v,\qquad 0<x\le y<1,\qquad
\rho=\frac{S(y)}{S(x)}.
\]
Then
\[
D=\frac{xy+x+2}{x(1-y)},\qquad
\omega=4+\frac{\rho-1}{\rho+1}.
\tag{23}
\]
For the second identity, the three even contributions each equal one,
the retained \(P(y)\) contribution equals one, the \(q_3=\rho\) piece
has raw active margin \(\ell\), and the \(q_5=1\) contribution is zero.

Put
\[
w=\sqrt{xy},\qquad R=\sqrt{y/x}\ge1,\qquad wR<1.
\]
Equation (23) becomes
\[
D+1=\frac{2(R+w)}{w(1-wR)},\qquad
E:=\omega-4=
\frac{R^2-1}{R^2+1}\frac{1+w^2}{1-w^2}.
\tag{24}
\]
Let \(K=D-11E\). At fixed \(w\),
\[
K_R=(1+w^2)\left[
\frac2{w(1-wR)^2}
-\frac{44R}{(1-w^2)(R^2+1)^2}
\right],
\tag{25}
\]
\[
K_{RR}=
\frac{4(1+w^2)}{(1-wR)^3}
+\frac{44(1+w^2)(3R^2-1)}
{(1-w^2)(R^2+1)^3}>0.
\tag{26}
\]
At \(R=1\),
\[
K_R(w,1)=
\frac{(1+w^2)(11w^2-9w+2)}
{w(1-w)^2(1+w)}>0,
\]
because
\[
11w^2-9w+2=
11\left(w-\frac9{22}\right)^2+\frac7{44}>0.
\]
Consequently \(K\) strictly increases for \(R\ge1\), and
\[
K(w,R)\ge K(w,1)
=\frac2w+\frac4{1-w}-1\ge5+4\sqrt2.
\tag{27}
\]
This proves (P2) on the entire mixed-five boundary. Equality requires
\(R=1,w=\sqrt2-1\), the four-arc octagon boundary. Symmetry gives the
same result on \(q_3=1\).

### 6.1 The first target by averaging two four-arc values

The other exact boundary moment is
\[
t=\frac{T_4(x)+T_4(y)}2+(\rho-\rho^{-1}),\qquad
T_4(z)=8+2\bigl(Q(z)+Q(z)^{-1}+P(z)+P(z)^{-1}\bigr).
\tag{28}
\]
Let \(H_{\rm mix}=2(t+\omega)-D\), and write
\[
D_4(z)=\frac2z+\frac4{1-z}-1,\qquad
H_4(z)=2T_4(z)+8-D_4(z).
\]
Section 4 proves \(H_4(z)\le19+8\sqrt2\), with equality only at
\(z=\sqrt2-1\). We will prove the stronger comparison
\[
H_{\rm mix}\le\frac{H_4(x)+H_4(y)}2,
\tag{28a}
\]
strictly when \(x<y\).

Put \(s=x+y\), \(p=xy\), and \(d=y-x\). Substituting (23) and (28) and
collecting the rational terms gives the exact identity
\[
H_{\rm mix}-\frac{H_4(x)+H_4(y)}2
=\frac{y-x}{xy(1-x)(1-y)}\,\mathcal B,
\tag{28b}
\]
where
\[
\mathcal B=(1+p)\left\{
\frac{2s(1-p)}{1+s+p}
+\frac{2p(1-s+p)}{s(1-p)}-1
\right\}-d.
\]
All denominators are positive. The expression in braces is
\[
-\frac{\mathcal Q(s,p)}{s(1-p)(1+s+p)},
\qquad
\mathcal Q(s,p)=
s(1-p^2)+s^2(-1+5p-2p^2)-2p(1+p)^2.
\tag{28c}
\]
It remains to prove \(\mathcal Q>0\) on
\(0<p<1,\ 2\sqrt p\le s<1+p\).

Set \(c=-1+5p-2p^2\). If \(c\ge0\), then
\(\mathcal Q_s=1-p^2+2sc>0\), so its minimum is at \(s=2\sqrt p\).
If \(c<0\), the quadratic is concave in \(s\), so its minimum on
\([2\sqrt p,1+p]\) is at an endpoint. Both endpoint values are positive:
\[
\mathcal Q(1+p,p)=2p(1-p)(1+p)^2>0,
\]
\[
\mathcal Q(2z,z^2)
=2z(1-z)(1+z)^2(5z^2-4z+1)>0
\qquad(0<z<1),
\tag{28d}
\]
where \(5z^2-4z+1=5(z-2/5)^2+1/5>0\).
Thus \(\mathcal B<0\), proving (28a).

It follows that \(H_{\rm mix}\le19+8\sqrt2\), with equality only at
\(x=y=\sqrt2-1\). This proves (P1) on the whole mixed-five boundary.
The case \(q_3=1\) follows by interchanging \(u,v\). Both moment targets
are therefore proved on every finite face where a single positive
six-arc factor tends to one.

## 7. A stronger rational alternative for the first target

On the four-arc boundary, \(s=(D+3)/(D-1)\), so (17) becomes
\[
2(t+\omega)-D=
29+\frac{16}{D-1}-\frac4{D+1}.
\tag{29}
\]
This suggests the stronger rational interior inequality
\[
\boxed{
2(t+\omega)\le D+29+\frac{16}{D-1}-\frac4{D+1}.}
\tag{R}
\]
It is exact on every four-arc boundary member. The excess on its right
strictly decreases for \(D>1\), since
\[
-\frac{16}{(D-1)^2}+\frac4{(D+1)^2}<0.
\]
The proved \(D>D_*\) therefore shows that (R), if proved, would imply
(P1).

Because \(N>\ell^2>0\), clearing the two positive denominators makes
(R) equivalent to
\[
\boxed{
N^3+29N^2\ell^2+11N\ell^4-9\ell^6
-2(N^2-\ell^4)(T+W)\ge0.}
\tag{30}
\]
This is another **open interior inequality**. Equality on a boundary
does not prove positivity away from that boundary.

## 8. Exact remaining scope

The boundary status is:

| Region | First target (P1) | Second target (P2) |
| --- | --- | --- |
| Four-arc boundary | Proved; equality only at the octagon | Proved; equality only at the octagon |
| Reverse-five boundary | Proved strictly | Proved strictly |
| Either mixed-five boundary | Proved by (28a)–(28d); equality only at the octagon | Proved by (24)–(27); equality only at the octagon |
| Positive six-arc interior | Open | Open |

No principle transferring these boundary estimates to the interior has
been established. In particular, this note assumes neither coordinate
monotonicity, a symmetrization inequality, nor a deformation without an
interior minimum. Exploratory attempts to use separate-coordinate or
radial monotonicity of the joint slack were rejected; those attempts are
not proof premises, and no numerical grid is used to assert an inequality.

Proving both (P1) and (P2), proving (J) directly, or finding another hand
comparison on the full domain (1) would close this six-arc class. Even
that would leave arbitrary longer words and general measurable controls
outside the result.

