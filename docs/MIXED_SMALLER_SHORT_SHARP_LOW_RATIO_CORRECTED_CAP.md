# A sharper corrected cap when the short ratio is at most two

Date: 2026-11-08 UTC. Analytic corrected-cap reduction. The original
coefficient-minimum step has been replaced by ten fully displayed
degree-six polynomials and an elementary endpoint sign argument.
The terminal low-ratio face signs are separate obligations.

This note strengthens the corrected-envelope comparison on the actual
short-shape range \(1<x\le2\). Its correction coefficient is
\[
c=\frac7{96}<\frac17.
\tag{1}
\]
It proves both the initial envelope inequality and the scale
comparisons needed to use this smaller coefficient. The competitive
upper cap always belongs to the original common covector.

Use the notation of
[the corrected-envelope theorem](MIXED_SMALLER_SHORT_CORRECTED_ENVELOPE_CAP.md)
and [the scale theorem](MIXED_SMALLER_SHORT_ENVELOPE_SCALE_MONOTONICITY.md).
In particular
\[
S=1+x,\quad r=S^{-1},\quad r_A=\frac\alpha{\alpha+\beta},
\quad q=\rho_A,\quad p=\tau q,\quad T=r_A/q,
\]
\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,
\quad \lambda=1-(1-\alpha^{-2})q,
\quad d=qD/\alpha^2.
\]
The actual ordered equal secants satisfy
\[
1\le\alpha<x\le\beta\le\alpha x,\qquad
\frac34<u\le U(r),\qquad U(s)=1-s+s^2,
\]
and the already proved lower and upper orders give the strip
\[
x+\frac{8x(\alpha-1)}{9x+8}\le\beta
\le x+\frac{x(7x+1)(\alpha-1)}{4x^2+11x+1}.
\tag{2}
\]
The coefficient 9/8 in the upper-order theorem is valid here because
\(x\le2<5\).

## 1. Retain the incoming deficit at the actual outer root

Set
\[
J_A=\frac{U(r_A)-u}{r_A}\ge0.
\]
The usual outer pairing bound has the stronger form
\[
\boxed{E_{L,\mathrm{actual}}\le3q-J_A.}
\tag{3}
\]
Indeed, first put both norms at their incident ceilings. The resulting
pairing is
\[
E_{\rm ceil}=-1+2r_A+2/\tau-q+\log(q\tau/r_A).
\]
At \(q=r_A/\tau\), its difference from \(3q\) is
\(-[1-2r_A][1-2/\tau]\le0\). The derivative of
\(E_{\rm ceil}-3q\) is \(1/q-4>0\) on the retained range.
Thus \(E_{\rm ceil}\le3q\) for the actual smaller value of q.
Restoring the incoming norm subtracts exactly \(J_A\), and restoring
the outgoing norm subtracts another nonnegative quantity. This proves
(3).

Along the two original envelope segments, \(E_L\) decreases. Hence
(3) persists without an artificial outer root or incident ceiling.
The exact derivative ratio is
\[
\frac{d\Gamma}{dR_\tau}
=\frac{2ub+E_L}{8(1-q)^2(1+\tau b)},
\qquad b=\lambda t-d.
\tag{4}
\]
The denominator is positive by the original envelope proof. Also
\(\tau(3q-J_A)<3r_A<3/2<2u\). Consequently replacing \(E_L\)
by \(3q-J_A\), then increasing b to
\[
b_0=\lambda/S-d=1/S-qK,
\quad K=(1-\alpha^{-2})/S+D/\alpha^2,
\tag{5}
\]
can only raise (4). This uses the derivative
\((2u-\tau E_L)/(1+\tau b)^2>0\) with respect to b.

The positive-diagonal theorem gives \(D>0\) here. Moreover
\[
D-4\alpha^2
\le-3\alpha^2+2\alpha x+1+2x-2x^2
\le-2(x-1)^2\le0.
\tag{6}
\]
For the second inequality, the preceding quadratic decreases with
\(\alpha\ge1\), since \(x\le2\). Hence
\[
0<K\le9/2,\qquad b_0\ge-2/7,
\qquad u\le\frac34+\frac{(x-1)^2}{12S^2}\le\frac{41}{54}.
\tag{7}
\]
The bound on b follows from \(\lambda\ge6/7\), \(S\le3\),
\(D/\alpha^2\le4\), and \(q\le1/7\).

If \(b_0\le0\), the numerator divided by \(1+\tau b_0\)
is at most \(3q-J_A\le3q\). Thus (4) is at most
\[
\frac{3q}{8(1-q)^2}\le\frac7{96}.
\tag{8}
\]
Suppose \(b_0>0\). The comparison numerator is nonnegative because
it bounds the original nonnegative ratio. Therefore replacing
\(\tau\ge2\) by two raises it once more. The desired bound follows
from
\[
F(q):=\frac7{12}(1-q)^2(1+2b_0)-2ub_0-3q+J_A\ge0.
\tag{9}
\]
Write \(C=7(1-q)^2/12\). On \(0\le q\le1/7\),
\[
F'(q)=-\frac76(1-q)(1+2b_0)+2K(u-C)-3<0.
\]
Indeed \(1+2b_0\ge3/7\), \(C\ge3/7\), and (7) give
\(2K(u-C)-3\le9(41/54-3/7)-3=-1/42\).
It suffices to prove
\[
F(1/7)=J_A-(2u-6/7)b_7>0,
\qquad b_7=\frac{6\alpha^2+1-SD}{7S\alpha^2}.
\tag{10}
\]
Its u derivative is \(-1/r_A-2b_7<0\), since
\(1/r_A\ge2\) and \(b_7\ge-2/7\). Thus use the upper value
\(u_0=3/4+(x-1)^2/(12S^2)\) in (10).

Here is a compact complete polynomial check of this last sign. Put
\(B=\alpha+\beta\), and define
\[
H_N=[3S^2-(x-1)^2]B^2-12S^2\alpha B+12S^2\alpha^2,
\]
\[
P=49S\alpha H_N
 -4B(17x^2+20x+17)(6\alpha^2+1-SD).
\tag{11}
\]
Direct substitution gives
\[
P=588S^3\alpha^2B\,
 [J_A-(2u_0-6/7)b_7].
\tag{12}
\]
The order strip (2) is contained in the simpler interval
\[
x+\frac8{17}(\alpha-1)\le\beta
 \le x+\frac45(\alpha-1).
\tag{13}
\]
The lower inequality follows because \(8x/(9x+8)\) increases for
\(x\ge1\). The upper follows from
\[
19x^2-39x-4\le0\qquad(1\le x\le2):
\]
this convex quadratic has endpoint values \(-24,-6\).

Parametrize this enlarged interval by
\[
x=1+z,\quad\alpha=1+zA,\quad
\beta=1+z+\left(\frac8{17}+\frac{28}{85}t\right)zA,
\qquad0\le z,A,t\le1.
\tag{14}
\]
For \(B_{j,n}(s)=\binom nj s^j(1-s)^{n-j}\), direct
multiplication of (11) gives the exact polynomial identity
\[
P=\sum_{j=0}^3\sum_{k=0}^2
 B_{j,3}(A)B_{k,2}(t)H_{jk}(z).
\tag{15}
\]
The following table prints every coefficient of each distinct
polynomial \(H_{jk}\), in ascending powers \(z^0,\ldots,z^6\),
and its exact value at one. For j=0 the three polynomials coincide.

| j | k | Complete coefficients of H | H(1) |
|---:|---:|---|---:|
| 0 | 0,1,2 | `432, 2376, 2000, -804, -1844, -878, -136` | `1146` |
| 1 | 0 | `432, 32400/17, 36232/17, -5432/17, -81680/51, -14690/17, -146` | `78436/51` |
| 1 | 1 | `432, 163008/85, 189112/85, -28336/85, -147128/85, -241126/255, -2414/15` | `357964/255` |
| 1 | 2 | `432, 9648/5, 11592/5, -1736/5, -27904/15, -15406/15, -2638/15` | `6348/5` |
| 2 | 0 | `432, 24408/17, 475112/289, -11264/289, -394420/289, -762508/867, -9008/51` | `911992/867` |
| 2 | 1 | `432, 124056/85, 153864/85, 8928/85, -358124/255, -242612/255, -3320/17` | `320168/255` |
| 2 | 2 | `432, 7416/5, 50472/25, 1408/5, -36564/25, -26132/25, -5472/25` | `37224/25` |
| 3 | 0 | `432, 16416/17, 155504/289, -88260/289, -200932/289, -139868/289, -28476/289` | `101888/289` |
| 3 | 1 | `432, 85104/85, 64256/85, 8244/85, -7244/17, -2204/5, -8876/85` | `22352/17` |
| 3 | 2 | `432, 5184/5, 27536/25, 4092/5, 2988/25, -7548/25, -2492/25` | `77664/25` |

Each displayed row has positive coefficients through one degree m
and negative coefficients thereafter. For \(0<z\le1\), comparison
of each term with its value at one times \(z^m\) gives
\[
H_{jk}(z)\ge z^mH_{jk}(1)>0.
\]
At z=0 all the constants are 432. Every polynomial is therefore
strictly positive on [0,1]. The weights in (15) are nonnegative and
sum to one, so \(P>0\) throughout (14). This proves (10), hence
(9). All coefficients in the finite sign argument are displayed;
there is no hidden minimum over a transformed coefficient family.

We have proved \(d\Gamma/dR_\tau\le7/96\) on both original
envelope segments. Integrating from the actual root, where
\(R_\tau=0\), yields
\[
\boxed{\Gamma_{\rm actual}\ge\Gamma_* -\frac7{96}R_\tau^*.}
\tag{16}
\]

## 2. A stronger slope bound at fixed normalized duration

Set \(J=S[U(1/S)-u]\ge0\), and use the unchanged scale slope
\(L(p)\) from the scale theorem. The order strip (2) gives
\[
\boxed{3\alpha^2L(p)>7J(2S-1).}
\tag{17}
\]
Here L(p) denotes the fixed-normalized-duration scale slope from the
accepted scale theorem.

The proof parallels the accepted corrected-cap scale proof. At fixed
\(x,\alpha,p,u\), the slope increases with beta. Lower beta to
\[
\beta_0=x+\frac{8x(\alpha-1)}{9x+8}.
\]
The bound \(p\le\alpha/(\alpha+\beta_0)\) persists. The difference
in (17) is affine in u, so use the two endpoints \(u=3/4,U(1/S)\).
At the upper endpoint J=0 and the positive-slope proof in Section 1
of the accepted corrected-cap scale theorem applies unchanged.

At the lower endpoint let
\[
z=\alpha-1\ge0,\quad y=x-\alpha\ge0,
\quad k=\alpha/p-\alpha-\beta_0\ge0,
\quad M=9x+8,\quad B_0=\alpha+\beta_0+k.
\]
Direct collection in \(L=pA_2+p^{-1}-1-A_3\) gives
\[
\boxed{
4S\alpha B_0 M^2[3\alpha^2L-7J(2S-1)]
=12S\alpha^2M^2 k^2+P_1(z,y)k+P_0(z,y).}
\tag{18}
\]
The following complete lists define the two polynomials. In a row
labelled d, the entries are the coefficients of
\(z^d,z^{d-1}y,\ldots,y^d\), in that order; unlisted degrees vanish.

| d | coefficients in P_1 |
|---:|---|
| 1 | 20400, 27744 |
| 2 | 73071, 145134, 57987 |
| 3 | 103891, 272820, 206625, 44428 |
| 4 | 74098, 241308, 266511, 114052, 14751 |
| 5 | 27306, 104832, 149949, 96408, 25767, 1782 |
| 6 | 4671, 19926, 33534, 27756, 11259, 1782, 0 |
| 7 | 243, 972, 1458, 972, 243, 0, 0, 0 |

| d | coefficients in P_0 |
|---:|---|
| 2 | 2862, 16524, 15606 |
| 3 | 14924, 104547, 157974, 64787 |
| 4 | 29180, 227323, 466764, 363497, 96514 |
| 5 | 28339, 231539, 587286, 659095, 342392, 67383 |
| 6 | 14791, 119770, 346533, 491947, 371938, 144063, 22518 |
| 7 | 4029, 30336, 90999, 145041, 134970, 74223, 22518, 2916 |
| 8 | 459, 2997, 7884, 10746, 8019, 3105, 486, 0, 0 |

For a direct way to reconstruct (18), write
\[
D_N=(\alpha^2+1+2x)M+2x(9x+8\alpha)(\alpha-x),
\quad B_N=\alpha M+x(9x+8\alpha)+kM,
\]
\[
e=\alpha^2-1,\quad E_N=4-S^2.
\]
The right side of (18) before collecting z,y is the explicit product
\[
\begin{split}
&12S(e^2+eS+S^2)M^2+9S D_N^2+3D_NeE_NM
 -12S D_N(2S-1)M\\
&+12S\alpha^2B_N^2
 -12S\alpha B_N\{[\alpha^2-(2S-1)]M+3D_N/2\}\\
&-3\alpha B_NeE_NM-7\alpha(x-1)^2(2S-1)B_NM.
\end{split}
\tag{19}
\]
Thus (18) and the lists involve only multiplication and collection of
the displayed products. Every coefficient is nonnegative, and
\(P_0\ge2862z^2+16524zy+15606y^2>0\) because \(x>1\).
This proves (17).

The exact Casimir derivative from the accepted scale theorem gives
\[
(\Gamma_*)_q\le\frac{J(2S-1)}{8\alpha^2(1-q)^2}
<\frac{3L(p)}{56(1-q)^2}
\le\frac7{96}L(p)\qquad(q\le1/7).
\tag{20}
\]
When J=0 the strict conclusion follows instead from \(L(p)>0\).
Therefore \(\Gamma_*-cR_{p/q}^*\) strictly decreases at fixed p.

## 3. The same corrected expression decreases at tau two

We prove, with the original incoming norm retained,
\[
(R_2^*)'>1\qquad(0<q\le1/7,\ 1<x\le2).
\tag{21}
\]
Put \(a=\alpha^{-2}\), \(\varepsilon=1-a\),
\(\Delta=D/\alpha^2\), and
\[
h=-E_0=S(1-u)-1/S,
\quad A=\varepsilon^2+\varepsilon Sa+S^2a^2,
\quad K_0=\varepsilon h+(2S-1)a.
\]
Here \(2<S\le3\), \(0\le h\le5/12\), and
\(3/4\le u\le u_0=3/4+(S-2)^2/(12S^2)\le41/54\).
The scale coefficients give, by completing the square in \(\Delta q\),
\[
\begin{split}
q(R_2^*)'&=1-[2+\varepsilon(3-h)]q+4Aq^2
 +4u(\Delta q)^2-[2(u-h)+4K_0q]\Delta q\\
&\ge F(q,a):=1-[2+\varepsilon(3-h)]q+4Aq^2
 -\frac{[u-h+2K_0q]^2}{4u}.
\end{split}
\tag{22}
\]
F is concave in a: its quadratic coefficient is
\(-q^2S^2[u-U(1/S)]^2/u\). It suffices to prove F>1/7 at
a=0 and a=1.

At a=0, \(0\le u-(1-2q)h\le u\), whence
\[
F(q,0)\ge1-5q+4q^2-u/4
\ge\frac{18}{49}-\frac{41}{216}
=\frac{1879}{10584}>\frac17.
\tag{23}
\]
At a=1,
\[
F(q,1)=1-2q+4S^2q^2
 -\frac{[u-h+2(2S-1)q]^2}{4u}.
\tag{24}
\]
Its quadratic coefficient in q is positive on this domain. Moreover
\(uF_q(1/7,1)\) decreases with u: its u derivative is
\(-6S^2/7-S-1<0\). At u=3/4 the derivative is
\[
F_q(1/7,1)=\frac{6S^3-17S^2-85S+28}{21S}<0:
\]
use \(6S^3\le18S^2\), then \(S^2\le3S\). Thus (24)
decreases on \([0,1/7]\). At q=1/7 it is concave in u, so only
u=3/4 and u=u_0 need checking. With z=S-2, their excesses over
1/7 are respectively
\[
\frac{111z^4+654z^3+1931z^2+2700z+348}{2352S^2}>0,
\]
\[
\frac{191z^6+1794z^5+8523z^4+24408z^3+38904z^2+27432z+3132}
 {1176S^2(5S^2-2S+2)}>0.
\tag{25}
\]
This proves F>1/7 and hence (21).

Finally \(J\le(S-2)^2/(4S)\le1/12\), so
\[
(\Gamma_*)_q\le\frac{245}{3456},
\qquad
\frac d{dq}(\Gamma_*-cR_2^*)
<\frac{245}{3456}-\frac7{96}=-\frac7{3456}<0.
\tag{26}
\]

## 4. Consequence for the original covector

Begin with (16) at the original outer root and hold its p fixed.
Increase q to \(\min\{q_c,1/7,p/2\}\), using (20). If the
last face is reached first, keep tau=2 and increase q further to
\(\min\{q_c,1/7\}\), using (26). The resulting corrected scalar
is still a lower bound on \(\Gamma_{\rm actual}\).

Here \(r_A\ge1/(1+x)\ge1/3\), so at either final scale face
\(T=r_A/q\ge7/3>2\). Thus the final duration belongs to [2,T],
including the tau-two continuation. No other positive scale face is
left. The incoming norm and exact short shape are unchanged throughout.
No uncorrected competitive cap or physical completion cost is moved
to the artificial comparison point.
