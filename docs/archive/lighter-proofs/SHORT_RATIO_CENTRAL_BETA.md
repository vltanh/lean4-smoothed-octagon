# Central ratio: two increasing beta tests

This replaces the beta step needed for the new duration tangent in the
[central-ratio assembly](SHORT_RATIO_CENTRAL_COMPLETE.md). All polynomial
identities used here are printed in the
[small algebra appendix](SHORT_RATIO_CENTRAL_BETA_ALGEBRA.md).

## 1. Domain and the two tests

Use the unchanged central transport in equations (3)--(4) of
[the source statement](../../archive/notes/MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_SIGN.md).
Its elementary Section 2 comparison, involving only a cubic and a
quadratic, embeds the source domain in
\[
13/6\le x\le12/5,\qquad 1\le a\le4/3,\qquad
b=x+c(a-1),\quad5/8\le c\le7/8.                 \tag{1}
\]
It also proves \(K-2aB\ge25/36\), so \(T>2\) on this enlarged set.
We retain exactly the source's incoming ceiling
\[
u=\frac34+
 \frac{680(x-1)^3+3S^2(b-x)}{9600S^2(b-1)},
\quad S=x+1,\quad K=x(x+2)+a^2,\quad B=a+b.       \tag{2}
\]
For clarity put
\[
\begin{gathered}
D=a^2+2ab+1+2x-2bx,\quad M=S^2(S^2-S+1),\\
E=S^3(u-1)+3S-1,\quad w=(M+uD^2-DE)/K^2,\\
E_L=(2Du-E)/K,\quad k=aB/K,\quad T=1/k,\quad h=w-3/4,\\
R=(u-1)B/a+a/B+1-a^2/K-E_L.
\end{gathered}                                      \tag{3}
\]
The two tests whose beta monotonicity we prove are
\[
G=R+(4-7k/2)h+\log(2k),\qquad
H=R+(T+1/4)h+\log(2k).                              \tag{4}
\]
The first is exactly the source's \(G_2\). We prove
\[
G_b>0,\qquad H_b>0                                  \tag{5}
\]
throughout (1), including the beta dependence of (2).

We may further enlarge the lower beta endpoint to \(b=x\) for this
proof. All ensuing algebraic and elementary bounds hold on
\(x\le b\le x+7(a-1)/8\).

## 2. Keep the incoming pole visible

Define
\[
u_f=2401/3200,\quad
J=\frac{(x-1)[680(x-1)^2-3S^2]}{9600S^2},\quad C=a+1,
\]
\[
\delta=2(a-x),\quad D_0=(a+1)(2x+1-a),\quad
E_f=S^3(u_f-1)+3S-1.
\]
Then \(u=u_f+J/(B-C)\), \(D=D_0+\delta B\), and
\[
\begin{aligned}
w&=c_2B^2+c_1B+c_0+\frac{c_w}{B-C},\\
E_L&=e_1B+e_0+\frac{c_e}{B-C},\\
R&=l_1B+l_0+\frac aB+\frac{c_b}{B-C},                \tag{6}
\end{aligned}
\]
where the complete coefficient formulas are
\[
\begin{aligned}
c_2&=u_f\delta^2/K^2,\\
c_1&=[\delta(2u_fD_0-E_f)+J\delta^2]/K^2,\\
c_0&=[M+u_fD_0^2-D_0E_f+J\delta(2D_0-S^3+\delta C)]/K^2,\\
c_w&=JC^2(C^2-S^3)/K^2,\\
e_1&=2u_f\delta/K,\qquad e_0=(2u_fD_0-E_f+2J\delta)/K,\\
c_e&=J(2C^2-S^3)/K,\\
l_1&=(u_f-1)/a-e_1,\quad l_0=J/a+1-a^2/K-e_0,\quad
c_b=JC/a-c_e.
\end{aligned}                                        \tag{7}
\]
These are polynomial division by the single linear factor \(B-C\),
performed before any two-variable expansion. Their elementary checks
use \(D_0+\delta C=C^2\).

Here \(0<J<1/50\) and \(c_w<0\). Positivity of J follows directly
from \(x-1\ge7/6\), \(S\le17/5\). For its upper bound put
\(v=x-2\in[1/6,2/5]\); then
\[
9600S^2(1/50-J)=1075-843v-1827v^2-677v^3>400.         \tag{8}
\]
For \(c_w<0\), use \(C^2\le49/9<(19/6)^3\le S^3\).

## 3. Both beta derivatives increase

Put \(\ell=7a/(2K)\). The cubic polynomial part of G has coefficients
\[
p_3=-\ell c_2<0,\qquad p_2=4c_2-\ell c_1,
\quad p_1=l_1+4c_1-\ell(c_0-3/4),
\]
\[
p_0=l_0+4(c_0-3/4)-\ell c_w,
\qquad p_c=c_b+(4-\ell C)c_w.
\]
Thus
\[
G=p_3B^3+p_2B^2+p_1B+p_0+a/B+p_c/(B-C)+\log(2k),
\]
and consequently
\[
G_{bb}=6p_3B+2p_2+\frac{2a}{B^3}
       +\frac{2p_c}{(b-1)^3}-\frac1{B^2}.             \tag{9}
\]
The first two groups of identities in the appendix prove
\[
p_c>0,\qquad 6p_3B_{\max}+2p_2>1/10,
\quad B_{\max}=a+x+7(a-1)/8.                          \tag{10}
\]
As \(p_3<0\), the second bound holds with \(B\) in place of
\(B_{\max}\). The elementary cubic identity
\[
B^3-27a^2(b-a)=(b-2a)^2(b+7a)\ge0
\]
therefore gives
\[
G_{bb}>1/10-1/(27a^2)\ge1/10-1/27>0.                 \tag{11}
\]

For H define
\[
A_1=a+K(c_0-3/4)/a-Kc_w/(aC),
\qquad P_c=c_b+Kc_w/(aC)+c_w/4.
\]
In particular \(P_c=JS^2(a-x)/(aK)+c_w/4\).
Polynomial division in (6) now gives
\[
H_{bb}=c_2/2+\frac{2A_1-B}{B^3}
                      +\frac{2P_c}{(b-1)^3}.        \tag{12}
\]
The appendix proves \(A_1>9/2\), \(P_c>-2J\).
Since \(B\le161/40\), \(b-1\ge7/6\), (8) yields
\[
H_{bb}>
\frac{9-161/40}{(161/40)^3}
-\frac{2/25}{(7/6)^3}>0.                              \tag{13}
\]
The last comparison is of two positive rational numbers. Therefore
the two first derivatives in (5) are minimized at \(b=x\).

## 4. A simple incoming lower comparison at b=x

At this endpoint the original norm and its beta derivative satisfy
\[
u_0=3/4+17(x-1)^2/(240S^2)\ge v:=3/4+(x-1)/125,
\qquad u_b\ge-9/1000.                                \tag{14}
\]
For the first inequality, clear the positive factors to get
\(2125(x-1)-240S^2\ge0\). This concave quadratic has endpoint
values \(145/2\) and \(1003/5\). For the second, clearing the
positive denominator gives, with \(z=x-2\),
\[
\frac{432}{5}z^3-\frac{361}{5}z^2-46z+\frac{623}{5}>0.
\tag{15}
\]
Discard the positive cubic and use \(0\le z\le2/5\) in the two
negative terms.

We justify the directions in (14) before substituting. Temporarily
let u be independent of beta. Put
\[
z=D/K,\quad L=S^3/K,\quad \xi=2(x-a)/K>0,
\quad n=4-7k/2.
\]
Throughout the enlarged domain, \(0<z\le1/3\), \(L>1\), \(L\le S\),
\(0<n<3\), and \(D<aB\). Here D is minimized at the upper beta
endpoint, then at \(a=1\), giving
\(D\ge2+4x-2x^2\ge2/25>0\).
The polynomial \(K-3D\) is minimized at \(b=x,a=4/3,x=13/6\),
where it equals \(11/36\). The bounds on L follow from
\(S^2\le K\le S^2+7/9\). Also \(k\ge1/S\) follows by increasing
a from one in \(a(a+x)S-K\), and hence \(n<3\).
Finally
\[
D-aB\le x(a-2x)+1+2x\le-7/6.
\]

The fixed-norm coefficients are
\[
G_u=B/a+L-2z+nz(z-L)>B/a-2z>0,
\]
\[
H_u=B/a+L-2z+(T+1/4)z(z-L)
>B/a-2z-zL/4\ge67/40>0.                              \tag{16}
\]
For the first inequality use \(nz<1\); for the second use
\(Tz=D/(aB)<1\). Their beta derivatives at fixed u satisfy
\[
(G_u)_b=1/a+2\xi+\ell z(L-z)+n\xi(L-2z)>0,
\]
\[
(H_u)_b=\frac{(a-2x)^2+x(x+2)}{aK}
+\frac{D_0(S^3-D_0)}{aKB^2}+\frac\xi4(L-2z)>0.        \tag{17}
\]
Indeed \(0<D_0\le(7/3)(24/5)<S^3\), and all other factors have
the indicated strict signs.

Write \(G^{\mathrm{rat}}=G-\log(2k)\) and
\(H^{\mathrm{rat}}=H-\log(2k)\), keeping u independent in them.
By (14)--(17), the original total beta derivatives at \(b=x\)
are bounded below by
\[
f_0=\left[G^{\mathrm{rat}}_b+1/B-(9/1000)G_u\right]_{b=x,u=v},
\]
\[
f_1=\left[H^{\mathrm{rat}}_b+1/B-(9/1000)H_u\right]_{b=x,u=v}.
\tag{18}
\]
The inequalities (17) control the increase from v to \(u_0\);
(16) controls the replacement of \(u_b\) by \(-9/1000\).

## 5. Two small base-face sign arguments

Now set \(b=x\), \(B=a+x\), \(u=v\), and keep the corresponding
D,E,M from (3). Define
\[
\eta=x-a,\quad Q=2vD-E,\quad W=M+vD^2-DE,
\quad N_n=4K-7aB/2,
\]
\[
Q_0=a^2K+M+vD_0^2-D_0E-3K^2/4.
\]
The following factored sums specify the two numerator sources
without expanding the first, degree-ten, parent:
\[
\begin{aligned}
N_0={}&2000(v-1)B^2K^3+2000axK^3+8000aB^2\eta vK^2\\
&-4000aB^2\eta N_nQ-7000a^2B^2(W-3K^2/4)\\
&-18B^3K^3-18aB^2(S^3-2D)K^2-18aB^2N_nD(D-S^3),
\end{aligned}                                        \tag{19}
\]
\[
\begin{aligned}
N_1={}&4000(v-1)B^2K^2+16000v\eta xB^2K+4000aBK^2-4000KQ_0\\
&-2000aB^2\eta Q-36B^3K^2-36aB^2(S^3-2D)K\\
&-36BKD(D-S^3)-9aB^2D(D-S^3).
\end{aligned}                                        \tag{20}
\]
Direct differentiation of (3)--(4), still in factored form, gives
\[
f_0=\frac{N_0}{2000a(a+x)^2K^3},\qquad
f_1=\frac{N_1}{4000a(a+x)^2K^2}.                      \tag{21}
\]
All denominators are positive. The appendix expands only
\((N_0)_{xx}\), \((N_0)_x(2,a)\), \(-(N_0)_a(2,a)\), and \(N_1\).
Each has degree at most eight. Elementary termwise bounds give
\[
(N_0)_{xx}>22000000,\quad (N_0)_x(2,a)>5000000,
\quad -(N_0)_a(2,a)>1000000,
\]
\[
N_0(2,4/3)=6582707200/6561>1000000,
\quad N_1>200000.                                    \tag{22}
\]
Thus \(f_0,f_1>0\). By (11),(13),(18), this proves (5) on the
whole enlarged beta range.

## 6. The duration tangents inherit beta monotonicity

For any \(t=t(a)\ge2\), the assembly's two tests are
\[
F_0=G+4/t-2/t^2-3/2+\log(t/2),
\]
\[
F_1=H+T\phi(t)+2/t-1+\log(t/2),\qquad
\phi(t)=-\frac{(t-2)^2}{4t^2}\le0.                   \tag{23}
\]
The added terms for \(F_0\) are independent of beta. For \(F_1\),
\(T_b<0\), so \(\partial_b[T\phi(t)]\ge0\). Consequently
\[
(F_0)_b>0,\qquad(F_1)_b>0.
\]
Both may therefore be evaluated at the source-enclosing upper face
\(b_+(x,a)=x+(24x+51)(a-1)/128\), with the norm (2) evaluated there.
No outgoing norm floor is asserted at a comparison endpoint.

The largest expanded identity has 43 monomials and total degree eight
in two variables. All polynomial coefficient numerators, including
separately differentiated contributions before summation, have at most
twelve digits. The beta proof requires no interval subdivision.
