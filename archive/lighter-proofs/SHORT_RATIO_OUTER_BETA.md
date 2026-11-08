# Outer upper-ratio tests: lower-shape beta comparison

This note uses the exact transport and tests \(H_0,H_1\) of
[the archived outer-ratio sign](../../archive/notes/MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_SIGN.md),
and the notation and norm-coefficient bounds of
[the reciprocal proof](SHORT_RATIO_OUTER_RECIPROCAL.md).
It proves the beta comparison needed after reciprocal convexity reaches

\[
a=a_f(x)=\frac{36x+25}{84},\qquad
\frac{13}{6}\le x\le\frac{12}{5},\qquad
\frac58\le c\le\frac78,
\quad b=x+c(a_f-1).
\tag{1}
\]

Throughout this note the moving norm is

\[
u_s=\frac34+
\frac{17(x-1)^3/(240S^2)+(b-x)/1200}{b-1},\quad S=x+1.
\]

The conclusions are

\[
\boxed{\frac{d}{db}H_j(x,a_f,b;u_s)>
\frac{307}{34000}>0\quad(j=0,1),}
\tag{2}
\]

and, on the entire lower-shape face,

\[
\boxed{w<3/4.}
\tag{3}
\]

In particular increasing \(c\) to the actual upper comparison bound
\(c_+(x)=(24x+51)/128\) raises both tests. Statement (3) is derived
from the continued rational transport, not from an outgoing physical
floor.

## 1. Two transport bounds at the lower shape

The interval in (1) has
\(6/5<a_f<3/2\), so \(2/3<r=1/a_f<5/6\).
Recall the reciprocal quantities

\[
D_r=d_0+d_1r+d_2r^2,\quad
N_u=S(6+r^2),\quad j=N_u-2D_r>0,
\quad t=D_r(N_u-D_r)>0.
\]

The exact transport derivatives are

\[
(E_L)_u=-j/7<0,\qquad w_u=-t/49<0.
\tag{4}
\]

Thus an upper bound for either transport quantity follows by lowering
\(u_s\) to \(3/4\). At that fixed norm,

\[
E_0=-S/4+S^{-1}<-7/15,\quad
J_2=7S/4-1+S^{-1}<21/4.
\]

Together with \(D_r\ge53/72,r\le5/6\), this gives

\[
6E_0+J_2r^2<203/240,
\qquad 2uD_r\ge53/48,
\qquad E_L>0.
\tag{5}
\]

Since \((D_r)_c=2(1-r)(1-xr)<0\), differentiation at fixed
\(x,r,u=3/4\) yields

\[
(E_L)_c=2u(D_r)_c/7<0,
\qquad w_c=(D_r)_cE_L/7<0.
\tag{6}
\]

It remains to bound the two functions at \(c=5/8,u=3/4\).
Put \(A=36x+25\), \(h=x-2\), so \(1/6\le h\le2/5\),
and write \(E_f,w_f\) for this fixed scalar face. The complete
univariate identities are

\[
168SA^2(1/3-E_f)=
-46656h^4-137376h^3+182520h^2+492047h+90213,
\tag{7}
\]

\[
\begin{aligned}
784SA^4(3/4-w_f)=\frac14\big[&1110786048h^6+10265688576h^5
+39296105856h^4\\
&+83068492464h^3+97377690816h^2
+48493013565h-135636633\big].
\end{aligned}
\tag{8}
\]

The right side of (7) is greater than
\(90213-137376(2/5)^3-46656(2/5)^4>80000\).
The bracket in (8) is greater than
\(48493013565/6-135636633>7000000000\).
All denominators are positive. Equations (4)--(8) prove

\[
E_L<1/3,\qquad w<3/4
\tag{9}
\]

at the moving norm on all of (1).

## 2. The exact beta derivative and its signs

Let \(p=a/(a+b)=1/Z\), \(U(p)=1-p+p^2\), and

\[
C_0=\frac{2(x-a)}{7a^2},\quad
m_0=4-\frac{a+b}{2a},\quad
m_1=\frac{7a}{a+b}+\frac14.
\]

Differentiating the exact logarithm before any norm substitution gives

\[
(H_j)_b=\frac{u-U(p)}a+
C_0(2u-m_jE_L)+(m_j)_b(w-3/4).
\tag{10}
\]

At \(a=a_f\), one has

\[
\frac{14}{5}<Z<\frac{25}{8},\quad
0<m_j<\frac{11}{4},\quad
C_0>\frac3{20}.
\tag{11}
\]

Indeed \(Z=1+c+84(x-c)/(36x+25)\) increases in \(x,c\).
Its corner values \(2375/824\) and \(13479/4456\) lie between
the bounds in (11). The last inequality follows from the quadratic

\[
20A^2(C_0-3/20)=-3888h^2+2088h+5853>0.
\tag{12}
\]

Now \(p\ge8/25\), and \(U\) is decreasing below \(1/2\),
so \(U(p)\le U(8/25)=489/625\). Therefore

\[
\frac{u_s-U(p)}{a_f}>-\frac{27}{1000}.
\tag{13}
\]

By (9), (11), and \(u_s\ge3/4\),

\[
C_0(2u_s-m_jE_L)>
\frac3{20}\left(\frac32-\frac{11}{12}\right)=\frac7{80}.
\tag{14}
\]

Both \((m_j)_b\) are negative, so the last term in (10) is
positive by (9).

To include the norm motion, put
\(k=17(x-1)^3/(240S^2)-(x-1)/1200>0\). Then

\[
-(u_s)_b=\frac{k}{(b-1)^2}
<\frac{17(x-1)}{240S^2}\le\frac{119}{13872}.
\tag{15}
\]

The last function increases on the present x interval. The reciprocal
proof gives \(0<(H_j)_u<6\) on the entire smaller-shape rectangle.
Combining (10)--(15) and the chain rule gives

\[
\frac{d}{db}H_j(x,a_f,b;u_s)
>\frac7{80}-\frac{27}{1000}-\frac{119}{2312}
=\frac{307}{34000}>0.
\]

This proves (2); since \(db/dc=a_f-1>0\), it also proves the
required strict c comparison.

## 3. Compatibility of the two norm bounds at the shared shape

For the larger shapes the original incoming norm is raised to

\[
u_v=\frac34+\frac{2(x-1)^2}{S(35x+13)}.
\]

At \(a=3/2\), the smaller-shape norm decreases in \(b\) by
(15). Its maximum on \(5/8\le c\le7/8\) is therefore at
\(b=x+5/16\). Direct cancellation gives the quartic identity

\[
\begin{aligned}
&240S^2(16x-11)(35x+13)
\{u_v-u_s(x,x+5/16)\}\\
&\qquad=-1840h^4-2691h^3+7579h^2+15539h+6917>0.
\end{aligned}
\tag{16}
\]

For positivity, discard the two positive higher terms and bound the
negative powers by \((2/5)^i\); the result exceeds 6000.
Moreover

\[
20S(35x+13)(4/5-u_v)=-5h^2+108h+209>0.
\tag{17}
\]

Thus \(3/4<u_v<4/5\) and \(u_s\le u_v\) at \(a=3/2\).
Because \((H_j)_u>0\) there, the middle terminal signs at norm
\(u_v\) also control the endpoint of the moving-\(u_s\) comparison.

## Expansion boundary

The five expanded sign identities (7), (8), (12), (16), (17) have
5, 7, 3, 5 and 3 monomials respectively, in one variable, of degrees
4, 6, 2, 4 and 2. The largest printed coefficient is
\(97,377,690,816\). The normalization in (8) deliberately keeps the
factor \(1/4\) on its right: every individual cleared transport
contribution then also satisfies the twelve-digit bound.
The transport is specialized to \(a=a_f,c=5/8,u=3/4\) before
expansion. No global numerator for a moving-norm beta derivative is used.
