# S4: two complete small derivative signs

This replaces the first two signs in equations (4)--(5) of
[the extended Casimir derivative note](../../archive/notes/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md).
It proves on the original full rectangle
\[
2\le x\le13/6,\qquad0\le d\le1/19,\qquad13/5\le e\le3,
\quad a=1+ed,\quad b=x(1+d),
\]
that
\[
\boxed{-\Phi_d>27/5000,\qquad \Psi_e/(xd)>0.}                 \tag{1}
\]
At `d=0`, the second quotient means its continuous extension `Psi_a/x`;
the actual derivative `Psi_e` is zero. **The other four S4 derivative
signs and the full S4 row remain separate obligations.**

The first proof bounds three partial derivatives before following the
actual displacement curve. The second first raises neither beta nor
the incoming norm: their two positive derivative signs reduce both to
their lower faces. All displayed expansions are univariate or bivariate,
of degree at most eight. No complete three-variable numerator is expanded.

## 1. The original source and a containing rectangle

Use independent `x,a,b,u` until explicitly following the displacement
curve. Set
\[
S=x+1,\quad X=x(x+2),\quad K=X+a^2,\quad B=a+b,
\quad D=a^2+2ab+1+2x-2bx,
\]
\[
E=S^3(u-1)+3S-1,\quad M=S^2(S^2-S+1),
\]
\[
w=(M+uD^2-DE)/K^2,\qquad E_L=(2uD-E)/K,
\quad \Gamma=(4Mu-E^2)/(16X^2),\quad y=2aB/K.
\]
The same two residuals are
\[
R_0=2w-1/2+(u-1)B/a+a/B-a^2/K-E_L+\log y,
\]
\[
R_1=K(w-3/4)/(aB)+1+(u-1)B/a+a/B-a^2/K-E_L+\log y,
\]
and `Phi=Gamma-R_0/7`, `Psi=Gamma-R_1/7`.
These are exactly the original functions, with the factor `S^2` already
absorbed into the present `E`.

All partial-derivative comparisons use the containing rectangle
\[
2\le x\le13/6,\quad1\le a\le22/19,\quad x\le b\le20x/19,
\quad3/4\le u\le19/25.                                      \tag{2}
\]
On it,
\[
1<D\le1073/361<3,\quad9\le K<21/2,\quad
9/100<D/K<1/3,\quad B<7/2,\quad x-a\ge16/19.                 \tag{3}
\]
For the lower `D` bound, replace `a` by one and `b` by `20x/19`;
`2+2x-40x(x-1)/19` decreases and is `173/171>1` at `13/6`.
For the upper bound replace `b` by `x`, raise `a` to `22/19`,
and lower `x` to two. These replacements have the stated signs by the
quadratic definition of `D`. The other bounds follow directly.

At the original incoming upper value,
\[
u=3/4+\frac{2(x-1)^3}{SZ(b-1)}+\frac{(b-x)^3}{48x^2(b-1)},
\qquad Z=35x+13,
\]
we have `u_d<0` at `b=x(1+d)`. Indeed, with
`J=2(x-1)^3/(SZ)` and `b-1=x-1+xd`,
\[
u_d=\frac{x d^2[3(x-1)+2xd]/48-xJ}{(x-1+xd)^2}<0.             \tag{4}
\]
The first numerator term after division by `x` is less than
`(1/361)(7/2+13/57)/48<1/4000`, whereas `J>=2/(3\cdot83)>1/125`.
The function `J` increases, as its logarithmic derivative
`3/(x-1)-1/S-35/Z` is positive. Also
\[
-u_d\le\frac{2x(x-1)}{SZ}<9/500,                              \tag{5}
\]
because the numerator of the last difference after multiplying by
`500SZ` is `-685x^2+1432x+117`, a concave quadratic with positive
endpoint values `241` and `143/36`.
The maximum of `u` is at `d=0`; its remaining term
`2(x-1)^2/(SZ)` increases in `x` and is less than `1/100` at `13/6`.
Thus the actual upper norm belongs to (2).

## 2. Elementary partial-derivative reductions for Phi

Write `eta=x-a`, `z=D/K`, `C=S^3/K`, and `F=E+u(K-2D)`.
All of `eta,E,K-2D,F` are positive on (2). For `E`, its minimum
is at `u=3/4,x=13/6`, where it is `485/864>0`.
Differentiating before collecting any shape polynomial gives
\[
(R_0)_b=(u-1)/a+b/B^2+4\eta F/K^2,
\]
\[
(R_0)_{bb}=(a-b)/B^3+16u\eta^2/K^2>0,                       \tag{6}
\]
since `(b-a)/B^3<=1/(27a^2)<=1/27` and
`16u eta^2/K^2 >=12(16/19)^2/(21/2)^2>1/27`.
Moreover
\[
(R_0)_{bu}=1/a+4\eta(S^3+K-2D)/K^2>0.
\]
Consequently `Phi_b` is largest at `b=x,u=3/4`.

For the other partial derivative,
\[
(R_0)_{ab}=(1-u)/a^2-2b/B^3-4F/K^2
           -8u\eta(a+2b)/K^2-16a\eta F/K^3<0.                \tag{7}
\]
An explicit upper bound, discarding the two negative terms containing `F`,
is `1/4-32/343-1920/8379<0`.
Also
\[
(R_0)_u=B/a+C(1-2z)-2z(1-z),\quad
z_a=2(B-az)/K>0,\quad C_a=-2aC/K<0,
\]
\[
(R_0)_{au}=-b/a^2+C_a(1-2z)-2Cz_a-2z_a(1-2z)<0.              \tag{8}
\]
Therefore `Phi_a` is largest at `b=20x/19,u=19/25`.

Finally `B/a=1+b/a<33/10`, `C<=S<=19/6`, and (3) give
\[
(R_0)_u<33/10+(19/6)(41/50)-3/25=1733/300.
\]
Here `2z(1-z)>(2)(9/100)(2/3)=3/25`. We have `Gamma_u>=4/25`:
it decreases in `u`, and at `u=19/25` the numerator of
`Gamma_u-4/25`, after multiplication by `200X^2`, is the following
positive polynomial in `h=x-2`.

\[
\begin{aligned}
P_\Gamma(h)={}&6 h^{6} + 108 h^{5} + 753 h^{4} + 2531 h^{3}\\
&{}+ 4101 h^{2} + 2601 h + 76
\end{aligned}
\]
This polynomial has 7 monomials, total degree 6, and largest cleared coefficient 4101.

It follows that
\[
-\Phi_u<1733/2100-4/25=1397/2100<7/10.                       \tag{9}
\]

## 3. Two small polynomial comparisons finish the Phi bounds

The following convention supplies every sign estimate used in this
section and the next. Put `c=a-1`, `h=x-2`, so that
`0<=c<=3/19` and `0<=h<=1/6`. In a printed polynomial in `c,h`,
discard positive terms containing `c`, and replace `c^j` by `(3/19)^j`
in each negative term. Round each resulting coefficient of `h` downward
to the printed integer. This gives the displayed lower polynomial.
This is an elementary monomial inequality on one small polynomial at a
time, not an undisplayed coefficient table or whole-domain expansion.

### 3.1. Beta derivative

The exact source at the two lower faces is
\[
-9/500-\Phi_b(x,a,x,3/4)
=P_b(c,h)/[3500a(a+x)^2K^2].                                 \tag{10}
\]

\[
\begin{aligned}
P_b(c,h)={}&- 63 c^{7} - 126 c^{6} h + 682 c^{6} - 189 c^{5} h^{2}\\
&{}+ 5986 c^{5} h + 19655 c^{5} + 248 c^{4} h^{3} - 1836 c^{4} h^{2}\\
&{}+ 23280 c^{4} h + 73808 c^{4} + 311 c^{3} h^{4} - 10024 c^{3} h^{3}\\
&{}- 79766 c^{3} h^{2} - 124864 c^{3} h + 7463 c^{3} - 626 c^{2} h^{5}\\
&{}- 6206 c^{2} h^{4} - 63636 c^{2} h^{3} - 301372 c^{2} h^{2} - 530778 c^{2} h\\
&{}- 269590 c^{2} - 563 c h^{6} - 2010 c h^{5} + 15103 c h^{4}\\
&{}+ 73116 c h^{3} + 37827 c h^{2} - 162850 c h - 156207 c\\
&{}- 688 h^{6} - 3384 h^{5} + 8620 h^{4} + 82480 h^{3}\\
&{}+ 179080 h^{2} + 145896 h + 33948
\end{aligned}
\]
This polynomial has 35 monomials, total degree 7, and largest cleared coefficient 530778.

\[
\begin{aligned}
L_{b}(h)={}&- 777 h^{6} - 3717 h^{5} + 8465 h^{4} + 80854 h^{3}\\
&{}+ 171251 h^{2} + 106458 h + 2562
\end{aligned}
\]
This polynomial has 7 monomials, total degree 6, and largest cleared coefficient 171251.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{b}(h)>2560>0.
\]

Thus `Phi_b<-9/500` throughout (2), by (6).

### 3.2. Shape derivative

After the justified beta and norm reductions define the normalized
source, still before expansion,
\[
N(x,a)=3325a^2(19a+20x)^2K^3\Phi_a(x,a,20x/19,19/25).
\]
Differentiate this source twice in `x` before expanding. Its exact
source is `-N_xx=P_N(c,h)` with the following degree-eight polynomial.

\[
\begin{aligned}
P_N(c,h)={}&- 493848 c^{7} h - 5372896 c^{7} - 8317440 c^{6} h^{2} + 821064 c^{6} h\\
&{}+ 17904608 c^{6} - 4911120 c^{5} h^{3} + 69503784 c^{5} h^{2} + 588053628 c^{5} h\\
&{}+ 842261304 c^{5} + 47289600 c^{4} h^{4} + 322024400 c^{4} h^{3} + 1312248840 c^{4} h^{2}\\
&{}+ 3567218220 c^{4} h + 3719761880 c^{4} + 59068800 c^{3} h^{5} + 505890900 c^{3} h^{4}\\
&{}+ 1202862800 c^{3} h^{3} + 648953520 c^{3} h^{2} + 496121760 c^{3} h + 1853070800 c^{3}\\
&{}+ 10752000 c^{2} h^{6} + 251685840 c^{2} h^{5} + 1314887100 c^{2} h^{4} + 1183126000 c^{2} h^{3}\\
&{}- 6268171920 c^{2} h^{2} - 14675499648 c^{2} h - 8463256816 c^{2} + 37251200 c h^{6}\\
&{}+ 585994080 c h^{5} + 3055947900 c h^{4} + 6279212800 c h^{3} + 2516207400 c h^{2}\\
&{}- 7030594116 c h - 6417881512 c + 3456000 h^{7} + 91011200 h^{6}\\
&{}+ 901409040 h^{5} + 4388462100 h^{4} + 11547694080 h^{3} + 16603897224 h^{2}\\
&{}+ 12109411788 h + 3430692024
\end{aligned}
\]
This polynomial has 42 monomials, total degree 8, and largest cleared coefficient 16603897224.

\[
\begin{aligned}
L_{N}(h)={}&3456000 h^{7} + 91011200 h^{6} + 901409040 h^{5} + 4388462100 h^{4}\\
&{}+ 11547693598 h^{3} + 16447626881 h^{2} + 10633446796 h + 2206346976
\end{aligned}
\]
This polynomial has 8 monomials, total degree 7, and largest cleared coefficient 16447626881.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{N}(h)>2206346975>0.
\]

The two boundary jets are the complete polynomials
`N(2,a)=V(a)` and `N_x(2,a)=W(a)` printed next. Together with the
second derivative they give a source interface using no degree-ten
expansion. Each coefficient identity is checked after the indicated
differentiation or boundary substitution.

\[
\begin{aligned}
V(a)={}&1010800 a^{8} + 7782704 a^{7} - 67738240 a^{6} - 224073888 a^{5}\\
&{}+ 174466560 a^{4} + 959667200 a^{3} - 202055680 a^{2} - 575897600 a\\
&{}-196608000
\end{aligned}
\]
This polynomial has 9 monomials, total degree 8, and largest cleared coefficient 959667200.

\[
\begin{aligned}
W(a)={}&505400 a^{8} + 8976170 a^{7} - 80987040 a^{6} - 435736672 a^{5}\\
&{}+ 226700800 a^{4} + 2482515200 a^{3} - 346757120 a^{2} - 1871667200 a\\
&{}-737280000
\end{aligned}
\]
This polynomial has 9 monomials, total degree 8, and largest cleared coefficient 2482515200.

\[
\begin{aligned}
-W(1+c)={}&- 505400 c^{8} - 13019370 c^{7} + 4002650 c^{6} + 704856942 c^{5}\\
&{}+ 2817244210 c^{4} + 2245320770 c^{3} - 3091471730 c^{2} - 3191438150 c\\
&{}+ 753730462
\end{aligned}
\]
This polynomial has 9 monomials, total degree 8, and largest cleared coefficient 3191438150.

\[
\begin{aligned}
L_{W}(h)={}&172746440
\end{aligned}
\]
This polynomial has 1 monomials, total degree 0, and largest cleared coefficient 172746440.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{W}(h)>172746439>0.
\]

\[
\begin{aligned}
V'(1+c)={}&8086400 c^{7} + 111083728 c^{6} + 90258528 c^{5} - 2052308720 c^{4}\\
&{}- 6475303360 c^{3} - 4826912400 c^{2} + 1317343968 c + 1132625328
\end{aligned}
\]
This polynomial has 8 monomials, total degree 7, and largest cleared coefficient 6475303360.

\[
\begin{aligned}
L_{V}(h)={}&985521591
\end{aligned}
\]
This polynomial has 1 monomials, total degree 0, and largest cleared coefficient 985521591.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{V}(h)>985521590>0.
\]

It follows that `N_x<0`, and that `V` increases on the whole
shape interval. The scalar comparisons
\[
V(11/10)<-5000000,\qquad V(22/19)<65000000,
\]
\[
3325(11/10)^2[19(11/10)+40]^2[(11/10)^2+8]^3
>11600000000
\]
follow by substitution into the printed polynomial and product.
For `a<=11/10`, the numerator `N` is negative. For larger `a`, its
numerator is at most `V(22/19)` and its positive denominator is at
least the last product. Thus in both cases
\[
\Phi_a<65000000/11600000000=13/2320<3/500.                     \tag{11}
\]
On the original curve `a=1+ed,b=x(1+d),u=bar u`, combine (5),
(9)--(11):
\[
\Phi_d=e\Phi_a+x\Phi_b+u_d\Phi_u
<3(3/500)-2(9/500)+(9/500)(7/10)=-27/5000.
\]
This proves the first assertion of (1), on its unchanged full domain.

## 4. Positive norm and beta derivatives of Psi_a

To eliminate beta before considering the shape sign, put `z=b-x>=0`.
The source identities below are cubic polynomial identities in `z`,
holding `a,x` fixed. Their four coefficient checks are the printed
polynomials in `c,h`. They can equivalently be checked as the first
four boundary jets at `b=x` and a vanishing fourth beta derivative
of the cleared numerator. No expansion in `a,b,x` is performed.

The three exact identities are
\[
7a^2B^2K^2\Psi_{au}=\sum_{i=0}^3 U_i(c,h)z^i,
\]
\[
28a^2B^3K^2\Psi_{ab}|_{u=3/4}=\sum_{i=0}^3 J_i(c,h)z^i,
\]
\[
700a^2B^3K^2\Psi_{ab}|_{u=19/25}=\sum_{i=0}^3 H_i(c,h)z^i.    \tag{12}
\]
For each coefficient, the same printed monomial rule gives the displayed
positive lower polynomial. Thus all three sources are positive. The
beta derivative is affine in `u`, so its two positive endpoint signs
give `Psi_ab>0` for the entire norm interval. Consequently
\[
\Psi_a(x,a,b,u)\ge\Psi_a(x,a,x,3/4).                           \tag{13}
\]

### Coefficient `U_0`

\[
\begin{aligned}
U_{0}(c,h)={}&4 c^{5} h^{2} + 20 c^{5} h + 24 c^{5} - 3 c^{4} h^{4}\\
&{}- 37 c^{4} h^{3} - 113 c^{4} h^{2} - 81 c^{4} h + 42 c^{4}\\
&{}+ 6 c^{3} h^{5} + 74 c^{3} h^{4} + 282 c^{3} h^{3} + 478 c^{3} h^{2}\\
&{}+ 464 c^{3} h + 280 c^{3} + 5 c^{2} h^{6} + 96 c^{2} h^{5}\\
&{}+ 688 c^{2} h^{4} + 2318 c^{2} h^{3} + 3939 c^{2} h^{2} + 3282 c^{2} h\\
&{}+ 1096 c^{2} + 4 c h^{7} + 92 c h^{6} + 844 c h^{5}\\
&{}+ 4000 c h^{4} + 10556 c h^{3} + 15468 c h^{2} + 11572 c h\\
&{}+ 3352 c + 2 h^{8} + 49 h^{7} + 504 h^{6}\\
&{}+ 2853 h^{5} + 9704 h^{4} + 20219 h^{3} + 25032 h^{2}\\
&{}+ 16655 h + 4470
\end{aligned}
\]
This polynomial has 38 monomials, total degree 8, and largest cleared coefficient 25032.

\[
\begin{aligned}
L_{U0}(h)={}&2 h^{8} + 49 h^{7} + 504 h^{6} + 2853 h^{5}\\
&{}+ 9703 h^{4} + 20218 h^{3} + 25031 h^{2} + 16654 h\\
&{}+ 4470
\end{aligned}
\]
This polynomial has 9 monomials, total degree 8, and largest cleared coefficient 25031.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{U0}(h)>4469>0.
\]

### Coefficient `U_1`

\[
\begin{aligned}
U_{1}(c,h)={}&4 c^{5} h + 8 c^{5} - 3 c^{4} h^{3} - 41 c^{4} h^{2}\\
&{}- 91 c^{4} h - 39 c^{4} + 4 c^{3} h^{4} + 56 c^{3} h^{3}\\
&{}+ 176 c^{3} h^{2} + 264 c^{3} h + 220 c^{3} + 11 c^{2} h^{5}\\
&{}+ 182 c^{2} h^{4} + 1068 c^{2} h^{3} + 2846 c^{2} h^{2} + 3641 c^{2} h\\
&{}+ 1900 c^{2} + 4 c h^{6} + 110 c h^{5} + 1060 c h^{4}\\
&{}+ 4744 c h^{3} + 10808 c h^{2} + 12266 c h + 5568 c\\
&{}+ 4 h^{7} + 93 h^{6} + 876 h^{5} + 4413 h^{4}\\
&{}+ 12884 h^{3} + 21815 h^{2} + 19868 h + 7535
\end{aligned}
\]
This polynomial has 32 monomials, total degree 7, and largest cleared coefficient 21815.

\[
\begin{aligned}
L_{U1}(h)={}&4 h^{7} + 93 h^{6} + 876 h^{5} + 4413 h^{4}\\
&{}+ 12883 h^{3} + 21814 h^{2} + 19867 h + 7534
\end{aligned}
\]
This polynomial has 8 monomials, total degree 7, and largest cleared coefficient 21814.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{U1}(h)>7533>0.
\]

### Coefficient `U_2`

\[
\begin{aligned}
U_{2}(c,h)={}&2 c^{5} - 9 c^{4} h - 8 c^{4} - 2 c^{3} h^{3}\\
&{}- 18 c^{3} h^{2} - 66 c^{3} h - 54 c^{3} + 6 c^{2} h^{4}\\
&{}+ 98 c^{2} h^{3} + 424 c^{2} h^{2} + 706 c^{2} h + 430 c^{2}\\
&{}+ 22 c h^{4} + 306 c h^{3} + 1294 c h^{2} + 2214 c h\\
&{}+ 1364 c + 2 h^{6} + 49 h^{5} + 432 h^{4}\\
&{}+ 1900 h^{3} + 4468 h^{2} + 5363 h + 2586
\end{aligned}
\]
This polynomial has 24 monomials, total degree 6, and largest cleared coefficient 5363.

\[
\begin{aligned}
L_{U2}(h)={}&2 h^{6} + 49 h^{5} + 432 h^{4} + 1899 h^{3}\\
&{}+ 4467 h^{2} + 5362 h + 2585
\end{aligned}
\]
This polynomial has 7 monomials, total degree 6, and largest cleared coefficient 5362.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{U2}(h)>2584>0.
\]

### Coefficient `U_3`

\[
\begin{aligned}
U_{3}(c,h)={}&c^{4} - 8 c^{3} h - 12 c^{3} + 14 c^{2} h^{2}\\
&{}+ 36 c^{2} h + 22 c^{2} + 28 c h^{2} + 96 c h\\
&{}+ 84 c + 5 h^{4} + 52 h^{3} + 210 h^{2}\\
&{}+ 372 h + 241
\end{aligned}
\]
This polynomial has 14 monomials, total degree 4, and largest cleared coefficient 372.

\[
\begin{aligned}
L_{U3}(h)={}&5 h^{4} + 52 h^{3} + 210 h^{2} + 371 h\\
&{}+ 240
\end{aligned}
\]
This polynomial has 5 monomials, total degree 4, and largest cleared coefficient 371.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{U3}(h)>239>0.
\]

### Coefficient `J_0`

\[
\begin{aligned}
J_{0}(c,h)={}&- c^{7} + 5 c^{6} h + 3 c^{6} + 3 c^{5} h^{3}\\
&{}- 32 c^{5} h^{2} - 93 c^{5} h - 58 c^{5} - 7 c^{4} h^{4}\\
&{}- 23 c^{4} h^{3} - 209 c^{4} h^{2} - 497 c^{4} h - 280 c^{4}\\
&{}- 3 c^{3} h^{5} - 21 c^{3} h^{4} - 24 c^{3} h^{3} - 312 c^{3} h^{2}\\
&{}- 861 c^{3} h - 491 c^{3} - 5 c^{2} h^{6} - 22 c^{2} h^{5}\\
&{}+ 171 c^{2} h^{4} + 1320 c^{2} h^{3} + 2901 c^{2} h^{2} + 2542 c^{2} h\\
&{}+ 869 c^{2} + 14 c h^{6} + 274 c h^{5} + 1970 c h^{4}\\
&{}+ 6820 c h^{3} + 12074 c h^{2} + 10506 c h + 3606 c\\
&{}+ 8 h^{7} + 138 h^{6} + 1030 h^{5} + 4252 h^{4}\\
&{}+ 10316 h^{3} + 14490 h^{2} + 10790 h + 3264
\end{aligned}
\]
This polynomial has 40 monomials, total degree 8, and largest cleared coefficient 14490.

\[
\begin{aligned}
L_{J0}(h)={}&8 h^{7} + 137 h^{6} + 1029 h^{5} + 4251 h^{4}\\
&{}+ 10315 h^{3} + 14488 h^{2} + 10786 h + 3261
\end{aligned}
\]
This polynomial has 8 monomials, total degree 7, and largest cleared coefficient 14488.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{J0}(h)>3260>0.
\]

### Coefficient `J_1`

\[
\begin{aligned}
J_{1}(c,h)={}&5 c^{6} - 78 c^{5} h - 126 c^{5} + c^{4} h^{3}\\
&{}- 26 c^{4} h^{2} - 471 c^{4} h - 756 c^{4} - 4 c^{3} h^{4}\\
&{}+ 68 c^{3} h^{3} + 292 c^{3} h^{2} - 412 c^{3} h - 1288 c^{3}\\
&{}- c^{2} h^{5} + 113 c^{2} h^{4} + 1288 c^{2} h^{3} + 4480 c^{2} h^{2}\\
&{}+ 5601 c^{2} h + 1815 c^{2} + 64 c h^{5} + 1018 c h^{4}\\
&{}+ 5952 c h^{3} + 15996 c h^{2} + 19776 c h + 8970 c\\
&{}+ 30 h^{6} + 472 h^{5} + 3144 h^{4} + 11192 h^{3}\\
&{}+ 22126 h^{2} + 22768 h + 9452
\end{aligned}
\]
This polynomial has 31 monomials, total degree 7, and largest cleared coefficient 22768.

\[
\begin{aligned}
L_{J1}(h)={}&30 h^{6} + 471 h^{5} + 3143 h^{4} + 11192 h^{3}\\
&{}+ 22125 h^{2} + 22766 h + 9446
\end{aligned}
\]
This polynomial has 7 monomials, total degree 6, and largest cleared coefficient 22766.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{J1}(h)>9445>0.
\]

### Coefficient `J_2`

\[
\begin{aligned}
J_{2}(c,h)={}&- 3 c^{5} - 75 c^{4} h - 165 c^{4} + 30 c^{3} h^{2}\\
&{}- 192 c^{3} h - 534 c^{3} + 102 c^{2} h^{3} + 690 c^{2} h^{2}\\
&{}+ 1050 c^{2} h + 126 c^{2} + 33 c h^{4} + 528 c h^{3}\\
&{}+ 2430 c h^{2} + 4104 c h + 2169 c + 33 h^{5}\\
&{}+ 423 h^{4} + 2214 h^{3} + 5778 h^{2} + 7353 h\\
&{}+ 3591
\end{aligned}
\]
This polynomial has 21 monomials, total degree 5, and largest cleared coefficient 7353.

\[
\begin{aligned}
L_{J2}(h)={}&33 h^{5} + 423 h^{4} + 2214 h^{3} + 5778 h^{2}\\
&{}+ 7352 h + 3588
\end{aligned}
\]
This polynomial has 6 monomials, total degree 5, and largest cleared coefficient 7352.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{J2}(h)>3587>0.
\]

### Coefficient `J_3`

\[
\begin{aligned}
J_{3}(c,h)={}&- c^{4} - 24 c^{3} h - 52 c^{3} + 34 c^{2} h^{2}\\
&{}+ 60 c^{2} h - 22 c^{2} + 68 c h^{2} + 192 c h\\
&{}+ 108 c + 11 h^{4} + 108 h^{3} + 414 h^{2}\\
&{}+ 684 h + 399
\end{aligned}
\]
This polynomial has 14 monomials, total degree 4, and largest cleared coefficient 684.

\[
\begin{aligned}
L_{J3}(h)={}&11 h^{4} + 108 h^{3} + 414 h^{2} + 683 h\\
&{}+ 398
\end{aligned}
\]
This polynomial has 5 monomials, total degree 4, and largest cleared coefficient 683.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{J3}(h)>397>0.
\]

### Coefficient `H_0`

\[
\begin{aligned}
H_{0}(c,h)={}&- 25 c^{7} + 129 c^{6} h + 83 c^{6} + 72 c^{5} h^{3}\\
&{}- 845 c^{5} h^{2} - 2436 c^{5} h - 1513 c^{5} - 168 c^{4} h^{4}\\
&{}- 495 c^{4} h^{3} - 5037 c^{4} h^{2} - 12311 c^{4} h - 6981 c^{4}\\
&{}- 72 c^{3} h^{5} - 423 c^{3} h^{4} + 248 c^{3} h^{3} - 5118 c^{3} h^{2}\\
&{}- 17800 c^{3} h - 10275 c^{3} - 120 c^{2} h^{6} - 417 c^{2} h^{5}\\
&{}+ 5573 c^{2} h^{4} + 39158 c^{2} h^{3} + 87634 c^{2} h^{2} + 82075 c^{2} h\\
&{}+ 30801 c^{2} + 381 c h^{6} + 7428 c h^{5} + 53587 c h^{4}\\
&{}+ 187312 c h^{3} + 337419 c h^{2} + 301740 c h + 107685 c\\
&{}+ 207 h^{7} + 3597 h^{6} + 27085 h^{5} + 113015 h^{4}\\
&{}+ 277929 h^{3} + 397499 h^{2} + 303579 h + 95265
\end{aligned}
\]
This polynomial has 40 monomials, total degree 8, and largest cleared coefficient 397499.

\[
\begin{aligned}
L_{H0}(h)={}&207 h^{7} + 3594 h^{6} + 27074 h^{5} + 113013 h^{4}\\
&{}+ 277928 h^{3} + 397475 h^{2} + 303501 h + 95220
\end{aligned}
\]
This polynomial has 8 monomials, total degree 7, and largest cleared coefficient 397475.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{H0}(h)>95219>0.
\]

### Coefficient `H_1`

\[
\begin{aligned}
H_{1}(c,h)={}&129 c^{6} - 1968 c^{5} h - 3162 c^{5} + 24 c^{4} h^{3}\\
&{}- 663 c^{4} h^{2} - 11886 c^{4} h - 19017 c^{4} - 96 c^{3} h^{4}\\
&{}+ 1792 c^{3} h^{3} + 7732 c^{3} h^{2} - 9656 c^{3} h - 31884 c^{3}\\
&{}- 24 c^{2} h^{5} + 2919 c^{2} h^{4} + 33180 c^{2} h^{3} + 115698 c^{2} h^{2}\\
&{}+ 145908 c^{2} h + 48783 c^{2} + 1632 c h^{5} + 25998 c h^{4}\\
&{}+ 152280 c h^{3} + 410220 c h^{2} + 508872 c h + 232038 c\\
&{}+ 767 h^{6} + 12082 h^{5} + 80579 h^{4} + 287252 h^{3}\\
&{}+ 568869 h^{2} + 586682 h + 244281
\end{aligned}
\]
This polynomial has 31 monomials, total degree 7, and largest cleared coefficient 586682.

\[
\begin{aligned}
L_{H1}(h)={}&767 h^{6} + 12081 h^{5} + 80578 h^{4} + 287252 h^{3}\\
&{}+ 568868 h^{2} + 586636 h + 244143
\end{aligned}
\]
This polynomial has 7 monomials, total degree 6, and largest cleared coefficient 586636.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{H1}(h)>244142>0.
\]

### Coefficient `H_2`

\[
\begin{aligned}
H_{2}(c,h)={}&- 72 c^{5} - 1896 c^{4} h - 4152 c^{4} + 768 c^{3} h^{2}\\
&{}- 4800 c^{3} h - 13392 c^{3} + 2592 c^{2} h^{3} + 17568 c^{2} h^{2}\\
&{}+ 26928 c^{2} h + 3600 c^{2} + 840 c h^{4} + 13440 c h^{3}\\
&{}+ 61920 c h^{2} + 104832 c h + 55704 c + 840 h^{5}\\
&{}+ 10776 h^{4} + 56448 h^{3} + 147456 h^{2} + 187896 h\\
&{}+ 91944
\end{aligned}
\]
This polynomial has 21 monomials, total degree 5, and largest cleared coefficient 187896.

\[
\begin{aligned}
L_{H2}(h)={}&840 h^{5} + 10776 h^{4} + 56448 h^{3} + 147456 h^{2}\\
&{}+ 187875 h + 91888
\end{aligned}
\]
This polynomial has 6 monomials, total degree 5, and largest cleared coefficient 187875.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{H2}(h)>91887>0.
\]

### Coefficient `H_3`

\[
\begin{aligned}
H_{3}(c,h)={}&- 24 c^{4} - 608 c^{3} h - 1312 c^{3} + 864 c^{2} h^{2}\\
&{}+ 1536 c^{2} h - 528 c^{2} + 1728 c h^{2} + 4896 c h\\
&{}+ 2784 c + 280 h^{4} + 2752 h^{3} + 10560 h^{2}\\
&{}+ 17472 h + 10216
\end{aligned}
\]
This polynomial has 14 monomials, total degree 4, and largest cleared coefficient 17472.

\[
\begin{aligned}
L_{H3}(h)={}&280 h^{4} + 2752 h^{3} + 10560 h^{2} + 17469 h\\
&{}+ 10197
\end{aligned}
\]
This polynomial has 5 monomials, total degree 4, and largest cleared coefficient 17469.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{H3}(h)>10196>0.
\]

## 5. The remaining two-variable shape sign

On the lower beta and norm faces,
\[
28a^2(a+x)^2K^2\Psi_a(x,a,x,3/4)=P_*(c,h).                    \tag{14}
\]

\[
\begin{aligned}
P_*(c,h)={}&- c^{6} h - 2 c^{6} + 2 c^{5} h^{2} + 2 c^{5} h\\
&{}- 4 c^{5} + 3 c^{4} h^{4} + 12 c^{4} h^{3} + 51 c^{4} h^{2}\\
&{}+ 138 c^{4} h + 120 c^{4} - 6 c^{3} h^{5} - 22 c^{3} h^{4}\\
&{}+ 26 c^{3} h^{3} + 366 c^{3} h^{2} + 900 c^{3} h + 704 c^{3}\\
&{}- 5 c^{2} h^{6} - 71 c^{2} h^{5} - 374 c^{2} h^{4} - 1024 c^{2} h^{3}\\
&{}- 1447 c^{2} h^{2} - 769 c^{2} h + 90 c^{2} - 4 c h^{7}\\
&{}- 62 c h^{6} - 398 c h^{5} - 1424 c h^{4} - 3216 c h^{3}\\
&{}- 4654 c h^{2} - 3870 c h - 1348 c - 2 h^{8}\\
&{}- 32 h^{7} - 210 h^{6} - 712 h^{5} - 1278 h^{4}\\
&{}- 1024 h^{3} + 74 h^{2} + 616 h + 264
\end{aligned}
\]
This polynomial has 40 monomials, total degree 8, and largest cleared coefficient 4654.

\[
\begin{aligned}
L_{*}(h)={}&- 2 h^{8} - 33 h^{7} - 220 h^{6} - 777 h^{5}\\
&{}- 1513 h^{4} - 1558 h^{3} - 697 h^{2} - 15 h\\
&{}+ 51
\end{aligned}
\]
This polynomial has 9 monomials, total degree 8, and largest cleared coefficient 1558.

The preceding polynomial is at least the displayed lower polynomial. Discarding its nonconstant positive terms and using `h<=1/6` in its negative terms gives
\[
 L_{*}(h)>19>0.
\]

Equations (13)--(14) prove `Psi_a>0` on (2). Along the actual
shape, `a_e=d` and beta and norm are independent of `e`, so
`Psi_e/(xd)=Psi_a/x>0` for positive `d`, with the stated continuous
extension at zero. This proves the second assertion of (1).

## 6. Scope and verification

Only the two stated S4 signs are proved here. They remove the original
large three-variable signs for displacement monotonicity of `Phi` and
shape monotonicity of `Psi`. The `x` comparisons and two remaining
terminal derivatives are not inferred from them.

Every displayed sign polynomial and each coefficient identity has at
most two variables and total degree at most eight. The shape-source
connection uses its second derivative and two boundary jets before any
collection; the beta-source connections use four small coefficient
identities with the other variables fixed. For the shape boundary jets,
combine the logarithm derivative before clearing denominators:
\[
(\log y)_a=\frac{X(2a+b)-a^2b}{aBK}.
\]
This follows from the degree-three identity
`(2a+b)(X+a^2)-2a^2(a+b)=X(2a+b)-a^2b`, with `X=x(x+2)`.
It avoids expanding degree-nine terms which cancel in those one-variable
jets. Split the remaining source only into `2M/K^2`, `2uD^2/K^2`,
`-2DE/K^2`, `(u-1)B/a`, `a/B`, `-a^2/K`, `-2uD/K`, and `E/K`.
After differentiation and the indicated boundary substitutions, these
eight pieces and the combined logarithm piece all have degree at most
eight. Their largest coefficient is 35,762,100,480 and their largest
support has 41 monomials. Exact symbolic arithmetic
checks source transcription and rational bounds, rather than supplying
a computational sign certificate. No Lean, Lake, typechecking or CI is
used or claimed.
