# Outer displacement: the three terminal shape faces

Use the exact functions R_n,P_n,A_n,U,Z,K from
[reciprocal convexity](SHORT_DISPLACEMENT_OUTER_RECIPROCAL.md).
The domain is `2<=x<=13/6`,
`8x/(9x+8)<=C<=19x/50`. Write `h=x-2` and
\[
a_*=5(x+1)/13,\qquad r_*=13/[5(x+1)].
\]
The algebra used below is fully printed in
[the terminal algebra companion](SHORT_DISPLACEMENT_OUTER_TERMINAL_ALGEBRA.md).

## 1. The lower shape increases with beta slope

At `r=r_*`, the companion proves, for every `5/2<=n<=7/2`,
\[
(P_n)_C>-53/2000,\quad (A_n)_C>0,\quad A_n<4,
\quad U_C>-3/4000.
\tag{1}
\]
It is enough to check the two endpoints of n. The norm is independent
of n, and all other quantities are affine in n. The partial derivatives
in (1) keep r fixed before substituting r=r_*.

As in the reciprocal proof, let
\[
f(z)=-1/z^2+280/(5z+14)^2.
\]
It is positive and decreasing for `23/10<=z<=3`, so
`f(Z)>=f(3)=1679/7569`. Also `1-r_*>=2/15`.
Using `1<A_n`, `U_C<0`, `U>3/4` and (1) in the source derivative gives
\[
\begin{aligned}
(R_n)_C&=(P_n)_C+(U-3/4)(A_n)_C+U_CA_n+(1-r_*)f(Z)\\
&>-\frac{53}{2000}-\frac{3}{4000}\,4+
\frac2{15}\frac{1679}{7569}
=\frac{3487}{45414000}>0.
\end{aligned}
\tag{2}
\]
Thus both lower-shape tests are bounded above by the single slope
`C=19x/50`.

## 2. The two lower-shape curves decrease in x

For `n_0=25/8`, `n_1=7/2`, put
\[
p_j(x)=P_{n_j}(r_*),\quad d_j(x)=A_{n_j}(r_*),
\quad V(x)=U(r_*)-3/4,
\]
with `C=19x/50` in every expression. In this section primes are total
x derivatives along that curve. The exact remaining scalar functions are
\[
V=\frac{(x-1)^2(95x^2+1148x-1300)}
{(x+1)(35x+13)(95x^2+498x-650)},
\]
\[
z=Z(r_*)=\frac{95x^2+748x+250}{250(x+1)},\quad
R_{n_j}=p_j+Vd_j+1/z-56/(5z+14).
\tag{3}
\]
The positive denominator factor `95x^2+498x-650` has value 726 at x=2
and increases. The univariate polynomials in the companion prove
\[
0<V<1/110,\qquad V'<7/800,\qquad0<d_j<18/5,
\]
\[
p_0'<-41/200,\quad d_0'<19/4,
\qquad p_1'<-23/100,\quad d_1'<26/5.
\tag{4}
\]
Each derivative is taken before clearing denominators and expansion.
In particular the constant logarithm coefficient disappears from p_j'.

Now `17/6<z<3`, and
\[
0<z'=19/50+403/[250(x+1)^2]<14/25.
\]
Since f decreases and `f(17/6)<8/35`,
\[
[1/z-56/(5z+14)]'=z'f(z)<(14/25)(8/35)=16/125.
\tag{5}
\]
The product rule, positivity of V,d_j, and (4)--(5) give
\[
R_{25/8}'<-41/200+16/125+(7/800)(18/5)+(1/110)(19/4)
=-51/22000<0,
\]
\[
R_{7/2}'<-23/100+16/125+(7/800)(18/5)+(1/110)(26/5)
=-511/22000<0.
\tag{6}
\]
Their initial values can be checked as the following short rational sums;
no large common-denominator numerator is needed:
\[
\begin{aligned}
R_{25/8}(2)&=\frac{4804549207}{2976750000}
+\frac{688}{90387}\frac{680445623}{248062500}
+\frac{375}{1063}-\frac{4200}{2113}<-1/100000,\\
R_{7/2}(2)&=\frac{34309031231}{21262500000}
+\frac{688}{90387}\frac{543885023}{221484375}
+\frac{375}{1063}-\frac{4200}{2113}<-1/400.
\end{aligned}
\tag{7}
\]
This proves the two claimed lower-face signs for every original slope.

## 3. The middle face a=5/4

On the comparison rectangle `1<A_n`, so increasing the norm is a valid
scalar comparison. The reciprocal proof gives `U<19/25`.
Also `319847/180000<16/9`. Use these two upper values at a=5/4,
n=5/2 and denote the resulting rational upper bound by M(x,C).

The companion prints the complete identity
\[
153125S(C+4x+5)^2(C+4x+19)^2 M_C=Q(h,C),
\tag{8}
\]
where every coefficient of Q in h,C is positive. Hence M increases
in C, and `C<=5/6` reduces this face to C=5/6.
There
\[
M(x,5/6)=\frac{N(h)}{11025000S(24x+35)(24x+119)}.
\tag{9}
\]
The printed degree-seven N has a negative constant and all other
coefficients positive. It increases with h, and `N(1/6)<-1000000000`.
Therefore `R_{5/2}(x,5/4,C)<0`.

## 4. The upper face a=x

Here keep the actual lower slope before choosing the norm ceiling.
The strong beta bound gives
\[
b-1\ge\frac{(x-1)(17x+8)}{9x+8},\qquad
\frac{x-1}{b-1}\le\frac{9x+8}{17x+8}\le13/21.
\]
Together with `c<=49/10127`, this proves
\[
U-3/4\le\frac{49}{10127}\frac{34}{21}
=\frac{238}{30381}<1/125.
\tag{10}
\]
Increase the norm to `u_h=379/500=3/4+1/125` and the logarithm constant
to 16/9, obtaining a rational upper bound H_n(x,C). The first comparison
uses the already proved `A_n>1`.

At a=x the transport w,E_L is independent of b when u is fixed.
Therefore
\[
(H_n)_C=(1-1/x)[-121/500+f(Z)]<0,
\tag{11}
\]
since `Z>=23/10`, f decreases, and
\[
121/500-f(23/10)=297409/687964500>0.
\]
Thus use the lower slope `C=8x/(9x+8)`.
Furthermore
\[
\partial_u w\bigm|_{a=x}=-S^3(6x-1)/(49x^3)<0,
\]
\[
w\bigm|_{a=x,u=19/25}-3/4
=\frac{144h^4+1585h^3+5414h^2+7516h+3728}{4900x^3}>0.
\tag{12}
\]
Since `u_h<19/25`, (12) implies H_n increases with n. It remains only
to check n=7/2. The complete numerator identity is
\[
H_{7/2}\left(x,\frac{8x}{9x+8}\right)
=\frac{W(h)}{63000x^3S(9x+8)(13x+4)(32x+19)},
\tag{13}
\]
where the companion prints the degree-eight W with every coefficient
negative. This proves `R_n(x,x,C)<0` for the whole multiplier interval.

These are scalar norm and beta comparisons after the actual norm and
logarithm substitutions. Equation (12) is proved for this face; it is
not an outgoing-floor hypothesis transported from the original root.
