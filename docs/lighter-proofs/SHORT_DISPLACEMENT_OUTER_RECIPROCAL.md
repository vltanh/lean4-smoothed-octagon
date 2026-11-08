# Outer displacement: convexity in reciprocal shape

This supplies the shape comparison in the [complete outer displacement
replacement](SHORT_DISPLACEMENT_OUTER_COMPLETE.md). The incoming ceiling
moves with shape throughout this proof.

## 1. Exact source, with slope fixed

Fix
\[
2\le x\le13/6,\qquad3/5\le C\le5/6,\qquad
1/x\le r\le7/8,\qquad5/2\le n\le7/2.
\]
Here `r=1/a`, `b=x+C(a-1)`. Put
\[
S=x+1,\quad M=35x+13,\quad e=x-C,\quad d=e-1,
\quad H=C+dr,\quad Z=1+C+er,\quad K=5Z+14,
\]
\[
c=\frac{(x-1)^2}{SM},\qquad
U=\frac34+c+\frac{c(x-1)r}{H}.
\tag{1}
\]
This is exactly the incoming ceiling in the archived outer-face note:
`b-1=H/r` and `(x+b-2)/(b-1)=1+(x-1)r/H`.
Every denominator is positive. In particular `e>1`, `d>0`,
\[
H\ge(1+C)(x-1)/x\ge4/5,
\qquad23/10\le Z\le3.
\tag{2}
\]
The upper bound for Z follows from `r<=7/8`, `x<=13/6`, `C<=5/6`.

The residual with a constant duration multiplier is
\[
R_n=J+n(w-3/4),\qquad
J=(U-1)(a+b)/a+a/(a+b)+6/7-E_L+
319847/180000-56a/(19a+5b).
\tag{3}
\]
For a coefficient-preserving source description put
\[
d_0=1+2C,\quad d_1=2[x-C(x+1)],
\quad d_2=1+2x-2x^2+2Cx,
\]
\[
E_0=S(u-1)+1/S,\quad A_0=(x^2+x+1)/S,\quad J_2=Su+A_0.
\]
The normalized transport is the quartic `49w=sum W_i r^i`, with
\[
\begin{aligned}
W_0&=36+u d_0^2-6d_0E_0,\\
W_1&=d_1(2u d_0-6E_0),\\
W_2&=12-6S+u(d_1^2+2d_0d_2)-6d_2E_0-d_0J_2,\\
W_3&=d_1(2u d_2-J_2),\\
W_4&=(S-d_2)(A_0-u d_2),
\end{aligned}
\]
\[
E_L=\frac{2ud_0-6E_0+2ud_1r+(2ud_2-J_2)r^2}{7}.
\tag{4}
\]
These are identities of degree four in the single variable r, with their
coefficients kept separate. All their expanded coefficient comparisons in
x,C are printed in [the algebra companion](SHORT_DISPLACEMENT_OUTER_CURVATURE_ALGEBRA.md).
The affine norm dependence gives quartics A and P such that
\[
\boxed{R_n=P_n(r)+(U-3/4)A_n(r)+1/Z-56/K.}
\tag{5}
\]
Here `A_n=sum A_i r^i` is the coefficient of u and
`P_n=sum (3A_i/4+B_i)r^i` is the polynomial part at `u=3/4`.
The companion prints every A_i and B_i through scalar-affine coefficient
identities. No expansion in all of r,x,C is used.

## 2. The quartic part has curvature greater than 2/5

The leading coefficient of P is
\[
[P_n]_{r^4}=\frac{nx(2e-1)}{49}
\left\{\frac34[2x(e-1)-1]+\frac{x^2+x+1}{S}\right\}>0.
\tag{6}
\]
Indeed the bracket is greater than `-3/4+7/3=19/12`.
The complete small boundary identities in the companion prove
\[
P_n^{(3)}(1/x)>0,\qquad P_n''(1/x)>2/5.
\tag{7}
\]
The first is linear in positive n; the second follows at `n=5/2,7/2`
and hence by affinity for the full interval. Since P is quartic, (6)
makes the third derivative increase. Thus P'' increases on `r>=1/x`, proving
\[
P_n''(r)>2/5.
\tag{8}
\]

## 3. Bounds for the incoming coefficient

Write `A_n=sum A_i r^i`. Its quadratic second derivative is
\[
A_n''(r)=2A_2+6A_3r+12A_4r^2.
\]
The companion proves the following bounds, first at the two endpoints
of n and then throughout by affinity:
\[
A_n''(1/x)>-1,\quad A_n''(7/8)>-1,
\quad A_3+4A_4/x>0,
\]
\[
A_n'(1/x)>1,\qquad A_n(7/8)<5.
\tag{9}
\]
If `A_4<0`, the quadratic A'' is concave, so its minimum is at a boundary.
If `A_4>=0`, its derivative is positive for `r>=1/x` by (9).
Both cases give `A''>-1`. Therefore
\[
A_n'(r)>1-(r-1/x)>1/8>0.
\tag{10}
\]
For the remaining lower bound, direct substitution gives
\[
\partial_n A_n(1/x)=-\frac{S^3(6x-1)}{49x^3}<0,
\]
\[
14x^3[A_{7/2}(1/x)-1]=14Cx^2(x-1)
+6h^4+53h^3+153h^2+163h+43>0,\qquad h=x-2.
\tag{11}
\]
Combining (9)--(11) yields
\[
\boxed{1<A_n<5,\qquad A_n'>0,\qquad A_n''>-1.}
\tag{12}
\]

## 4. The two remaining curvature contributions

The elementary function c increases, since
\[
c'=\frac{2(x-1)(59x+37)}{S^2M^2}>0.
\]
Thus `c<=49/10127<1/200`. Because `a>1` and `b>=x`,
\[
0<U-3/4\le2c\le98/10127<1/100.
\tag{13}
\]
Differentiating (1),
\[
U'=\frac{c(x-1)C}{H^2}>0,\qquad
U''=-\frac{2c(x-1)Cd}{H^3}.
\]
As `Cd<= (x-1)^2/4<=49/144`, (2) gives
\[
|U''|<2\frac1{200}\frac76\frac{49}{144}
\left(\frac54\right)^3<1/125.
\tag{14}
\]
All primes in (13)--(14), except the displayed c', are r derivatives.
The product rule and (12)--(14) now give
\[
[(U-3/4)A_n]''>-1/100-5/125=-1/20.
\tag{15}
\]

Put `f(z)=-1/z^2+280/(5z+14)^2`. On `23/10<=z<=3`,
\[
f'(z)=2/z^3-2800/(5z+14)^3<0,\qquad
f''(z)=-6/z^4+42000/(5z+14)^4<0.
\]
For the first sign use `(255/23)^3<1400`; for the second use
`(29/3)^4>7000`. Consequently, with `e<=47/30`,
\[
[1/Z-56/K]''=e^2f'(Z)
\ge-\left(\frac{47}{30}\right)^2\frac{26822}{658503}>-1/10.
\tag{16}
\]
Combining (8), (15) and (16) proves the required uniform convexity:
\[
\boxed{\partial_r^2R_n>2/5-1/20-1/10=1/4.}
\tag{17}
\]
This comparison follows the beta-dependent norm U. It requires no sign
of `w-3/4` and no transported outgoing norm floor.
