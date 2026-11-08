# The outer-ratio lower-shape terminal curve

This proves both original tests H_0,H_1 strictly negative on the exact
one-variable terminal curve from Section 5 of
[the outer-ratio hand sign](../../archive/notes/MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_SIGN.md):
\[
13/6\le x\le12/5,\quad a=a_f=(36x+25)/84,
\quad c=c_+=(24x+51)/128,\quad b=x+c(a-1),
\]
\[
u=u_s=\frac34+
\frac{17(x-1)^3/[240(x+1)^2]+(b-x)/1200}{b-1}.
\tag{1}
\]
The exact transport and tests are those of equations (3),(6) of that
source. No norm replacement is made in the curve comparison below.
Every auxiliary polynomial is printed in
[the algebra companion](SHORT_RATIO_OUTER_TERMINAL_ALGEBRA.md).

## 1. A constant duration multiplier on each of two intervals

Write `Z=(a+b)/a`, and let `w` be the transport norm at (1).
The [lower-face beta lemma](SHORT_RATIO_OUTER_BETA.md), equations (3),(9),
proves `w<3/4` on the full a_f face, including (1).
Here
\[
Z=\frac{864x^2+15780x+191}{128(36x+25)}
\]
increases with x: its derivative has numerator
`3888x^2+5400x+48453` and denominator `16(36x+25)^2`.
In particular
\[
Z(9/4)=20035/6784<74/25,
\qquad Z(12/5)<31/10<7/2.
\tag{2}
\]
The multiplier in H_0 is `m_0=4-Z/2`. Therefore
\[
m_0\ge n_+:=63/25\quad(x\le9/4),\qquad
m_0\ge n_-:=49/20\quad(x\ge9/4).
\tag{3}
\]
For a constant n define the exact-log function
\[
R_n=6/7+(u_s-1)Z+1/Z-E_L+n(w-3/4)+\log(2Z/7).
\tag{4}
\]
Since `w<3/4`, (3) gives `H_0<=R_{n_+}` or `H_0<=R_{n_-}`
on the respective interval. Also
\[
H_1-H_0=
\frac{(2Z-7)(Z-4)}{4Z}(w-3/4)<0.
\tag{5}
\]
Thus it suffices to prove the two signs for (4).

## 2. Reparameterize the curve before expanding

Put `r=1/a_f` and `t=1-r`. Then
\[
420/557\le r\le84/103,
\qquad 3/4\le r\le49/60,\qquad11/60\le t\le1/4.
\tag{6}
\]
The second interval is used only for the following explicit scalar
bounds. In this coordinate the curve has the simple source formulas
\[
x=\frac7{3r}-\frac{25}{36},\quad a=1/r,
\quad b=\frac7{16r^2}+\frac{277}{128r}-\frac{1109}{1152},
\]
\[
S=\frac{84+11r}{36r},\quad
Z=\frac{504+3645r-1109r^2}{1152r},
\quad\rho=\frac{r^2}{7},\quad\lambda=\frac{6+r^2}{7},
\]
\[
\delta=-\frac{35789r^3-212325r^2+86328r+24192}{145152r},
\quad A_* =\lambda^2-\lambda S\rho+S^2\rho^2.
\tag{7}
\]
Here `delta=D/(7a^2)` is the normalized transport parameter.
For a free incoming norm u the source identities are
\[
N_* =\lambda[S(u-1)+1/S]+(2S-1)\rho,
\quad E_L=2u\delta-N_*,\quad w=A_*+u\delta^2-\delta N_*.
\tag{8}
\]
Let `V=u_s-3/4`. Separating the constant norm and the single S pole gives
\[
R_n=L_n+VA_n+Q_n+1/Z+\log(2Z/7),
\tag{9}
\]
where
\[
A_n=Z-2\delta+(1-n\delta)\lambda S+n\delta^2,
\]
\[
L_n=6/7-Z/4-3\delta/2
 +(1-n\delta)[-\lambda S/4+(2S-1)\rho]
 +n[A_*-3/4+3\delta^2/4],
\]
\[
Q_n=(1-n\delta)\lambda/S.
\tag{10}
\]
The numerator polynomials for L_n,A_n have degree six after clearing
`r^2`; Q_n has a degree-five numerator and one linear denominator.
The algebra companion prints these six source numerators at n_-,n_+.
Neither the product VA_n nor the complete derivative of R_n is expanded.

## 3. The incoming ceiling has simple derivative bounds

Define
\[
K=504+2493r-2261r^2>0,
\quad F=\frac{r(84-61r)}K,
\quad q=\frac{84-61r}{84+11r}.
\]
Exact substitution of (1) gives the small product identity
\[
V=1/1200+(2/75)F(85q^2-1).
\tag{11}
\]
On the larger interval (6), elementary linear comparisons give
\[
11/30<q<5/12,\quad q'=-6048/(84+11r)^2,
\quad |q'|<5/7,\quad 0<q''=133056/(84+11r)^3<1/5.
\tag{12}
\]
The four small polynomials K_0,...,K_3 in the companion prove
\[
0<F<11/400,\qquad7/500<F'<1/50,\qquad F''<1/12.
\tag{13}
\]
All primes in the rest of this note are derivatives in r.
In particular `1877/180<85q^2-1<1981/144`. From (11)--(13),
\[
0<V<\frac1{1200}+\frac2{75}\frac{11}{400}\frac{1981}{144}
=\frac{23591}{2160000}<11/1000,
\]
\[
V'>\frac2{75}\left[
\frac7{500}\frac{1877}{180}
-170\frac{11}{400}\frac5{12}\frac57\right]
=-\frac{1569179}{47250000}>-1/30,
\]
\[
V'<\frac2{75}\frac1{50}\frac{1981}{144}<1/30.
\tag{14}
\]
For the second derivative, the cross term `340F'qq'` is negative.
Consequently
\[
V''<\frac2{75}\left[
\frac1{12}\frac{1981}{144}
+170\frac{11}{400}\left(\frac{25}{49}+\frac1{12}\right)\right]
=\frac{1660079}{15876000}<11/100.
\tag{15}
\]
This avoids clearing the high-degree product derivative of the
original incoming ceiling.

## 4. Concavity of the complete terminal function

The remaining component signs in the companion give, for both n_-,n_+,
\[
0<A_n<5,\qquad-17<A_n'<0,\qquad A_n''<53,
\]
\[
L_n''<-1,\qquad Q_n''<-17/10,
\qquad [1/Z+\log(2Z/7)]''<7/20.
\tag{16}
\]
The A bounds are obtained at the appropriate multiplier endpoints.
The displayed polynomials J_0,J_1,J_2 prove respectively
`partial_n A_n<0`, `partial_n A_n'<0` and `partial_n A_n''>0`,
so they also hold for every intervening n.
The product rule now gives
\[
\begin{aligned}
R_n''&=L_n''+Q_n''+VA_n''+2V'A_n'+V''A_n
 +[1/Z+\log(2Z/7)]''\\
&<-1-17/10+(11/1000)53+2(1/30)17+(11/100)5+7/20\\
&=-251/3000<0.
\end{aligned}
\tag{17}
\]
At the largest actual r, namely r_0=84/103, substitution in the printed
small source polynomials gives the following elementary rational bounds
for both multipliers:
\[
0<A_n(r_0)<4,\quad A_n'(r_0)>-14,
\quad L_n'(r_0)>36/25,\quad Q_n'(r_0)>-83/100,
\]
\[
V(r_0)<17/2000,\quad V'(r_0)>-11/400,
\quad [1/Z+\log(2Z/7)]'(r_0)>-37/100.
\tag{18}
\]
In particular
\[
R_n'(r_0)>36/25-83/100-(17/2000)14-(11/400)4-37/100
=11/1000>0.
\tag{19}
\]
By (17), R_n' decreases in r. Thus it is positive throughout the actual
interval in (6). Since `dr/dx=-3r^2/7<0`, each R_n strictly decreases
with x along the exact curve (1).

## 5. Two scalar terminal values close both duration tests

For `0<y<=1`, the elementary bound
\[
\log y\le\ell_3(y)=(y-1)-(y-1)^2/2+(y-1)^3/3
\tag{20}
\]
follows by integrating the first three nonnegative terms of
`(1-z)^{-1}`. Here y=2Z/7<1 by (2).
Only these two scalar evaluations use (20).

The companion gives separate rational upper bounds for the five terms
`L_n`, `VA_n`, `Q_n`, `1/Z`, `ell_3(2Z/7)` at the two initial points.
Their sums yield
\[
R_{63/25}(13/6)<-240/1000000<-1/5000,
\]
\[
R_{49/20}(9/4)<-1074/1000000<-1/1000.
\tag{21}
\]
The strict inequalities follow even with the upper-rounded scalar terms.
Together with x monotonicity, (3) and (5), this proves
\[
\boxed{
H_1<H_0<-1/5000\quad(13/6\le x\le9/4),
}
\]
\[
\boxed{
H_1<H_0<-1/1000\quad(9/4\le x\le12/5).
}
\tag{22}
\]
The original lower-shape terminal caller therefore closes on its entire
stated x interval, with its unchanged c_+, u_s and a_f.

## 6. Algebra boundary

There is one rational split, at x=9/4. Each displayed sign polynomial
has one variable, at most nine monomials and degree at most eight.
The largest printed cleared coefficient is 869107196544. The source
identities are checked component by component after reparameterizing
and separating the incoming norm and the linear pole. No large combined
numerator is needed. All source contributions and rational bounds have
been checked by exact symbolic arithmetic used only for transcription
and verification. No Lean, Lake, typechecking, compilation or CI was run.
