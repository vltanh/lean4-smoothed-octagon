# Six explicit derivative signs for the extended Casimir floor

Date: 2026-11-08 UTC. Hand proof accepted in the
[independent extended-shape review](MIXED_SMALLER_SHORT_EXTENDED_SHAPE_AUDIT.md),
including its final independent reading in Section 6.
This note supplies all six signs used by the
[extended Casimir floor](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md).
Its arithmetic consists of explicit polynomial products and their
coefficientwise bounds. The older extracted coefficient-group bounds
and the seventeen positive-basis coefficients are not premises.

## 1. The scalar functions and the six assertions

Throughout this note,
\[
2\le x\le13/6,\qquad 0\le d\le1/19,\qquad 13/5\le\eta\le3,
\quad \alpha=1+\eta d,\quad\beta=x(1+d).
\tag{1}
\]
Put
\[
S=1+x,\quad X=x(x+2),\quad \Sigma=X+\alpha^2,\quad
A=\alpha+\beta,\quad B=\beta-1,\quad Z=35x+13,
\]
\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,\qquad
u=\frac34+\frac{2(x-1)^3}{SZB}
                    +\frac{(\beta-x)^3}{48x^2B}.
\tag{2}
\]
The letter \(u\) in this note denotes the specified rational upper
value of the incoming norm. Its substitution for the original norm
is justified before this note is applied.

Define
\[
U_1=1-S^{-1}+S^{-2},\qquad
E=S(u-1)+3S^{-1}-S^{-2},
\]
\[
w=\frac{S^4U_1+D^2u-DS^2E}{\Sigma^2},
\quad E_L=\frac{2Du-S^2E}{\Sigma},
\quad G=\frac{S^4(4uU_1-E^2)}{16X^2},
\]
\[
r_A=\frac{\alpha}{A},\quad q=\frac{\alpha^2}{\Sigma},
\quad T=\frac{\Sigma}{\alpha A},\quad y=\frac2T.
\]
The two scalar lower bounds are
\[
\begin{aligned}
R&=2w-\frac12+\frac{u-1}{r_A}+r_A-q-E_L+\log y,\\
\Phi&=G-\frac R7,\qquad
\Psi=\Phi-\frac{(T-2)(w-3/4)}7.
\end{aligned}
\tag{3}
\]
We prove, on the entire closed rectangle (1),
\[
W_1:=-\Phi_d>0,\qquad
W_2:=\frac{\Psi_\eta}{xd}>0,\qquad
W_3:=-\Psi_x>0,
\tag{4}
\]
\[
W_4:=-\Phi_x\big|_{d=1/19}>0,\quad
W_5:=-\Phi_\eta\big|_{x=13/6,d=1/19}>0,\quad
W_6:=-\Psi_{dd}\big|_{x=13/6,\eta=13/5}>0.
\tag{5}
\]
The quotient defining \(W_2\) has its polynomial extension at \(d=0\).
In particular, the assertion there gives \(\Psi_\eta=0\), not a
strictly positive derivative at a shape independent of \(\eta\).

## 2. Explicit polynomial definitions

Here are product formulas from which every polynomial in the proof
can be formed without logarithms. Set
\[
V=S^2-S+1,\qquad J=48x^2SZB,
\]
\[
N=36x^2SZB+96x^2(x-1)^3+SZ(\beta-x)^3,
\]
\[
N_E=S^3(N-J)+(3S-1)J,
\quad N_w=S^2VJ+D^2N-DN_E,
\]
\[
N_L=2DN-N_E,\qquad N_G=4S^2VNJ-N_E^2.
\tag{6}
\]
Thus
\[
u=N/J,\quad E=N_E/(S^2J),\quad w=N_w/(J\Sigma^2),
\quad E_L=N_L/(J\Sigma),\quad G=N_G/(16X^2J^2).
\]
The rational parts of the residuals in (3) have the following
polynomial numerators:
\[
\begin{aligned}
M_\Phi={}&4\alpha A N_w-\alpha A\Sigma^2J
 +2(N-J)A^2\Sigma^2+2\alpha^2\Sigma^2J\\
&-2\alpha^3A\Sigma J-2\alpha A\Sigma N_L,\\
M_\Psi={}&4N_w+4\alpha A\Sigma J+4(N-J)A^2\Sigma
 +4\alpha^2\Sigma J\\
&-4\alpha^3AJ-4\alpha A N_L-3\Sigma^2J.
\end{aligned}
\tag{7}
\]
Indeed the second residual equals
\[
Tw+1+(u-1)/r_A+r_A-q-E_L-3T/4+\log y.
\]
Consequently
\[
\Phi=N_\Phi/L_\Phi-\log y/7,\qquad
\Psi=N_\Psi/L_\Psi-\log y/7,
\tag{8}
\]
where
\[
\begin{aligned}
L_\Phi&=112X^2J^2\alpha A\Sigma^2,&
N_\Phi&=7\alpha A\Sigma^2N_G-8X^2JM_\Phi,\\
L_\Psi&=112X^2J^2\alpha A\Sigma,&
N_\Psi&=7\alpha A\Sigma N_G-4X^2JM_\Psi.
\end{aligned}
\tag{9}
\]
All the displayed denominators are positive.

For a variable \(v\in\{x,d,\eta\}\), define the polynomial operation
\[
\mathscr D_v(N_*,L_*)
=7\alpha A\Sigma\{(N_*)_vL_*-N_*(L_*)_v\}
 -L_*^2\{(\alpha A)_v\Sigma-\alpha A\Sigma_v\}.
\tag{10}
\]
For \(F=N_*/L_*-\log y/7\), this gives
\[
F_v=\frac{\mathscr D_v(N_*,L_*)}
                 {7L_*^2\alpha A\Sigma}.
\]
For the last sign one differentiates this quotient once more.
Thus (6)--(10), ordinary differentiation and exact polynomial
division specify the six derivative polynomials completely.

Multiply \(W_i\) by the following positive factors:
\[
\begin{array}{c|l}
i&Q_i\\ \hline
1&xS(x+2)^2Z^2\alpha^2B^3A^2\Sigma^3\\
2&SZ\alpha^2BA^2\Sigma^2\\
3&x^3S^2(x+2)^3Z^3\alpha B^3A^2\Sigma^2\\
4&x^3S^2(x+2)^3Z^3\alpha B^3A^2\Sigma^3\\
5&\alpha^2A^2\Sigma^3\\
6&\alpha^3B^4A^3\Sigma^3.
\end{array}
\tag{11}
\]
The specializations in (5) are made in \(Q_4,Q_5,Q_6\) as well.
In row two, the factor \(xd\) is cancelled before this multiplication.
Each \(P_i=Q_iW_i\) is a polynomial.

Use \(h=x-2\). In rows one and four put \(\eta=13/5+z\);
in rows two, three and five put \(\eta=3-z\). In row six use \(d\)
alone. Divide each shifted polynomial by its value at the origin,
and denote the result by \(\widehat P_i\). Hence
\[
0\le h\le1/6,\quad0\le d\le1/19,\quad0\le z\le2/5.
\tag{12}
\]
Variables absent from a specialized polynomial may be ignored.
The respective values of \(W_i\) at these normalization origins are
\[
\begin{array}{c|l}
1&35322804569/269987074560\\
2&4229/423549\\
3&171516573839/31870474223616\\
4&13795954844326628649722636697841/
   2813435823143289494140377799458816\\
5&3000038035142073660693109787/
   40256125884623918254324579111872\\
6&77655213507192032489/173694363867167364000.
\end{array}
\tag{13}
\]
These are positive, so the normalization preserves all six signs.
The degrees of \(\widehat P_i\), in \(h,d,z\), are respectively
\[
(19,16,10),\ (10,10,6),\ (21,14,7),\
(23,0,9),\ (0,0,8),\ (0,18,0).
\tag{14}
\]

## 3. Complete polynomial bounds

Write \(F\preceq H\) when every ordinary monomial coefficient of
\(H-F\) is nonnegative. This implies \(F\le H\) when the variables
are nonnegative. The following bounds give the complete adverse
parts of the six normalized polynomials by a small number of
explicit products.

For row one set
\[
\begin{aligned}
M_0(d,z)={}&d(3/5+4z+z^2)
 +d^2(77+70z+19z^2+2z^3)\\
&+d^3(379+390z+235z^2+23z^3)\\
&+d^4(1034+2186z+852z^2+68z^3)\\
&+d^5(3303+4270z+1350z^2)\\
&+d^6(3858+3963z+627z^2)
 +d^7(2051+1098z)+131d^8,\\
M(d,z)={}&M_0(d,z)+10000d^6z^4(1+d)^{10}(1+z)^6,\\
H(h,d,z)={}&\frac{h^{11}}{10^6}(1+h)^8
                          (1+19d)^{16}(1+5z/2)^{10}.
\end{aligned}
\tag{15}
\]
Then
\[
\boxed{\widehat P_1\succeq(1+h)^9-(1+h)^{10}M-H.}
\tag{16}
\]
For the other five rows the bounds are
\[
\boxed{\widehat P_i\succeq1-E_i\qquad(2\le i\le6),}
\tag{17}
\]
where
\[
\begin{aligned}
E_2={}&\frac d2(1+h/2)^{10}(1+2d)^9(1+z/2)^6\\
&+2h^5(1+h/2)^5(1+2d)^{10}(1+z/2)^6,
\end{aligned}
\tag{18}
\]
\[
\begin{aligned}
E_3={}&60h^4(1+h/2)^{17}(1+d)^{14}\\
&+180d^3z(1+h/2)^{21}(1+d)^{11}(1+z/4)^6\\
&+60h^3d^2z(1+h/2)^{18}(1+d)^{12}(1+z/4)^6\\
&+1300d^7(1+h/2)^{21}(1+d)^7
 +\frac{h^{19}dz}{100000}(1+h)^2,
\end{aligned}
\tag{19}
\]
\[
\begin{aligned}
E_4&=h^4(1+h/2)^{19}(88+z)
                   +\frac{z^2}{100}(1+h/2)^{23}(1+z)^7,\\
E_5&=\frac{z^3}{50}(1+z)^5,\\
E_6&=89d^2+646d^3+2141d^4+3679d^5+2086d^6+380d^{12}.
\end{aligned}
\tag{20}
\]

Here is the full coefficient convention for verifying (16)--(20)
directly from the product definitions (6)--(11). A term
\[
c h^i d^j z^k(1+\lambda h)^p(1+\mu d)^q(1+\nu z)^r
\]
has coefficient at \(h^a d^b z^e\)
\[
c\binom p{a-i}\binom q{b-j}\binom r{e-k}
       \lambda^{a-i}\mu^{b-j}\nu^{e-k}.
\tag{21}
\]
A binomial coefficient outside its usual range is zero. Products
with a missing factor have the corresponding exponent zero.

For (16), the retained \(d=z=0\) coefficients of \(h^0,\ldots,h^9\)
are at least the coefficients of \((1+h)^9\); coefficients of
degrees ten through sixteen are positive. Its two adverse terms
of degrees seventeen and eighteen have magnitudes below \(10^{-6}\).
For \(0\le a\le10\), every other adverse coefficient at \(h^a d^b z^e\)
is bounded by
\[
\binom{10}{a}[d^bz^e]M.
\]
For \(11\le a\le19\), it is bounded by
\[
\frac1{10^6}\binom8{a-11}\binom{16}b19^b
                            \binom{10}e(5/2)^e.
\tag{22}
\]
This includes both adverse terms on the \(d=z=0\) line.
The polynomial \(M_0\) in (15) prints the low-degree bounds
individually; its final product covers all remaining \(d,z\) degrees.
These inequalities give (16).

For rows two through four, expansion of (6)--(11) and collection of
powers gives exactly (17) with (18)--(20): subtract the constant one
and apply (21) to the displayed products. Thus every adverse
coefficient has the printed binomial-product bound; no sum of
unprinted coefficient magnitudes is used. For row five, the only
adverse powers are \(z^3,z^5,z^6,z^8\), each bounded by \(E_5\).
For row six, the only adverse powers are \(d^2,d^3,d^4,d^5,d^6,d^{12}\);
their individual upward bounds are the six integers in \(E_6\).
The degrees (14) show that no higher power is omitted. This is a
finite polynomial expansion and comparison, with its entire
majorant specified by (15) and (18)--(21).

## 4. Elementary signs of all six bounds

We give the numerical size estimates as rational inequalities.
Every polynomial used as a majorant has nonnegative coefficients,
so it is enough to bound its value at the upper endpoints (12).

First,
\[
M_0(d,z)\le \frac{12}5d+109d^2+575d^3+2050d^4
          +5227d^5+5544d^6+2491d^7+131d^8.
\]
At \(d=1/19\), the right side is less than \(27/50\).
Also
\[
(20/19)^{10}<7/4,\quad(7/5)^6<8
\]
give
\[
10000d^6z^4(1+d)^{10}(1+z)^6
 <3584/19^6<1/10000.
\]
In particular \(M<3/5\). Since
\[
(7/6)^8<7/2,\qquad 2^{26}(7/2)<6^{11},
\]
we also have \(H<10^{-6}\). Equation (16) therefore gives
\[
\widehat P_1>
(1+h)^9\{1-(7/6)(3/5)\}-10^{-6}
\ge3/10-10^{-6}>1/4.
\tag{23}
\]

For the remaining product estimates, the following elementary
integer-power comparisons suffice:
\[
\begin{array}{c|rrrrrr}
m&5&17&18&19&21&23\\ \hline
(13/12)^m<&3/2&4&9/2&5&11/2&7
\end{array}
\]
\[
\begin{array}{c|rrrrr}
m&7&10&11&12&14\\ \hline
(20/19)^m<&3/2&7/4&9/5&19/10&21/10
\end{array}
\tag{24}
\]
and
\[
(21/19)^9<5/2,\quad(21/19)^{10}<11/4,\quad
(6/5)^6<3,\quad(11/10)^6<9/5,
\]
\[
(7/5)^5<11/2,\quad(7/5)^7<11.
\tag{25}
\]
All are direct comparisons of positive integer powers.

For row two, (24)--(25), including
\((13/12)^{10}<9/4\), give
\[
E_2<\frac{135}{304}+\frac{99}{31104}<1/2.
\tag{26}
\]
The five respective terms of \(E_3\) are bounded by
\[
\frac7{18},\qquad \frac{19}{100},\qquad
\frac1{200},\qquad \frac1{50000},\qquad\frac1{10^6}.
\]
For example, the second bound follows from
\[
\frac{180}{19^3}\frac25\frac{11}2\frac95\frac95
 =\frac{32076}{171475}<\frac{19}{100};
\]
the third follows from
\[
\frac{60}{6^3\,19^2}\frac25\frac92\frac{19}{10}\frac95
 <\frac1{200}.
\]
For the fourth use \(1300(11/2)(3/2)/19^7<1/50000\).
For the fifth, \(h^{19}\le h^2\le1/36\),
\(d,z\le1\) and \((1+h)^2<2\) suffice.
Their sum is less than \(3/5\), so
\[
E_3<3/5.
\tag{27}
\]
For row four,
\[
E_4<\frac{221}{648}+\frac{77}{625}<1/2.
\tag{28}
\]
For row five,
\[
E_5<\frac1{50}\frac8{125}\frac{11}2<1/100.
\tag{29}
\]
Finally,
\[
E_6(1/19)=\frac{793869650016231}{19^{12}}<9/25,
\tag{30}
\]
where the numerator of the positive difference after multiplication
by \(25\cdot19^{12}\) is \(73093021189674\).

Equations (17), (26)--(30) prove all five remaining polynomials
positive. Positive denominators and the positive normalizations
(11)--(13) now prove every sign in (4)--(5), including the specialized
terminal derivatives. These signs are uniform on the whole rectangle;
there is no subdivision or executable sign-cover premise.

## 5. The endpoint implication

The first, fourth and fifth signs give successively
\[
\Phi(x,d,\eta)\ge\Phi(x,1/19,\eta)
 \ge\Phi(13/6,1/19,\eta)
 \ge\Phi(13/6,1/19,3).
\]
The second and third signs first lower \(\eta\) to \(13/5\), then
raise \(x\) to \(13/6\), without increasing \(\Psi\).
The sixth sign makes the remaining function strictly concave in \(d\).
Thus
\[
\Psi(x,d,\eta)\ge
\min\{\Psi(13/6,0,13/5),\Psi(13/6,1/19,13/5)\}.
\tag{31}
\]
The three rational logarithm estimates in the extended floor
therefore apply on the complete rectangle (1). This note proves
only scalar derivative comparisons; the corrected-envelope
argument in that floor is what connects their values to the
squared Casimir of the original common covector.
