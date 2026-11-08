# Small source identities for the outer B F1 lower chord

## Scope

This gives the exact derivative source and the scalar residue bounds used
in the lower-chord terminal proof. The fixed source \(F_1\) and logarithm
majorant are those of [the beta note](SHORT_OUTER_BETA.md).
Throughout,
\[
 5/3\le x\le2,\qquad a=(6x+3)/13,\qquad
 \beta=x+C(a-1),\quad
 (C,u)\in\{1/2,10/13\}\times\{3/4,19/25\}.
\]
Write \(B=a+\beta\), \(S=x+1\), and
\[
 Q(x)=F_1(x,a,\beta,u)+\frac7{96}\ell\!\left(\frac{2B}{7a}\right).
\]
The conclusion here is an exact partial-fraction derivative identity and
small upper bounds on its one remaining residue. No terminal sign is
asserted in this source note.

## 1. Source numerators of degree at most eight

Use \(T=2x+1\), so \(a=3T/13\), \(S=(T+1)/2\), and
\[
 Z=26B=(19+6C)T-13(1+2C).
\]
The complete small source polynomials are
\[
 M=2916T^4-4563T^3+\frac{83317}{4}T^2+\frac{85683}{4},
\]
\[
 J=\frac{27}{2}(u-1)T^4+27(u-1)T^3
       +\frac{223u+331}{4}T^2+\frac{169u}{2}T+\frac{169(u+3)}4,
\]
\[
 \overline D=-\frac{73+42C}{2}T^2+(299+130C)T
                    -\frac{169}{2}(1+2C).
\]
They have four, five, and three monomials and degrees four, four, and two.
Here \(\overline D=169D\), and the original source identities give
\[
 \mathcal G=4uMS^2-J^2,\quad
 \mathcal E=2u\overline D S-J,\quad
 \mathcal W=(M+u\overline D^2)S-\overline D J,
\]
\[
 \Gamma=\frac{\mathcal G}{46656T^4S^2},\qquad
 E_L=\frac{\mathcal E}{63T^2S},\qquad
 w=\frac{\mathcal W}{3969T^4S}.
 \tag{1}
\]
These identities are checked separately. In particular, the numerator of
\(\Gamma\) has degree eight; it is not multiplied by the extra beta
denominator before expansion.

The resulting exact rational source is
\[
\begin{aligned}
 Q={}&\frac{\mathcal G}{46656T^4S^2}
       +\frac{\mathcal E}{864T^2S}
       -\frac{7(u-1)Z}{576T}
       -\frac{\mathcal W}{1296T^3SZ}\\
     &+\frac{119T}{64Z}-\frac1{16}-\frac{9193}{50000}.
\end{aligned}
 \tag{2}
\]
Keep the terms in (2) separate. Their full polynomial inputs follow.

For \(u=3/4\), independently of \(C\),
\[
\begin{aligned}
 256\mathcal G={}&-2916T^8-11664T^7+763452T^6+783648T^5-672349T^4\\
                 &+3628092T^3-3020706T^2+3084588T-2313441.
\end{aligned}
\]
For \(u=19/25\),
\[
\begin{aligned}
 2500\mathcal G={}&-26244T^8-104976T^7+7462368T^6+7505352T^5
                     -6706701T^4\\
                  &+35452482T^3-29418337T^2+30388904T-22391824.
\end{aligned}
\]
Each has nine monomials and degree eight.

For \(C=1/2,u=3/4\),
\[
 16\mathcal E=54T^4-456T^3+1811T^2+1326T-4563,
\]
\[
 16\mathcal W=-2538T^6+51162T^5-81361T^4+119080T^3
                         +405600T^2-1146834T+771147.
\]
For \(C=1/2,u=19/25\),
\[
 50\mathcal E=162T^4-1462T^3+5790T^2+4199T-14365,
\]
\[
 200\mathcal W=-30456T^6+634444T^5-1058872T^4+1579149T^3
                          +5056649T^2-14432093T+9682179.
\]
For \(C=10/13,u=3/4\),
\[
 208\mathcal E=702T^4-6810T^3+28121T^2+15600T-66417,
\]
\[
\begin{aligned}
 5408\mathcal W={}&-961038T^6+18867819T^5-37923578T^4+68877094T^3\\
                  &+130716430T^2-464263449T+335020530.
\end{aligned}
\]
For \(C=10/13,u=19/25\),
\[
 650\mathcal E=2106T^4-21799T^3+89767T^2+49400T-209222,
\]
\[
\begin{aligned}
 33800\mathcal W={}&-5766228T^6+117052291T^5-245325153T^4
                      +450046077T^3\\
                   &+812170229T^2-2922370308T+2104717212.
\end{aligned}
\]
Each \(\mathcal E\) identity has five monomials and degree four; each
\(\mathcal W\) identity has seven monomials and degree six.

## 2. The four regular parts

For the four pairs \((C,u)\), respectively, define the following complete
rational functions:
\[
\begin{aligned}
 R_{00}={}&-\frac{x^2}{256}+\frac{127x}{4224}
 +\frac{1848431}{124416T}-\frac{1189591}{110592T^2}
 +\frac{300989}{55296T^3}-\frac{28561}{36864T^4}\\
 &-\frac{37241}{5184S}-\frac{49729}{46656S^2},
\end{aligned}
\]
\[
\begin{aligned}
 R_{01}={}&-\frac{9x^2}{2500}+\frac{401x}{13750}
 +\frac{72287969}{4860000T}-\frac{629095909}{58320000T^2}
 +\frac{317921279}{58320000T^3}-\frac{1399489}{1822500T^4}\\
 &-\frac{37241}{5184S}-\frac{49729}{46656S^2},
\end{aligned}
\]
\[
\begin{aligned}
 R_{10}={}&-\frac{x^2}{256}+\frac{3659x}{117888}
 +\frac{7366622471}{496793088T}-\frac{1322317607}{120434688T^2}
 +\frac{9998885}{1824768T^3}-\frac{28561}{36864T^4}\\
 &-\frac{5100233}{715392S}-\frac{49729}{46656S^2},
\end{aligned}
\]
\[
\begin{aligned}
 R_{11}={}&-\frac{9x^2}{2500}+\frac{23099x}{767500}
 +\frac{192108297503}{12937320000T}
 -\frac{38858817257}{3528360000T^2}\\
 &+\frac{440236043}{80190000T^3}
 -\frac{1399489}{1822500T^4}
 -\frac{5100233}{715392S}-\frac{49729}{46656S^2}.
\end{aligned}
\]
Each regular part has eight displayed terms. Its scalar fractions are kept
separate; they are not put over a common numerical denominator.
There is a scalar \(V\), described below, for which
\[
 \boxed{Q'(x)=R_{ij}'(x)+V\,\frac{B'}{B^2}.}
 \tag{3}
\]

### Verification without a degree-nine numerator

The following explicit principal-part checks prove (3). They are scalar
jet identities using the printed \(\mathcal G,\mathcal E,\mathcal W\);
no numerator of degree nine is expanded.

At \(T=0\), the first four divided derivatives of \(T^4Q\) are those of
\[
 H(T)=\frac{\mathcal G}{46656S^2}
      +\frac{T^2\mathcal E}{864S}
      -\frac{7(u-1)ZT^3}{576}
      -\frac{T\mathcal W}{1296SZ}.
 \tag{4}
\]
They are, in order, the coefficients of \(T^{-4},T^{-3},T^{-2},T^{-1}\)
printed in the corresponding \(R_{ij}\). For example, for the last pair
the four exact scalar results are
\[
 -\frac{1399489}{1822500},\quad
 \frac{440236043}{80190000},\quad
 -\frac{38858817257}{3528360000},\quad
 \frac{192108297503}{12937320000}.
\]
For the other pairs the results are exactly their four already printed
fractions, with the same alternating signs. Differentiate and evaluate
each of the four terms of (4) separately, then combine the resulting
scalars. In all sixteen checks, even before cancellation between these
four scalar contributions, the largest common numerator is
\(192108297503\); the largest common denominator is \(12937320000\).

At \(S=0\), put \(T=2S-1\). The value and first derivative of \(S^2Q\)
are those of
\[
 \frac{\mathcal G}{46656T^4}
 +\frac{S\mathcal E}{864T^2}
 -\frac{S\mathcal W}{1296T^3Z}.
 \tag{5}
\]
They are \(-49729/46656\) and, respectively,
\(-37241/5184\) or \(-5100233/715392\), as printed.
The largest cleared numerator in these scalar checks is \(5100233\).

For the polynomial part at infinity, let \(g_8,g_7,e_4,w_6\) be the
indicated coefficients of the printed source numerators.
Its quadratic and linear coefficients in \(x\) are exactly
\[
 q_2=g_8/2916,\qquad
 q_1=q_2+2\left\{\frac{g_7-2g_8}{11664}
                         +\frac{e_4}{432}
                         -\frac{w_6}{648(19+6C)}\right\}.
 \tag{6}
\]
These are precisely the first two terms in the appropriate \(R_{ij}\).
Formula (6) is obtained by retaining only the two leading powers in
(2); all discarded terms remain bounded at infinity.

The only other pole is the simple zero of \(B\). Write its location as
\((x_0,a_0)\). It is
\[
 (x_0,a_0)=(1/11,3/11)\quad(C=1/2),\qquad
 (x_0,a_0)=(61/307,99/307)\quad(C=10/13).
 \tag{7}
\]
Its exact residue is \(-V\), with
\[
 V=\frac{7a_0}{96}\left(7w(x_0,a_0,-a_0,u)-17/4\right).
 \tag{8}
\]
This follows directly from the sole \(1/B\) term in the source \(F_1\).
It is intentionally retained as the small product in (8).

These three poles are distinct. Subtract the matched principal parts
from \(Q\); the difference is a polynomial. Subtract the matched
quadratic and linear terms from (6); it is bounded at infinity and
therefore constant. Differentiating gives (3). This is the elementary
uniqueness of partial fractions, derived from polynomial divisibility;
it does not require expanding a common numerator of (2).
The evaluation points in this verification are algebraic anchors only.
No geometric inequality is asserted at them.

## 3. Small upper bounds for the B residue

For either point in (7), the residue decreases in \(u\).
Indeed
\[
 w_u=\frac{D_0(D_0-KS)}{49a_0^4},\qquad
 D_0=(a_0+1)(2x_0+1-a_0)>0.
\]
At the two points, respectively,
\[
 KS-D_0=560/1331>0,\qquad
 KS-D_0=15192380/28934443>0.
 \tag{9}
\]
Thus it suffices to use \(u=3/4\) in (8).

For \(C=1/2\), direct scalar arithmetic gives
\[
 V(3/4)=190441/3763584<507/10000.
 \tag{10}
\]

For \(C=10/13\), keep the scalar arithmetic factored. At the second
point of (7), with \(u=3/4\), the exact inputs are
\[
 \lambda=\frac{153055}{68607},\quad
 \delta=\frac{44660}{22869},\quad
 v=1-\frac{112976}{153055}
                  +\left(\frac{112976}{153055}\right)^2,
\]
\[
 E=-\frac{92}{307}+\frac{307}{368}+\frac{131703}{153055}.
\]
The initial scalar enclosures can also be checked in small stages.
Put \(r=112976/153055\). On the finer grid \(M=10^6\),
\[
 738139\le Mr\le738140.
\]
The three-monomial quadratic \(1-r+r^2\) increases for \(r\ge1/2\).
Its endpoint squares are checked by the twelve-digit products
\[
 738139^2=544849183321,\qquad738140^2=544850659600.
\]
Consequently
\[
 806710\le Mv\le806711.
\]
For \(E\), first combine only its two small-denominator terms:
\[
 -92/307+307/368=60393/112976.
\]
Then direct scalar division gives
\[
 534564\le M(60393/112976)\le534565,\qquad
 860494\le M(131703/153055)\le860495.
\]
Adding yields \(1395058\le ME\le1395060\). All cross-products in
these divisions have at most twelve digits. No common denominator for
the full expression for \(v\) or \(E\) is needed.

Thus on the grid \(N=100000\), with direct division for
\(\lambda,\delta\), the initial bounds are
\[
 223089\le N\lambda\le223090,\quad
 195286\le N\delta\le195287,
\]
\[
 80671\le Nv\le80672,\quad
 139505\le NE\le139506.
\]
Round after each product, keeping the same grid. The complete upper
and lower product bounds are
\[
 N\lambda^2\le497692,\quad
 N\lambda^2v\le401499,\quad
 N\delta^2\le381371,\quad N\delta^2u\le286029,
\]
\[
 N\delta\lambda\ge435661,\qquad
 N\delta\lambda E\ge607768.
\]
For example, the last lower bound is
\(\lfloor435661\cdot139505/100000\rfloor=607768\);
all the other steps use the same directed division.
Every integer product in this product-propagation step has at most
eleven digits.
Consequently
\[
 w\le(401499+286029-607768)/100000=79760/100000,
\]
\[
 V\le\frac{769923}{24560000}<\frac{157}{5000}.
 \tag{11}
\]
The last difference is \(1261/24560000>0\).
Equations (9)--(11) prove the uniform bounds
\[
 \boxed{V<507/10000\ (C=1/2),\qquad V<157/5000\ (C=10/13).}
 \tag{12}
\]

All polynomial inputs to the source checks have been printed. They have
at most nine monomials and degree at most eight; their largest printed
coefficient is \(2922370308\). Principal-part checks are scalar evaluations
after differentiation, not expanded high-degree identities. In particular,
neither the large common numerator of \(Q\) nor the long exact fraction
for the second \(V(3/4)\) is needed.
