# The negative reciprocal-shape residue for outer S1

## Scope

This supplies one common sign used when reducing the outer S1 residual
\(F_1\) in reciprocal shape. It is an auxiliary lemma, not a complete S1
replacement. The definitions of \(F_1,\Gamma,w,E_L\) and the fixed logarithm
majorant are those of [the beta reduction](SHORT_OUTER_BETA.md).

Assume
\[
 3/2\le x\le2,\qquad 3/4\le u\le19/25,\qquad
 C\in\{1/2,24/43,10/13\}.
\]
Write \(r=1/a\), \(\beta=x+C(a-1)\), and
\[
 S=x+1,\quad d=1+C,\quad e=x-C,\quad
 z=(a+\beta)/a=d+er.
\]
The part of \(F_1+(7/96)\ell\) with denominator \(z\) is
\[
 \frac{119/4-W(r)}{96z},\qquad W(r)=49w.
\]
After polynomial division in \(r\), its simple-pole coefficient is
\[
 Q(x,u,C)=\frac{119/4-W(-d/e)}{96}.
\]
We prove
\[
 \boxed{Q(x,u,C)<0.}
\]
The range of \(u\) is independent of \(r\). The sign consequently remains
available when using the same norm interval on a shape comparison segment.

## 1. A low-degree source identity

Put
\[
 E_0=S(u-1)+1/S,\qquad J_2=Su+S-1+1/S,
\]
\[
 d_0=1+2C,\quad d_1=2[x-C(1+x)],\quad
 d_2=1+2x-2x^2+2Cx,\qquad D_r=d_0+d_1r+d_2r^2.
\]
The complete factored quartic is
\[
 W(r)=36+(12-6S)r^2+(S^2-S+1)r^4
          +uD_r^2-D_r(6E_0+J_2r^2).
 \tag{1}
\]
This is obtained directly from the displayed source definition of \(w\);
it is kept as a quartic in \(r\), with its coefficient expressions opaque.
No polynomial in three free variables is expanded.

At the sole argument needed for this residue, put
\[
 T=-(3+2C)x^2+(2+8C+4C^2)x+1+2C.
 \tag{2}
\]
Then \(e^2D_{-d/e}=T\). This is a three-monomial quadratic identity in
\(x\), with \(C\) fixed. Substitute this identity into (1) before any
further expansion. It gives
\[
\begin{aligned}
 -384Se^4Q={}&25Se^4+4(12-6S)Sd^2e^2
       +4S(S^2-S+1)d^4+4SuT^2\\
 &-4T\{6[S^2(u-1)+1]e^2+[S^2u+S^2-S+1]d^2\}
 =:\mathcal R(x,u,C).
\end{aligned}
 \tag{3}
\]
All factors in (3) are printed in (2)--(3). For fixed \(u,C\), every
product has degree at most six in \(x\). The full collected polynomial
has seven monomials. The complete endpoint polynomials are printed next.
The scalar \(S e^4\) is positive throughout the stated domain.

The expression \(\mathcal R\) is affine in \(u\), so its positivity at
\(u=3/4\) and \(u=19/25\) suffices for the whole norm interval. This
reduces the sign to six univariate polynomials without changing that interval.

## 2. The slope C=1/2

At \(u=3/4\), \(\mathcal R=P/16\), where
\[
 P=-384x^6+1456x^5+512x^4-4784x^3+4336x^2-1171x+109.
\]
At \(u=19/25\), \(\mathcal R=\widetilde P/400\), where
\[
 \widetilde P=-9216x^6+36368x^5+11152x^4-119812x^3
                    +109520x^2-29231x+2669.
\]
Each identity has seven monomials and degree six. Put \(v=x-3/2\),
so \(0\le v\le1/2\). The complete shift identities are
\[
 P(3/2+v)=1237+5816v+9700v^2+5128v^3
                          -1528v^4-2000v^5-384v^6,
\]
\[
 2\widetilde P(3/2+v)
 =57055+283622v+496996v^2+286600v^3
                          -54256v^4-93152v^5-18432v^6.
\]
They have seven monomials and degree six. Absorb each negative higher
power into \(v^3\), using \(v^4\le v^3/2\),
\(v^5\le v^3/4\), and \(v^6\le v^3/8\). The two remaining cubic
coefficients are respectively \(3816\) and \(233880\), both positive.
All other coefficients in the resulting lower polynomials are positive.
Thus both endpoint signs are strict.

## 3. The slope C=24/43

At \(u=3/4\), \(\mathcal R=P/3418801\), where
\[
\begin{aligned}
 P={}&-84436434x^6+342811996x^5+55997137x^4-1129797454x^3\\
    &+1134306926x^2-330711121x+33361344.
\end{aligned}
\]
At \(u=19/25\), \(\mathcal R=\widetilde P/85470025\), where
\[
\begin{aligned}
 \widetilde P={}&-2026474416x^6+8544667213x^5+1014020797x^4
                 -28248239552x^3\\
               &+28645881560x^2-8267882136x+818256384.
\end{aligned}
\]
Each source identity has seven monomials and degree six.

For the first polynomial, put \(v=x-3/2\in[0,1/2]\). Then
\[
\begin{aligned}
 32P(3/2+v)={}&6443173869+33034618132v+62854172500v^2
                  +39039871456v^3\\
              &-7124561296v^4-13347709120v^5-2701965888v^6.
\end{aligned}
\]
The three negative terms are absorbed into the positive cubic term,
as in Section 2. Its remaining coefficient is
\[
 39039871456-7124561296/2-13347709120/4-2701965888/8>0.
\]
The remaining coefficients are positive.

For the second polynomial, use the smaller shift \(v=x-1\in[1/2,1]\):
\[
\begin{aligned}
 \widetilde P(1+v)={}&480229850-1100264915v+5034843576v^2
                        +20725027446v^3\\
                    &+13340240622v^4-3614179283v^5-2026474416v^6.
\end{aligned}
\]
The two negative highest powers are absorbed in \(v^4\), leaving
\(7699586923v^4>0\). Since \(v^2\ge v/2\), its quadratic and linear
terms together are at least \(1417156873v>0\). The constant and cubic
terms are positive. Both shift identities have seven monomials and
degree six. The shift at \(1\), rather than at \(3/2\), keeps every
expanded coefficient within twelve digits.

## 4. The slope C=10/13

At \(u=3/4\), \(\mathcal R=P/28561\), where
\[
 P=-777738x^6+3922828x^5-1672723x^4-12639366x^3
                       +17731054x^2-6514761x+830300.
\]
At \(u=19/25\), \(\mathcal R=\widetilde P/714025\), where
\[
\begin{aligned}
 \widetilde P={}&-18665712x^6+97215053x^5-45973707x^4-314136704x^3\\
               &+447349104x^2-163466264x+20457200.
\end{aligned}
\]
Each source identity has seven monomials and degree six.
For \(v=x-3/2\in[0,1/2]\), the complete shifts are
\[
\begin{aligned}
 32P(3/2+v)={}&24226009+84538116v+371459588v^2+418899552v^3\\
              &+47994544v^4-98458048v^5-24887616v^6,
\end{aligned}
\]
\[
\begin{aligned}
 32\widetilde P(3/2+v)
   ={}&462486505+1530008882v+8853421608v^2+10797573968v^3\\
      &+1701485136v^4-2264843360v^5-597302784v^6.
\end{aligned}
\]
These have seven monomials and degree six. Absorbing the last two terms
into \(v^3\) leaves positive cubic coefficients:
\[
 418899552-98458048/4-24887616/8>0,
\]
\[
 10797573968-2264843360/4-597302784/8>0.
\]
All remaining terms are nonnegative and the constants are positive.

## 5. Consequence and size boundary

All six endpoint polynomials are positive. Affinity in \(u\) proves
\(\mathcal R>0\) on the full stated norm interval, and (3) gives \(Q<0\).
This is only the simple-pole residue sign; reciprocal-shape concavity
still requires separate bounds for its polynomial part and logarithm term.

Every expanded source or shift identity above is univariate, has at most
seven monomials and degree at most six. The largest printed integer
coefficient is \(62854172500\), eleven digits. The quartic (1) is evaluated
at its single pole argument before clearing denominators; no global
polynomial in \(x,r,u\) is expanded.
