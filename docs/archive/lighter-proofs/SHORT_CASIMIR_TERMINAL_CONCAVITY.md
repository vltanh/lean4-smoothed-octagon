# S4: terminal concavity from six small source terms

This replaces the sixth sign in equations (4)--(5) of the
[extended Casimir derivative note](../../archive/notes/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md).
On its unchanged terminal line,
\[
x=13/6,\qquad \eta=13/5,\qquad 0\le d\le1/19,
\]
the result is
\[
\boxed{W_6=-\Psi_{dd}>81/1000.}                              \tag{1}
\]
The incoming norm is the specified rational upper value in that source.
All derivatives here include its dependence on displacement. This note
proves the terminal concavity sign; the other five S4 signs are separate
obligations.

## 1. Specialize the original source before expanding

Put \(r=13d\), so \(0\le r\le13/19<7/10\), and define
\[
A=r+5,\quad B=11r+95,\quad
K=36r^2+360r+9025,\quad D=48r^2+395r+575.                    \tag{2}
\]
Then the original shapes and transport quantities are
\[
\alpha=A/5,\quad \beta=(r+13)/6,\quad
\alpha+\beta=B/30,\quad \Sigma=K/900,\quad D_{\rm old}=D/450.
\]
In particular all displayed denominators are positive. The incoming
upper value becomes
\[
u=\frac34+\frac{686/10127+r^3/8112}{r+7}
  =\frac{r^2-7r+6133}{8112}+\frac{v}{r+7},
\qquad v=\frac{160867}{6319248}.                             \tag{3}
\]
Both forms are exact; their equality is a cubic identity.

The original Casimir expression and logarithm argument are
\[
G(u)=\frac{-47045881u^2+83616986u-25230529}{60840000},
\qquad y=\frac{12AB}{K}.
\tag{4}
\]
Let \(R_1\) denote the rational part of the source's second residual,
so \(\Psi=G-(R_1+\log y)/7\). Its complete small source identity is
\[
R_1=C_0(r)+uC_1(r),\qquad
C_0=\frac{P_0}{72ABK},\quad C_1=\frac{P_1}{18ABK},
\tag{5}
\]
with
\[
\begin{aligned}
P_0={}&-48384r^4-1347840r^3-13234200r^2-220817500r-995850625,\\
P_1={}&2700r^4-19800r^3+107550r^2+61496875r+374408125.
\end{aligned}
\]

For a direct check against the transport definition, multiplication by
\(72ABK\), before any collection, gives the following ten source products:
\[
\begin{aligned}
72ABK R_1={}&766222500+48uD^2-100D(6859u-5023)-9K^2\\
&+72ABK+12(u-1)B^2K+432A^2K-2592A^3B\\
&-288uABD+300AB(6859u-5023)\\
={}&P_0+4uP_1.
\end{aligned}                                                \tag{6}
\]
Here \(r,u\) are independent while checking the identity. Every source
product has degree at most five in these two variables; the collected
answer has ten monomials. Thus the incoming rational function is
substituted only after this small transport identity is established.

## 2. A small partial fraction interface

For \(j=0,1\), write
\[
C_j=c_{\infty,j}+\frac{c_{A,j}}A+\frac{c_{B,j}}B
                   +\frac{e_{0,j}+e_{1,j}r}{K}.
\tag{7}
\]
All coefficients are given here.

| \(j\) | \(c_{\infty,j}\) | \(c_{A,j}\) | \(c_{B,j}\) | \(e_{0,j}\) | \(e_{1,j}\) |
|---|---:|---:|---:|---:|---:|
| 0 | \(-56/33\) | \(-2077/576\) | \(-20425821365/87920448\) | \(3690640915/249774\) | \(157928748/249774\) |
| 1 | \(25/66\) | \(227/18\) | \(98342375/457919\) | \(-697700705/249774\) | \(-394433796/249774\) |

Here is a scalar verification of the complete source link, keeping
every polynomial at degree four or less. If \(P=P_j\) and \(k=72,18\),
respectively, its leading coefficient and two residues give
\[
c_\infty=\frac{[r^4]P}{396k},\quad
c_A=\frac{P(-5)}{kB(-5)K(-5)},\quad
c_B=\frac{P(-95/11)}{kA(-95/11)K(-95/11)}.                    \tag{8}
\]
After these three cancellations the remaining numerator over \(K\)
has degree at most one. Its two values are
\[
\begin{aligned}
e_0&=9025\{C_j(0)-c_\infty-c_A/5-c_B/95\},\\
e_0+e_1&=9421\{C_j(1)-c_\infty-c_A/6-c_B/106\}.
\end{aligned}                                                \tag{9}
\]
Substitution of the printed quartics gives exactly the table. Equations
(8)--(9), polynomial degree, and cancellation of the two simple poles
prove (7). In particular no large combined coefficient numerator is a
premise of this decomposition.

For the derivative argument, define
\[
\alpha_A=227/18,\quad\beta_A=-2077/576,\qquad
\alpha_B=98342375/457919,\quad\beta_B=-20425821365/87920448,
\]
\[
n=\frac{157928748r+3690640915}{249774},\quad
m=\frac{394433796r+697700705}{249774},\quad f=n-mu,
\]
\[
H_A=\frac{\alpha_Au+\beta_A}{A},\quad
H_B=\frac{\alpha_Bu+\beta_B}{B},\quad H_C=\frac fK.
\]
The original residual is now the six-term expression
\[
\Psi=G(u)-\frac17\left\{-\frac{56}{33}+\frac{25u}{66}
                 +H_A+H_B+H_C+\log(12AB/K)\right\}.           \tag{10}
\]

## 3. Elementary bounds for the incoming function

From (3),
\[
u'=\frac{2r-7}{8112}-\frac v{(r+7)^2},\quad
u''=\frac2{8112}+\frac{2v}{(r+7)^3},\quad
u'''=-\frac{6v}{(r+7)^4}.                                    \tag{11}
\]
Thus \(u\) decreases. Endpoint substitution gives
\[
\frac{379}{500}<u<\frac{19}{25}.
\]
For later use, the complete derivative bounds are
\[
\frac{11}{10000}<-u'<\frac7{5000},\qquad
\frac7{20000}<u''<\frac1{2500},\qquad
\frac1{24000}<-u'''<\frac1{15000}.                            \tag{12}
\]
For explicit rational checks, use \(1/40<v<13/500\) and
\(7\le r+7<77/10\). The six endpoint comparisons needed in (12) are
\[
\begin{array}{ll}
\displaystyle\frac{28/5}{8112}+\frac{1/40}{(77/10)^2}>
 \frac{11}{10000},
&
\displaystyle\frac7{8112}+\frac{13/500}{7^2}<\frac7{5000},
\\[2mm]
\displaystyle\frac2{8112}+\frac{2/40}{(77/10)^3}>
 \frac7{20000},
&
\displaystyle\frac2{8112}+\frac{26/500}{7^3}<\frac1{2500},
\\[2mm]
\displaystyle\frac{6/40}{(77/10)^4}>\frac1{24000},
&
\displaystyle\frac{78/500}{7^4}<\frac1{15000}.
\end{array}
\]
All follow by multiplication by positive denominators.

Also put \(\kappa=K/1000\). The quadratic (2) gives
\[
9<\kappa<93/10,\qquad 9/25\le\kappa'<41/100,\qquad
\kappa''=9/125.                                             \tag{13}
\]
The upper bounds can be checked at \(r=13/19\); no subdivision is used.

## 4. A uniform positive third derivative

We prove
\[
\boxed{\Psi_{rrr}>11/60000.}                                \tag{14}
\]

### Casimir and linear incoming terms

From (4) and the bounds on \(u\),
\[
0<G_u<1/4,\qquad G_{uu}<0.
\]
Consequently
\[
(G(u))'''=3G_{uu}u'u''+G_u u'''>-1/60000.
\tag{15}
\]
The contribution \(-25u'''/462\) from the next term in (10) is positive.

### The two linear poles

For any positive affine function \(L\), with constant derivative
\(\ell=L'\), the product rule gives
\[
\left(\frac{\alpha u+\beta}{L}\right)'''
=\frac{\alpha u'''}L-\frac{3\ell\alpha u''}{L^2}
 +\frac{6\ell^2\alpha u'}{L^3}
 -\frac{6\ell^3(\alpha u+\beta)}{L^4}.
\tag{16}
\]
Both values of \(\alpha\) used here are positive.

For \(H_A\), all four terms on the right are negative:
\(\alpha_Au+\beta_A>119/20\) and \(A<57/10\). Therefore
\[
-\frac17H_A'''>
\frac{6(119/20)}{7(57/10)^4}>\frac3{625}.                    \tag{17}
\]
For \(H_B\), the first three terms in (16) are negative.
The bound \(\alpha_Bu+\beta_B>-70\) and \(B\ge95\) give
\[
H_B'''<\frac{6\cdot11^3\cdot70}{95^4}<\frac7{1000},
\qquad -\frac17H_B'''>-\frac1{1000}.                        \tag{18}
\]
The two bounds for the affine numerators are direct substitutions of
\(u>379/500\).

### The quadratic pole

The explicit affine functions \(n,m\) satisfy
\[
14700<n<15300,\quad2700<m<3900,\quad
632<n'<633,\quad1570<m'<1580.
\]
Together with (12), these imply
\[
0<f<14000,\qquad -600<f'<-500,\qquad f''>0,\qquad f'''<0.
\tag{19}
\]
For completeness, use \(f'=n'-m'u-mu'\),
\(f''=-2m'u'-mu''\), and \(f'''=-3m'u''-mu'''\).
The lower and upper comparisons for \(f'\) are
\[
632-1580(19/25)+2700(11/10000)>-600,
\]
\[
633-1570(379/500)+3900(7/5000)<-500.
\]
The last two signs follow from
\[
2(1570)(11/10000)-3900/2500>0,\qquad
-3(1570)(7/20000)+3900/15000<0.
\]

Set \(h=1/K=1/(1000\kappa)\). Its exact derivatives are
\[
h'=-\frac{\kappa'}{1000\kappa^2},\quad
h''=\frac{2(\kappa')^2-\kappa\kappa''}{1000\kappa^3},\quad
h'''=\frac{6\kappa'(\kappa\kappa''-(\kappa')^2)}
             {1000\kappa^4}.
\]
Equation (13) gives
\[
h'<0,\quad -6/10^7<h''<0,\quad0<h'''<21/10^8.                \tag{20}
\]
The two quantitative bounds follow from the small rational comparisons
\[
\frac{(93/10)(9/125)-2(9/25)^2}{1000\cdot9^3}<\frac6{10^7},
\quad
\frac{6(41/100)((93/10)(9/125)-(9/25)^2)}
 {1000\cdot9^4}<\frac{21}{10^8}.
\]
For the signs, \(2(41/100)^2<9(9/125)\) and
\((41/100)^2<9(9/125)\) suffice.

In the product rule
\[
H_C'''=f'''h+3f''h'+3f'h''+fh''',
\]
the first two terms are negative. Equations (19)--(20) therefore give
\[
H_C'''<
3(600)\frac6{10^7}+14000\frac{21}{10^8}
=\frac{201}{50000}<\frac{21}{5000}.
\]
Thus
\[
-\frac17H_C'''>-\frac3{5000}.                               \tag{21}
\]

### The exact logarithm

The logarithm is differentiated exactly. Since \(\kappa'''=0\),
\[
(\log(12AB/K))'''
=\frac2{A^3}+\frac{2662}{B^3}
 +\frac{3\kappa'\kappa''}{\kappa^2}
 -\frac{2(\kappa')^3}{\kappa^3}
<\frac2{125}+\frac{2662}{95^3}
 +\frac{3(41/100)(9/125)}{9^2}
<\frac{21}{1000}.
\]
Its contribution to \(\Psi'''\) is consequently greater than
\(-3/1000\). Combining this with (15), (17), (18), and (21) gives
\[
\Psi_{rrr}>
-\frac1{60000}+\frac3{625}-\frac1{1000}
-\frac3{5000}-\frac3{1000}
=\frac{11}{60000},
\]
as claimed.

## 5. The terminal scalar value

It remains to bound \(W_6\) at \(r_*=13/19\), because (14) implies
\[
\frac{dW_6}{dd}=-13^3\Psi_{rrr}<-24167/60000<0.
\tag{22}
\]
Here are complete rational recipes for the six contributions. Put
\[
A_*=\frac{108}{19},\quad B_*=\frac{1948}{19},\quad
K_*=\frac{3353029}{361},\quad K'_*=\frac{7776}{19},
\]
\[
U=\frac{r_*^2-7r_*+6133}{8112}+\frac v{r_*+7},
\quad U_1=\frac{2r_*-7}{8112}-\frac v{(r_*+7)^2},
\quad U_2=\frac2{8112}+\frac{2v}{(r_*+7)^3}.
\]
The symbols \(m,n,m',n'\) in the following formulas are the explicit
affine functions in Section 2 evaluated at \(r_*\). Set
\[
f_0=n-mU,\quad f_1=n'-m'U-mU_1,\quad
f_2=-2m'U_1-mU_2,\quad
a_0=\alpha_AU+\beta_A,\quad b_0=\alpha_BU+\beta_B.
\]
The contributions to \(W_6=-169\Psi_{rr}\) are
\[
\begin{aligned}
V_G&=-169\{G_{uu}U_1^2+G_u(U)U_2\},\\
V_0&=\frac{169}{7}\frac{25}{66}U_2,\\
V_A&=\frac{169}{7}\left\{\frac{\alpha_AU_2}{A_*}
 -\frac{2\alpha_AU_1}{A_*^2}+\frac{2a_0}{A_*^3}\right\},\\
V_B&=\frac{169}{7}\left\{\frac{\alpha_BU_2}{B_*}
 -\frac{22\alpha_BU_1}{B_*^2}+\frac{242b_0}{B_*^3}\right\},\\
V_C&=\frac{169}{7}\left\{\frac{f_2}{K_*}
 -\frac{2f_1K'_*}{K_*^2}
 +\frac{f_0(2(K'_*)^2-72K_*)}{K_*^3}\right\},\\
V_{\log}&=\frac{169}{7}\left\{-\frac1{A_*^2}
 -\frac{121}{B_*^2}-\frac{72}{K_*}
 +\frac{(K'_*)^2}{K_*^2}\right\}.
\end{aligned}                                                \tag{23}
\]

Direct substitution and positive-denominator multiplication give these
coarse directed bounds; the formulas (23) specify every scalar exactly.

| Term | Strict lower bound |
|---|---:|
| \(V_G\) | \(-12/1000\) |
| \(V_0\) | \(3/1000\) |
| \(V_A\) | \(1600/1000\) |
| \(V_B\) | \(-350/1000\) |
| \(V_C\) | \(10/1000\) |
| \(V_{\log}\) | \(-1170/1000\) |

Their sum is \(81/1000\). Hence \(W_6(r_*)>81/1000\), and (22)
proves (1) on the whole original displacement interval.

## 6. Caller and algebraic size

The original extended-floor argument first fixes
\(x=13/6,\eta=13/5\), then invokes strict concavity in displacement.
The \(W_6\) proved here is exactly that second derivative of the same
scalar function with the same incoming upper value. Thus its comparison
with the two displacement endpoints is unchanged.

The source reduction precedes the incoming substitution and all
derivative estimates. Identity (6) has ten monomials and degree five in
two variables; each separate source product also has at most ten
monomials and degree five. Its largest collected coefficient is
1,497,632,500. The two residue polynomials each have five monomials and
degree four, and their interface is established by scalar residues and
two scalar values. The largest displayed residue numerator is
20,425,821,365, which has eleven digits. All remaining polynomial
identities are cubic, quadratic, or affine. The proof uses no
subdivision and no coefficient-table sign premise.

Exact rational arithmetic checked the source transcription, scalar
residue data, all elementary bounds, and the six directed endpoint
roundings. No Lean source is changed and no Lean, Lake, typechecking,
or CI check is used.
