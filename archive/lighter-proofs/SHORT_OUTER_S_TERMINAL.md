# The S1 outer S branch: terminal faces and exact caller closure

Combine [the norm and beta reduction](SHORT_OUTER_S_BETA.md) with
[reciprocal-shape concavity](SHORT_OUTER_S_RECIPROCAL.md). This note proves
\[
 F_1\bigl(x,a,x+\tfrac8{17}(a-1),u\bigr)\ge\frac1{1000}
 \quad\left(1\le a\le x\le\frac32,\quad\frac34\le u\le\frac{19}{25}\right).
 \tag{1}
\]
It follows that both original rational tests in the S row satisfy
\[
 \boxed{F_0\ge F_1\ge\frac1{1000}-\frac{77}{176800}
 =\frac{499}{884000}>0.}
 \tag{2}
\]
This is a replacement of the four S-row terminal signs in the outer low-ratio
note: both tests, at both original norm endpoints. It does not replace the
A or B rows, nor assert that S1 as a whole has closed.

For (1), norm concavity first reduces u to \(3/4,19/25\). Reciprocal-shape
concavity then reduces a to 1 or x. The remainder of this proof has only the
single free variable x. The cubic rational bound for the logarithm is unchanged.

## 1. The lower-shape face a=1

Here beta=x. Write
\[
 F_u(x)=F_1(x,1,x,u),\qquad
 Q_u(x)=F_u(x)+\frac7{96}\ell\bigl(2(x+1)/7\bigr),
 \qquad S=x+1.
\]
The exact complete rational formulas are
\[
\begin{aligned}
Q_f(x)={}&- \frac{548293}{28800000} - \frac{223 x}{1536}\\
&{}- \frac{217}{576 (x + 1)^{2}} - \frac{x^{3}}{32}\\
&{}+ \frac{289}{1152 (x + 1)} + \frac{1151 x^{2}}{9216}
\end{aligned}
\]

\[
\begin{aligned}
Q_v(x)={}&- \frac{28643}{1800000} - \frac{2921 x}{20000}\\
&{}- \frac{217}{576 (x + 1)^{2}} - \frac{19 x^{3}}{600}\\
&{}+ \frac{1251 x^{2}}{10000} + \frac{7177}{28800 (x + 1)}
\end{aligned}
\]

The subscripts f and v throughout this note mean the fixed norm endpoints
\(3/4\) and \(19/25\), respectively. Each displayed Q identity, after clearing
its positive denominator proportional to \(S^2\), has six monomials and degree
five. The largest coefficient before collecting source contributions is below
\(10^8\).

Their third derivatives are bounded above without a large rational clearing.
For f,
\[
 Q_f'''=-\frac3{16}-\frac{289}{192S^4}+\frac{217}{24S^5}
 =-\frac3{16}+\frac{217/24-(289/192)S}{S^5}
 \le\frac1{1024}.
 \tag{3}
\]
Indeed, \(2\le S\le5/2\), the numerator in the last fraction is positive,
and it is at most \(193/32\), while \(S^5\ge32\).
For v, the same calculation gives
\[
 Q_v'''=-\frac{19}{100}-\frac{7177}{4800S^4}+\frac{217}{24S^5}
 \le-\frac{23}{25600}<\frac1{1024}.
 \tag{4}
\]
The largest polynomial in these derivative identities has degree five in S;
no expanded common numerator of F is used.

The single logarithm majorant has
\[
 \ell'''(y)=\frac{16(3y^2-6y+11)}{(1+y)^6}
 =\frac{16(3(y-1)^2+8)}{(1+y)^6}.
\]
For \(4/7\le y\le5/7\),
\[
 \ell'''(y)\ge128(7/12)^6>5,
 \qquad128\cdot7^6-5\cdot12^6=129152>0.
\]
The numerator has three monomials and degree two; the square completion has
three monomials. Therefore both endpoint functions satisfy
\[
 F_u'''<\frac1{1024}-\frac7{96}\Bigl(\frac27\Bigr)^3\!5
 =\frac1{1024}-\frac5{588}<0.
 \tag{5}
\]
Their derivatives are concave, and their initial derivatives are positive:
\[
 F_f'(1)=\frac{45435}{7496192}>0,
 \qquad F_v'(1)=\frac{201429457}{42166080000}>0.
 \tag{6}
\]
A concave derivative that is positive at the left endpoint can change from
positive to negative at most once. Thus the function's minimum is at an
endpoint. The required values are
\[
\begin{aligned}
 F_f(1)&=\frac{1522747}{1064800000}>\frac1{1000},&
 F_f(3/2)&=\frac{10344481}{3110400000}>\frac1{1000},\\
 F_v(1)&=\frac{6339407}{2395800000}>\frac1{1000},&
 F_v(3/2)&=\frac{344633}{97200000}>\frac1{1000}.
\end{aligned}
\tag{7}
\]
All these are scalar substitutions in the displayed six-term formulas and the
single cubic logarithm majorant. No coefficient list is used as a sign premise.

## 2. A source interface for the upper-shape face a=x

Put
\[
 \beta=x+\frac8{17}(x-1),\quad
 F_u^*(x)=F_1(x,x,\beta,u),\quad
 y_*(x)=\frac{4(21x-4)}{119x},\quad L=21x-4.
\]
For this face, write
\[
 Q_u^*(x)=F_u^*(x)+\frac7{96}\ell(y_*(x))
 =\mathcal G_u(x)+\mathcal T_u(x).
 \tag{8}
\]
Here \(\mathcal G_u=\Gamma_*\), while the transport part is exactly
\[
 \mathcal T_u=-\frac7{96}
 \left[\frac67+(u-1)\frac Ba-E_L+\frac{a(7w-17/4)}B\right]-g
 \quad(a=x).
 \tag{9}
\]
Keep these two source contributions separate. Their complete formulas are:
\[
\begin{aligned}
\mathcal G_f(x)={}&\frac{43}{192} - \frac{49}{576 (x + 1)^{2}}\\
&{}- \frac{7}{288 (x + 1)} - \frac{x}{128}\\
&{}- \frac{x^{2}}{256} - \frac{1}{9216 x^{4}}\\
&{}+ \frac{1}{1536 x^{3}} + \frac{7}{1152 x}\\
&{}+ \frac{19}{9216 x^{2}}
\end{aligned}
\]

\[
\begin{aligned}
\mathcal T_f(x)={}&- \frac{219677081}{999600000} - \frac{188819}{602112 (21 x - 4)}\\
&{}- \frac{25}{3072 x^{2}} - \frac{7}{96 (x + 1)}\\
&{}+ \frac{25 x}{2688} + \frac{9751}{208896 x}
\end{aligned}
\]

\[
\begin{aligned}
\mathcal G_v(x)={}&\frac{563}{2500} - \frac{49}{576 (x + 1)^{2}}\\
&{}- \frac{9 x}{1250} - \frac{9 x^{2}}{2500}\\
&{}- \frac{7}{288 (x + 1)} - \frac{1}{10000 x^{4}}\\
&{}+ \frac{19}{30000 x^{3}} + \frac{707}{360000 x^{2}}\\
&{}+ \frac{943}{180000 x}
\end{aligned}
\]

\[
\begin{aligned}
\mathcal T_v(x)={}&- \frac{1326778111}{5997600000} - \frac{69479}{225792 (21 x - 4)}\\
&{}- \frac{7}{96 (x + 1)} - \frac{1}{128 x^{2}}\\
&{}+ \frac{x}{112} + \frac{1249}{26112 x}
\end{aligned}
\]

Each Casimir identity in (8) has nine monomials and degree eight after
clearing a denominator proportional to \(x^4S^2\). Each transport identity
has six monomials and degree five after clearing a denominator proportional
to \(x^2SL\). The largest coefficient before collecting the displayed
partial-fraction terms is 147622998432, twelve digits.

Adding these verified rational functions is a generic addition step. Do not
expand their joint denominator: the resulting global numerator would have
degree nine. The subsequent derivative argument retains the printed reciprocal
powers as separate terms.

## 3. Concavity of the upper-shape x-functions

The chain rule and the two logarithm derivative bounds in the beta note give
\[
 (F_u^*)''\le (Q_u^*)''+
 \frac7{96}\left(\frac{441}{L^2}-\frac1{x^2}\right).
 \tag{10}
\]
In detail, \(y_*'>0\) and \(y_*''<0\), so use
\(\ell''(y_*)\ge-1/y_*^2\) and \(\ell'(y_*)\le1/y_*\)
separately. The resulting correction is \(-(7/96)(\log y_*)''\), with the
small rational expression printed in (10).

The common negative S-terms in \((Q_u^*)''\) are
\(-7/(36S^3)-49/(96S^4)\). Put \(v=(x-1)/(2x)\in[0,1/6]\), so
\(S=2x(1-v)\). Two elementary reciprocal bounds give
\[
 \frac1{S^3}\ge\frac{1+3v}{8x^3},\qquad
 \frac1{S^4}\ge\frac{1+4v}{16x^4}.
 \tag{11}
\]
Their complete polynomial verification is
\[
\begin{aligned}
 1-(1-v)^3(1+3v)&=6v^2-8v^3+3v^4
                =v^2(6-8v+3v^2)\ge0,\\
 1-(1-v)^4(1+4v)&=10v^2-20v^3+15v^4-4v^5
                =v^2(10-20v+15v^2-4v^3)\ge0.
\end{aligned}
\tag{12}
\]
These identities have three and four monomials, of degrees four and five.
For the second sign, its bracket is at least \(10-20/6-4/6^3>0\);
the first bracket is at least \(6-8/6>0\).

Also discard the negative term \(-20h_u/x^6\) from \((Q_u^*)''\), where
\(h_f=1/9216\), \(h_v=1/10000\). Cancel these exact S- and x-terms before
clearing any denominator. Combining (10)--(12) gives the explicit upper bound
\[
\begin{aligned}
 (F_u^*)''\le\mathcal J_u(x):={}&(Q_u^*)''+
 \frac7{96}\left(\frac{441}{L^2}-\frac1{x^2}\right)
 +\frac7{36S^3}+\frac{49}{96S^4}+\frac{20h_u}{x^6}\\
 &-\frac7{288x^3}-\frac{49}{1536x^4}
 -\frac{7(x-1)}{192x^4}-\frac{49(x-1)}{768x^5}.
\end{aligned}
\tag{13}
\]
After the stipulated cancellations, every remaining term has denominator
proportional to \(x^5L^3\). With \(z=x-1\), the exact identities are
\[
 \mathcal J_f(x)=\frac{J_f(z)}{39168x^5L^3},\qquad
 \mathcal J_v(x)=\frac{J_v(z)}{48960000x^5L^3}.
 \tag{14}
\]
\[
\begin{aligned}
J_f(z)={}&- 2833866 z^{8} - 21051576 z^{7} - 68321232 z^{6}\\
&{}- 111047670 z^{5} - 115723008 z^{4} - 92967711 z^{3}\\
&{}- 51692869 z^{2} - 14306231 z -981733
\end{aligned}
\]
This polynomial has 9 monomials, degree 8, and largest coefficient 115723008.

\[
\begin{aligned}
J_v(z)={}&- 3264613632 z^{8} - 24251415552 z^{7} - 78706059264 z^{6}\\
&{}- 125869777704 z^{5} - 127164509397 z^{4} - 98815009962 z^{3}\\
&{}- 52733277704 z^{2} - 13104619966 z -396097331
\end{aligned}
\]
This polynomial has 9 monomials, degree 8, and largest coefficient 127164509397.

Both polynomials have only negative coefficients. Thus both upper-shape
functions are strictly concave in x. The identities (13)--(14) have degree at
most eight even before collecting their separate rational contributions.
For f, the common source denominator is eight times the primitive denominator
in (14); retain that scalar until coefficient collection. The largest individual
coefficient before collection or the shift to z is 486476760000, twelve digits.

## 4. Explicit scalar endpoints without a large common denominator

At x=1 these functions equal the corresponding lower-shape functions, already
bounded in (7). At x=3/2,
\[
 y_*=220/357,\qquad (y_*-1)/(y_*+1)=-137/577.
\]
Adding like reciprocal terms in (8), then substituting the endpoint, expresses
the full F value as a sum of the following twelve scalar fractions. Their order
is immaterial; the logarithm contributes the last two positive terms.
\[
\begin{aligned}
F_f^*(3/2)={}&\frac{1397223}{333200000} - \frac{188819}{16558080}\\
&{}- \frac{49}{3600} - \frac{7}{180}\\
&{}- \frac{7}{2592} - \frac{9}{1024}\\
&{}- \frac{1}{46656} + \frac{1}{448}\\
&{}+ \frac{1}{5184} + \frac{33061}{940032}\\
&{}+ \frac{959}{27696} + \frac{17999471}{27662404752}
\end{aligned}
\]

Downward rounding these twelve terms, in the displayed order, gives
\[
 F_f^*(3/2)\ge\frac{419 -1141 -1362 -3889 -271 -879 -3 +223 +19 +3517 +3462 +60}{100000}=\frac{155}{100000}>\frac1{1000}.
\]

\[
\begin{aligned}
F_v^*(3/2)={}&\frac{23881409}{5997600000} - \frac{69479}{6209280}\\
&{}- \frac{4211}{1620000} - \frac{49}{3600}\\
&{}- \frac{81}{10000} - \frac{7}{180}\\
&{}- \frac{1}{50625} + \frac{19}{101250}\\
&{}+ \frac{363}{140000} + \frac{2598371}{73440000}\\
&{}+ \frac{959}{27696} + \frac{17999471}{27662404752}
\end{aligned}
\]

Downward rounding these twelve terms, in the displayed order, gives
\[
 F_v^*(3/2)\ge\frac{390 -1119 -260 -1362 -810 -3889 -2 +18 +259 +3538 +3462 +60}{100000}=\frac{285}{100000}>\frac1{1000}.
\]

A term rounded on a 1/10000 grid is written with a multiple of ten in the
common 1/100000 numerator. In particular, the last term is bounded below by
\(6/10000\); the constant \(23881409/5997600000\) is bounded below by
\(39/10000\). Every other term is rounded directly on the 1/100000 grid.
The largest integer in any of these individual scalar comparisons is
259837100000. Thus neither endpoint needs its much larger fully collected
rational numerator or denominator.

Concavity in x now gives \(F_u^*(x)\ge1/1000\) on the entire interval.
Together with Section 1, this proves both shape endpoint bounds. The shape
concavity of the preceding note and norm concavity of the beta note prove (1).

## 5. Exact original caller and budget

The original caller is Section 2, row S, of
[MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN](../../archive/notes/MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN.md).
That row has \(1\le x\le3/2\), \(1\le a\le x\),
\(8/17\le C\le10/13\), \(\beta=x+C(a-1)\), and original incoming endpoints
\(u_f,u_v\). The beta note proves that both endpoints, and the whole actual
incoming interval between them, are contained in \([3/4,19/25]\).
Therefore (2) proves both of the caller's original inequalities \(F_0>0\) and
\(F_1>0\), throughout its unchanged S domain. There is no weakened conclusion
at this caller; the quantified slope loss is absorbed by the explicit terminal
margin before returning to it.

The original logarithm majorant, cap coefficient c, and target g are unchanged.
No arctangent or square-root bound is introduced. No new interval split is
needed. The largest two-variable sign certificate in the three-note proof has
37 monomials and degree eight; the largest final univariate identity has nine
monomials and degree eight. Every source expansion, including individual
contributions before cancellation, stays within twelve-digit coefficients.
The largest audited coefficient is 486476760000.

This is a hand-proof replacement only. It does not claim a new Lean theorem,
a Lean kernel check, or a measured improvement in Lean memory or runtime.
