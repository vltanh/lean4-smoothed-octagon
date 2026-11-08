# Outer-ratio lower terminal: complete small algebra

This supplies all polynomial data for
[the lower-shape terminal proof](SHORT_RATIO_OUTER_TERMINAL_AF.md).
Use its variables r,t=1-r and its interval
\[
3/4\le r\le49/60,\qquad 11/60\le t\le1/4.
\]
Write `n_-=49/20`, `n_+=63/25`. A subscript l denotes n_- and h denotes
n_+. All derivatives of source functions below are in r; derivatives
of the displayed P,J,K,T polynomials are in t.

## 1. Complete component source identities

The following table gives positive denominators for the identities
`A_n=A^s/D_A`, `L_n=L^s/D_L`, `Q_n=Q^s/D_Q`.
The numerators are printed immediately after it.

| Numerator | Corresponding denominator |
|---|---|
| A_l^s | $60197437440 r^{2}$ |
| L_l^s | $80263249920 r^{2}$ |
| Q_l^s | $887040 r + 6773760$ |
| A_h^s | $8360755200 r^{2}$ |
| L_h^s | $11147673600 r^{2}$ |
| Q_h^s | $123200 r + 940800$ |

\[
\begin{aligned}
A_l^s(r)={}&10553281375 r^{6} - 103680325518 r^{5} + 332580904767 r^{4}\\
&{}+- 411951691728 r^{3} - 142211039040 r^{2} + 377902651392 r\\
&{}+53258010624
\end{aligned}
\]

\[
\begin{aligned}
L_l^s(r)={}&8904843871 r^{6} - 62623679118 r^{5} + 267084640575 r^{4}\\
&{}+- 350015430096 r^{3} + 204186495168 r^{2} - 60228790272 r\\
&{}+-12290310144
\end{aligned}
\]

\[
\begin{aligned}
Q_l^s(r)={}&250523 r^{5} - 1486275 r^{4} + 2522154 r^{3}\\
&{}+- 8748306 r^{2} + 6114096 r + 1016064
\end{aligned}
\]

\[
\begin{aligned}
A_h^s(r)={}&1507611625 r^{6} - 14811475074 r^{5} + 47383333641 r^{4}\\
&{}+- 58001053104 r^{3} - 21418395840 r^{2} + 53324199936 r\\
&{}+7608287232
\end{aligned}
\]

\[
\begin{aligned}
L_h^s(r)={}&1272120553 r^{6} - 8946239874 r^{5} + 38058322185 r^{4}\\
&{}+- 49565800368 r^{3} + 28885149504 r^{2} - 8489650176 r\\
&{}+-1755758592
\end{aligned}
\]

\[
\begin{aligned}
Q_h^s(r)={}&35789 r^{5} - 212325 r^{4} + 358662 r^{3}\\
&{}+- 1249758 r^{2} + 863568 r + 145152
\end{aligned}
\]


These identities follow directly from (7)--(10) of the terminal note.
The five pieces in the full expression (9) are kept separate.

## 2. Component inequalities and their positive multipliers

Set
\[
K=504+2493r-2261r^2,\qquad J=504+3645r-1109r^2.
\]
Both are positive on the interval. The following mappings mean
`D times the listed quantity = the named polynomial in t`.
Each derivative is taken before clearing its denominator.

| Polynomial | Quantity | Positive D |
|---|---|---|
| P_0 | A_{n_+} | 8360755200r² |
| P_1 | 5-A_{n_-} | 60197437440r² |
| P_2 | 17+A'_{n_+} | 4180377600r³ |
| P_3 | -A'_{n_-} | 30098718720r³ |
| P_4 | 53-A''_{n_+} | 1393459200r⁴ |
| P_5 | -1-L''_{n_-} | 13377208320r⁴ |
| P_6 | -1-L''_{n_+} | 1857945600r⁴ |
| P_7 | -17/10-Q''_{n_-} | 13440(11r+84)³ |
| P_8 | -17/10-Q''_{n_+} | 5600(11r+84)³ |
| J_0 | -partial_n A_n | 21069103104r² |
| J_1 | -partial_n A'_n | 10534551552r³ |
| J_2 | partial_n A''_n | 3511517184r⁴ |
| K_0 | 11/400-F | (400/3)K |
| K_1 | F'-7/500 | 500K² |
| K_2 | 1/50-F' | 50K² |
| K_3 | 1/12-F'' | 12K³ |
| T | 7/20-[1/Z+log(2Z/7)]'' | 20r²J³ |

F and Z are the explicit functions in the terminal note. The three
partial-n quantities are independent of n because A_n is affine in n.
All clearing factors in the table are positive.

## 3. Full polynomials

\[
\begin{aligned}
P_0(t)={}&1507611625 t^{6} + 5765805324 t^{5} - 4059867354 t^{4}\\
&{}+- 13569763220 t^{3} - 36622129671 t^{2} + 38994122112 t\\
&{}+15592508416
\end{aligned}
\]

\[
\begin{aligned}
P_1(t)={}&- 10553281375 t^{6} - 40360637268 t^{5} + 27521502198 t^{4}\\
&{}+92634299660 t^{3} + 562071907377 t^{2} - 869107196544 t\\
&{}+184535395328
\end{aligned}
\]

\[
\begin{aligned}
P_2(t)={}&3015223250 t^{6} + 4125873111 t^{5} - 18474380664 t^{4}\\
&{}+- 69731566102 t^{3} + 233553902430 t^{2} - 196074188985 t\\
&{}+35976849728
\end{aligned}
\]

\[
\begin{aligned}
P_3(t)={}&- 21106562750 t^{6} - 28881111777 t^{5} + 128423095368 t^{4}\\
&{}+- 8725854566 t^{3} - 138951449490 t^{2} - 127518309105 t\\
&{}+250018202944
\end{aligned}
\]

\[
\begin{aligned}
P_4(t)={}&- 3015223250 t^{6} + 3279864426 t^{5} + 86887919673 t^{4}\\
&{}+- 320045857952 t^{3} + 451239760308 t^{2} - 270426874770 t\\
&{}+44472124333
\end{aligned}
\]

\[
\begin{aligned}
P_5(t)={}&- 17809687742 t^{6} + 44234447334 t^{5} - 56432342385 t^{4}\\
&{}+139578651040 t^{3} - 255341056020 t^{2} + 183285154818 t\\
&{}+-25224856901
\end{aligned}
\]

\[
\begin{aligned}
P_6(t)={}&- 2544241106 t^{6} + 6319206762 t^{5} - 7976470215 t^{4}\\
&{}+19598635360 t^{3} - 35965535820 t^{2} + 25880575854 t\\
&{}+-3556412243
\end{aligned}
\]

\[
\begin{aligned}
P_7(t)={}&60626566 t^{5} - 1280709815 t^{4} + 6878830526 t^{3}\\
&{}+4388662940 t^{2} - 1477681300 t + 306346123
\end{aligned}
\]

\[
\begin{aligned}
P_8(t)={}&25982814 t^{5} - 548875635 t^{4} + 2947509062 t^{3}\\
&{}+1895394780 t^{2} - 758858100 t + 394970887
\end{aligned}
\]

\[
\begin{aligned}
J_0(t)={}&- 1507611625 t^{6} - 5765805324 t^{5} + 8547713754 t^{4}\\
&{}+25339977620 t^{3} + 12973067271 t^{2} - 68124285312 t\\
&{}+20928656384
\end{aligned}
\]

\[
\begin{aligned}
J_1(t)={}&- 3015223250 t^{6} - 4125873111 t^{5} + 22962227064 t^{4}\\
&{}+- 4425438698 t^{3} - 38009966430 t^{2} + 21089075385 t\\
&{}+13133486272
\end{aligned}
\]

\[
\begin{aligned}
J_2(t)={}&3015223250 t^{6} - 3279864426 t^{5} - 14530530873 t^{4}\\
&{}+30616302752 t^{3} - 17095427508 t^{2} - 11280594030 t\\
&{}+20163178067
\end{aligned}
\]

\[
\begin{aligned}
K_0(t)={}&- 157 t^{2} + 2373 t - 368
\end{aligned}
\]

\[
\begin{aligned}
K_1(t)={}&- 35784847 t^{4} + 64225966 t^{3} + 13404957 t^{2}\\
&{}+- 28013816 t + 5557628
\end{aligned}
\]

\[
\begin{aligned}
K_2(t)={}&5112121 t^{4} - 9175138 t^{3} - 1103901 t^{2}\\
&{}+3697388 t - 393254
\end{aligned}
\]

\[
\begin{aligned}
K_3(t)={}&- 11558505581 t^{6} + 31117480527 t^{5} - 16636969335 t^{4}\\
&{}+- 9851687651 t^{3} + 4258698216 t^{2} + 6341351160 t\\
&{}+-637416296
\end{aligned}
\]

\[
\begin{aligned}
T(t)={}&- 9547566203 t^{8} - 17760711521 t^{7} + 67976898030 t^{6}\\
&{}+213366437074 t^{5} - 699019209839 t^{4} + 272508170139 t^{3}\\
&{}+709452628300 t^{2} - 658787691740 t + 119250564480
\end{aligned}
\]


## 4. Explicit sign mechanisms

For a printed univariate polynomial `p(t)=sum c_i t^i`, on this interval
one may bound a positive term below by `c_i(11/60)^i` and a negative
term below by `c_i/4^i`. Applying this termwise rule directly proves
\[
P_0,P_3,P_7,P_8,J_0,J_1,J_2,K_0,K_2,K_3>0.
\tag{1}
\]
Every coefficient used in this operation is in Section 3. The resulting
scalar bounds are all positive, including K_0>57 and K_2>78000.

The remaining P and K signs use monotonicity. The following small
normalized derivative identities are complete; each positive scalar
normalization is applied before expanding the derivative.

For `P_1`,

\[
\frac1{6}P_1'(t)=D_{P_1}(t).
\]

\[
\begin{aligned}
D_{P_1}(t)={}&- 10553281375 t^{5} - 33633864390 t^{4} + 18347668132 t^{3}\\
&{}+46317149830 t^{2} + 187357302459 t - 144851199424
\end{aligned}
\]

For `P_2`,

\[
\frac1{3}P_2'(t)=D_{P_2}(t).
\]

\[
\begin{aligned}
D_{P_2}(t)={}&6030446500 t^{5} + 6876455185 t^{4} - 24632507552 t^{3}\\
&{}+- 69731566102 t^{2} + 155702601620 t - 65358062995
\end{aligned}
\]

For `P_4`,

\[
\frac1{6}P_4'(t)=D_{P_4}(t).
\]

\[
\begin{aligned}
D_{P_4}(t)={}&- 3015223250 t^{5} + 2733220355 t^{4} + 57925279782 t^{3}\\
&{}+- 160022928976 t^{2} + 150413253436 t - 45071145795
\end{aligned}
\]

For `P_5`,

\[
\frac1{6}P_5'(t)=D_{P_5}(t).
\]

\[
\begin{aligned}
D_{P_5}(t)={}&- 17809687742 t^{5} + 36862039445 t^{4} - 37621561590 t^{3}\\
&{}+69789325520 t^{2} - 85113685340 t + 30547525803
\end{aligned}
\]

For `P_6`,

\[
\frac1{6}P_6'(t)=D_{P_6}(t).
\]

\[
\begin{aligned}
D_{P_6}(t)={}&- 2544241106 t^{5} + 5266005635 t^{4} - 5317646810 t^{3}\\
&{}+9799317680 t^{2} - 11988511940 t + 4313429309
\end{aligned}
\]

For `K_1`,

\[
\frac1{2}K_1'(t)=D_{K_1}(t).
\]

\[
\begin{aligned}
D_{K_1}(t)={}&- 71569694 t^{3} + 96338949 t^{2} + 13404957 t\\
&{}+-14006908
\end{aligned}
\]


The same monomial rule gives
\[
D_{P_1},D_{P_2},D_{P_4},D_{K_1}<0,
\qquad D_{P_5},D_{P_6}>0;
\tag{2}
\]
for an upper bound, reverse which interval endpoint is used for each
coefficient sign. Direct substitution in the original polynomials gives
\[
P_1(1/4),P_2(1/4),P_4(1/4)>100000000,
\quad K_1(1/4)>250000,
\]
\[
P_5(11/60)>500000000,
\qquad P_6(11/60)>90000000.
\tag{3}
\]
Equations (2)--(3) prove all six polynomials positive throughout.
These are ordinary degree-six signs and endpoint evaluations; no
external coefficient list is used.

For T, retain its constant, linear, quadratic and cubic terms and
bound the three negative higher powers by multiples of t². Specifically,
\[
\frac{699019209839}{16}+
\frac{17760711521}{1024}+\frac{9547566203}{4096}
<709452628300-665000000000.
\]
This gives
\[
T(t)\ge C_*(t):=
272508170139t^3+665000000000t^2
-658787691740t+119250564480.
\tag{4}
\]
For `0<=t<=s=1/4`, the degree-two and degree-three power-difference
identities give
\[
\begin{aligned}
C_*(t)-C_*(s)
&=(s-t)\{658787691740-665000000000(t+s)\\
&\hspace{32mm}-272508170139(t^2+ts+s^2)\}\\
&\ge(s-t)\{658787691740-665000000000/2
-3(272508170139)/16\}\ge0.
\end{aligned}
\]
The last bracket exceeds 270000000000. Also
\[
C_*(1/4)=23941229019/64>370000000.
\]
Thus T>0. This uses a cubic comparison, without expanding a large
unnormalized derivative of the degree-eight T.

## 5. Scalar endpoint checks

All derivative bounds at r_0=84/103 in equation (18) of the terminal
proof follow by substituting that rational value in the six source
polynomials of Section 1 and in (11) of the terminal proof. The
quantities are separate rational functions; their common denominator
is never expanded.

For completeness, the two terminal-value evaluations have the following
individual upper bounds, each with denominator 1000000. The logarithm
column uses the stated cubic upper bound ell_3.

| Point (n,r) | L_n | V A_n | Q_n | 1/Z | ell_3(2Z/7) | Sum |
|---|---:|---:|---:|---:|---:|---:|
| (63/25,84/103) | -319761 | 32518 | 126521 | 343003 | -182521 | -240 |
| (49/20,42/53) | -357409 | 38311 | 149094 | 338608 | -169678 | -1074 |

Every entry is an upper rounding of an explicit rational value from
Sections 1 and (11) of the terminal proof. Their sums establish the
strict bounds used in (21), with room to spare over 1/5000 and 1/1000.

## 6. Size audit

All complete source numerators have degree at most six in r and at most
seven monomials. Every component sign and normalized derivative is
univariate of degree at most eight and has at most nine monomials.
The largest printed cleared coefficient is 869107196544, in P_1.
Positive scalar factors are kept outside before expanding derivatives;
the separate source contributions obey the same twelve-digit boundary.
