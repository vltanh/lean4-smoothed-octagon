# Central S1: the two fixed-shape second-test terminals

The [shape proof](SHORT_CENTRAL_SHAPE_F1.md) reduces the second test to a=1 and a=7/6 at u=19/25 and b=x+(10/13)(a−1). This note proves the uniform bound
\[
 \boxed{F_1>1/50000}\qquad(8/5\le x\le2)\tag{1}
\]
on both curves. It uses the exact logarithm while differentiating, and the single shared rational logarithm bound only at the final scalar endpoints.

## 1. Complete rational sources

Write \(F_1=Q_j-(7/96)\log y_j\), where
\[
 y_1=2/(x+1),\qquad
 y_7=\frac{14(78x+101)}{13(36x^2+72x+49)}.
\]
The two rational functions, obtained from the printed central transport formulas, are
\[
Q_1=\frac{157 x^{2}}{5000} - \frac{67703 x}{240000} + \frac{1151533}{1200000} - \frac{119}{500 \left(x + 2\right)} - \frac{49}{625 \left(x + 2\right)^{2}} - \frac{4837}{2400 \left(x + 1\right)} + \frac{2149}{1200 \left(x + 1\right)^{2}} - \frac{119}{200 \left(x + 1\right)^{3}} + \frac{9}{500 x} - \frac{9}{10000 x^{2}} .
\]
\[
Q_7=\frac{33 x^{2}}{1250} - \frac{10013 x}{40000} + \frac{1413329262 x + 4338329093}{85051200 \left(36 x^{2} + 72 x + 49\right)} + \frac{13783429}{15600000} - \frac{761959567}{4252560 \left(78 x + 101\right)} - \frac{119}{500 \left(x + 2\right)} - \frac{49}{625 \left(x + 2\right)^{2}} + \frac{9}{500 x} - \frac{9}{10000 x^{2}} .
\]

These partial fractions are checked one source pole at a time. In particular, the complete Casimir division is
\[
 \Gamma=-9x^2/2500-9x/1250+673/2500+E_*(x).
\]
Its numerator identity has degree six. Subtract this piece first; each remaining identity is the division of the degree-five N by the degree-three V at the stated constant shape. The common four fractions
\[
 E_*(x)=-119/(500(x+2))-49/(625(x+2)^2)+9/(500x)-9/(10000x^2)
\]
come from Gamma. For Q1 the remaining pole is x+1, of order three; for Q7 they are 78x+101 and 36x²+72x+49. Polynomial division and each separate proper-fraction identity use degree at most eight. All numerators are printed; no full high-degree common numerator is expanded.

## 2. Both exact logarithmic derivatives are negative

Set \(D_j=(Q_j-E_*)'-(7/96)(\log y_j)'\).
The logarithmic derivatives are
\[
 (\log y_1)'=-1/(x+1),\qquad
 (\log y_7)'=-\frac{6(468x^2+1212x+575)}{(78x+101)(36x^2+72x+49)}.
\]
With z=x−3/2, the exact small identities are
\[
 -D_1-9/500=P_1(z)/(3840000(x+1)^4),
\]
\[
 -D_7-9/500=P_7(z)/(16250(78x+101)^2(36x^2+72x+49)^2),
\]
where
\[
\begin{aligned}
P_1={}&- 241152 z^{5} - 1759120 z^{4} - 2799200 z^{3}\\
&{}- 446200 z^{2} + 1162600 z + 268975
\end{aligned}
\]
\[
\begin{aligned}
P_7={}&- 6765213312 z^{7} - 85848181614 z^{6} - 393060457764 z^{5}\\
&{}- 781485953859 z^{4} - 534509381250 z^{3} + 229036518774 z^{2}\\
&{}+ 366011607627 z + 64232098925
\end{aligned}
\]

For P1 bound z5≤z²/8, z4≤z²/4, z3≤z²/2, then z²≤z/2. This gives
\(P_1\ge268975+4738z>0\).
For P7 bound each negative power z^m, m≥3, by z²/2^(m−2), then bound any resulting negative z² coefficient by half its coefficient times z. What remains has a positive constant and a z coefficient greater than 220000000000. Thus both Dj<−9/500.

The shared extra derivative is also elementary:
\[
 -E_*''=\frac{2200x^5+5699x^4-4104x^3-5112x^2-2016x+432}{5000x^4(x+2)^4}>0.
\]
Its numerator at x=3/2+z is exactly
\[
 2200z^5+22199z^4+79590z^3+(255213/2)z^2+87570z+281799/16>0.
\]
Hence
\[
 E_*'(x)\le E_*'(8/5)=225937/14929920<2/125,
\]
so both exact terminal derivatives satisfy
\[
 F_1'=D_j+E_*'<-9/500+2/125=-1/500<0.\tag{2}
\]
The largest polynomial here has degree seven, eight terms, and largest coefficient 781485953859.

## 3. Two scalar endpoints close the signs

At x=2 the logarithm arguments are 2/3 and 3598/4381; both are below one. Apply
\[
 L_P(y)=\frac{(y-1)(11y^2+38y+11)}{3(y+1)(y^2+8y+1)}\ge\log y
\]
from [the shared logarithm proof](LOG_BOUND.md).
Substitution in the separate fractions above gives the rational inequalities
\[
 Q_1(2)>-2946695/10^8,\qquad
 -(7/96)L_P(2/3)>2956511/10^8,
\]
\[
 Q_7(2)>-1432747/10^8,\qquad
 -(7/96)L_P(3598/4381)>1435720/10^8.
\]
They can be checked by multiplying positive factors in each displayed fraction and adding the resulting scalar bounds, without combining all source terms into a large polynomial. The two resulting margins exceed 9816/10^8 and 2973/10^8 respectively; each exceeds 1/50000.
Together with (2), this proves (1) on both full terminal intervals. Combined with the shape and norm/beta reductions, it proves the original central F1 sign with a uniform margin greater than 1/50000.
