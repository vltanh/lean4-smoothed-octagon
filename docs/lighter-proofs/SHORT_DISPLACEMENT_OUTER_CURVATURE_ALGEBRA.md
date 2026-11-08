# Outer displacement: source coefficients and curvature algebra

This is the complete algebra used in
[reciprocal convexity](SHORT_DISPLACEMENT_OUTER_RECIPROCAL.md).
All source comparisons are in one polynomial coefficient at a time.

## 1. All source coefficients

For `i=0,...,4` define the coefficient functions by
\[
49A_i=n\alpha_i+\beta_i,\qquad
49S B_i=n\gamma_i+\delta_i.
\tag{1}
\]
The scalar n is outside each polynomial; dependence on n is affine.
The four coefficient polynomials for every i are printed below.
Each has degree at most four in x,C. Matching the five r coefficients
of the source quartic proves (5) of the reciprocal note. In particular,
no combined r,x,C polynomial is expanded.

\[
\begin{aligned}
\alpha_{0}={}&x\bigl(- 12 C - 6\bigr)\\
&+\bigl(4 C^{2} - 8 C - 5\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\beta_{0}={}&x\bigl(42\bigr)\\
&+\bigl(21 C + 77\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\gamma_{0}={}&x^{2}\bigl(12 C + 6\bigr)\\
&+x\bigl(24 C + \frac{45}{4}\bigr)\\
&+\bigl(- \frac{3}{4}\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\delta_{0}={}&x^{2}\bigl(-42\bigr)\\
&+x\bigl(- 49 C - \frac{707497}{180000}\bigr)\\
&+\bigl(- 49 C + \frac{14412503}{180000}\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\alpha_{1}={}&x^{2}\bigl(12 C - 12\bigr)\\
&+x\bigl(- 8 C^{2} + 28 C - 8\bigr)\\
&+\bigl(- 8 C^{2} + 8 C\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\beta_{1}={}&x\bigl(28 C + 21\bigr)\\
&+\bigl(- 21 C\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\gamma_{1}={}&x^{3}\bigl(- 12 C + 12\bigr)\\
&+x^{2}\bigl(- 36 C + 24\bigr)\\
&+x\bigl(- 24 C\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\delta_{1}={}&x^{2}\bigl(-49\bigr)\\
&+x\bigl(49 C - 49\bigr)\\
&+\bigl(49 C\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\alpha_{2}={}&x^{3}\bigl(12\bigr)\\
&+x^{2}\bigl(4 C^{2} - 28 C\bigr)\\
&+x\bigl(16 C^{2} - 10 C - 15\bigr)\\
&+\bigl(4 C^{2} + 2 C - 5\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\beta_{2}={}&x^{2}\bigl(28\bigr)\\
&+x\bigl(- 28 C - 21\bigr)\\
&+\bigl(-7\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\gamma_{2}={}&x^{4}\bigl(-12\bigr)\\
&+x^{3}\bigl(12 C - 12\bigr)\\
&+x^{2}\bigl(22 C + 23\bigr)\\
&+x\bigl(- 2 C + 11\bigr)\\
&+\bigl(- 2 C + 5\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\delta_{2}={}&x^{2}\bigl(7\bigr)\\
&+x\bigl(7\bigr)\\
&+\bigl(7\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\alpha_{3}={}&x^{3}\bigl(8 C - 8\bigr)\\
&+x^{2}\bigl(- 8 C^{2} + 10 C + 6\bigr)\\
&+x\bigl(- 8 C^{2} - 8 C + 2\bigr)\\
&+\bigl(- 2 C\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\beta_{3}={}&\bigl(0\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\gamma_{3}={}&x^{3}\bigl(2 C - 2\bigr)\\
&+x^{2}\bigl(4 C - 2\bigr)\\
&+x\bigl(4 C - 2\bigr)\\
&+\bigl(2 C\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\delta_{3}={}&\bigl(0\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\alpha_{4}={}&x^{4}\bigl(4\bigr)\\
&+x^{3}\bigl(- 8 C - 6\bigr)\\
&+x^{2}\bigl(4 C^{2} + 6 C\bigr)\\
&+x\bigl(2 C + 1\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\beta_{4}={}&\bigl(0\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\gamma_{4}={}&x^{4}\bigl(2\bigr)\\
&+x^{3}\bigl(- 2 C + 1\bigr)\\
&+x^{2}\bigl(- 2 C + 1\bigr)\\
&+x\bigl(- 2 C - 1\bigr)
\end{aligned}
\]

\[
\begin{aligned}
\delta_{4}={}&\bigl(0\bigr)
\end{aligned}
\]


## 2. Boundary identities

Set `h=x-2`, `v=C-3/5`; then `0<=h<=1/6`, `0<=v<=7/30`.
The subscripts ell and h below denote the two scalar multipliers
`n_ell=5/2` and `n_h=7/2`.

The common third-derivative and quadratic-slope identities are
\[
P_n^{(3)}(1/x)=\frac{3n(x-1)}{1225S}T(h,v),\qquad
A_3+4A_4/x=\frac{2n}{1225}B(h,v).
\tag{2}
\]
The other positive clearing factors are as follows. Each row means
`D times the quantity = the named polynomial`.

| Polynomial | Quantity | Positive D |
|---|---|---|
| V_ell | P''_{5/2}(1/x)-2/5 | 980xS |
| V_h | P''_{7/2}(1/x)-2/5 | 700xS |
| E_ell | A''_{5/2}(1/x)+1 | 245x |
| E_h | A''_{7/2}(1/x)+1 | 175x |
| F_ell | A''_{5/2}(7/8)+1 | 7840 |
| F_h | A''_{7/2}(7/8)+1 | 5600 |
| G_ell | A'_{5/2}(1/x)-1 | 245x² |
| G_h | A'_{7/2}(1/x)-1 | 35x² |
| H_ell | 5-A_{5/2}(7/8) | 2007040 |
| H_h | 5-A_{7/2}(7/8) | 1433600 |

## 3. Complete polynomials and their elementary lower bounds

Beside each full polynomial Q(h,v), the displayed univariate
underline Q(h) is a lower bound. It follows one monomial at a time:
keep the v^0 terms; discard positive terms containing v; replace
`-c h^i v^j` by `-c h^i(7/30)^j` for c>0 and j>0.
These are inequalities between the printed polynomials, with no
coefficient-table premise.

For every displayed lower polynomial, discard its positive powers of h
and replace each negative power contribution `-c h^i` by `-c/6^i`.
The resulting scalar is greater than 1 (the smallest occurs for B).
This proves every polynomial in (2) and the mapping above is positive.
The polynomials themselves are small enough for the indicated arithmetic
without any external data.

### Polynomial `T`

\[
\begin{aligned}
T(h,v)={}&h^{3}\bigl(300 v + 480\bigr)\\
&+h^{2}\bigl(- 300 v^{2} + 1315 v + 2922\bigr)\\
&+h\bigl(- 1500 v^{2} + 750 v + 5215\bigr)\\
&+\bigl(- 1800 v^{2} - 1285 v + 2677\bigr)
\end{aligned}
\]

\[
\underline{T}(h)=480 h^{3} + \frac{8717 h^{2}}{3} + \frac{15400 h}{3} + \frac{13675}{6}.
\]

### Polynomial `V_l`

\[
\begin{aligned}
V_{\ell}(h,v)={}&h^{5}\bigl(-300\bigr)\\
&+h^{4}\bigl(300 v^{2} + 1260 v - 1812\bigr)\\
&+h^{3}\bigl(2100 v^{2} + 9280 v - 1953\bigr)\\
&+h^{2}\bigl(5100 v^{2} + 22990 v + 4156\bigr)\\
&+h\bigl(5100 v^{2} + 22580 v + 7667\bigr)\\
&+\bigl(1800 v^{2} + 7130 v + 2238\bigr)
\end{aligned}
\]

\[
\underline{V_{\ell}}(h)=- 300 h^{5} - 1812 h^{4} - 1953 h^{3} + 4156 h^{2} + 7667 h + 2238.
\]

### Polynomial `V_h`

\[
\begin{aligned}
V_{h}(h,v)={}&h^{5}\bigl(-300\bigr)\\
&+h^{4}\bigl(300 v^{2} + 1260 v - 2052\bigr)\\
&+h^{3}\bigl(2100 v^{2} + 9520 v - 3869\bigr)\\
&+h^{2}\bigl(5100 v^{2} + 24670 v - 1164\bigr)\\
&+h\bigl(5100 v^{2} + 26420 v + 1791\bigr)\\
&+\bigl(1800 v^{2} + 10010 v + 278\bigr)
\end{aligned}
\]

\[
\underline{V_{h}}(h)=- 300 h^{5} - 2052 h^{4} - 3869 h^{3} - 1164 h^{2} + 1791 h + 278.
\]

### Polynomial `B`

\[
\begin{aligned}
B(h,v)={}&h^{3}\bigl(100 v + 160\bigr)\\
&+h^{2}\bigl(- 100 v^{2} + 205 v + 534\bigr)\\
&+h\bigl(- 300 v^{2} - 60 v + 397\bigr)\\
&+\bigl(- 200 v^{2} - 65 v + 33\bigr)
\end{aligned}
\]

\[
\underline{B}(h)=160 h^{3} + \frac{4757 h^{2}}{9} + \frac{1100 h}{3} + \frac{125}{18}.
\]

### Polynomial `E_l`

\[
\begin{aligned}
E_{\ell}(h,v)={}&h^{4}\bigl(300\bigr)\\
&+h^{3}\bigl(100 v^{2} + 20 v + 2656\bigr)\\
&+h^{2}\bigl(400 v^{2} - 1100 v + 7041\bigr)\\
&+h\bigl(500 v^{2} - 4170 v + 6338\bigr)\\
&+\bigl(200 v^{2} - 3630 v + 1200\bigr)
\end{aligned}
\]

\[
\underline{E_{\ell}}(h)=300 h^{4} + 2656 h^{3} + \frac{20353 h^{2}}{3} + 5365 h + 353.
\]

### Polynomial `F_l`

\[
\begin{aligned}
F_{\ell}(h,v)={}&h^{4}\bigl(14700\bigr)\\
&+h^{3}\bigl(- 12600 v + 80790\bigr)\\
&+h^{2}\bigl(1100 v^{2} - 53630 v + 166286\bigr)\\
&+h\bigl(400 v^{2} - 94530 v + 137933\bigr)\\
&+\bigl(- 400 v^{2} - 74100 v + 23034\bigr)
\end{aligned}
\]

\[
\underline{F_{\ell}}(h)=14700 h^{4} + 77850 h^{3} + \frac{461317 h^{2}}{3} + 115876 h + \frac{51500}{9}.
\]

### Polynomial `G_l`

\[
\begin{aligned}
G_{\ell}(h,v)={}&h^{4}\bigl(150 v + 240\bigr)\\
&+h^{3}\bigl(1290 v + 2159\bigr)\\
&+h^{2}\bigl(3580 v + 5953\bigr)\\
&+h\bigl(3690 v + 5494\bigr)\\
&+\bigl(1005 v + 673\bigr)
\end{aligned}
\]

\[
\underline{G_{\ell}}(h)=240 h^{4} + 2159 h^{3} + 5953 h^{2} + 5494 h + 673.
\]

### Polynomial `H_l`

\[
\begin{aligned}
H_{\ell}(h,v)={}&h^{4}\bigl(-240100\bigr)\\
&+h^{3}\bigl(- 68600 v - 1993810\bigr)\\
&+h^{2}\bigl(- 4900 v^{2} - 343630 v - 6372394\bigr)\\
&+h\bigl(- 8400 v^{2} - 730570 v - 8863063\bigr)\\
&+\bigl(- 3600 v^{2} - 667820 v + 3642234\bigr)
\end{aligned}
\]

\[
\underline{H_{\ell}}(h)=- 240100 h^{4} - \frac{6029450 h^{3}}{3} - \frac{58075570 h^{2}}{9} - \frac{27101960 h}{3} + \frac{10458640}{3}.
\]

### Polynomial `E_h`

\[
\begin{aligned}
E_{h}(h,v)={}&h^{4}\bigl(300\bigr)\\
&+h^{3}\bigl(100 v^{2} + 20 v + 2576\bigr)\\
&+h^{2}\bigl(400 v^{2} - 1020 v + 6669\bigr)\\
&+h\bigl(500 v^{2} - 3850 v + 5760\bigr)\\
&+\bigl(200 v^{2} - 3310 v + 892\bigr)
\end{aligned}
\]

\[
\underline{E_{h}}(h)=300 h^{4} + 2576 h^{3} + 6431 h^{2} + \frac{14585 h}{3} + \frac{359}{3}.
\]

### Polynomial `F_h`

\[
\begin{aligned}
F_{h}(h,v)={}&h^{4}\bigl(14700\bigr)\\
&+h^{3}\bigl(- 12600 v + 80790\bigr)\\
&+h^{2}\bigl(1100 v^{2} - 53630 v + 163726\bigr)\\
&+h\bigl(400 v^{2} - 91970 v + 131149\bigr)\\
&+\bigl(- 400 v^{2} - 68980 v + 18106\bigr)
\end{aligned}
\]

\[
\underline{F_{h}}(h)=14700 h^{4} + 77850 h^{3} + \frac{453637 h^{2}}{3} + \frac{329068 h}{3} + \frac{17900}{9}.
\]

### Polynomial `G_h`

\[
\begin{aligned}
G_{h}(h,v)={}&h^{4}\bigl(30 v + 48\bigr)\\
&+h^{3}\bigl(250 v + 405\bigr)\\
&+h^{2}\bigl(690 v + 1069\bigr)\\
&+h\bigl(730 v + 938\bigr)\\
&+\bigl(225 v + 85\bigr)
\end{aligned}
\]

\[
\underline{G_{h}}(h)=48 h^{4} + 405 h^{3} + 1069 h^{2} + 938 h + 85.
\]

### Polynomial `H_h`

\[
\begin{aligned}
H_{h}(h,v)={}&h^{4}\bigl(-240100\bigr)\\
&+h^{3}\bigl(- 68600 v - 1993810\bigr)\\
&+h^{2}\bigl(- 4900 v^{2} - 343630 v - 6121514\bigr)\\
&+h\bigl(- 8400 v^{2} - 694730 v - 7319639\bigr)\\
&+\bigl(- 3600 v^{2} - 565420 v + 3715194\bigr)
\end{aligned}
\]

\[
\underline{H_{h}}(h)=- 240100 h^{4} - \frac{6029450 h^{3}}{3} - \frac{55817650 h^{2}}{9} - 7482200 h + \frac{10749200}{3}.
\]


## 4. Size boundary

Each expanded source coefficient has degree at most four in x,C.
The boundary identities have at most sixteen monomials and degree six
in two variables. Every lower polynomial is printed, has at most six
monomials and degree five. All their cleared coefficients have fewer
than twelve digits. Affinity in n is used before the endpoint checks;
it does not introduce a third polynomial variable.
