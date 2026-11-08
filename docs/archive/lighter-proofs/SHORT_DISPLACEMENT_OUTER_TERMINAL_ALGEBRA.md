# Outer displacement: complete terminal algebra

This contains every polynomial used by
[the terminal argument](SHORT_DISPLACEMENT_OUTER_TERMINALS.md).
Write `S=x+1`, `h=x-2`, `v=C-3/5`. On the lower-shape comparison
`0<=h<=1/6`, `0<=v<=7/30`, and `r_*=13/(5S)`.

## 1. Lower-shape beta monotonicity

The subscripts ell and h denote n=5/2 and 7/2. Each row gives the complete
identity `D times the quantity = the named polynomial`.

| Polynomial | Quantity, evaluated at r=r_* | Positive D |
|---|---|---|
| I_ell | (P_{5/2})_C+53/2000 | 490000S⁵ |
| I_h | (P_{7/2})_C+53/2000 | 350000S⁵ |
| J_ell | (A_{5/2})_C | 30625S⁴ |
| J_h | (A_{7/2})_C | 21875S⁴ |
| K_ell | 4-A_{5/2} | 306250S⁴ |
| K_h | 4-A_{7/2} | 218750S⁴ |
| L | 3/4000+U_C | 100000SM[5Cx-8C+13x-13]² |

The derivatives keep r fixed before evaluation. The last bracket is
positive since `C(5x-8)+13(x-1)>0`.

The full polynomials and explicit lower polynomials are printed next.
To obtain each lower polynomial, keep v^0 terms, discard positive terms
containing v, and use `-c h^i v^j>=-c h^i(7/30)^j` for negative terms.
In each displayed lower polynomial, discarding positive powers of h
and replacing negative powers by their values at 1/6 leaves a positive
scalar greater than 1. These short monomial inequalities prove every
sign without an external coefficient table.

### Polynomial `I_l`

\[
\begin{aligned}
I_{\ell}(h,v)={}&h^{6}\bigl(-120000\bigr)\\
&+h^{5}\bigl(384000 v - 317715\bigr)\\
&+h^{4}\bigl(2515200 v + 1351255\bigr)\\
&+h^{3}\bigl(5721840 v + 4993694\bigr)\\
&+h^{2}\bigl(5646480 v + 4409598\bigr)\\
&+h\bigl(2365440 v + 1102949\bigr)\\
&+\bigl(348480 v + 1560683\bigr)
\end{aligned}
\]

\[
\underline{I_{\ell}}(h)=- 120000 h^{6} - 317715 h^{5} + 1351255 h^{4} + 4993694 h^{3} + 4409598 h^{2} + 1102949 h + 1560683.
\]

### Polynomial `J_l`

\[
\begin{aligned}
J_{\ell}(h,v)={}&h^{5}\bigl(30000\bigr)\\
&+h^{4}\bigl(32000 v + 474275\bigr)\\
&+h^{3}\bigl(113600 v + 2128815\bigr)\\
&+h^{2}\bigl(136020 v + 4134982\bigr)\\
&+h\bigl(62480 v + 3510138\bigr)\\
&+\bigl(9680 v + 866868\bigr)
\end{aligned}
\]

\[
\underline{J_{\ell}}(h)=30000 h^{5} + 474275 h^{4} + 2128815 h^{3} + 4134982 h^{2} + 3510138 h + 866868.
\]

### Polynomial `K_l`

\[
\begin{aligned}
K_{\ell}(h,v)={}&h^{5}\bigl(- 300000 v - 1128750\bigr)\\
&+h^{4}\bigl(- 160000 v^{2} - 4742750 v - 15059525\bigr)\\
&+h^{3}\bigl(- 568000 v^{2} - 21288150 v - 65429935\bigr)\\
&+h^{2}\bigl(- 680100 v^{2} - 41349820 v - 116036681\bigr)\\
&+h\bigl(- 312400 v^{2} - 35101380 v - 63325164\bigr)\\
&+\bigl(- 48400 v^{2} - 8668680 v + 20686266\bigr)
\end{aligned}
\]

\[
\underline{K_{\ell}}(h)=- 1198750 h^{5} - \frac{145573900 h^{4}}{9} - \frac{633852850 h^{3}}{9} - 125722000 h^{2} - \frac{643792450 h}{9} + \frac{167948450}{9}.
\]

### Polynomial `I_h`

\[
\begin{aligned}
I_{h}(h,v)={}&h^{6}\bigl(-120000\bigr)\\
&+h^{5}\bigl(384000 v - 382425\bigr)\\
&+h^{4}\bigl(2515200 v + 695205\bigr)\\
&+h^{3}\bigl(5721840 v + 2539394\bigr)\\
&+h^{2}\bigl(5646480 v + 275898\bigr)\\
&+h\bigl(2365440 v - 2079001\bigr)\\
&+\bigl(348480 v + 367553\bigr)
\end{aligned}
\]

\[
\underline{I_{h}}(h)=- 120000 h^{6} - 382425 h^{5} + 695205 h^{4} + 2539394 h^{3} + 275898 h^{2} - 2079001 h + 367553.
\]

### Polynomial `J_h`

\[
\begin{aligned}
J_{h}(h,v)={}&h^{5}\bigl(30000\bigr)\\
&+h^{4}\bigl(32000 v + 457525\bigr)\\
&+h^{3}\bigl(113600 v + 1984365\bigr)\\
&+h^{2}\bigl(136020 v + 3705632\bigr)\\
&+h\bigl(62480 v + 3025188\bigr)\\
&+\bigl(9680 v + 732768\bigr)
\end{aligned}
\]

\[
\underline{J_{h}}(h)=30000 h^{5} + 457525 h^{4} + 1984365 h^{3} + 3705632 h^{2} + 3025188 h + 732768.
\]

### Polynomial `K_h`

\[
\begin{aligned}
K_{h}(h,v)={}&h^{5}\bigl(- 300000 v - 1053750\bigr)\\
&+h^{4}\bigl(- 160000 v^{2} - 4575250 v - 13686025\bigr)\\
&+h^{3}\bigl(- 568000 v^{2} - 19843650 v - 57064235\bigr)\\
&+h^{2}\bigl(- 680100 v^{2} - 37056320 v - 93954581\bigr)\\
&+h\bigl(- 312400 v^{2} - 30251880 v - 38743464\bigr)\\
&+\bigl(- 48400 v^{2} - 7327680 v + 28537866\bigr)
\end{aligned}
\]

\[
\underline{K_{h}}(h)=- 1123750 h^{5} - \frac{132860650 h^{4}}{9} - \frac{555528100 h^{3}}{9} - \frac{307914250 h^{2}}{3} - \frac{412373200 h}{9} + \frac{241428950}{9}.
\]

### Polynomial `L`

\[
\begin{aligned}
L(h,v)={}&h^{4}\bigl(65625 v^{2} + 420000 v - 5828000\bigr)\\
&+h^{3}\bigl(405000 v^{2} + 2796750 v - 17297600\bigr)\\
&+h^{2}\bigl(759375 v^{2} + 6041700 v - 15582855\bigr)\\
&+h\bigl(429900 v^{2} + 4647930 v - 2970956\bigr)\\
&+\bigl(74700 v^{2} + 1060740 v + 1165627\bigr)
\end{aligned}
\]

\[
\underline{L}(h)=- 5828000 h^{4} - 17297600 h^{3} - 15582855 h^{2} - 2970956 h + 1165627.
\]


## 2. Two lower-shape curves

Set C=19x/50 and r=r_*. Use p_j,d_j,V of the terminal note, with
n_0=25/8 and n_1=7/2. Again each mapping means `D times the quantity`
equals the displayed polynomial in h.

| Polynomial | Quantity | Positive D |
|---|---|---|
| M_0 | 18/5-d_0 | 3062500S⁴ |
| N_0 | 19/4-d'_0 | 3062500S⁵ |
| O_0 | -p'_0-41/200 | 6125000S⁶ |
| Y_0 | 1/110-V | 110SM(95x²+498x-650) |
| Z_0 | 7/800-V' | 800S²M²(95x²+498x-650)² |
| M_1 | 18/5-d_1 | 5468750S⁴ |
| N_1 | 26/5-d'_1 | 5468750S⁵ |
| O_1 | -p'_1-23/100 | 21875000S⁶ |

The O_0,O_1,Z_0 polynomials have positive coefficients.
For every other polynomial below, use `0<=h<=1/6` in each negative
power term. Even after discarding the positive powers, the result
exceeds1. Thus all eight quantities in the table are positive.

### Polynomial `M_0`

\[
M_0(h)=- 1713800 h^{6} - 37292690 h^{5} - 285159828 h^{4} - 983843464 h^{3} - 1551465687 h^{2} - 809079076 h + 212579377.
\]

### Polynomial `N_0`

\[
N_0(h)=- 3427600 h^{6} - 53594215 h^{5} - 341187225 h^{4} - 1128855722 h^{3} - 1824003552 h^{2} - 990072519 h + 257335889.
\]

### Polynomial `O_0`

\[
O_0(h)=558600 h^{7} + 10651040 h^{6} + 86143320 h^{5} + 342670492 h^{4} + 691815823 h^{3} + 709620600 h^{2} + 292950023 h + 4785838.
\]

### Polynomial `Y_0`

\[
Y_0(h)=- 7125 h^{4} - 140390 h^{3} - 283841 h^{2} - 115690 h + 29414.
\]

### Polynomial `Z_0`

\[
Z_0(h)=77389375 h^{8} + 2261864500 h^{7} + 27371661650 h^{6} + 153729796040 h^{5} + 405804725187 h^{4} + 503827505900 h^{3} + 286854745744 h^{2} + 60769341560 h + 689585532.
\]

### Polynomial `M_1`

\[
M_1(h)=- 3427600 h^{6} - 73545505 h^{5} - 555438081 h^{4} - 1887824303 h^{3} - 2904167349 h^{2} - 1395804152 h + 506917454.
\]

### Polynomial `N_1`

\[
N_1(h)=- 6855200 h^{6} - 106804805 h^{5} - 676620075 h^{4} - 2218057669 h^{3} - 3503959029 h^{2} - 1720404138 h + 695230228.
\]

### Polynomial `O_1`

\[
O_1(h)=2234400 h^{7} + 42467535 h^{6} + 342114030 h^{5} + 1358603668 h^{4} + 2757913492 h^{3} + 2900959275 h^{2} + 1291446542 h + 43690402.
\]


## 3. Middle-face beta derivative and terminal value

For this derivative the slope is kept as C; only x=2+h is substituted.
The logarithm upper constant 16/9 is combined with the constant
coefficient before clearing the middle-face value.

The full Q(h,C) of equation (8) in the terminal proof is

\[
\begin{aligned}
Q(h,C)={}&h^{8}\bigl(1245184\bigr)\\
&+h^{7}\bigl(1556480 C + 31551488\bigr)\\
&+h^{6}\bigl(778240 C^{2} + 32952320 C + 321821696\bigr)\\
&+h^{5}\bigl(194560 C^{3} + 13232640 C^{2} + 273387520 C + 1701993984\bigr)\\
&+h^{4}\bigl(24320 C^{4} + 2497280 C^{3} + 84751488 C^{2} + 1135620352 C + 5008527744\bigr)\\
&+h^{3}\bigl(1216 C^{5} + 210800 C^{4} + 11327936 C^{3} + 257136288 C^{2} + 2499943040 C + 8222843104\bigr)\\
&+h^{2}\bigl(5472 C^{5} + 574204 C^{4} + 22046784 C^{3} + 379369096 C^{2} + 2869398104 C + 7418853236\bigr)\\
&+h\bigl(6156 C^{5} + 544540 C^{4} + 17454536 C^{3} + 249238183 C^{2} + 1639188350 C + 3861571483\bigr)\\
&+\bigl(2052 C^{5} + 150114 C^{4} + 3600024 C^{3} + 48714393 C^{2} + 403215522 C + 942621879\bigr)
\end{aligned}
\]

All coefficients are positive for h,C>=0. The complete N of its
middle terminal identity is

\[
N(h)=403439616 h^{7} + 6862897152 h^{6} + 42994741248 h^{5} + 126236766720 h^{4} + 185797060288 h^{3} + 137194124304 h^{2} + 28358242681 h - 12914813589.
\]

All nonconstant coefficients are positive. Direct substitution of 1/6
in the seven positive powers gives `N(1/6)<-1000000000`.

## 4. Upper-face value

The complete W of equation (13) in the terminal proof is

\[
W(h)=- 24463296 h^{8} - 412280226 h^{7} - 2909495636 h^{6} - 11176434083 h^{5} - 25317396372 h^{4} - 33983546668 h^{3} - 25312811671 h^{2} - 8458571328 h - 404024580.
\]

Every coefficient is negative for h>=0.

## 5. Audit boundary

The beta-monotonicity polynomials have at most seventeen monomials and
degree six in two variables. Their printed lower polynomials have at
most seven monomials and degree six. The middle beta derivative has
39 monomials and degree eight in h,C. The remaining univariate identities
have at most nine monomials and degree eight. The largest printed cleared
coefficient is 503827505900, in Z_0. All separate source contributions are
checked after differentiating or restricting to the stated face; no
large common-denominator polynomial in the original variables is used.
