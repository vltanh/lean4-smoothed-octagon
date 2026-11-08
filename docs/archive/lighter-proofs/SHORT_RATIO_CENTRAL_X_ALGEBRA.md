# Central-ratio x comparison: complete small algebra

Companion to [the derivative proof](SHORT_RATIO_CENTRAL_X.md). Throughout this appendix, \(X=x-13/6\), \(A=4/3-a\); thus \(0\le X\le7/30\), \(0\le A\le1/3\). The source polynomials below are the primitives defined in Section 4 of that proof, expanded only in these two variables.

## 1. Primitive source polynomials

### P_a

\[
\begin{aligned}
P_a={}&\frac{17 X}{800} - \frac{203699}{921600}\\
&+\bigl(\frac{13153}{307200} - \frac{7 X}{6400}\bigr)A\\
&+\bigl(- \frac{3 X}{6400} - \frac{279}{51200}\bigr)A^{2}\end{aligned}
\]

6 monomials; degree 3; coefficient numerators/denominators at most 6/6 digits.

### P_b

\[
\begin{aligned}
P_b={}&\frac{289 X}{256} + \frac{15895}{6144}\\
&+\bigl(- \frac{51 X}{128} - \frac{1343}{1024}\bigr)A\\
&+\bigl(\frac{9 X}{256} + \frac{309}{2048}\bigr)A^{2}\end{aligned}
\]

6 monomials; degree 3; coefficient numerators/denominators at most 5/4 digits.

### P_1

\[
\begin{aligned}
P_1={}&- \frac{49 X^{3}}{1200} + \frac{197 X^{2}}{640} - \frac{18199 X}{28800} + \frac{6911431}{2073600}\\
&+\bigl(- \frac{X^{3}}{400} - \frac{17 X^{2}}{640} + \frac{34289 X}{38400} - \frac{475283}{691200}\bigr)A\\
&+\bigl(\frac{3 X^{2}}{1600} + \frac{11 X}{512} + \frac{22483}{38400}\bigr)A^{2}\\
&+\bigl(\frac{3 X}{1600} + \frac{43}{2560}\bigr)A^{3}\end{aligned}
\]

13 monomials; degree 4; coefficient numerators/denominators at most 7/7 digits.

### P_2

\[
\begin{aligned}
P_2={}&- \frac{X^{5}}{48} + \frac{379 X^{4}}{2880} - \frac{140941 X^{3}}{69120} - \frac{6005791 X^{2}}{414720} - \frac{19794707 X}{2488320} + \frac{528666203}{14929920}\\
&+\bigl(\frac{9 X^{4}}{1600} + \frac{12913 X^{3}}{12800} + \frac{430979 X^{2}}{230400} - \frac{39243407 X}{1382400} - \frac{640188907}{8294400}\bigr)A\\
&+\bigl(\frac{37 X^{3}}{1600} + \frac{50491 X^{2}}{38400} + \frac{1580479 X}{115200} + \frac{42846083}{1382400}\bigr)A^{2}\\
&+\bigl(\frac{3 X^{2}}{400} + \frac{243 X}{3200} + \frac{3173}{19200}\bigr)A^{3}\end{aligned}
\]

18 monomials; degree 5; coefficient numerators/denominators at most 9/8 digits.

### G_0

\[
\begin{aligned}
G_0={}&4 X^{2} + \frac{163 X}{8} + \frac{14767}{576}\\
&+\bigl(\frac{147 X}{32} + \frac{8405}{768}\bigr)A\\
&+\bigl(- \frac{21 X}{32} - \frac{593}{256}\bigr)A^{2}\end{aligned}
\]

7 monomials; degree 3; coefficient numerators/denominators at most 5/3 digits.

### C_0

\[
\begin{aligned}
C_0={}&- 16 X^{3} - \frac{3053 X^{2}}{24} - \frac{93733 X}{288} - \frac{51253}{192}\\
&+\bigl(- \frac{735 X^{2}}{32} - \frac{55751 X}{384} - \frac{163301}{768}\bigr)A\\
&+\bigl(\frac{105 X^{2}}{32} + \frac{3867 X}{128} + \frac{34595}{768}\bigr)A^{2}\\
&+\bigl(\frac{203}{32}\bigr)A^{3}\\
&+\bigl(- \frac{21}{32}\bigr)A^{4}\end{aligned}
\]

12 monomials; degree 4; coefficient numerators/denominators at most 6/3 digits.

### G_1

\[
\begin{aligned}
G_1={}&X^{2} + \frac{107 X}{16} + \frac{13895}{1152}\\
&+\bigl(- \frac{21 X}{64} - \frac{6467}{1536}\bigr)A\\
&+\bigl(\frac{3 X}{64} + \frac{743}{512}\bigr)A^{2}\end{aligned}
\]

7 monomials; degree 3; coefficient numerators/denominators at most 5/4 digits.

### C_1

\[
\begin{aligned}
C_1={}&- \frac{51 X^{4}}{16} - \frac{683 X^{3}}{16} - \frac{55859 X^{2}}{256} - \frac{18559651 X}{36864} - \frac{293217427}{663552}\\
&+\bigl(\frac{9 X^{4}}{16} + \frac{2869 X^{3}}{256} + \frac{91167 X^{2}}{1024} + \frac{14925707 X}{49152} + \frac{329706427}{884736}\bigr)A\\
&+\bigl(- \frac{57 X^{3}}{128} - \frac{7071 X^{2}}{512} - \frac{690329 X}{8192} - \frac{22485353}{147456}\bigr)A^{2}\\
&+\bigl(\frac{9 X^{3}}{256} + \frac{1575 X^{2}}{1024} + \frac{205977 X}{16384} + \frac{3223907}{98304}\bigr)A^{3}\\
&+\bigl(- \frac{33}{16}\bigr)A^{4}\\
&+\bigl(\frac{3}{16}\bigr)A^{5}\end{aligned}
\]

20 monomials; degree 6; coefficient numerators/denominators at most 9/6 digits.

### H_0

\[
\begin{aligned}
H_0={}&\frac{17 X^{6}}{768} - \frac{9613 X^{5}}{46080} - \frac{1147051 X^{4}}{1105920} + \frac{1781111 X^{3}}{53084160} + \frac{329042659 X^{2}}{318504960} - \frac{9410806847 X}{1911029760} - \frac{47741692883}{11466178560}\\
&+\bigl(- \frac{X^{6}}{256} + \frac{2549 X^{5}}{51200} - \frac{35533 X^{4}}{115200} - \frac{37648691 X^{3}}{44236800} + \frac{1347569257 X^{2}}{88473600} + \frac{69139047467 X}{1592524800} + \frac{61024967671}{3185049600}\bigr)A\\
&+\bigl(- \frac{221 X^{5}}{51200} + \frac{18453 X^{4}}{204800} - \frac{12804493 X^{3}}{29491200} - \frac{1620199289 X^{2}}{176947200} - \frac{4388881589 X}{353894400} + \frac{116547265757}{6370099200}\bigr)A^{2}\\
&+\bigl(\frac{9 X^{4}}{5120} + \frac{19701 X^{3}}{102400} + \frac{5073743 X^{2}}{4915200} - \frac{1707659 X}{327680} - \frac{730783861}{35389440}\bigr)A^{3}\\
&+\bigl(\frac{147 X^{3}}{51200} + \frac{27853 X^{2}}{204800} + \frac{14999177 X}{9830400} + \frac{250636603}{58982400}\bigr)A^{4}\\
&+\bigl(\frac{9 X^{2}}{12800} + \frac{501 X}{51200} + \frac{27889}{819200}\bigr)A^{5}\end{aligned}
\]

32 monomials; degree 7; coefficient numerators/denominators at most 12/11 digits.

### H_1

\[
\begin{aligned}
H_1={}&\frac{629 X^{5}}{4800} - \frac{245959 X^{4}}{230400} - \frac{11757779 X^{3}}{2764800} - \frac{14565421 X^{2}}{265420800} + \frac{1627175849 X}{796262400} - \frac{46356310673}{9555148800}\\
&+\bigl(- \frac{57 X^{5}}{3200} + \frac{50137 X^{4}}{153600} - \frac{845353 X^{3}}{921600} - \frac{993599 X^{2}}{460800} + \frac{2012089799 X}{66355200} + \frac{535775831}{12441600}\bigr)A\\
&+\bigl(- \frac{3 X^{5}}{3200} - \frac{1729 X^{4}}{51200} + \frac{108311 X^{3}}{307200} - \frac{30894809 X^{2}}{29491200} - \frac{1557008807 X}{88473600} - \frac{12719631121}{1061683200}\bigr)A^{2}\\
&+\bigl(- \frac{3 X^{4}}{5120} - \frac{1331 X^{3}}{102400} + \frac{716897 X^{2}}{1638400} + \frac{5292847 X}{2949120} - \frac{929995849}{176947200}\bigr)A^{3}\\
&+\bigl(\frac{9 X^{3}}{12800} + \frac{333 X^{2}}{25600} + \frac{209801 X}{819200} + \frac{4716271}{3276800}\bigr)A^{4}\\
&+\bigl(\frac{9 X^{2}}{25600} + \frac{129 X}{20480} + \frac{43921}{1638400}\bigr)A^{5}\end{aligned}
\]

30 monomials; degree 7; coefficient numerators/denominators at most 11/10 digits.

## 2. Two complete upper polynomials

The coefficient comparisons in Section 5 of the proof use \(Z_i/10^7\), with all coefficients of \(Z_i\) printed here. For every monomial \(X^jA^k\), the finite scalar recurrence gives

\[
[ X^jA^k ]Z_i-1<10^7 r^{(i)}_{jk}\le[ X^jA^k ]Z_i.
\]

These are 45 explicitly specified rational comparisons per polynomial. The scalars \(r^{(i)}_{jk}\) are defined by the printed finite recurrence; no unprinted exact Taylor polynomial is assumed as a sign premise.

\[
\begin{aligned}
Z_0={}&1758 X^{8} - 28434 X^{7} + 99976 X^{6} - 218760 X^{5} + 256356 X^{4} + 165964 X^{3} - 969041 X^{2} - 504621 X - 58181\\
&+\bigl(- 99566 X^{7} - 8840 X^{6} + 475610 X^{5} - 1458074 X^{4} + 2307871 X^{3} - 824190 X^{2} - 3102276 X - 36665\bigr)A\\
&+\bigl(- 750462 X^{6} + 813305 X^{5} + 336296 X^{4} - 3523259 X^{3} + 6938200 X^{2} - 4540837 X - 3265458\bigr)A^{2}\\
&+\bigl(- 2263809 X^{5} + 3837653 X^{4} - 3323709 X^{3} - 1597172 X^{2} + 7775690 X - 5953168\bigr)A^{3}\\
&+\bigl(- 1669923 X^{4} + 5638708 X^{3} - 7936795 X^{2} + 4485105 X + 890848\bigr)A^{4}\\
&+\bigl(3390269 X^{3} + 339870 X^{2} - 3962223 X + 2679231\bigr)A^{5}\\
&+\bigl(4418725 X^{2} - 2986304 X + 259339\bigr)A^{6}\\
&+\bigl(493509 X - 798888\bigr)A^{7}\\
&+\bigl(-418362\bigr)A^{8}\end{aligned}
\]

45 monomials; degree 8; coefficient numerators/denominators at most 7/1 digits.

\[
\begin{aligned}
Z_1={}&3271 X^{8} - 10623 X^{7} + 27848 X^{6} - 56333 X^{5} + 60768 X^{4} + 153300 X^{3} - 818336 X^{2} - 599188 X - 114863\\
&+\bigl(- 6490 X^{7} + 6241 X^{6} + 5944 X^{5} - 54569 X^{4} + 207763 X^{3} - 292386 X^{2} - 1803283 X - 163307\bigr)A\\
&+\bigl(24353 X^{6} - 49322 X^{5} + 52007 X^{4} + 99491 X^{3} - 419466 X^{2} - 745956 X - 573251\bigr)A^{2}\\
&+\bigl(18425 X^{5} - 148929 X^{4} + 422040 X^{3} - 590520 X^{2} - 875716 X + 281285\bigr)A^{3}\\
&+\bigl(- 172897 X^{4} + 165885 X^{3} + 63592 X^{2} - 1268123 X + 293362\bigr)A^{4}\\
&+\bigl(- 181819 X^{3} + 268020 X^{2} - 845023 X - 84901\bigr)A^{5}\\
&+\bigl(- 1065 X^{2} - 349743 X - 225141\bigr)A^{6}\\
&+\bigl(- 171717 X - 187239\bigr)A^{7}\\
&+\bigl(-133826\bigr)A^{8}\end{aligned}
\]

45 monomials; degree 8; coefficient numerators/denominators at most 7/1 digits.

## 3. Primitive coefficient majorants

For a primitive \(P=\sum p_{jk}X^jA^k\), define the scalar sums

\[
 n_{P,r}=\sum_{j+k=r}|p_{jk}|(7/30)^j(1/3)^k.
\]

The following rows print every coefficient of
\[
 m_P(z)=10^{-6}\sum_{r=0}^7 m_{Pr}z^r,\qquad n_{P,r}\le10^{-6}m_{Pr}.
\]
Each integer is an upward rounding of the indicated rational sum. Trailing zeros are included. These ten polynomials have at most eight monomials and degree at most seven.

| P | m0 | m1 | m2 | m3 | m4 | m5 | m6 | m7 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| P_a | 221028 | 19231 | 691 | 13 | 0 | 0 | 0 | 0 |
| P_b | 2587077 | 700586 | 47754 | 912 | 0 | 0 | 0 | 0 |
| P_1 | 3333059 | 376653 | 151265 | 2180 | 39 | 0 | 0 | 0 |
| P_2 | 35409849 | 27583935 | 6440163 | 421662 | 13273 | 68 | 0 | 0 |
| G_0 | 25637153 | 8402171 | 832448 | 17014 | 0 | 0 | 0 | 0 |
| C_0 | 266942709 | 146818259 | 23223010 | 1638300 | 27952 | 0 | 0 | 0 |
| G_1 | 12061632 | 2963846 | 241207 | 1216 | 0 | 0 | 0 | 0 |
| C_1 | 441890654 | 241694911 | 52441242 | 5557408 | 274560 | 5058 | 17 | 0 |
| H_0 | 4163697 | 7535649 | 5465836 | 1363178 | 159567 | 7679 | 237 | 2 |
| H_1 | 4851449 | 14831241 | 3692626 | 744075 | 46665 | 2642 | 37 | 1 |

## 4. Complete scalar remainder arithmetic

For the positive-series majorants \(\mathcal M_i\) defined in Section 6 of the proof, the next rows give

\[
10^{-6}c_{ij}\le[z^j]\mathcal M_i,\qquad
\mathcal M_i(1)<10^{-6}U_i.
\]

Every coefficient needed for the degree-eight remainder bound is printed. All entries follow from the one-variable recurrence in Section 6, with ordinary convolution for products.

| i | c0 | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | U | U−sum cj |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 1139804 | 1170737 | 874557 | 505103 | 243680 | 100985 | 37385 | 12724 | 4062 | 4090778 | 1741 |
| 1 | 1136468 | 1214196 | 1047130 | 747544 | 458495 | 243186 | 114363 | 48783 | 19231 | 5040235 | 10839 |
