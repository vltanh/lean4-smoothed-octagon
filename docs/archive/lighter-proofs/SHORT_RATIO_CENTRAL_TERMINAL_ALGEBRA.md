# Algebra for the central upper-ratio terminals

This is the complete polynomial and scalar input to
[the four terminal signs](SHORT_RATIO_CENTRAL_TERMINALS.md).
Throughout, z lies in [-1,1]. A separate nonnegative variable v is
used only for the absolute-coefficient majorants.

## 1. Source formulas before expansion

For L set a=13/12+z/12, and for H set a=5/4+z/12. At x=13/6,
\[
\begin{array}{c|cccc}
 &a&B&K&t\\\hline
L&(13+z)/12&(5095+231z)/1536&(1469+26z+z^2)/144&(7-z)/3\\
H&(15+z)/12&(5557+231z)/1536&(1525+30z+z^2)/144&2
\end{array}                                         \tag{A1}
\]
Here S=19/6, b=B-a, D=a^2+2ab+1+2x-2bx,
M=S^2(S^2-S+1), and E_f=-S^3/4+3S-1. Write
\[
\begin{aligned}
V&=u-3/4,&U&=(u-1)B,\\
J_0&=a^2+3D/2-E_f,&J_1&=2D-S^3,\\
W_0&=M+3D^2/4-DE_f-3K^2/4,&W_1&=D(D-S^3),\\
C_0&=4K-7aB/2,&C_1&=K+aB/4,\qquad Y=taB.
\end{aligned}                                       \tag{A2}
\]
Thus a^2+E_L K=J_0+VJ_1, and K^2(w-3/4)=W_0+VW_1.
These are norm-affine identities; expanding their two pieces
separately avoids a needless large coefficient in the shifted
combined W. The value of u is the corresponding affine chord in the
main note.

Put gamma=-488/2187-33/25. The four exact rational upper functions
are given by the following common source, with i=L or H:
\[
\begin{aligned}
f_{i0}={}&U/a+a/B+1-(J_0+VJ_1)/K
+C_0(W_0+VW_1)/K^3+e_0\\
&+\gamma+41Y/(20K)-Y^2/(2K^2),\\
f_{i1}={}&U/a+a/B+1-(J_0+VJ_1)/K
+C_1(W_0+VW_1)/(aBK^2)+e_1\\
&+\gamma+41Y/(20K)-Y^2/(2K^2).                       \tag{A3}
\end{aligned}
\]
For L,
\[
e_0=4/t-2/t^2-3/2,
\qquad e_1=K(t-1)/(aBt^2)-K/(4aB)+2/t-1.             \tag{A4}
\]
For H, e_0=e_1=0. Formula (A3) follows directly from (A2),
the original transport and Q(y)=gamma+(41/20)y-y^2/2.
Only the following primitive identities are expanded. Products in
(A3) are handled by the scalar series recurrence in Section 3.

## 2. All primitive source polynomials

For each displayed identity, its leading positive scalar is the
normalization of the named source polynomial.

### Lower interval

\[
\begin{aligned}
76800000\,U_{L}(z)={}&- 5544 z^{2} - 2904213 z - 61359085
\end{aligned}
\]
\[
\begin{aligned}
55296\,J_{0L}(z)={}&1887 z^{2} + 43788 z + 172141
\end{aligned}
\]
\[
\begin{aligned}
13824\,J_{1L}(z)={}&501 z^{2} + 11268 z - 392881
\end{aligned}
\]
\[
\begin{aligned}
1019215872\,W_{0L}(z)={}&214137 z^{4} + 9373608 z^{3} + 29561158 z^{2}\\
&{}+- 2010342792 z + 1964067937
\end{aligned}
\]
\[
\begin{aligned}
254803968\,W_{1L}(z)={}&83667 z^{4} + 3763512 z^{3} - 88899646 z^{2}\\
&{}+- 2951322072 z - 12781482805
\end{aligned}
\]
\[
\begin{aligned}
36864\,C_{0L}(z)={}&- 593 z^{2} - 30062 z + 1040611
\end{aligned}
\]
\[
\begin{aligned}
73728\,C_{1L}(z)={}&743 z^{2} + 21410 z + 818363
\end{aligned}
\]
\[
\begin{aligned}
55296\,Y_{L}(z)={}&- 231 z^{3} - 6481 z^{2} - 9549 z\\
&{}+463645
\end{aligned}
\]
\[
\begin{aligned}
50000\,V_{L}(z)={}&- 24 z + 457
\end{aligned}
\]

### Upper interval

\[
\begin{aligned}
153600000\,U_{H}(z)={}&- 9009 z^{2} - 5800686 z - 134329361
\end{aligned}
\]
\[
\begin{aligned}
55296\,J_{0H}(z)={}&1887 z^{2} + 51336 z + 267265
\end{aligned}
\]
\[
\begin{aligned}
13824\,J_{1H}(z)={}&501 z^{2} + 13272 z - 368341
\end{aligned}
\]
\[
\begin{aligned}
1019215872\,W_{0H}(z)={}&214137 z^{4} + 11086704 z^{3} + 90942094 z^{2}\\
&{}+- 1772762480 z - 1859957959
\end{aligned}
\]
\[
\begin{aligned}
254803968\,W_{1H}(z)={}&83667 z^{4} + 4432848 z^{3} - 64310566 z^{2}\\
&{}+- 3259081168 z - 19008278765
\end{aligned}
\]
\[
\begin{aligned}
36864\,C_{0H}(z)={}&- 593 z^{2} - 32434 z + 978115
\end{aligned}
\]
\[
\begin{aligned}
73728\,C_{1H}(z)={}&743 z^{2} + 24382 z + 864155
\end{aligned}
\]
\[
\begin{aligned}
9216\,Y_{H}(z)={}&231 z^{2} + 9022 z + 83355
\end{aligned}
\]
\[
\begin{aligned}
100000\,V_{H}(z)={}&- 39 z + 827
\end{aligned}
\]

## 3. Scalar recurrence and rounded comparison polynomials

The inputs in (A1) and Section 2 determine every scalar calculation.
For a factor q(z)=q_0+q_1z+q_2z^2 with q_0>0, the coefficients of
its reciprocal are determined by
\[
r_{-1}=0,\qquad r_0=1/q_0,\qquad
r_n=-(q_1r_{n-1}+q_2r_{n-2})/q_0\quad(1\le n\le8).
\tag{A5}
\]
Use q_2=0 for a,B,t; for the constant upper t use q_1=q_2=0.
For products use the finite convolution
\[
[fg]_n=\sum_{j=0}^n f_jg_{n-j}\quad(0\le n\le8),     \tag{A6}
\]
and for sums add the coefficients. Polynomial source coefficients
above their printed degrees are zero. Apply (A5)--(A6) to (A3),
including (A4) and its constant terms. If c_{ij,n} is the resulting
scalar coefficient, the following printed integer polynomials satisfy
\[
|10^9c_{ij,n}-[z^n]p_{ij}|<1/2
\quad(ij=L0,L1,H0,H1,\ 0\le n\le8).                 \tag{A7}
\]
These are 36 scalar rational comparisons, not a cleared polynomial
identity. The uniform approximation error following from them is
9/(2*10^9), including for negative z.

For an explicit example of (A5), the first three coefficients of 1/K
on L are
\[
144/1469,\qquad -3744/2157961,\qquad -114192/3170044709.
\tag{A8}
\]
For a worked complete coefficient comparison, evaluate (A3) for L0
at zero. The inputs include
\[
U_0=-12043\cdot5095/76800000,\quad
J_{00}=172141/55296,\quad J_{10}=-392881/13824,
\]
\[
W_{00}=1964067937/1019215872,\quad
W_{10}=-12781482805/254803968,\quad V_0=457/50000,
\]
\[
C_{00}=1040611/36864,\quad Y_0=463645/55296,
\quad e_0(0)=-15/98.
\]
Substitution gives the scalar expression
\[
\begin{aligned}
c_{L0,0}={}&\frac{U_0}{13/12}+\frac{13/12}{5095/1536}+1
-\frac{J_{00}+(457/50000)J_{10}}{1469/144}\\
&+\frac{(1040611/36864)[W_{00}+(457/50000)W_{10}]}{(1469/144)^3}
-\frac{15}{98}-\frac{488}{2187}-\frac{33}{25}\\
&+\frac{41}{20}\frac{463645/55296}{1469/144}
-\frac12\left(\frac{463645/55296}{1469/144}\right)^2.
\end{aligned}                                       \tag{A9}
\]
Ordinary rational comparison yields
\[
-5767975/10^{10}<c_{L0,0}<-5767965/10^{10},           \tag{A10}
\]
which is the n=0 instance of (A7). The same finite recurrence checks
all eight remaining coefficients without differentiating or clearing
a combined rational numerator. The four polynomials used in the sign
argument, in their entirety, are:
\[
\begin{aligned}
p_{L0}(z)={}&- 277 z^{8} - 1482 z^{7} - 7212 z^{6}\\
&{}+- 30114 z^{5} - 142289 z^{4} + 511102 z^{3}\\
&{}+- 808511 z^{2} + 862262 z - 576797
\end{aligned}
\]
\[
\begin{aligned}
p_{L1}(z)={}&- 217 z^{8} - 1166 z^{7} - 5429 z^{6}\\
&{}+- 24329 z^{5} - 73856 z^{4} - 6673 z^{3}\\
&{}+- 1510742 z^{2} + 832241 z - 316335
\end{aligned}
\]
\[
\begin{aligned}
p_{H0}(z)={}&z^{7} - 6 z^{6} + 733 z^{5}\\
&{}+- 19814 z^{4} + 64809 z^{3} + 382870 z^{2}\\
&{}+- 805545 z - 1296429
\end{aligned}
\]
\[
\begin{aligned}
p_{H1}(z)={}&- 5 z^{7} + 77 z^{6} - 1217 z^{5}\\
&{}+20837 z^{4} - 284972 z^{3} + 1266770 z^{2}\\
&{}+- 496534 z - 3176966
\end{aligned}
\]

## 4. Positive-series majorants and the analytic tail

For each primitive N in Section 2, let m_N(v) be its following
polynomial. Each coefficient is a rational upper bound for the
absolute value of the corresponding coefficient of N. Thus products
of m_N dominate absolute coefficients of the corresponding products.
The bounds were rounded upward to six decimal places; the explicit
polynomials below make each scalar comparison immediate from
Section 2. Subscripts L and H choose their respective rows.

### Lower majorants

\[
\begin{aligned}
10^6 m_{L,U}(v)={}&73 v^{2} + 37816 v + 798947
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{L,J0}(v)={}&34126 v^{2} + 791884 v + 3113083
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{L,J1}(v)={}&36242 v^{2} + 815105 v + 28420212
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{L,W0}(v)={}&211 v^{4} + 9197 v^{3} + 29004 v^{2}\\
&{}+1972441 v + 1927039
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{L,W1}(v)={}&329 v^{4} + 14771 v^{3} + 348895 v^{2}\\
&{}+11582717 v + 50162025
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{L,C0}(v)={}&16087 v^{2} + 815484 v + 28228380
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{L,C1}(v)={}&10078 v^{2} + 290392 v + 11099759
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{L,Y}(v)={}&4178 v^{3} + 117206 v^{2} + 172689 v\\
&{}+8384784
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{L,V}(v)={}&480 v + 9140
\end{aligned}
\]

### Upper majorants

\[
\begin{aligned}
10^6 m_{H,U}(v)={}&59 v^{2} + 37765 v + 874541
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{H,J0}(v)={}&34126 v^{2} + 928386 v + 4833352
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{H,J1}(v)={}&36242 v^{2} + 960070 v + 26645038
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{H,W0}(v)={}&211 v^{4} + 10878 v^{3} + 89228 v^{2}\\
&{}+1739340 v + 1824892
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{H,W1}(v)={}&329 v^{4} + 17398 v^{3} + 252393 v^{2}\\
&{}+12790544 v + 74599619
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{H,C0}(v)={}&16087 v^{2} + 879829 v + 26533068
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{H,C1}(v)={}&10078 v^{2} + 330703 v + 11720853
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{H,Y}(v)={}&25066 v^{2} + 978950 v + 9044597
\end{aligned}
\]
\[
\begin{aligned}
10^6 m_{H,V}(v)={}&390 v + 8270
\end{aligned}
\]

The reciprocal majorants are
\[
\begin{array}{c|cccc}
&I_a&I_B&I_K&I_t\\\hline
L&12/(13-v)&1536/(5095-231v)&144/(1469-26v-v^2)&3/(7-v)\\
H&12/(15-v)&1536/(5557-231v)&144/(1525-30v-v^2)&1/2.
\end{array}                                         \tag{A11}
\]
They have nonnegative power-series coefficients and dominate the
absolute coefficients of the corresponding reciprocals in (A1).
This follows by geometric-series expansion; the minus signs in the
majorant denominators retain all absolute products, including any
cancellation present in the actual inverse of K.

Set a_+(v)=a_0+v/12, K_+(v)=K_0+K_1v+K_2v^2, with the positive
coefficients from (A1). Define
\[
\mathcal C=m_UI_a+a_+I_B+(m_{J0}+m_Vm_{J1})I_K,
\qquad \mathcal W=m_{W0}+m_Vm_{W1},
\]
\[
\mathcal Q=(41/20)m_YI_K+(1/2)m_Y^2I_K^2,
\]
\[
M_0=\mathcal C+m_{C0}\mathcal W I_K^3+\mathcal Q+\mathcal E_0,
\]
\[
M_1=\mathcal C+m_{C1}\mathcal W I_aI_BI_K^2+\mathcal Q+\mathcal E_1.
\tag{A12}
\]
For H take both additional terms to be zero. For L take
\[
\mathcal E_0=4I_t+2I_t^2,
\]
\[
\mathcal E_1=K_+I_aI_B\{(4/3+v/3)I_t^2+1/4\}+2I_t.
\tag{A13}
\]
These are exactly the absolute-coefficient majorants of the
nonconstant source contributions in (A3)--(A4). Pure constants have
no contribution to the tail of order nine or higher.

Every denominator in (A11) is strictly positive at v=5; in
particular the lower quadratic denominator is 1314 and the upper is
1350, while 7-v=2. Substitution of v=5 into the fully displayed
rational expressions (A12)--(A13) gives
\[
M_{L0}(5)<18,\quad M_{L1}(5)<58,\quad
M_{H0}(5)<9,\quad M_{H1}(5)<9.                       \tag{A14}
\]
These four scalar rational comparisons and (A7) are all the rounding
checks used. The main note's geometric estimate then bounds the
whole infinite tail, without printing or using a high-degree cleared
numerator or an exact large-coefficient Taylor identity.

## 5. Expanded-identity accounting

The eighteen primitive source identities in Section 2 have degree
at most four and at most five monomials. Their largest printed
integer coefficient is 19008278765. The eighteen majorants have
the same degree bounds, and the four sign polynomials have degree
at most eight and at most nine monomials. The source (A2) is checked
by expanding its separate norm-affine pieces, whose individual
contributions also stay within twelve digits. Reciprocals are then
handled by (A5); all subsequent coefficient comparisons are scalar.
No full denominator-cleared source or degree greater than eight
polynomial is an intermediate sign premise.
