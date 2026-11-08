# The maximum-duration face of the simpler low-t residual

Date: 2026-11-08.

This closes the maximum-duration face for the new residual \(G_n\) in
[the low-t shape proof](NONSHORT_LOW_T_SHAPE.md). It uses the two explicitly
proved small signs in [the auxiliary note](NONSHORT_LOW_T_QMAX_AUXILIARIES.md).
It does not by itself supply the separate reduction from the full low-t
domain to this face and the other comparison faces.

Assume
\[
\frac14\le h\le\frac13,\qquad
\frac1{30}\le j\le\frac{5h}{7},\qquad
 t=\frac{1-h}{2},\quad x=h+j,\quad
 q=\frac{1+h+j}{1+2j},\quad k=1.
\tag{1}
\]
We prove the exact, unchanged face conclusion
\[
\boxed{G_n(t,x,q,1)>0.}
\tag{2}
\]
No logarithm or incoming-norm bound is altered. The logarithm majorant and
\(T_L=(912-401x)/(24(17x+76))\) are exactly those in the linked shape note.

The proof first establishes a positive derivative in \(j\), using the
already proved monotonicity in \(h\) of a degree-eight lower polynomial.
It then checks the minimum-gap face. The two source identities are verified
by divided derivatives and zero jets before any polynomial expansion;
no degree-thirteen or degree-fourteen polynomial is expanded as a proof step.

## 1. A factored circuit for the exact numerator

Put
\[
\begin{gathered}
W=1+h+j,\quad d=1+2j,\quad Z=W+d=h+3j+2,\quad r=h-j,\\
R=17h+17j+76,\quad p=(1+h+2j)/2,\quad t=(1-h)/2,\quad x=h+j,\\
B=1+h+j+hj+j^2,\quad Y=x(x+2),\quad J=t+Y,\\
H_q=h^2+22hj+12h+25j^2+36j+12=W^2+10Wd+d^2,\\
A_f=-\tfrac12(2h^2+44hj+23h-74j^2-52j-8),\qquad
D_f=h^2+hj+h-j^2,\\
m_d=(96j^2-2j+48h-1)/6.
\end{gathered}
\tag{3}
\]
These have degree at most two; \(H_q,A_f,D_f,m_d\) have respectively
6, 6, 4 and 4 monomials. The last three are
\(A_f=(a+1)d^2-J\), \(D_f=J-pd\), and \(m_d=dm\), for the multipliers
\(a=7/2-10(q-1)\), \(m=8j+8(q-1)-1/6\).

Here are the complete affine source polynomials:
\[
\begin{aligned}
8\mathcal N_0={}&- h^{6} - 3 h^{5} j - 6 h^{5} - 9 h^{4} j^{2}\\
 &- 22 h^{4} j - 4 h^{4} - 7 h^{3} j^{3} - 17 h^{3} j^{2}\\
 &- 8 h^{3} j + 14 h^{3} + 12 h^{2} j^{4} + 23 h^{2} j^{3}\\
 &+ 15 h^{2} j^{2} + 34 h^{2} j + 21 h^{2} + 12 h j^{5}\\
 &+ 16 h j^{4} + 3 h j^{3} + 9 h j^{2} + 27 h j\\
 &+ 8 h - 12 j^{5} - 28 j^{4} - 27 j^{3}\\
 &- 6 j^{2} + 4 j.
\end{aligned}
\]

\[
\begin{aligned}
\mathcal N_v={}&\frac{xW}{2}
 [h^4+h^3j+2h^3-h^2j^2+h^2j-h^2-hj^3-2hj^2-hj-4h
   +j^3+3j^2+j-2],\\
\mathcal N_L={}&-tBWdp,\\
\Theta_v={}&2(h^2+2hj+2h-3j^2-2j-1)\\
 &\quad\cdot(h^3+2h^2j+h^2-3hj^2-4hj-3h+3j^2+2j-1).
\end{aligned}
\tag{4}
\]
\[
\begin{aligned}
2\Theta_0={}&- h^{5} - 2 h^{4} j - 5 h^{4} - 4 h^{3} j\\
 &+ 5 h^{3} + 6 h^{2} j^{3} + 18 h^{2} j^{2} + 30 h^{2} j\\
 &+ 23 h^{2} - 3 h j^{4} - 12 h j^{3} - 42 h j^{2}\\
 &- 24 h j - 3 h + 3 j^{4} + 6 j^{3}\\
 &-3.
\end{aligned}
\]

The counts of \(\mathcal N_0,\mathcal N_v,\mathcal N_L,\Theta_0,\Theta_v\)
are 26, 24, 23, 17 and 18 monomials, with degrees 6, 6, 6, 5 and 5.
For the original product expressions \(N\) and \(\mathcal P\) in equation
(10) of the shape note, substitution of \(q=W/d\) gives the affine identities
\[
N=\frac W{d^2}(\mathcal N_0+\mathcal N_v\,v+\mathcal N_L\,L),\qquad
\mathcal P=\frac{W^4}{d^4}(\Theta_0+\Theta_v\,v).
\tag{5}
\]
Check the coefficients of \(1,v,L\) separately after canceling powers of
\(W,d\). Each check is one of the bivariate identities of degree at most six
just printed; no free third scalar variable is included in a ring expansion.

Define
\[
\mathcal A=4A_f\mathcal N_0+WD_f\Theta_0,
\qquad\mathcal L=-4A_ftBWp.
\tag{6}
\]
Their expanded forms, used only for these small local identities, are
\[
\begin{aligned}
4\mathcal A={}&42 h^{7} j + 21 h^{7} + 68 h^{6} j^{2} + 285 h^{6} j\\
 &+ 126 h^{6} + 202 h^{5} j^{3} + 623 h^{5} j^{2} + 402 h^{5} j\\
 &+ 72 h^{5} - 360 h^{4} j^{4} - 1147 h^{4} j^{3} - 697 h^{4} j^{2}\\
 &- 708 h^{4} j - 300 h^{4} - 1082 h^{3} j^{5} - 2964 h^{3} j^{4}\\
 &- 2849 h^{3} j^{3} - 1493 h^{3} j^{2} - 1052 h^{3} j - 359 h^{3}\\
 &+ 348 h^{2} j^{6} + 1322 h^{2} j^{5} + 1844 h^{2} j^{4} + 2795 h^{2} j^{3}\\
 &+ 1833 h^{2} j^{2} + 311 h^{2} j - 34 h^{2} + 894 h j^{7}\\
 &+ 2366 h j^{6} + 2778 h j^{5} + 2944 h j^{4} + 3441 h j^{3}\\
 &+ 2036 h j^{2} + 528 h j + 58 h - 894 j^{7}\\
 &- 2714 j^{6} - 3562 j^{5} - 2072 j^{4} - 226 j^{3}\\
 &+ 166 j^{2} + 32 j.
\end{aligned}
\]

\[
\begin{aligned}
2\mathcal L={}&- 2 h^{6} j - 2 h^{6} - 52 h^{5} j^{2} - 77 h^{5} j\\
 &- 27 h^{5} - 112 h^{4} j^{3} - 198 h^{4} j^{2} - 149 h^{4} j\\
 &- 38 h^{4} + 72 h^{3} j^{4} + 199 h^{3} j^{3} + 178 h^{3} j^{2}\\
 &+ 85 h^{3} j + 20 h^{3} + 282 h^{2} j^{5} + 662 h^{2} j^{4}\\
 &+ 760 h^{2} j^{3} + 528 h^{2} j^{2} + 235 h^{2} j + 48 h^{2}\\
 &+ 148 h j^{6} + 192 h j^{5} - 14 h j^{4} - 199 h j^{3}\\
 &- 126 h j^{2} - 8 h j + 7 h - 148 j^{6}\\
 &- 474 j^{5} - 720 j^{4} - 648 j^{3} - 330 j^{2}\\
 &- 84 j -8.
\end{aligned}
\]

They have 42 and 34 expanded monomials and degrees eight and seven,
respectively. The only needed cancellation before clearing the incoming
norm denominator is
\[
4A_f\mathcal N_v+WD_f\Theta_v=-dW\mathcal K,
\tag{7}
\]
where the complete degree-six factor is
\[
\begin{aligned}
\mathcal K={}&19 h^{6} + 6 h^{5} j + 34 h^{5} - 58 h^{4} j^{2}\\
 &- 9 h^{4} j - 27 h^{4} - 44 h^{3} j^{3} - 129 h^{3} j^{2}\\
 &- 28 h^{3} j - 74 h^{3} + 31 h^{2} j^{4} - h^{2} j^{3}\\
 &+ 86 h^{2} j^{2} + 73 h^{2} j - 18 h^{2} + 46 h j^{5}\\
 &+ 95 h j^{4} + 37 h j^{3} + 129 h j^{2} + 52 h j\\
 &+ 14 h - 46 j^{5} - 126 j^{4} - 60 j^{3}\\
 &+ 66 j^{2} + 16 j.
\end{aligned}
\]

The factor \(\mathcal K\) has 26 monomials. Identity (7), including its
outer factors, has 42 monomials and total degree eight.
The two rational substitution numerators are
\[
\begin{aligned}
2\mathcal V={}&204 h^{4} + 408 h^{3} j + 1123 h^{3} + 204 h^{2} j^{2}\\
 &+ 1946 h^{2} j + 4267 h^{2} + 1639 h j^{2} + 7622 h j\\
 &+ 6084 h + 816 j^{3} + 4267 j^{2} + 6084 j\\
 &+ 2736.
\end{aligned}
\]

\[
\begin{aligned}
2\mathcal F={}&2 h^{3} + 21 h^{2} j + 11 h^{2} + 75 h j^{2}\\
 &+ 92 h j + 27 h + 58 j^{3} + 119 j^{2}\\
 &+ 81 j + 18.
\end{aligned}
\]

They have 13 and 10 monomials and degrees four and three. Their exact
normalizations, obtained by scalar fraction arithmetic, are
\[
V_L=\frac{\mathcal V}{24RW^2},\qquad
F_\ell=\frac{\mathcal F}{6dWZ},\qquad
L=\frac{rH_q}{6dWZ}.
\tag{8}
\]
Consequently the exact polynomial circuit for the cleared residual is
\[
\boxed{
\begin{aligned}
P={}&144W^3ZR\mathcal A-6dW^2Z\mathcal K\mathcal V
 +24W^2RrH_q\mathcal L\\
 &+96d^2WRm_d\mathcal F-24d^3Zm_d\mathcal V,
\end{aligned}}
\tag{9}
\]
with
\[
\boxed{P=576d^4W^2ZR\,G_n(t,x,q,1).}
\tag{10}
\]
To derive (9)--(10), insert (5) into the definition of \(G_n\), use (7),
and cancel the three denominators in (8). This is field arithmetic with
factored expressions. The source inputs have all been printed; the product
in (9) is not globally expanded. Each summand has total degree at most
fourteen, degree at most thirteen in \(h\), and degree at most twelve in \(j\).
Those bounds will control the small derivative checks below.

## 2. A positive-product identity for the gap derivative

Let \(\mathcal M\) be the 43-monomial, degree-eight polynomial (3) of the
auxiliary note. Here is the complete positive-coefficient error polynomial:
\[
\begin{aligned}
\mathcal E={}&\frac{13130 h^{8}}{27} + \frac{10220 h^{7} j}{27} + 73 h^{7} + \frac{3881 h^{6} j^{2}}{18}\\
 &+ 430 h^{6} j + 198 h^{6} + \frac{10739 h^{5} j^{3}}{27} + 236 h^{5} j^{2}\\
 &+ 202 h^{5} j + 471 h^{5} + \frac{1025 h^{4} j^{4}}{32} + 228 h^{4} j^{3}\\
 &+ 372 h^{4} j^{2} + 328 h^{4} j + 162 h^{4} + \frac{7817 h^{3} j^{5}}{16}\\
 &+ 375 h^{3} j^{4} + 232 h^{3} j^{3} + 278 h^{3} j^{2} + 88 h^{3} j\\
 &+ 100 h^{3} + \frac{13483 h^{2} j^{6}}{48} + 370 h^{2} j^{5} + 290 h^{2} j^{4}\\
 &+ 272 h^{2} j^{3} + 340 h^{2} j^{2} + 392 h^{2} j + 58 h^{2}\\
 &+ \frac{5674 h j^{7}}{27} + 176 h j^{6} + 98 h j^{5} + 95 h j^{4}\\
 &+ 336 h j^{3} + 224 h j^{2} + 300 h j + 92 h\\
 &+ \frac{106467959 j^{8}}{48} + 136 j^{7} + 340 j^{6} + 20 j^{5}\\
 &+ 390 j^{4} + 128 j^{3} + 106 j^{2} + 24 j.
\end{aligned}
\]

It has 44 monomials and degree eight. Clearing its common denominator 864
gives largest coefficient 1,916,423,262.

The ten homogeneous factors below all have total degree eight and positive
coefficients. Their outer powers remain factored.
\[
\mathsf U_1=3 j^{2} (36992574 h^{6} + 164169772 h^{5} j + 109268020 h^{4} j^{2} + 104488568 h j^{5} + 26740647 j^{6}).
\]

\[
\mathsf V_1=3 h^{2} (3521643 h^{6} + 11093150 h^{5} j + 141038346 h j^{5} + 85726270 j^{6}).
\]

\[
\mathsf U_2=12 j^{3} (22389836 h^{5} + 41974935 h^{4} j + 7237179 h^{3} j^{2} + 14527359 j^{5}).
\]

\[
\mathsf V_2=12 h (484214 h^{7} + 2757346 h^{6} j + 346518 h^{5} j^{2} + 33621357 h j^{6} + 10626482 j^{7}).
\]

\[
\mathsf U_3=6 h^{3} j^{3} (11047356 h^{2} + 40510145 h j + 35225268 j^{2}).
\]

\[
\mathsf V_3=3 (613707 h^{8} + 4841140 h^{7} j + 7462464 h^{6} j^{2} + 32878608 h^{2} j^{6} + 73145480 h j^{7} + 11089647 j^{8}).
\]

\[
\mathsf U_4=12 h^{2} j^{3} (543688 h^{3} + 4693755 h^{2} j + 6677982 h j^{2} + 1002176 j^{3}).
\]

\[
\mathsf V_4=6 (53739 h^{8} + 558514 h^{7} j + 1381158 h^{6} j^{2} + 11584880 h j^{7} + 9646515 j^{8}).
\]

\[
\mathsf U_5=2448 h^{2} j^{4} (2355 h^{2} + 5010 h j + 2884 j^{2}).
\]

\[
\mathsf V_5=1224 (19 h^{8} + 278 h^{7} j + 978 h^{6} j^{2} + 304 h^{5} j^{3} + 6112 h j^{7} + 11547 j^{8}).
\]

The monomial counts for \((\mathsf U_r,\mathsf V_r)\), in order
\(r=1,\ldots,5\), are \((5,4),(4,5),(3,6),(4,5),(3,6)\).
Their largest expanded coefficient is 503,699,220.
The remaining three small polynomials and integer lower bounds are
\[
\begin{aligned}
D_9(h)={}&-8457840h^4-4353180h^3+64229940h^2+42415740h-93834660,
 &\ell_9&=-79482001,\\
D_{10}(h)={}&-1858032h^3+10115028h^2+18447000h-26703996,
 &\ell_{10}&=-21528873,\\
D_{11}(h)={}&2531232h-2531232,
 &\ell_{11}&=-1898424.
\end{aligned}
\tag{11}
\]
They have five, four and two monomials, and degrees four, three and one.
Termwise use of \(1/4\le h\le1/3\) gives
\[
D_9\ge-953784005/12>\ell_9,\qquad
D_{10}\ge-86115491/4>\ell_{10},\qquad D_{11}\ge\ell_{11}.
\tag{12}
\]

Define the following fully factored polynomial:
\[
\begin{aligned}
\mathcal R={}&500\mathcal M+\mathcal E\\
 &+\sum_{r=1}^5\bigl[(h^r-4^{-r})\mathsf U_r
                    +(3^{-r}-h^r)\mathsf V_r\bigr]\\
 &+\sum_{b=9}^{11}\bigl[
 j^b(D_b-\ell_b)+(-\ell_b)j^8(4^{8-b}-j^{b-8})\bigr].
\end{aligned}
\tag{13}
\]
The exact structural identity is
\[
\boxed{\partial_jP=\mathcal R.}
\tag{14}
\]
Section 3 supplies the complete small verification interface for (14).
In particular, it does not ask for expansion of the degree-thirteen
polynomial in (13).

On the rectangle \(1/4\le h\le1/3\), \(0\le j\le1/4\), every displayed
summand of \(\mathcal R-500\mathcal M\) is nonnegative: use (12),
\(h^r\ge4^{-r}\), \(h^r\le3^{-r}\), and
\(j^{b-8}\le4^{8-b}\). Thus
\[
\boxed{\partial_jP\ge500\mathcal M.}
\tag{15}
\]
The auxiliary note proves \(\mathcal M>0\) on
\(1/4\le h\le1/3,\ 1/30\le j\le3h/4\).
Since \(5h/7<3h/4\), (15) makes \(P\) strictly increasing in \(j\)
on the entire original face (1).

## 3. Verification by a sixth derivative and small zero jets

For either \(S=\partial_jP\) or \(S=\mathcal R\), direct product-rule
differentiation gives the same divided sixth derivative:
\[
\frac1{6!}\partial_h^6 S=H(h,j),
\tag{16}
\]
where the complete bivariate polynomial is
\[
\begin{aligned}
H={}&- 39907296 h^{7} - 314411328 h^{6} j - 297929016 h^{6} - 553047264 h^{5} j^{2}\\
 &- 1548200808 h^{5} j - 850597902 h^{5} - 78140160 h^{4} j^{3} - 1740259080 h^{4} j^{2}\\
 &- 3049918200 h^{4} j - 1220219280 h^{4} + 484263360 h^{3} j^{4} + 548037504 h^{3} j^{3}\\
 &- 1880540928 h^{3} j^{2} - 2779404768 h^{3} j - 887454036 h^{3} + 343405440 h^{2} j^{5}\\
 &+ 1577101680 h^{2} j^{4} + 1855955808 h^{2} j^{3} - 116430048 h^{2} j^{2} - 931824600 h^{2} j\\
 &- 282085608 h^{2} + 49420224 h j^{6} + 560950488 h j^{5} + 1701426090 h j^{4}\\
 &+ 1880746224 h j^{3} + 776844054 h j^{2} + 61818162 h j - 17173989 h\\
 &- 7481088 j^{7} + 12026112 j^{6} + 211351608 j^{5} + 503699220 j^{4}\\
 &+ 492509316 j^{3} + 232255206 j^{2} + 52341930 j + 4134198.
\end{aligned}
\]

It has 36 monomials and total degree seven. Its largest coefficient is
3,049,918,200. For the source \(P\), differentiate (9) once in \(j\)
and six times in \(h\) **before expanding**. Each product then has total
degree at most seven. For \(\mathcal R\), apply the same product rule to
(13) before expanding. Comparing either expression with the printed \(H\)
is therefore a bivariate degree-seven identity.

The six boundary jets are
\[
J_n^S(j)=\frac1{n!}\partial_h^nS(0,j),\qquad0\le n\le5.
\]
They need not be expanded at their original degrees. Instead use
\[
(r_0,r_1,r_2,r_3,r_4,r_5)=(3,3,3,2,1,0),
\qquad
\frac1{r_n!}\partial_j^{r_n}J_n^S=E_n(j).
\tag{17}
\]
Every polynomial required on the right is printed here:
\[
\begin{aligned}
E_0={}&- 417653280 j^{8} - 3204479520 j^{7} - 7882111440 j^{6} - 9725676912 j^{5}\\
 &- 6679640240 j^{4} - 2560023200 j^{3} - 527194800 j^{2} - 52860440 j\\
 &-1917872.
\end{aligned}
\]

\[
\begin{aligned}
E_1={}&417653280 j^{8} + 2213640000 j^{7} + 3562922160 j^{6} + 4492428696 j^{5}\\
 &+ 6038589480 j^{4} + 5225103520 j^{3} + 2212525980 j^{2} + 401048380 j\\
 &+ 22236336.
\end{aligned}
\]

\[
\begin{aligned}
E_2={}&1213803360 j^{7} + 5395314960 j^{6} + 9762385248 j^{5} + 10971299640 j^{4}\\
 &+ 7526296680 j^{3} + 2502488700 j^{2} + 258077160 j -9051728.
\end{aligned}
\]

\[
\begin{aligned}
E_3={}&- 83611440 j^{8} - 156714480 j^{7} - 931530348 j^{6} - 2677873464 j^{5}\\
 &- 3857682150 j^{4} - 3771064260 j^{3} - 2243220750 j^{2} - 624744804 j\\
 &-54049722.
\end{aligned}
\]

\[
\begin{aligned}
E_4={}&- 76120560 j^{8} - 463032720 j^{7} - 1536055080 j^{6} - 2420737704 j^{5}\\
 &- 2115575190 j^{4} - 1186604640 j^{3} - 382481316 j^{2} - 34502256 j\\
 &+ 5369328.
\end{aligned}
\]

\[
\begin{aligned}
E_5={}&- 14133528 j^{8} - 69509280 j^{7} - 98635824 j^{6} + 86846148 j^{5}\\
 &+ 327804060 j^{4} + 322441548 j^{3} + 160096236 j^{2} + 41361702 j\\
 &+ 3769971.
\end{aligned}
\]

Their monomial counts are 9, 9, 8, 9, 9, 9; the degrees are 8, 8, 7, 8,
8, 8. All coefficients have at most eleven digits.
For both choices of \(S\), the remaining scalar zero jets are
\[
\begin{aligned}
(J_0^S(0),(J_0^S)'(0),(J_0^S)''(0)/2)&=(0,24,-128394),\\
(J_1^S(0),(J_1^S)'(0),(J_1^S)''(0)/2)&=(-2408,-42700,1711224),\\
(J_2^S(0),(J_2^S)'(0),(J_2^S)''(0)/2)&=(110558,124392,-5568660),\\
(J_3^S(0),(J_3^S)'(0))&=(97600,-4110912),\\
J_4^S(0)&=945162.
\end{aligned}
\tag{18}
\]
No further scalar jet is required for \(n=5\), since \(r_5=0\).

**Order of verification.** For a source jet, take the indicated \(h\)
derivatives of each factored summand of (9), put \(h=0\), then take the
indicated \(j\) derivatives before expanding. The source has \(j\)-degree
at most twelve. After the original \(\partial_j\) and the three extra
\(j\) derivatives in the first three rows, the remaining univariate
degree is at most eight. In rows \(n=3,4,5\) the total-degree bound
also gives degree at most eight after the stated derivatives and \(h=0\).
The same reasoning applies to (13). The scalar comparisons in (18) require
only product-rule differentiation and evaluation at \((h,j)=(0,0)\).

These anchors are used solely for polynomial identity verification.
No inequality hypothesis is claimed at \(h=0\) or \(j=0\).

Taylor uniqueness in \(j\), applied to (17)--(18), gives
\(J_n^{\partial_jP}=J_n^{\mathcal R}\) for all six values of \(n\).
Taylor uniqueness in \(h\), using (16) and those six zero jets, then proves
(14) identically. Thus the large residual identity is derived from small
derivative identities and scalar endpoint values.

The exact size audit for the comparisons with (13) is:

| Check | Monomials | Degree | Common denominator after differentiating each summand | Largest coefficient after clearing |
| --- | ---: | ---: | ---: | ---: |
| Sixth \(h\)-derivative | 36 | 7 in \((h,j)\) | 54 | 164695582800 |
| Jet \(n=0\) | 9 | 8 in \(j\) | 6 | 58354061472 |
| Jet \(n=1\) | 9 | 8 in \(j\) | 27 | 215188312500 |
| Jet \(n=2\) | 8 | 7 in \(j\) | 12 | 131655595680 |
| Jet \(n=3\) | 9 | 8 in \(j\) | 16 | 81454400000 |
| Jet \(n=4\) | 9 | 8 in \(j\) | 16 | 38731803264 |
| Jet \(n=5\) | 9 | 8 in \(j\) | 216 | 100098828000 |

The maxima include coefficients in individual differentiated summands before
cancellation. The source-side comparisons from (9) have integer coefficients
after its displayed scalar factors cancel the input denominators. Their
individual expanded coefficient magnitudes are also at most twelve digits.
This is an expansion audit; all polynomial premises have been printed above.

## 4. The zero-gap value without a large expansion

The exact zero-gap identity is
\[
\begin{aligned}
P(h,0)={}&12h^2-22762h^3-38304h^4+80212h^5+116136h^6
             -578049h^7-1754001h^8\\
 &-h^8(2140842h+1430898h^2+552873h^3+118887h^4+11628h^5).
\end{aligned}
\tag{19}
\]
The outer \(h^8\) remains factored. The two explicit input polynomials have
seven and five monomials and degrees eight and five.
To verify (19), its divided fifth derivative agrees with that of (9) at
\(j=0\), and is the following small polynomial:
\[
\begin{aligned}
T_0={}&- 14965236 h^{8} - 94158504 h^{7} - 255427326 h^{6} - 360586296 h^{5}\\
 &- 269746092 h^{4} - 98224056 h^{3} - 12139029 h^{2} + 696816 h\\
 &+ 80212.
\end{aligned}
\]

It has nine monomials and degree eight, with largest coefficient 360,586,296.
On both sides the first five divided zero jets are
\[
(P(0,0),\partial_hP(0,0),\partial_h^2P(0,0)/2,
 \partial_h^3P(0,0)/6,\partial_h^4P(0,0)/24)
 =(0,0,12,-22762,-38304).
\tag{20}
\]
Put \(j=0\) in each source product first, then differentiate five times in
\(h\), and only then expand. Its degree is at most thirteen before these
five derivatives and at most eight afterwards. This supplies a second
Taylor-uniqueness proof with no high-degree expanded identity.

## 5. Integrate the derivative lower bound to the minimum-gap face

Inequality (15) holds throughout \(0\le j\le1/30\), without requiring
\(\mathcal M\) to have a positive sign there. Therefore
\[
P(h,1/30)\ge P(h,0)+500\int_0^{1/30}\mathcal M(h,s)\,ds.
\tag{21}
\]
The complete integer lower polynomial for this integral is
\[
\begin{aligned}
\mathcal I={}&- 477150 h^{8} - 85406 h^{7} + 170070 h^{6} + 150747 h^{5}\\
 &+ 34227 h^{4} + 228 h^{3} + 3679 h^{2} - 81 h\\
 &-8.
\end{aligned}
\]

It has nine monomials, degree eight, and coefficients of at most six digits.
Here are all arithmetic bounds used to obtain it. If
\(\mathcal M=\sum c_{ab}h^aj^b\), a term contributes
\(500c_{ab}/((b+1)30^{b+1})\) to the coefficient of \(h^a\) in the integral.
Round each such contribution downward. In increasing order of \(b\), the
nine resulting coefficient estimates are
\[
\begin{aligned}
I_0&\ge-2-1-1-1-1-1-1=-8,\\
I_1&\ge-84-24+21+6+0+0+0+0=-81,\\
I_2&\ge3683+68-69-3+0+0+0=3679,\\
I_3&\ge3250-2284-668-65-4-1=228,\\
I_4&\ge31500+2982-213-40-2=34227,\\
I_5&\ge125650+22978+1976+143=150747,\\
I_6&\ge137800+29078+3192=170070,\\
I_7&\ge-81784-3622=-85406,\\
I_8&=-477150.
\end{aligned}
\tag{22}
\]
The coefficients \(c_{ab}\) are all printed in the auxiliary note's (3).
For \(b\ge6\), no large denominator needs to be evaluated: the bound
\(500|c_{ab}|\le509090000<30^6\) puts every such contribution strictly
between \(-1\) and \(1\), and its displayed sign determines rounding to
\(-1\) or zero. For \(b\le5\), the largest denominator needed for these
scalar checks is \(6\cdot30^6=4374000000\). All are elementary integer
comparisons of at most twelve digits. Since \(h\ge0\), these coefficient
bounds prove the integral is at least \(\mathcal I(h)\).

Define the intermediate, fully printed polynomial
\[
\begin{aligned}
\mathcal B_1={}&- 3125747 h^{8} - 663455 h^{7} + 286206 h^{6} + 230959 h^{5}\\
 &- 4077 h^{4} - 22534 h^{3} + 3691 h^{2} - 81 h\\
 &-8.
\end{aligned}
\]

It has nine monomials and degree eight. Combining (19) with \(\mathcal I\)
and keeping the outer \(h^8\) gives the positive-factor identity
\[
\begin{aligned}
P(h,0)+\mathcal I(h)=\mathcal B_1(h)+h^8\bigl[&26/27
 +2140842(1/3-h)+1430898(1/9-h^2)\\
 &+552873(1/27-h^3)+118887(1/81-h^4)\\
 &+11628(1/243-h^5)\bigr].
\end{aligned}
\tag{23}
\]
To check (23), compare the displayed degree-eight lower parts, then the
five-term polynomial inside the common outer factor. Each identity to expand
has degree at most eight. Every bracket in (23) is nonnegative for \(h\le1/3\).
Thus (21) gives \(P(h,1/30)\ge\mathcal B_1(h)\).

Let \(\mathcal B\) be the nine-monomial polynomial (22) of the auxiliary
note, where \(\mathcal B>39\) is already proved. The small exact difference is
\[
\mathcal B_1-\mathcal B
 =h^7(25707h-9985)+164h^6+30h^5+h^4+2h^3+3-3h-3h^2.
\tag{24}
\]
It has nine monomials and degree eight. Use
\(25707h-9985\ge-14233/4\), \(h^7\le3^{-7}\), and
\(3-3h-3h^2\ge5/3\). After discarding the other positive terms,
\[
\mathcal B_1-\mathcal B\ge\frac53-\frac{14233}{8748}
 =\frac{347}{8748}>0.
\tag{25}
\]
Consequently \(P(h,1/30)>39\).

Section 2 makes \(P\) increasing from this minimum-gap face to every \(j\)
in (1). Hence \(P(h,j)>39\) on the whole maximum-duration face. The positive
normalization (10) proves (2), with the same multipliers and scalar bounds.

## Validation and implementation boundary

The proof consists of the printed positive factors, the independently proved
auxiliary signs, the divided-derivative interfaces (16)--(20), and the scalar
bounds (22). Exact symbolic arithmetic checks their transcription; no such
computation is a proof premise. A global expansion of (9), (13), or (19)
is outside the proposed verification interface. Differentiate and restrict
to the indicated zero face before each polynomial expansion.

This is a hand proof of one comparison face. No Lean compilation, CI run,
or measured Lean time or memory improvement is claimed.
