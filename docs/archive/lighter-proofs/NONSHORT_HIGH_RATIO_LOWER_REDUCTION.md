# High-ratio lower shape: reduce h before checking the face

## Scope and exact caller

This supplies the dimension reduction for the lower-shape sign N4a in
`MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_EXCLUSION` (13).
It uses the same constant multipliers 4 and 1, and the slightly larger
rational incoming-norm bound already used in the low-t replacement:
\[
 T_L(x)=\frac{912-401x}{24(17x+76)},\qquad
 V_L=1-\frac{(1-t)(t+x)}{(1+x)^2}
   +\frac{(1-t)x}{(1+x)^2}(T_L-t).
 \tag{R1}
\]
The logarithm and floor bounds are unchanged:
\[
 L=\frac{(q-1)(q^2+10q+1)}{6q(q+1)},\qquad
 F_\ell=1+\frac{(t+x)^2q}{(1+x)^2}
   -\frac{t+x}{1+x}\frac{q^2+10q+1}{6(q+1)}.
 \tag{R2}
\]
The logarithm inequality is valid for \(q\ge1\). The incoming comparison is
valid for \(x\ge0\), because
\[
 T_L-T_G=
 \frac{5x(7x-3)^2}{24(17x+76)(x^2+10x+15)}\ge0.
 \tag{R3}
\]
This identity has three numerator monomials and degree three; it is checked
with the displayed factored denominators, of total degree at most four.
Only this rational logarithm bound is used; no square-root or arctangent
approximation is introduced.

Let \(G_{4,L}\) be the original constant-multiplier residual with \(V_L\)
in place of \(V_G\). Put
\[
 k=29t^2/4,\quad h=1-2t,\quad j=x-h,\quad q=1+y,
 \quad W=1+x,\quad D=17x+76,
\]
\[
 S=96q(q+1)W^3D\,G_{4,L},\qquad
 \mathcal H=\partial_x-\tfrac12\partial_t.
 \tag{R4}
\]
The dependence \(k=29t^2/4\) is included before differentiating.

**Derivative claims.** On
\[
 3/8\le t\le2/5,\quad7/30\le x\le3/7,\quad0\le y\le1/4,
 \tag{R5}
\]
we have \(-\mathcal H^2S>30000\). At \(t=2/5\) on the same x,y rectangle,
\(-\mathcal HS>680\).
Consequently, on the original face domain
\[
 1/5\le h\le1/4,\quad1/30\le j\le5h/7,\quad
 0\le y\le\frac{h-j}{1+2j},
 \tag{R6}
\]
the normalized residual decreases strictly in h and
\[
 S(h,j,y)\ge S(1/4,j,y).
 \tag{R7}
\]
The [two-variable endpoint proof](NONSHORT_HIGH_RATIO_LOWER_FACE.md) supplies
`S>=13/4` on `h=1/4`. Together the two notes prove the original lower-shape
sign throughout (R6); section 7 states the complete conclusion.

For the original sign, \(G_4\ge G_{4,L}\) on the entire domain (R6).
Indeed the already proved constant-multiplier scalar derivative
`fh_LGB_Cv` in `FwdHand/LargeGap.lean` is negative for
\(t\in[1/3,2/5]\), \(j\ge1/30\), \(k\ge1\), and the same event cap;
it does not require \(k\le1+j\). Here \(k=29t^2/4>1\), and (R3) gives
\(V_L\ge V_G\). The logarithm and floor arguments agree.
Thus a positive endpoint in (R7) proves the original N4a sign on its
unchanged domain.

The exact Lean caller is `hA` in `fh_LGB_core` in
`SmoothedOctagon/Exclusion/Mixed/FwdHand/LargeGap.lean`.
Its existing `fhCLGc_pos_y` and `fh_LGc_link` are the lower-shape dependency
replaced by this proof and its endpoint. The normalization is
\(S=24(q+1)WD\,\mathrm{fhComb}(4,1;V_L,L,F_\ell)\).
The [high-ratio shape monotonicity](NONSHORT_HIGH_RATIO_SHAPE.md) already
removes the caller's other endpoint dependency.

## 1. Complete source interface

For \(p=t+x\), \(Y=x(x+2)\), \(J=t+Y\), and
\(B_s=29t^2/4+2tx+x^2\), the source residual is affine in a free norm v
and logarithm scalar ell:
\[
 G(v,\ell)=\frac{C}{4qW^2}+\frac{A}{qW}v
              -\frac{pqB}{W(q-1)}\ell.
 \tag{R8}
\]
Write \(A=\sum_{i=0}^4A_iq^i\), \(B=\sum_{i=0}^3B_iq^i\),
and \(C=\sum_{i=0}^5C_iq^i\). The full coefficient polynomials follow.
The v numerator's W factor is cancelled before clearing any other
norm denominator. Each coefficient identity for (R8) has at most 27
monomials and degree at most eight in t,x.

\[
\begin{aligned}
A_{0}(t,x)={}&t^{2} x^{4} + 4 t^{2} x^{3} + 6 t^{2} x^{2} + 4 t^{2} x\\
&{}+t^{2} + t x^{5} + 4 t x^{4} + 6 t x^{3}\\
&{}+4 t x^{2} + t x
\end{aligned}
\]
This identity has 10 monomials, total degree 6, and largest cleared coefficient 6.

\[
\begin{aligned}
A_{1}(t,x)={}&- t^{2} x^{3} - 3 t^{2} x^{2} - 3 t^{2} x - t^{2}\\
&{}- t x^{5} - 5 t x^{4} - 9 t x^{3} - 7 t x^{2}\\
&{}- 2 t x - x - 1
\end{aligned}
\]
This identity has 11 monomials, total degree 6, and largest cleared coefficient 9.

\[
\begin{aligned}
A_{2}(t,x)={}&\frac{1}{4}\bigl[- 145 t^{3} x^{3} - 319 t^{3} x^{2} - 203 t^{3} x - 29 t^{3}\\
&{}- 8 t^{2} x^{4} + 124 t^{2} x^{3} + 272 t^{2} x^{2} + 140 t^{2} x\\
&{}+12 t x^{5} + 68 t x^{4} + 100 t x^{3} + 44 t x^{2}\bigr]
\end{aligned}
\]
This identity has 12 monomials, total degree 6, and largest cleared coefficient 319.

\[
\begin{aligned}
A_{3}(t,x)={}&\frac{1}{4}\bigl[29 t^{3} x + 29 t^{3} - 108 t^{2} x^{3} - 324 t^{2} x^{2}\\
&{}- 216 t^{2} x - 12 t x^{5} - 60 t x^{4} - 96 t x^{3}\\
&{}- 48 t x^{2}\bigr]
\end{aligned}
\]
This identity has 9 monomials, total degree 6, and largest cleared coefficient 324.

\[
\begin{aligned}
A_{4}(t,x)={}&\frac{1}{4}\bigl[29 t^{4} x + 29 t^{3} x^{3} + 87 t^{3} x^{2} + 21 t^{3} x\\
&{}+4 t^{2} x^{4} + 4 t^{2} x^{3} - 12 t^{2} x^{2} - 4 t x^{4}\\
&{}- 8 t x^{3}\bigr]
\end{aligned}
\]
This identity has 9 monomials, total degree 6, and largest cleared coefficient 87.

\[
\begin{aligned}
B_{0}(t,x)={}&\frac{1}{4}\bigl[- 145 t^{3} x^{2} - 290 t^{3} x - 145 t^{3} - 40 t^{2} x^{3}\\
&{}- 80 t^{2} x^{2} - 40 t^{2} x - 20 t x^{4} - 40 t x^{3}\\
&{}- 20 t x^{2} + 4\bigr]
\end{aligned}
\]
This identity has 10 monomials, total degree 5, and largest cleared coefficient 290.

\[
\begin{aligned}
B_{1}(t,x)={}&\frac{5}{4}\bigl[29 t^{3} x^{2} + 58 t^{3} x + 29 t^{3} + 8 t^{2} x^{3}\\
&{}+16 t^{2} x^{2} + 8 t^{2} x + 4 t x^{4} + 8 t x^{3}\\
&{}+4 t x^{2}\bigr]
\end{aligned}
\]
This identity has 9 monomials, total degree 5, and largest cleared coefficient 290.

\[
\begin{aligned}
B_{2}(t,x)={}&\frac{1}{4}\bigl[29 t^{4} + 29 t^{3} x^{2} + 66 t^{3} x + 8 t^{2} x^{3}\\
&{}+20 t^{2} x^{2} + 4 t x^{4} + 8 t x^{3}\bigr]
\end{aligned}
\]
This identity has 7 monomials, total degree 5, and largest cleared coefficient 66.

\[
\begin{aligned}
B_{3}(t,x)={}&\frac{1}{4}\bigl[- 29 t^{4} - 29 t^{3} x^{2} - 66 t^{3} x - 8 t^{2} x^{3}\\
&{}- 20 t^{2} x^{2} - 4 t x^{4} - 8 t x^{3}\bigr]
\end{aligned}
\]
This identity has 7 monomials, total degree 5, and largest cleared coefficient 66.

\[
\begin{aligned}
C_{0}(t,x)={}&3\bigl[- t^{2} x^{5} - 5 t^{2} x^{4} - 10 t^{2} x^{3} - 10 t^{2} x^{2}\\
&{}- 5 t^{2} x - t^{2} - t x^{6} - 5 t x^{5}\\
&{}- 10 t x^{4} - 10 t x^{3} - 5 t x^{2} - t x\bigr]
\end{aligned}
\]
This identity has 12 monomials, total degree 7, and largest cleared coefficient 30.

\[
\begin{aligned}
C_{1}(t,x)={}&- 8 t^{3} x^{4} - 32 t^{3} x^{3} - 48 t^{3} x^{2} - 32 t^{3} x\\
&{}- 8 t^{3} - 16 t^{2} x^{5} - 61 t^{2} x^{4} - 84 t^{2} x^{3}\\
&{}- 46 t^{2} x^{2} - 4 t^{2} x + 3 t^{2} - 5 t x^{6}\\
&{}- 14 t x^{5} - 6 t x^{4} + 16 t x^{3} + 19 t x^{2}\\
&{}+6 t x + 4 x^{2} + 8 x + 4
\end{aligned}
\]
This identity has 20 monomials, total degree 7, and largest cleared coefficient 84.

\[
\begin{aligned}
C_{2}(t,x)={}&\frac{1}{2}\bigl[232 t^{5} x^{3} + 406 t^{5} x^{2} + 116 t^{5} x - 58 t^{5}\\
&{}+232 t^{4} x^{4} - 357 t^{4} x^{3} - 1803 t^{4} x^{2} - 1607 t^{4} x\\
&{}- 393 t^{4} - 665 t^{3} x^{4} - 1407 t^{3} x^{3} - 721 t^{3} x^{2}\\
&{}+119 t^{3} x + 98 t^{3} - 212 t^{2} x^{5} - 636 t^{2} x^{4}\\
&{}- 796 t^{2} x^{3} - 532 t^{2} x^{2} - 160 t^{2} x + 8 t^{2}\\
&{}- 60 t x^{6} - 148 t x^{5} - 124 t x^{4} - 44 t x^{3}\\
&{}- 8 t x^{2} + 16 t x + 8 x^{2}\bigr]
\end{aligned}
\]
This identity has 27 monomials, total degree 8, and largest cleared coefficient 1803.

\[
\begin{aligned}
C_{3}(t,x)={}&\frac{1}{2}\bigl[232 t^{5} x^{2} + 464 t^{5} x + 232 t^{5} - 232 t^{4} x^{4}\\
&{}+628 t^{4} x^{3} + 2353 t^{4} x^{2} + 1894 t^{4} x + 401 t^{4}\\
&{}+1185 t^{3} x^{4} + 2760 t^{3} x^{3} + 1883 t^{3} x^{2} + 226 t^{3} x\\
&{}- 82 t^{3} + 344 t^{2} x^{5} + 1076 t^{2} x^{4} + 1456 t^{2} x^{3}\\
&{}+1060 t^{2} x^{2} + 336 t^{2} x + 108 t x^{6} + 304 t x^{5}\\
&{}+284 t x^{4} + 88 t x^{3}\bigr]
\end{aligned}
\]
This identity has 22 monomials, total degree 8, and largest cleared coefficient 2760.

\[
\begin{aligned}
C_{4}(t,x)={}&\frac{1}{16}\bigl[377 t^{6} x + 841 t^{6} - 551 t^{5} x^{2} - 423 t^{5} x\\
&{}- 1392 t^{5} - 2216 t^{4} x^{3} - 4600 t^{4} x^{2} - 4288 t^{4} x\\
&{}- 64 t^{4} - 2136 t^{3} x^{4} - 5944 t^{3} x^{3} - 5504 t^{3} x^{2}\\
&{}- 656 t^{3} x - 688 t^{2} x^{5} - 2160 t^{2} x^{4} - 2112 t^{2} x^{3}\\
&{}- 320 t^{2} x^{2} - 240 t x^{6} - 752 t x^{5} - 704 t x^{4}\\
&{}- 128 t x^{3}\bigr]
\end{aligned}
\]
This identity has 21 monomials, total degree 7, and largest cleared coefficient 5944.

\[
\begin{aligned}
C_{5}(t,x)={}&\frac{1}{16}\bigl[- 841 t^{6} - 841 t^{5} x^{2} - 2146 t^{5} x - 464 t^{4} x^{3}\\
&{}- 1224 t^{4} x^{2} - 296 t^{3} x^{4} - 656 t^{3} x^{3} - 64 t^{2} x^{5}\\
&{}- 144 t^{2} x^{4} - 16 t x^{6} - 32 t x^{5}\bigr]
\end{aligned}
\]
This identity has 11 monomials, total degree 7, and largest cleared coefficient 2146.

The numerator of the incoming norm is \(V_n=24DW^2V_L\):

\[
\begin{aligned}
V_n(t,x)={}&408 t^{2} x^{2} + 2232 t^{2} x + 1824 t^{2} + 401 t x^{2}\\
&{}- 1320 t x - 1824 t + 408 x^{3} + 1831 x^{2}\\
&{}+3144 x + 1824
\end{aligned}
\]
This identity has 10 monomials, total degree 4, and largest cleared coefficient 3144.

After the removable cancellation at q=1, the exact source circuit is
\[
 S=24WD(q+1)C+4(q+1)AV_n
       -16W^2DpqB(q^2+10q+1).
 \tag{R9}
\]
Keep these three products and the powers of q factored.
Their coefficients have total degree at most ten in t,x.
For the next section, differentiate twice by \(\mathcal H\) before expanding
any coefficient; the resulting identities have degree at most eight.
The first-derivative boundary identities in section 4 specialize t before
expanding, and are univariate of degree at most eight.

## 2. A strictly negative second h derivative

Write \(-\mathcal H^2S=\sum_{i=0}^6R_i(t,x)y^i\). These are the seven
complete derivative identities from the source circuit:

\[
\begin{aligned}
R_{0}(t,x)={}&\frac{1}{2}\bigl[- 514692 t^{6} x - 938556 t^{6} + 1544076 t^{5} x^{2} + 5582964 t^{5} x\\
&{}+3027948 t^{5} + 3077915 t^{4} x^{3} - 4089471 t^{4} x^{2} - 9263544 t^{4} x\\
&{}- 2081736 t^{4} - 2937920 t^{3} x^{4} - 487862 t^{3} x^{3} + 15958326 t^{3} x^{2}\\
&{}+12670128 t^{3} x + 1061664 t^{3} + 88176 t^{2} x^{5} - 712944 t^{2} x^{4}\\
&{}- 15230760 t^{2} x^{3} - 27234108 t^{2} x^{2} - 12932160 t^{2} x - 1000704 t^{2}\\
&{}+39168 t x^{6} + 524040 t x^{5} + 4472136 t x^{4} + 13286018 t x^{3}\\
&{}+13807800 t x^{2} + 4530912 t x + 148960 t - 26112 x^{6}\\
&{}- 287136 x^{5} - 1209992 x^{4} - 2032632 x^{3} - 1356240 x^{2}\\
&{}- 220288 x + 52832\bigr]
\end{aligned}
\]
This identity has 34 monomials, total degree 7, and largest cleared coefficient 27234108.

\[
\begin{aligned}
R_{1}(t,x)={}&\frac{1}{4}\bigl[- 4632228 t^{6} x - 8103876 t^{6} - 3786240 t^{5} x^{3} - 1015812 t^{5} x^{2}\\
&{}+37804284 t^{5} x + 22487412 t^{5} + 16091520 t^{4} x^{4} + 94567235 t^{4} x^{3}\\
&{}+87542823 t^{4} x^{2} + 3556170 t^{4} x + 628544 t^{4} - 7840128 t^{3} x^{5}\\
&{}- 79804580 t^{3} x^{4} - 169710594 t^{3} x^{3} - 107525394 t^{3} x^{2} - 39818432 t^{3} x\\
&{}- 17885520 t^{3} + 39168 t^{2} x^{6} + 5753664 t^{2} x^{5} + 15174672 t^{2} x^{4}\\
&{}- 52607936 t^{2} x^{3} - 109537212 t^{2} x^{2} - 39778512 t^{2} x + 1640512 t^{2}\\
&{}+78336 t x^{7} + 1570432 t x^{6} + 14140512 t x^{5} + 67758112 t x^{4}\\
&{}+141898974 t x^{3} + 120676356 t x^{2} + 33922144 t x + 1088928 t\\
&{}- 52672 x^{7} - 991552 x^{6} - 7019312 x^{5} - 19481208 x^{4}\\
&{}- 24657864 x^{3} - 13629536 x^{2} - 2163744 x + 186912\bigr]
\end{aligned}
\]
This identity has 40 monomials, total degree 8, and largest cleared coefficient 169710594.

\[
\begin{aligned}
R_{2}(t,x)={}&\frac{1}{4}\bigl[- 8235072 t^{6} x - 13472820 t^{6} - 11358720 t^{5} x^{3} - 14672376 t^{5} x^{2}\\
&{}+69500820 t^{5} x + 40794996 t^{5} + 41028480 t^{4} x^{4} + 208903160 t^{4} x^{3}\\
&{}+223032855 t^{4} x^{2} + 26076201 t^{4} x - 3444028 t^{4} - 19916928 t^{3} x^{5}\\
&{}- 178069730 t^{3} x^{4} - 428454430 t^{3} x^{3} - 398993628 t^{3} x^{2} - 180045272 t^{3} x\\
&{}- 40441624 t^{3} + 489600 t^{2} x^{6} + 17946384 t^{2} x^{5} + 67894080 t^{2} x^{4}\\
&{}+55623284 t^{2} x^{3} + 15804864 t^{2} x^{2} + 28909752 t^{2} x + 11805728 t^{2}\\
&{}+156672 t x^{7} + 4372736 t x^{6} + 36214584 t x^{5} + 140467808 t x^{4}\\
&{}+244811494 t x^{3} + 180499518 t x^{2} + 44163008 t x + 1317344 t\\
&{}- 327296 x^{7} - 4063936 x^{6} - 20339416 x^{5} - 45252760 x^{4}\\
&{}- 48573592 x^{3} - 23494216 x^{2} - 3459920 x + 81120\bigr]
\end{aligned}
\]
This identity has 40 monomials, total degree 8, and largest cleared coefficient 428454430.

\[
\begin{aligned}
R_{3}(t,x)={}&\frac{1}{2}\bigl[- 3602844 t^{6} x - 5197380 t^{6} - 6152640 t^{5} x^{3} - 5695020 t^{5} x^{2}\\
&{}+43742556 t^{5} x + 21896276 t^{5} + 17874480 t^{4} x^{4} + 84334165 t^{4} x^{3}\\
&{}+78523983 t^{4} x^{2} - 21611512 t^{4} x - 12619984 t^{4} - 8040048 t^{3} x^{5}\\
&{}- 68524600 t^{3} x^{4} - 174082794 t^{3} x^{3} - 176676718 t^{3} x^{2} - 74106992 t^{3} x\\
&{}- 12358736 t^{3} + 195840 t^{2} x^{6} + 7716282 t^{2} x^{5} + 34036512 t^{2} x^{4}\\
&{}+60804196 t^{2} x^{3} + 64151904 t^{2} x^{2} + 36121464 t^{2} x + 5892960 t^{2}\\
&{}+58752 t x^{7} + 2491640 t x^{6} + 18828075 t x^{5} + 60741061 t x^{4}\\
&{}+89785916 t x^{3} + 57526596 t x^{2} + 12217248 t x + 336128 t\\
&{}- 298448 x^{7} - 2922176 x^{6} - 11331548 x^{5} - 21133328 x^{4}\\
&{}- 19889980 x^{3} - 8618592 x^{2} - 1161440 x - 1888\bigr]
\end{aligned}
\]
This identity has 40 monomials, total degree 8, and largest cleared coefficient 176676718.

\[
\begin{aligned}
R_{4}(t,x)={}&\frac{1}{2}\bigl[- 1544076 t^{6} x - 1614720 t^{6} - 2839680 t^{5} x^{3} + 1381212 t^{5} x^{2}\\
&{}+32453784 t^{5} x + 12557232 t^{5} + 5801760 t^{4} x^{4} + 24556505 t^{4} x^{3}\\
&{}+5816628 t^{4} x^{2} - 41636421 t^{4} x - 11915792 t^{4} - 2100384 t^{3} x^{5}\\
&{}- 16378910 t^{3} x^{4} - 42658044 t^{3} x^{3} - 42463770 t^{3} x^{2} - 11110588 t^{3} x\\
&{}- 1589468 t^{3} + 19584 t^{2} x^{6} + 1651692 t^{2} x^{5} + 8509392 t^{2} x^{4}\\
&{}+24433554 t^{2} x^{3} + 33440100 t^{2} x^{2} + 16226772 t^{2} x + 1752576 t^{2}\\
&{}+14688 t x^{7} + 1302244 t x^{6} + 8853138 t x^{5} + 22700346 t x^{4}\\
&{}+26489965 t x^{3} + 13480419 t x^{2} + 2316480 t x + 65664 t\\
&{}- 218500 x^{7} - 1793292 x^{6} - 5402340 x^{5} - 8089564 x^{4}\\
&{}- 6371832 x^{3} - 2352384 x^{2} - 262656 x\bigr]
\end{aligned}
\]
This identity has 39 monomials, total degree 8, and largest cleared coefficient 42658044.

\[
\begin{aligned}
R_{5}(t,x)={}&\frac{1}{4}\bigl[- 514692 t^{6} x + 90828 t^{6} - 946560 t^{5} x^{3} + 4613436 t^{5} x^{2}\\
&{}+23337228 t^{5} x + 5929572 t^{5} + 987360 t^{4} x^{4} + 1246075 t^{4} x^{3}\\
&{}- 21447525 t^{4} x^{2} - 41800050 t^{4} x - 7271280 t^{4} - 79968 t^{3} x^{5}\\
&{}+1205060 t^{3} x^{4} + 5428310 t^{3} x^{3} + 10829790 t^{3} x^{2} + 11652912 t^{3} x\\
&{}+371136 t^{3} - 19584 t^{2} x^{6} - 571836 t^{2} x^{5} - 2685600 t^{2} x^{4}\\
&{}+758400 t^{2} x^{3} + 7230492 t^{2} x^{2} + 2840256 t^{2} x + 116736 t^{2}\\
&{}+597888 t x^{6} + 3646062 t x^{5} + 6888930 t x^{4} + 4859038 t x^{3}\\
&{}+831456 t x^{2} - 14592 t x - 126480 x^{7} - 901504 x^{6}\\
&{}- 2071560 x^{5} - 2192920 x^{4} - 1158144 x^{3} - 233472 x^{2}\bigr]
\end{aligned}
\]
This identity has 36 monomials, total degree 8, and largest cleared coefficient 41800050.

\[
\begin{aligned}
R_{6}(t,x)={}&\frac{1}{4}\bigl[171564 t^{6} + 1029384 t^{5} x^{2} + 3052308 t^{5} x + 244180 t^{5}\\
&{}- 926840 t^{4} x^{3} - 5878305 t^{4} x^{2} - 7885895 t^{4} x - 1092580 t^{4}\\
&{}+243950 t^{3} x^{4} + 1362690 t^{3} x^{3} + 2857492 t^{3} x^{2} + 2502400 t^{3} x\\
&{}+76608 t^{3} - 106896 t^{2} x^{5} - 582960 t^{2} x^{4} - 492352 t^{2} x^{3}\\
&{}+307920 t^{2} x^{2} + 76608 t^{2} x + 14960 t x^{6} + 80376 t x^{5}\\
&{}+104024 t x^{4} - 8560 t x^{3} - 69312 t x^{2} - 2720 x^{7}\\
&{}- 10000 x^{6} + 12368 x^{5} + 47200 x^{4} + 21888 x^{3}\bigr]
\end{aligned}
\]
This identity has 28 monomials, total degree 7, and largest cleared coefficient 7885895.

For \(i=1,\ldots,6\), direct monomial comparison in
\(3/8\le t\le2/5\) gives \(R_i\ge Q_i(x)\).
For a positive coefficient of \(t^a x^b\), substitute \(t=3/8\);
for a negative one substitute \(t=2/5\), then round the resulting
coefficient of x down to an integer. The complete lower polynomials are:

\[
\begin{aligned}
Q_{1}(x)={}&- 5824 x^{7} - 99283 x^{6} - 352320 x^{5} + 818186 x^{4}\\
&{}+2776709 x^{3} + 2234327 x^{2} + 493954 x - 43180
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 2776709.

\[
\begin{aligned}
Q_{2}(x)={}&- 67136 x^{7} - 588828 x^{6} - 1377481 x^{5} + 1596291 x^{4}\\
&{}+6911621 x^{3} + 6285096 x^{2} + 1660270 x - 48447
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 6911621.

\[
\begin{aligned}
Q_{3}(x)={}&- 138208 x^{7} - 980136 x^{6} - 1850241 x^{5} + 1199427 x^{4}\\
&{}+6396883 x^{3} + 6081229 x^{2} + 1756567 x - 10042
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 6396883.

\[
\begin{aligned}
Q_{4}(x)={}&- 106496 x^{7} - 651099 x^{6} - 992285 x^{5} + 343090 x^{4}\\
&{}+2362147 x^{3} + 2406437 x^{2} + 672644 x - 24592
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 2406437.

\[
\begin{aligned}
Q_{5}(x)={}&- 31620 x^{7} - 170108 x^{6} - 200225 x^{5} + 10951 x^{4}\\
&{}+267963 x^{3} + 287842 x^{2} + 27239 x - 26484
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 287842.

\[
\begin{aligned}
Q_{6}(x)={}&- 680 x^{7} - 1098 x^{6} + 6351 x^{5} + 1449 x^{4}\\
&{}- 3045 x^{3} + 5853 x^{2} - 9128 x - 5411
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 9128.

Section 5 verifies these small one-variable signs:
\[
 Q_1,Q_2,Q_3>0,\qquad Q_4>288000,\qquad Q_5,Q_6>-10000.
 \tag{R10}
\]
Once \(R_0>30000\) is proved below, they imply
\[
\begin{aligned}
 -\mathcal H^2S
 &\ge R_0+R_1y+R_2y^2+R_3y^3
       +y^4(288000-10000y-10000y^2)\\
 &>30000,
\end{aligned}
 \tag{R11}
\]
because \(0\le y\le1/4\). This is an explicit sum of products with known
signs, not a three-variable expansion.

## 3. The constant coefficient: reduce x first

The full derivative polynomial is

\[
\begin{aligned}
\partial_xR_0(t,x)={}&\frac{1}{2}\bigl[- 514692 t^{6} + 3088152 t^{5} x + 5582964 t^{5} + 9233745 t^{4} x^{2}\\
&{}- 8178942 t^{4} x - 9263544 t^{4} - 11751680 t^{3} x^{3} - 1463586 t^{3} x^{2}\\
&{}+31916652 t^{3} x + 12670128 t^{3} + 440880 t^{2} x^{4} - 2851776 t^{2} x^{3}\\
&{}- 45692280 t^{2} x^{2} - 54468216 t^{2} x - 12932160 t^{2} + 235008 t x^{5}\\
&{}+2620200 t x^{4} + 17888544 t x^{3} + 39858054 t x^{2} + 27615600 t x\\
&{}+4530912 t - 156672 x^{5} - 1435680 x^{4} - 4839968 x^{3}\\
&{}- 6097896 x^{2} - 2712480 x - 220288\bigr]
\end{aligned}
\]
This identity has 27 monomials, total degree 6, and largest cleared coefficient 54468216.

The same monomial comparison in t gives \(\partial_xR_0\ge L_x\), where

\[
\begin{aligned}
L_x(x)={}&2\bigl[- 17136 x^{5} - 97777 x^{4} + 164961 x^{3} + 406760 x^{2}\\
&{}+106270 x - 30011\bigr]
\end{aligned}
\]
This identity has 6 monomials, total degree 5, and largest cleared coefficient 813520.

For \(1/5\le x\le1/2\), absorb the two negative high terms using
\(x^5\le x^3/4\) and \(x^4\le x^3/2\). Thus
\[
 L_x\ge223577x^3+813520x^2+212540x-60022
 \ge2101927/125>16000.
 \tag{R12}
\]
This lower polynomial has four monomials and degree three.
Hence \(R_0(t,x)\ge R_0(t,1/5)\) on (R5).
The endpoint polynomial is

\[
\begin{aligned}
R_0(t,1/5)={}&\frac{1}{15625}\bigl[- 8136675000 t^{6} + 32861748750 t^{5} - 31823440000 t^{4} + 33011086500 t^{3}\\
&{}- 37495772610 t^{2} + 13445845009 t - 498170296\bigr]
\end{aligned}
\]
This identity has 7 monomials, total degree 6, and largest cleared coefficient 37495772610.

Coefficientwise downward rounding gives \(R_0(t,1/5)\ge1000K_0(t)\), with

\[
\begin{aligned}
K_0(t)={}&- 521 t^{6} + 2103 t^{5} - 2037 t^{4} + 2112 t^{3}\\
&{}- 2400 t^{2} + 860 t - 32
\end{aligned}
\]
This identity has 7 monomials, total degree 6, and largest cleared coefficient 2400.

\[
\begin{aligned}
262144K_0(3/8+a)={}&- 136577024 a^{6} + 243990528 a^{5} + 211587072 a^{4} + 383870976 a^{3}\\
&{}- 206637504 a^{2} - 77050192 a + 10024135
\end{aligned}
\]
This identity has 7 monomials, total degree 6, and largest cleared coefficient 383870976.

Here \(0\le a\le1/40\). Discard its three positive nonconstant terms,
and bound its negative powers at 1/40. The resulting bound is
\(K_0>30\). This proves \(R_0>30000\), completing (R11).

## 4. The initial first derivative and transport in h

Put \(-\mathcal HS(2/5,x,1+y)=\sum_{i=0}^6B_i(x)y^i\).
These coefficients refer to the first derivative of the source circuit,
including the variation of k; they are not the source B_i from section 1.
The complete boundary polynomials are

\[
\begin{aligned}
B_{0}(x)={}&\frac{4}{15625}\bigl[3060000 x^{6} + 93538000 x^{5} + 286645500 x^{4} + 273027195 x^{3}\\
&{}+25939717 x^{2} - 28225548 x + 3507552\bigr]
\end{aligned}
\]
This identity has 7 monomials, total degree 6, and largest cleared coefficient 1146582000.

\[
\begin{aligned}
B_{1}(x)={}&\frac{2}{15625}\bigl[5945000 x^{7} + 171145000 x^{6} + 2278233450 x^{5} + 5887632050 x^{4}\\
&{}+5348931815 x^{3} + 1088785273 x^{2} - 387589548 x - 18569184\bigr]
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 11775264100.

\[
\begin{aligned}
B_{2}(x)={}&\frac{2}{15625}\bigl[- 25500000 x^{8} - 122510000 x^{7} + 707888000 x^{6} + 7535926925 x^{5}\\
&{}+18035006275 x^{4} + 16945689690 x^{3} + 5339867462 x^{2} - 226022080 x\\
&{}-64720992\bigr]
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 36070012550.

\[
\begin{aligned}
B_{3}(x)={}&\frac{8}{15625}\bigl[- 17000000 x^{8} - 80145625 x^{7} + 238697125 x^{6} + 2263812650 x^{5}\\
&{}+5110989525 x^{4} + 4867544280 x^{3} + 1784039742 x^{2} + 88968075 x\\
&{}-2757112\bigr]
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 40887916200.

\[
\begin{aligned}
B_{4}(x)={}&\frac{2}{15625}\bigl[- 59500000 x^{8} - 272058125 x^{7} + 511748125 x^{6} + 4400565450 x^{5}\\
&{}+9184567950 x^{4} + 8639017115 x^{3} + 3292686197 x^{2} + 280192520 x\\
&{}+52944288\bigr]
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 18369135900.

\[
\begin{aligned}
B_{5}(x)={}&\frac{2}{15625}\bigl[- 19125000 x^{8} - 85181250 x^{7} + 100356375 x^{6} + 772778975 x^{5}\\
&{}+1391652075 x^{4} + 1215760195 x^{3} + 363897102 x^{2} - 15698616 x\\
&{}+23148096\bigr]
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 2783304150.

\[
\begin{aligned}
B_{6}(x)={}&\frac{4}{15625}\bigl[- 265625 x^{8} - 1028125 x^{7} - 1597500 x^{6} - 15170750 x^{5}\\
&{}- 39580125 x^{4} - 49476845 x^{3} - 49763250 x^{2} - 24385604 x\\
&{}-1310168\bigr]
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 199053000.

Section 6 verifies
\[
 B_0>680,\qquad B_1,B_2,B_3,B_4>0,\qquad
 B_5>7600,\qquad B_6>-7000.
 \tag{R13}
\]
Therefore
\[
 -\mathcal HS(2/5,x,1+y)
 \ge B_0+B_1y+B_2y^2+B_3y^3+B_4y^4+y^5(7600-7000y)>680.
 \tag{R14}
\]

Fix an original j,y. Increase h from 1/5 to its given value.
The initial x is \(1/5+j\ge7/30\), and along the segment
\(x=h+j\le1/4+5/28=3/7\). Also \(0\le y\le1/4\).
Thus (R11) makes \(\mathcal HS\) strictly decreasing along this segment,
and (R14) gives \(\mathcal HS<-680\).
Finally increase h to 1/4 at fixed j,y. The event cap only increases,
and the whole segment stays in the same rectangle. This proves (R7).
No floor, incoming trajectory, or Casimir hypothesis is transferred along
these comparison segments; this is a scalar monotonicity proof of S.

## 5. The six univariate signs for the second derivative

For i=1,2,3,4, coefficientwise downward rounding gives
\(Q_i\ge1000U_i\). For i=5,6 it gives
\(Q_i+10000\ge1000U_i\). Each difference has nonnegative coefficients,
at most eight monomials and degree at most seven.

All six U_i and their shifted identities are printed below.
Use \(z=x-1/5\in[1/30,8/35]\), substitute 1/30 in each positive
monomial and 8/35 in each negative monomial. The resulting bounds are stated
beside the corresponding identities; no subdivision or coefficient table
is required.

### Second-derivative comparison 1

\[
\begin{aligned}
U_{1}(x)={}&- 6 x^{7} - 100 x^{6} - 353 x^{5} + 818 x^{4}\\
&{}+2776 x^{3} + 2234 x^{2} + 493 x - 44
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 2776.

\[
\begin{aligned}
78125U_{1}(1/5+z)={}&- 468750 z^{7} - 8468750 z^{6} - 37346875 z^{5} + 31509375 z^{4}\\
&{}+255692500 z^{3} + 317596850 z^{2} + 136162290 z + 13074794
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 317596850.

The monomial bounds give \(U_1>229\).

### Second-derivative comparison 2

\[
\begin{aligned}
U_{2}(x)={}&- 68 x^{7} - 589 x^{6} - 1378 x^{5} + 1596 x^{4}\\
&{}+6911 x^{3} + 6285 x^{2} + 1660 x - 49
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 6911.

\[
\begin{aligned}
78125U_{2}(1/5+z)={}&- 5312500 z^{7} - 53453125 z^{6} - 167337500 z^{5} - 12065625 z^{4}\\
&{}+588949375 z^{3} + 835141175 z^{2} + 393922395 z + 46231412
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 835141175.

The monomial bounds give \(U_2>770\).

### Second-derivative comparison 3

\[
\begin{aligned}
U_{3}(x)={}&- 139 x^{7} - 981 x^{6} - 1851 x^{5} + 1199 x^{4}\\
&{}+6396 x^{3} + 6081 x^{2} + 1756 x - 11
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 6396.

\[
\begin{aligned}
78125U_{3}(1/5+z)={}&- 10859375 z^{7} - 91843750 z^{6} - 245700000 z^{5} - 99962500 z^{4}\\
&{}+503910625 z^{3} + 783890775 z^{2} + 388869860 z + 49677306
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 783890775.

The monomial bounds give \(U_3>807\).

### Second-derivative comparison 4

\[
\begin{aligned}
U_{4}(x)={}&- 107 x^{7} - 652 x^{6} - 993 x^{5} + 343 x^{4}\\
&{}+2362 x^{3} + 2406 x^{2} + 672 x - 25
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 2406.

\[
\begin{aligned}
78125U_{4}(1/5+z)={}&- 8359375 z^{7} - 62640625 z^{6} - 145725000 z^{5} - 83684375 z^{4}\\
&{}+166319375 z^{3} + 297633825 z^{2} + 149966580 z + 17556558
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 297633825.

The monomial bounds give \(U_4>288\).

### Second-derivative comparison 5

\[
\begin{aligned}
U_{5}(x)={}&- 32 x^{7} - 171 x^{6} - 201 x^{5} + 10 x^{4}\\
&{}+267 x^{3} + 287 x^{2} + 27 x - 17
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 287.

\[
\begin{aligned}
78125U_{5}(1/5+z)={}&- 2500000 z^{7} - 16859375 z^{6} - 33834375 z^{5} - 23637500 z^{4}\\
&{}+12925625 z^{3} + 33531325 z^{2} + 13453855 z + 152838
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 33834375.

The monomial bounds give \(U_5>7\).

### Second-derivative comparison 6

\[
\begin{aligned}
U_{6}(x)={}&- x^{7} - 2 x^{6} + 6 x^{5} + x^{4}\\
&{}- 4 x^{3} + 5 x^{2} - 10 x + 4
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 10.

\[
\begin{aligned}
78125U_{6}(1/5+z)={}&- 78125 z^{7} - 265625 z^{6} + 215625 z^{5} + 431250 z^{4}\\
&{}- 91875 z^{3} + 255100 z^{2} - 656585 z + 169639
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 656585.

The monomial bounds give \(U_6>1/5\).

## 6. The seven univariate boundary signs

For i=0,...,5, downward coefficient rounding gives \(B_i\ge10Z_i\).
For i=6 it gives \(B_6+7000\ge10Z_6\). Each comparison has at most nine
monomials and degree at most eight. The differences have nonnegative
coefficients with small rational numerators. The complete Z_i and their
shifts use the same interval \(z\in[1/30,8/35]\).

### Boundary comparison 0

\[
\begin{aligned}
Z_{0}(x)={}&78 x^{6} + 2394 x^{5} + 7338 x^{4} + 6989 x^{3}\\
&{}+664 x^{2} - 723 x + 89
\end{aligned}
\]
This identity has 7 monomials, total degree 6, and largest cleared coefficient 7338.

\[
\begin{aligned}
15625Z_{0}(1/5+z)={}&1218750 z^{6} + 38868750 z^{5} + 152793750 z^{4} + 216085625 z^{3}\\
&{}+106436125 z^{2} + 9928090 z + 615373
\end{aligned}
\]
This identity has 7 monomials, total degree 6, and largest cleared coefficient 216085625.

The same monomial bounds give \(Z_0>68\).

### Boundary comparison 1

\[
\begin{aligned}
Z_{1}(x)={}&76 x^{7} + 2190 x^{6} + 29161 x^{5} + 75361 x^{4}\\
&{}+68466 x^{3} + 13936 x^{2} - 4962 x - 238
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 75361.

\[
\begin{aligned}
78125Z_{1}(1/5+z)={}&5937500 z^{7} + 179406250 z^{6} + 2488503125 z^{5} + 8270100000 z^{4}\\
&{}+10997957500 z^{3} + 5897514900 z^{2} + 896671785 z + 376426
\end{aligned}
\]
This identity has 8 monomials, total degree 7, and largest cleared coefficient 10997957500.

The same monomial bounds give \(Z_1>476\).

### Boundary comparison 2

\[
\begin{aligned}
Z_{2}(x)={}&- 327 x^{8} - 1569 x^{7} + 9060 x^{6} + 96459 x^{5}\\
&{}+230848 x^{4} + 216904 x^{3} + 68350 x^{2} - 2894 x\\
&{}-829
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 230848.

\[
\begin{aligned}
390625Z_{2}(1/5+z)={}&- 127734375 z^{8} - 817265625 z^{7} + 2537953125 z^{6} + 41354118750 z^{5}\\
&{}+129791818750 z^{4} + 172469482875 z^{3} + 102273027475 z^{2} + 22910135470 z\\
&{}+1352427578
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 172469482875.

The same monomial bounds give \(Z_2>5724\).

### Boundary comparison 3

\[
\begin{aligned}
Z_{3}(x)={}&- 871 x^{8} - 4104 x^{7} + 12221 x^{6} + 115907 x^{5}\\
&{}+261682 x^{4} + 249218 x^{3} + 91342 x^{2} + 4555 x\\
&{}-142
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 261682.

\[
\begin{aligned}
390625Z_{3}(1/5+z)={}&- 340234375 z^{8} - 2147500000 z^{7} + 2148390625 z^{6} + 49505715625 z^{5}\\
&{}+149873018750 z^{4} + 197904815500 z^{3} + 122348907925 z^{2} + 31375225210 z\\
&{}+2684739384
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 197904815500.

The same monomial bounds give \(Z_3>9917\).

### Boundary comparison 4

\[
\begin{aligned}
Z_{4}(x)={}&- 762 x^{8} - 3483 x^{7} + 6550 x^{6} + 56327 x^{5}\\
&{}+117562 x^{4} + 110579 x^{3} + 42146 x^{2} + 3586 x\\
&{}+677
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 117562.

\[
\begin{aligned}
390625Z_{4}(1/5+z)={}&- 297656250 z^{8} - 1836796875 z^{7} + 320453125 z^{6} + 23796837500 z^{5}\\
&{}+69046256250 z^{4} + 89061991000 z^{3} + 55213620600 z^{2} + 14819303745 z\\
&{}+1629362698
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 89061991000.

The same monomial bounds give \(Z_4>5601\).

### Boundary comparison 5

\[
\begin{aligned}
Z_{5}(x)={}&- 245 x^{8} - 1091 x^{7} + 1284 x^{6} + 9891 x^{5}\\
&{}+17813 x^{4} + 15561 x^{3} + 4657 x^{2} - 201 x\\
&{}+296
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 17813.

\[
\begin{aligned}
15625Z_{5}(1/5+z)={}&- 3828125 z^{8} - 23171875 z^{7} - 8090625 z^{6} + 162587500 z^{5}\\
&{}+439710625 z^{4} + 529808650 z^{3} + 298172585 z^{2} + 65315866 z\\
&{}+9348461
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 529808650.

The same monomial bounds give \(Z_5>760\).

### Boundary comparison 6

\[
\begin{aligned}
Z_{6}(x)={}&- 7 x^{8} - 27 x^{7} - 41 x^{6} - 389 x^{5}\\
&{}- 1014 x^{4} - 1267 x^{3} - 1274 x^{2} - 625 x\\
&{}+666
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 1274.

\[
\begin{aligned}
390625Z_{6}(1/5+z)={}&- 2734375 z^{8} - 14921875 z^{7} - 33843750 z^{6} - 181256250 z^{5}\\
&{}- 560915625 z^{4} - 875780250 z^{3} - 902288275 z^{2} - 516520130 z\\
&{}+186778958
\end{aligned}
\]
This identity has 9 monomials, total degree 8, and largest cleared coefficient 902288275.

The same monomial bounds give \(Z_6>24\).

## 7. Complete lower-shape sign and caller

For a point of (R6), the endpoint in (R7) has
\(x_0=1/4+j\in[17/60,3/7]\) and
\(y\le(1/4-j)/(1+2j)=(1-2x_0)/(1+4x_0)\).
The [terminal-face theorem](NONSHORT_HIGH_RATIO_LOWER_FACE.md) applies and gives
\[
 S(h,j,y)\ge S(1/4,j,y)\ge13/4>0.
 \tag{R15}
\]
Every normalizing factor in (R4) is positive. Thus \(G_{4,L}>0\), and
the norm comparison in the opening section gives \(G_4\ge G_{4,L}>0\).
This is the original N4a sign on its unchanged domain, including the
enlarged comparison points where \(29t^2/4>1+j\).

It supplies `hA` in `fh_LGB_core` without the old lower-shape certificate
or its large link. Applying the already proved
[shape monotonicity](NONSHORT_HIGH_RATIO_SHAPE.md) on
\([29t^2/4,k]\) makes the unchanged actual residual positive. The existing
substitution through `hG` makes it negative. This contradiction closes
the literal `fh_LGB_core` statement with its original constant-multiplier
`hcomb` premise; both old endpoint certificate dependencies are removed.

## Size and verification boundary

All expanded source identities are in t,x with degree at most eight.
The seven second-derivative identities have at most forty monomials and
degree eight; all endpoint and sign identities are univariate with at most
nine monomials and degree eight. Their largest cleared coefficient is
197904815500, twelve digits. The source's three products are differentiated
before collection; neither S nor its first derivative is expanded over
three free variables.

The source identities, sign reductions, scalar bounds, and caller mapping
have independent exact-algebra and mathematical reviews. This note and
its separately proved endpoint complete the hand replacement. They change
no Lean file and make no measured runtime or memory claim.
