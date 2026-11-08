# Small algebra for outer upper-ratio convexity

This is the complete algebra companion to
[reciprocal-shape convexity](SHORT_RATIO_OUTER_RECIPROCAL.md).
Its symbols \(S,e,d,Z_b,W_i,J_2,L,Q_0,\mathcal C,\mathcal D\)
have exactly the meanings there. Put

\[
h=x-2,\qquad t=c-5/8,
\qquad 1/6\le h\le2/5,\quad0\le t\le1/4.
\tag{1}
\]

Let \(u_0=3/4,u_1=4/5\). Define the eight polynomials by the
following positive normalizations, with \(x=2+h,c=5/8+t\):

| Polynomial | Exact source |
|---|---|
| \(P_{A,0}\) | \(392x^2S[Q_0-5/8]_{u=u_0}\) |
| \(P_{A,1}\) | \(1960x^2S[Q_0-5/8]_{u=u_1}\) |
| \(P_{B,0}\) | \(28SL\vert_{u=u_0}\) |
| \(P_{B,1}\) | \(140SL\vert_{u=u_1}\) |
| \(P_{C,0}\) | \(107520e^2S\mathcal C\vert_{u=u_0}\) |
| \(P_{C,1}\) | \(107520e^2S\mathcal C\vert_{u=u_1}\) |
| \(P_{D,0}\) | \(324S\mathcal D\vert_{u=u_0}\) |
| \(P_{D,1}\) | \(1620S\mathcal D\vert_{u=u_1}\) |

All four source functions are affine in \(u\), and their denominators
are positive on the stated rectangle. Positivity at the two norm
endpoints therefore gives their strict signs throughout the norm
interval. The different positive normalizations have no mathematical
effect on this interpolation.

## 1. Every polynomial

The common scalar factors outside the brackets below are retained;
they are not an instruction to multiply the source normalization.

\[
\begin{aligned}
P_{A,0}(h,t)=\frac1{64}\big[&(3072 t - 5760)h^{6}\\
 &{}+(- 1536 t^{3} + 192 t^{2} + 68088 t - 36231)h^{5}\\
 &{}+(- 12288 t^{3} - 2048 t^{2} + 467136 t - 11808)h^{4}\\
 &{}+(- 36864 t^{3} - 18432 t^{2} + 1469504 t + 343904)h^{3}\\
 &{}+(- 52224 t^{3} - 59520 t^{2} + 2322928 t + 853370)h^{2}\\
 &{}+(- 35328 t^{3} - 85184 t^{2} + 1768520 t + 705015)h\\
 &{}+(- 9216 t^{3} - 41856 t^{2} + 506832 t + 144758)\big].
\end{aligned}
\]

\[
\begin{aligned}
P_{A,1}(h,t)=\frac1{4}\big[&(768 t - 1440)h^{6}\\
 &{}+(- 512 t^{3} + 320 t^{2} + 19176 t - 5929)h^{5}\\
 &{}+(- 4096 t^{3} + 2176 t^{2} + 135168 t + 26694)h^{4}\\
 &{}+(- 12288 t^{3} + 5888 t^{2} + 424000 t + 189648)h^{3}\\
 &{}+(- 17408 t^{3} + 4224 t^{2} + 652048 t + 375906)h^{2}\\
 &{}+(- 11776 t^{3} - 5568 t^{2} + 465624 t + 281547)h\\
 &{}+(- 3072 t^{3} - 5760 t^{2} + 116208 t + 51682)\big].
\end{aligned}
\]

\[
\begin{aligned}
P_{B,0}(h,t)=\frac1{4096}\big[&(- 49152 t - 104448)h^{6}\\
 &{}+(245760 t^{2} + 110592 t - 796928)h^{5}\\
 &{}+(- 385024 t^{3} + 1125376 t^{2} + 2709888 t - 1719408)h^{4}\\
 &{}+(196608 t^{4} - 2408448 t^{3} - 643072 t^{2} + 7191296 t - 91120)h^{3}\\
 &{}+(1343488 t^{4} - 3768320 t^{3} - 6216704 t^{2} + 3953664 t + 3717096)h^{2}\\
 &{}+(2740224 t^{4} - 489472 t^{3} - 4194432 t^{2} - 4303584 t + 4108621)h\\
 &{}+(1896448 t^{4} + 1587200 t^{3} + 1836672 t^{2} - 3249952 t + 1371727)\big].
\end{aligned}
\]

\[
\begin{aligned}
P_{B,1}(h,t)=\frac1{4096}\big[&(- 196608 t - 417792)h^{6}\\
 &{}+(1048576 t^{2} + 720896 t - 2789376)h^{5}\\
 &{}+(- 1736704 t^{3} + 4067328 t^{2} + 11624960 t - 3418432)h^{4}\\
 &{}+(933888 t^{4} - 10215424 t^{3} - 6949376 t^{2} + 22857856 t + 9940580)h^{3}\\
 &{}+(6258688 t^{4} - 12812288 t^{3} - 30032896 t^{2} - 9893888 t + 27646552)h^{2}\\
 &{}+(12341248 t^{4} + 5179392 t^{3} - 8252544 t^{2} - 48897760 t + 22162581)h\\
 &{}+(8204288 t^{4} + 10614784 t^{3} + 19597440 t^{2} - 24232736 t + 5703587)\big].
\end{aligned}
\]

\[
\begin{aligned}
P_{C,0}(h,t)=\frac1{4096}\big[&(- 19906560 t - 42301440)h^{6}\\
 &{}+(99532800 t^{2} + 422277120 t + 290661120)h^{5}\\
 &{}+(- 155934720 t^{3} - 299197440 t^{2} + 2796197760 t + 4340736720)h^{4}\\
 &{}+(79626240 t^{4} - 597934080 t^{3} - 4459991040 t^{2} + 2945898240 t + 14653924688)h^{3}\\
 &{}+(544112640 t^{4} + 361267200 t^{3} - 9202437120 t^{2} - 4610661376 t + 19816821256)h^{2}\\
 &{}+(1109790720 t^{4} + 2066688000 t^{3} - 5653973632 t^{2} - 5398549600 t + 10230726353)h\\
 &{}+(768061440 t^{4} + 642816000 t^{3} - 2565453696 t^{2} + 706472544 t + 822346491)\big].
\end{aligned}
\]

\[
\begin{aligned}
P_{C,1}(h,t)=\frac1{4096}\big[&(- 15925248 t - 33841152)h^{6}\\
 &{}+(84934656 t^{2} + 461045760 t + 428371968)h^{5}\\
 &{}+(- 140673024 t^{3} - 475852800 t^{2} + 2753561088 t + 5070844608)h^{4}\\
 &{}+(75644928 t^{4} - 424796160 t^{3} - 5042416128 t^{2} + 1945858176 t + 16354258340)h^{3}\\
 &{}+(506953728 t^{4} + 975470592 t^{3} - 9604924416 t^{2} - 7197718528 t + 21631866328)h^{2}\\
 &{}+(999641088 t^{4} + 2835449856 t^{3} - 5045212288 t^{2} - 7703610592 t + 10999601957)h\\
 &{}+(664547328 t^{4} + 859797504 t^{3} - 2080526208 t^{2} + 45695712 t + 860023443)\big].
\end{aligned}
\]

\[
\begin{aligned}
P_{D,0}(h,t)=\frac1{4096}\big[&(3981312 t + 8460288)h^{6}\\
 &{}+(- 19906560 t^{2} - 8957952 t + 182565120)h^{5}\\
 &{}+(31186944 t^{3} - 91155456 t^{2} - 455528832 t + 1191563120)h^{4}\\
 &{}+(- 15925248 t^{4} + 195084288 t^{3} + 170102784 t^{2} - 2460883712 t + 3527515632)h^{3}\\
 &{}+(- 108822528 t^{4} + 305233920 t^{3} + 1329650688 t^{2} - 5621040128 t + 5210711192)h^{2}\\
 &{}+(- 221958144 t^{4} + 39647232 t^{3} + 2227972224 t^{2} - 5878050592 t + 3679676067)h\\
 &{}+(- 153612288 t^{4} - 128563200 t^{3} + 1267396992 t^{2} - 2229096160 t + 972792065)\big].
\end{aligned}
\]

\[
\begin{aligned}
P_{D,1}(h,t)=\frac1{4096}\big[&(15925248 t + 33841152)h^{6}\\
 &{}+(- 84934656 t^{2} - 58392576 t + 855347200)h^{5}\\
 &{}+(140673024 t^{3} - 329453568 t^{2} - 2200437248 t + 5862886720)h^{4}\\
 &{}+(- 75644928 t^{4} + 827449344 t^{3} + 1192307200 t^{2} - 11843334272 t + 17762341468)h^{3}\\
 &{}+(- 506953728 t^{4} + 1037795328 t^{3} + 6838518784 t^{2} - 27285915648 t + 26553223720)h^{2}\\
 &{}+(- 999641088 t^{4} - 419530752 t^{3} + 10738979968 t^{2} - 28805012256 t + 18859731163)h\\
 &{}+(- 664547328 t^{4} - 859797504 t^{3} + 5965500288 t^{2} - 10970915552 t + 5009150317)\big].
\end{aligned}
\]

## 2. Explicit positive lower polynomials

For each printed polynomial, discard every positive term containing a
positive power of \(t\), and replace \(t^k\) by \(4^{-k}\) in
every negative such term. This bounds it below by the following
complete univariate polynomial \(L_{X,i}(h)\):

\[
\begin{aligned}
L_{A,0}(h)=\frac1{64}\big[&(-5760)h^{6}\\
 &{}+(-36255)h^{5}\\
 &{}+(-12128)h^{4}\\
 &{}+(342176)h^{3}\\
 &{}+(848834)h^{2}\\
 &{}+(699139)h\\
 &{}+(141998)\big].
\end{aligned}
\]

\[
\begin{aligned}
L_{A,1}(h)=\frac1{4}\big[&(-1440)h^{6}\\
 &{}+(-5937)h^{5}\\
 &{}+(26630)h^{4}\\
 &{}+(189456)h^{3}\\
 &{}+(375634)h^{2}\\
 &{}+(281015)h\\
 &{}+(51274)\big].
\end{aligned}
\]

\[
\begin{aligned}
L_{B,0}(h)=\frac1{4096}\big[&(-116736)h^{6}\\
 &{}+(-796928)h^{5}\\
 &{}+(-1725424)h^{4}\\
 &{}+(-168944)h^{3}\\
 &{}+(3269672)h^{2}\\
 &{}+(2762925)h\\
 &{}+(559239)\big].
\end{aligned}
\]

\[
\begin{aligned}
L_{B,1}(h)=\frac1{4096}\big[&(-466944)h^{6}\\
 &{}+(-2789376)h^{5}\\
 &{}+(-3445568)h^{4}\\
 &{}+(9346628)h^{3}\\
 &{}+(23095832)h^{2}\\
 &{}+(9422357)h\\
 &{}+(-354597)\big].
\end{aligned}
\]

\[
\begin{aligned}
L_{C,0}(h)=\frac1{4096}\big[&(-47278080)h^{6}\\
 &{}+(290661120)h^{5}\\
 &{}+(4319600400)h^{4}\\
 &{}+(14365832528)h^{3}\\
 &{}+(18089003592)h^{2}\\
 &{}+(8527715601)h\\
 &{}+(662005635)\big].
\end{aligned}
\]

\[
\begin{aligned}
L_{C,1}(h)=\frac1{4096}\big[&(-37822464)h^{6}\\
 &{}+(428371968)h^{5}\\
 &{}+(5038905792)h^{4}\\
 &{}+(16032469892)h^{3}\\
 &{}+(19232128920)h^{2}\\
 &{}+(8758373541)h\\
 &{}+(729990555)\big].
\end{aligned}
\]

\[
\begin{aligned}
L_{D,0}(h)=\frac1{4096}\big[&(8460288)h^{6}\\
 &{}+(179081472)h^{5}\\
 &{}+(1071983696)h^{4}\\
 &{}+(2912232496)h^{3}\\
 &{}+(3805026072)h^{2}\\
 &{}+(2209296395)h\\
 &{}+(412909177)\big].
\end{aligned}
\]

\[
\begin{aligned}
L_{D,1}(h)=\frac1{4096}\big[&(33841152)h^{6}\\
 &{}+(835440640)h^{5}\\
 &{}+(5292186560)h^{4}\\
 &{}+(14801212412)h^{3}\\
 &{}+(19729764520)h^{2}\\
 &{}+(11648018083)h\\
 &{}+(2250391205)\big].
\end{aligned}
\]

Each lower polynomial is strictly positive. In a positive term put
\(h=1/6\), and in a negative term put \(h=2/5\). The resulting
scalar sums have the following deliberately rounded lower bounds:

| Polynomial | Strict lower bound |
|---|---:|
| \(L_{A,0}\) | \(4000\) |
| \(L_{A,1}\) | \(27000\) |
| \(L_{B,0}\) | \(250\) |
| \(L_{B,1}\) | \(430\) |
| \(L_{C,0}\) | \(648000\) |
| \(L_{C,1}\) | \(684000\) |
| \(L_{D,0}\) | \(220000\) |
| \(L_{D,1}\) | \(1174000\) |

These are scalar substitutions in the eight fully printed polynomials,
using positivity of monomials. There is no unspecified coefficient
minimum or numerical sampling premise.

## 3. Source order and size check

The only initial-edge jet formulas needed for A are, with
\(V_4=W_4/x=(2x-1-2c)(S-1+S^{-1}-ud_2)\),

\[
W'(1/x)=W_1+\frac{2W_2}{x}+\frac{3W_3+4V_4}{x^2},
\quad
W''(1/x)=2W_2+\frac{6W_3+12V_4}{x}.
\tag{2}
\]

Thus each denominator is cleared only after the displayed factor
\(x\) in \(W_4\) is cancelled. For B, use the six summands of
the residue identity (14) in the main note. For C and D, insert those
same six summands for \(L\) and keep the other displayed terms separate.
This also supplies direct source identities for every polynomial above.

| Family | Monomials after the shift | Total degree |
|---|---:|---:|
| A | 26 each | 8 |
| B | 29 each | 7 |
| C | 29 each | 7 |
| D | 29 each | 7 |

The largest integer printed inside a polynomial bracket is
\(28,805,012,256\). There are 72 individual normalized source
contributions when the initial jets and residue summands are kept
separate. Each has at most 29 monomials and degree at most eight;
its largest coefficient numerator is \(1,441,972,125\), and its
largest coefficient denominator is 4096. The shifts, lower polynomials
and all source contributions therefore stay within the requested
twelve-digit coefficient bound.

The logarithm was differentiated exactly before any expansion. The
quartic divisions and chain rules in the main note are identities in
one variable with their coefficient functions retained. No degree-eight
claim is being made about an unneeded expansion in \(x,c,r,u\).
