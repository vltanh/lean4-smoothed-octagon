# A hand Casimir sign after removing the first-event factor

Date: 2026-11-08 UTC. Scalar hand theorem; the application hypotheses listed
below are not asserted for every remaining actual forward window.

The purpose of this note is to prove the final Casimir inequality in a
possible forward-successor route. It does not prove the needed ratio
bounds or the preceding factor-elimination inequality. No numerical
minimum, interval cover, or executable sign verdict is a premise. The
polynomial estimates in the proof are finite displayed algebraic
identities with explicit coefficient bounds; Appendix A supplies the
sign parts used in those bounds.

## 1. The complete scalar statement

Suppose
\[
 \frac13\le t\le\frac25,\qquad
 0\le j\le\frac1{30},\qquad
 1\le k\le\frac{31}{30}.
\tag{1}
\]
Put
\[
 c=1-t,\quad x=1-2t+j,\quad p=t+x,\quad W=1+x,
 \quad Y=x(x+2),\quad B=k+2tx+x^2,\quad s=k-t^2.
\]
Every one of these denominators is positive. Define
\[
 V=1+\frac{c^2}{W}-\frac{3c(x+2)}{x^2+6x+6},\qquad
 g=1-\frac{cp}{W^2}.
\tag{2}
\]
For a norm parameter \(3/4\le v\le V\), set
\[
 H=\frac{k}{t}(v-1+t^2)+t(2-t),\qquad
 w_U=\frac{k^2-kt+t^2+HY+vY^2}{B^2},
\]
\[
 a_q=\frac{B(w_U-1)}{pW},\qquad b_q=\frac{pW}{B},\qquad
 h_1=\frac{Wv-c+p^2/W}{p}+a_q+b_q-\frac{p^2}{B}.
\tag{3}
\]
The subscript on \(a_q,b_q\) distinguishes these coefficients from
the physical margin and the comparison variables below; neither depends
on an event factor. Write
\[
 \mathcal G(t,j,k,v)=
 \frac{B^2\{4vw_U-[h_1+v-g]^2\}}{16s^2}.
\tag{4}
\]

**Scalar theorem.** Every point of (1)--(3) satisfies
\[
 \boxed{\mathcal G(t,j,k,v)>\frac{9193}{50000}.}
\tag{5}
\]

In the intended application the exact incoming secant is smaller than
V. Indeed the derivative of
\[
 \log(1+x)-\frac{3x(x+2)}{x^2+6x+6}
\]
is \(x^4/[(1+x)(x^2+6x+6)^2]>0\), and the expression vanishes
at zero. Substitution in the exact secant proves the assertion. This
one-variable inequality is proved here independently of any sign table.

## 2. Lower the comparison by raising the incoming norm

Let
\[
 N(v)=B^2\{4vw_U-[h_1+v-g]^2\},\qquad
 P_v=Y(k/t+Y)>0,
\]
where the notation \(P_v\) denotes this explicit scalar, not a
derivative of the polynomial P introduced later. The numerator of
\(w_U\) has derivative \(P_v\). Also
\[
 D(v)=B(h_1+v-g),\qquad
 D'(v)=B(1+W/p)+\frac{P_v}{pW}>0.
\]
The arithmetic--geometric mean inequality and \(B>p^2\) give
\[
 [D'(v)]^2\ge
 \frac{4B(1+W/p)P_v}{pW}>4P_v.
\]
Therefore
\[
 N''(v)=8P_v-2[D'(v)]^2<0.
\tag{6}
\]

It is enough to check \(N'(3/4)<0\). Define the polynomial
\[
 E(t,x,k)=2t^2p^2W^3[-N'(3/4)].
\tag{7}
\]
That this is a polynomial follows by substituting (3); the multiplier
clears all denominators. Introduce
\[
 A=\frac25-t,\qquad J=j,\qquad Z=k-1,
\quad 0\le A\le\frac1{15},\quad0\le J,Z\le\frac1{30},
\]
\[
 \widehat E(A,J,Z)=5^{10}
 E(2/5-A,1/5+2A+J,1+Z).
\tag{8}
\]
Its constant coefficient is 6465474. For any polynomial in
\(A,J,Z\), a monomial \(A^iJ^mZ^n\) is at most
\(15^{-i}30^{-m-n}\) on this box. The complete negative coefficient
part of \(\widehat E\) is displayed in Appendix A. Its three
weighted sums, grouped by the power n of Z, are the following exact
algebraic identities:

| n | Sum of the absolute negative coefficients times \(15^{-i}30^{-m-n}\) |
| --- | ---: |
| 0 | \(5267069385883/9447840\) |
| 1 | \(15651908324257/37791360\) |
| 2 | \(219146879111/7558272\) |

Their total is \(787831672153/787320<6465474\). For example,
the separate sums are less than \(9/100,7/100,1/100\) times
6465474, respectively, so even these simpler bounds sum to less than
one fifth of the constant. Dropping the nonnegative monomials now
proves \(\widehat E>0\), hence (7) gives \(N'(3/4)<0\).
Together with (6),
\[
 N(v)\ge N(V)\qquad(3/4\le v\le V).
\tag{9}
\]
It remains to prove (5) with v equal to V.

## 3. One concavity reduces the sign to two endpoints

Put \(Q=x^2+6x+6\), and define the polynomial
\[
 P(t,x,k)=3125t^2p^2W^4Q^2
 \left[N(V)-16(k-t^2)^2\frac{9193}{50000}\right].
\tag{10}
\]
Again the displayed multiplier clears all denominators; (2)--(3) and
(10) specify this polynomial without an unstated coefficient extraction.
All its multipliers are positive on (1). Define
\[
 \widehat P(A,J,Z)=5^{16}
 P(2/5-A,1/5+2A+J,1+Z).
\tag{11}
\]

**Concavity claim.** \(\widehat P_{AA}<0\) throughout the box in
(8). Here A varies with J and Z fixed, so it follows the required
relation \(x=1-2t+j\).

The constant coefficient of \(\widehat P_{AA}\) is
\(-20842670556105750\). Appendix A supplies its complete positive
nonconstant coefficient part. The corresponding weighted sums are

| n | Sum of the positive nonconstant coefficients times \(15^{-i}30^{-m-n}\) |
| --- | ---: |
| 0 | \(4459317828207872663820425/1632586752\) |
| 1 | \(10968819054424340770307875/14693280768\) |
| 2 | \(12569541255418605625/40310784\) |

They are respectively less than \(1/7,1/25,1/50000\) times
20842670556105750. These three fractions sum to less than \(1/5\).
Dropping all negative nonconstant terms therefore proves the claimed
strict concavity, with a margin greater than four fifths of the absolute
constant. This is one bound on an explicit polynomial; no partition
of the domain or numerical sign test is used.

For each fixed J,Z, a concave function on \([0,1/15]\) has its
minimum at an endpoint. It follows that
\[
 \widehat P(A,J,Z)\ge
 \min\{\widehat P(0,J,Z),\widehat P(1/15,J,Z)\}.
\tag{12}
\]

## 4. The two endpoint identities are positive

Appendix B gives the complete coefficient triples for the identities
\[
 \widehat P(0,J,Z)=\sum_{m=0}^{13}(a_m+b_mZ+c_mZ^2)J^m,
\tag{13}
\]
\[
 \frac{129140163}{305175781250}\widehat P(1/15,J,Z)
   =\sum_{m=0}^{13}(\widetilde a_m+
                 \widetilde b_mZ+\widetilde c_mZ^2)J^m.
\tag{14}
\]
In both tables every a coefficient is strictly positive. Every b
coefficient is nonnegative. If c is negative, direct multiplication of
the corresponding two displayed integers gives \(30b+c>0\).
For \(0\le Z\le1/30\), therefore,
\[
 a+bZ+cZ^2\ge
 \begin{cases}
 a+bZ,&c\ge0,\\
 a+Z(b+c/30),&c<0,
 \end{cases}
 \quad>0.
\tag{15}
\]
All powers of J are nonnegative, and the constant-in-J term is strictly
positive. Thus (13)--(15) prove both endpoint signs. Equations
(9)--(12), with their positive denominators, prove (5).

## 5. What this does and does not prove about an actual period

The [conditional actual Casimir monotonicity](MIXED_NONSHORT_FORWARD_CASIMIR_MONOTONICITY.md)
has a direct useful consequence. When its hypotheses hold, the actual
outgoing norm is smaller than the central upper-envelope norm w_U by
[the upper-envelope lemma](MIXED_NONSHORT_UPPER_ENVELOPE_GAP.md).
The Casimir decreases along the first-forward stationary line for
every \(w\ge3/4\). Hence the actual squared Casimir is strictly
greater than the value on that stationary line at w_U. The diagonal
at this point is the *forward stationary* diagonal; replacing it by
the central ceiling diagonal would be an invalid substitution.

On that line, normalized by B, the diagonal at w_U is
\[
 h(q)=\log q+a_q q+b_q/q+
       \frac{Wv-c+p^2/W}{p}-\frac{p^2}{B}.
\]
Its value at q=1 is h_1. If the additional scalar inequality
\[
 h(q)-h_1\le F_{p/W}(q)-g
\tag{16}
\]
is proved on the required actual domain, the unchanged incoming floor
\(F_{p/W}(q)\le v\) gives \(h(q)\le h_1+v-g\).
The conditional monotonicity also supplies a positive diagonal at the
actual norm, and the diagonal strictly increases with w; thus squaring
this upper bound at w_U has the correct direction. The actual Casimir
would then exceed \(\mathcal G\), contradicting (5).

This application still requires proofs of (16), \(t\ge1/3\),
\(j\le1/30\), and the ratio hypothesis needed by the referenced
actual monotonicity theorem. The common order already gives
\(k<1+j\), so the shape interval (1) follows once the j bound is
established. The present scalar sign does not prove these prerequisites
or close H-N-forward by itself.

## Appendix A. Explicit algebra for the coefficient bounds

The convention \(\operatorname{poly}(c_0,\ldots,c_d)=
\sum_{m=0}^d c_mJ^m\) is used below. For each table row (n,i), the
listed polynomial is multiplied by \(Z^nA^i\). Zero rows are omitted.
The first table gives the absolute negative coefficient part of
\(\widehat E\); the second gives the positive nonconstant coefficient
part of \(\widehat P_{AA}\). They are obtained by multiplication in
(7)--(11), so every coefficient has a fixed generating formula.
Evaluating a table at \(A=1/15,J=Z=1/30\) gives the corresponding
weighted sums in Sections 2--3. This makes the finite arithmetic
explicit independently of any accompanying calculation program.

### Negative part of the norm derivative

| n | i | Coefficients in ascending powers of J |
| --- | --- | --- |
| 0 | 1 | `0, 0, 0, 0, 0, 0, 180156250, 409531250, 175000000, 23437500` |
| 0 | 2 | `0, 0, 0, 4909960000, 11313550000, 11344218750, 6170312500, 1734765625, 109375000` |
| 0 | 3 | `1058491250, 8149750000, 27662597500, 47894637500, 43390156250, 19623437500, 2394531250` |
| 0 | 4 | `5800950000, 31966675000, 66492712500, 56274375000, 4112500000` |
| 0 | 5 | `10873575000, 31785950000` |
| 1 | 0 | `4452444` |
| 1 | 1 | `59043900, 135224150, 0, 0, 348875000, 791093750, 367656250, 30468750` |
| 1 | 2 | `527960500, 2529918500, 5695335000, 8379687500, 7246875000, 2510156250` |
| 1 | 3 | `2518205000, 11088302500, 19776168750, 16432812500, 2328125000, 0, 0, 39062500` |
| 1 | 4 | `5543275000, 15119162500, 7441562500, 0, 0, 0, 507812500` |
| 1 | 5 | `2249112500, 0, 0, 0, 0, 2812500000` |
| 1 | 6 | `0, 0, 0, 0, 8593750000` |
| 1 | 7 | `0, 0, 0, 15625000000` |
| 1 | 8 | `0, 4468750000, 16875000000` |
| 1 | 9 | `4062500000, 10000000000` |
| 1 | 10 | `2500000000` |
| 2 | 0 | `12152550, 75903625, 187035000, 230856250, 141656250, 32890625` |
| 2 | 1 | `109442750, 568472500, 1047193750, 725937500, 67812500` |
| 2 | 2 | `453477500, 1663550000, 1458750000` |
| 2 | 3 | `907612500, 1259687500, 0, 0, 0, 78125000` |
| 2 | 4 | `320937500, 0, 0, 556640625, 742187500` |
| 2 | 5 | `0, 0, 2347656250, 2812500000` |
| 2 | 6 | `0, 3500000000, 5312500000` |
| 2 | 7 | `1812500000, 5000000000` |
| 2 | 8 | `1875000000` |

### Positive nonconstant part of the concavity derivative

| n | i | Coefficients in ascending powers of J |
| --- | --- | --- |
| 0 | 0 | `0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 152587890625000` |
| 0 | 1 | `0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 935531616210937500, 256347656250000000, 18310546875000000` |
| 0 | 2 | `0, 0, 0, 68850622837687500000, 246066716222062500000, 372087615076171875000, 338938931692968750000, 226061585559375000000, 143228284497070312500, 83227035937500000000, 31573421264648437500, 5787963867187500000, 286102294921875000` |
| 0 | 3 | `0, 58563102262016875000, 572658433172800000000, 1818791304653046875000, 3161036974116718750000, 3460315908789062500000, 2607761114781250000000, 1506959258134765625000, 702989840087890625000, 224705348388671875000, 31391489257812500000` |
| 0 | 4 | `53081983810330781250, 740160642317953125000, 3126318162024210937500, 6503928848722265625000, 7670385089461523437500, 5332238292568359375000, 2217312113525390625000, 527862050463867187500` |
| 0 | 5 | `202966788666271875000, 1184913922099031250000, 1270212455230031250000` |
| 1 | 0 | `6953558303745000, 351653801700600000, 2688216616661062500, 8490962366789062500, 13384359763429687500, 10240476318281250000, 1816302567500000000, 0, 0, 0, 0, 457763671875000` |
| 1 | 1 | `0, 0, 5118191433567187500, 9221591919140625000, 0, 0, 0, 0, 0, 494852783203125000, 390776733398437500, 33187866210937500` |
| 1 | 2 | `0, 0, 0, 0, 0, 0, 0, 0, 24023415527343750000, 8027600097656250000, 468541259765625000` |
| 1 | 3 | `0, 0, 0, 0, 0, 0, 0, 196250577636718750000, 60543884277343750000, 767358398437500000, 0, 19073486328125000` |
| 1 | 4 | `0, 0, 0, 0, 0, 0, 726151471435546875000, 249479404907226562500, 0, 0, 429153442382812500` |
| 1 | 5 | `0, 0, 0, 0, 0, 1395880410278320312500, 697760583618164062500, 0, 0, 3725051879882812500` |
| 1 | 6 | `0, 0, 0, 0, 976337629394531250000, 1379807871093750000000, 27582221679687500000, 22911071777343750000, 15220642089843750000` |
| 1 | 7 | `0, 0, 0, 0, 1400776040039062500000, 67860131835937500000, 57403564453125000000, 19912719726562500000` |
| 2 | 0 | `0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 93688964843750` |
| 2 | 1 | `0, 0, 0, 0, 0, 0, 0, 774153442382812500, 475938720703125000, 83107910156250000, 4577636718750000` |
| 2 | 2 | `0, 0, 0, 0, 0, 37631065429687500000, 36993988769531250000, 11204670410156250000, 1481121826171875000, 34332275390625000` |
| 2 | 3 | `0, 0, 0, 114578296240234375000, 440170258154296875000, 302409973144531250000, 82149949951171875000, 6690112304687500000` |
| 2 | 4 | `0, 0, 801675131835937500000, 1631177617309570312500, 1151602429321289062500, 287112881469726562500` |
| 2 | 5 | `100558872836132812500, 1232389174467773437500, 2955711941088867187500, 2456391133300781250000, 542722874633789062500` |
| 2 | 6 | `625421920908203125000, 2681952048535156250000, 3063954449951171875000, 573162016601562500000` |
| 2 | 7 | `975656722851562500000, 2108379348632812500000, 330845185546875000000` |
| 2 | 8 | `619504490478515625000, 97758588867187500000` |
| 2 | 9 | `12888046875000000000` |


## Appendix B. Complete endpoint coefficient identities

The two tables below give every coefficient in (13)--(14), in ascending
power m of J. Their only negative entries occur in the quadratic Z
column, where (15) supplies the stated short sign argument.

### A = 0

| m | a | b | c |
| --- | ---: | ---: | ---: |
| 0 | 91598684752467 | 298040085496350 | 45493448866875 |
| 1 | 775844206632270 | 3601088642556000 | -60792945018750 |
| 2 | 3643488988968825 | 23387034072678750 | -1379582840109375 |
| 3 | 12724146336982500 | 92932990466625000 | -3019643479687500 |
| 4 | 34288270444985625 | 230889017515218750 | 1343446405078125 |
| 5 | 73641775079531250 | 367900252804687500 | 13603518457031250 |
| 6 | 129193889736234375 | 383764343819531250 | 21241017177734375 |
| 7 | 178847728475625000 | 264666726281250000 | 15878250390625000 |
| 8 | 183169543710937500 | 120090178710937500 | 6207495117187500 |
| 9 | 131474777367187500 | 34893830273437500 | 1156533203125000 |
| 10 | 63257915507812500 | 6031634765625000 | 68530273437500 |
| 11 | 19292871093750000 | 490722656250000 | 0 |
| 12 | 3363647460937500 | 0 | 0 |
| 13 | 256347656250000 | 0 | 0 |

### A = 1/15, with the positive multiplier in (14)

| m | a | b | c |
| --- | ---: | ---: | ---: |
| 0 | 8808186912 | 190213995552 | -222723733752 |
| 1 | 32844054752 | 2978204748192 | -2394372460392 |
| 2 | 454576231560 | 20646248864760 | -9890823549510 |
| 3 | 3087078374016 | 77323456741536 | -20623442939136 |
| 4 | 11092451460768 | 172464006399228 | -22838716765278 |
| 5 | 28191260252592 | 242600483705832 | -11479422892032 |
| 6 | 55315490251536 | 222051775615956 | 947740248819 |
| 7 | 80107540815456 | 133971580497276 | 4141352958624 |
| 8 | 80962571950920 | 53101772495820 | 1989438754680 |
| 9 | 55276145895060 | 13509598685760 | 378194673240 |
| 10 | 24808746791628 | 2068298221788 | 21234788037 |
| 11 | 6998044612500 | 152789287500 | 0 |
| 12 | 1127097787500 | 0 | 0 |
| 13 | 79716150000 | 0 | 0 |

