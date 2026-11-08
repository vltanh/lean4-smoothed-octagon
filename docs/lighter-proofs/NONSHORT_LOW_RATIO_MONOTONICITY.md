# Low-ratio monotonicity through small univariate sign claims

Date: 2026-11-08.

**Scope.** This proves the three monotonicity claims used
in Section 3 of
[MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION](../../archive/notes/MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION.md)
for the fully displayed, factored polynomials \(\mathcal A_i\) below. They
are the original \(A_i\), reconstructed exactly from the original definitions
of \(P,C_0,C_1,C_2\). The [fourth-derivative bridge](NONSHORT_LOW_RATIO_LINK.md)
derives their connection to the original residual by small boundary
calculations, and combines this result with the base and remainder proofs
to close the full unit-shape sign. It does not expand the original collection
identity \(P=\sum C_i j^i\) as one polynomial.

The completed mathematical result here is
\[
\boxed{
 \partial_h\mathcal A_0\ge3500,\qquad
 \partial_h\mathcal A_1\ge12400,\qquad
 \partial_h\mathcal A_2\ge5400
}
\tag{1}
\]
on \(1/3\le h\le1/2\), \(0\le z\le1\).
Each derivative is a sum of powers of \(z\) times explicitly factored
univariate polynomials in \(h\). Their signs follow from separate claims
of degree at most eight. There is no subdivision and no coefficient table.

The high powers of \(h\) in the factorizations remain powers. Product-rule
and power-rule differentiation, and coefficientwise identities in \(z\),
never require expanding the full bivariate polynomial. Every coefficient
identity that actually needs expansion is univariate, of degree at most eight
and at most nine monomials. Appendix A prints the starting polynomial blocks;
Sections 1–4 print every polynomial used for the derivative signs.

## 1. Factored derivatives

Put \(E_i=2\partial_h\mathcal A_i\). The following factorizations are obtained
coefficientwise from Appendix A by the product rule:
\[
\begin{aligned}
E_0={}&U_{00}+zU_{01}+z^2U_{02}+z^3U_{03}+z^4P_{04}
       +hz^5P_{05}+h^2z^6P_{06}-12h^4z^7S_0,\\
E_1={}&U_{10}+zU_{11}+z^2U_{12}+z^3(U_{13}+9360h^9)\\
 &+hz^4(P_{14}+3168h^9)+h^2z^5(P_{15}+216h^9)
       +h^3z^6P_{16}-12h^4z^7S_1,\\
E_2={}&U_{20}+zU_{21}+z^2U_{22}+z^3(U_{23}+72720h^9)\\
 &+h^2z^4P_{24}+h^3z^5P_{25}+h^4z^6P_{26}-6h^5z^7S_2.
\end{aligned}
\tag{2}
\]
All named factors depend only on \(h\). The extra \(h^9\) terms are positive
monomials, retained as factored powers; they need no sign expansion.

### Constant and first-degree coefficients in \(z\)

\[
U_{00}(h)=2570 + 19532 h + 19620 h^{2} + 4032 h^{3}.
\]
(4 monomials, degree 3.)

\[
U_{01}(h)=-6440 + 7858 h + 126009 h^{2} + 153696 h^{3} + 55380 h^{4} + 6048 h^{5}.
\]
(6 monomials, degree 5.)

\[
U_{10}(h)=-7780 + 34188 h + 174720 h^{2} + 173736 h^{3} + 48060 h^{4} + 2592 h^{5}.
\]
(6 monomials, degree 5.)

\[
U_{11}(h)=1950 - 91660 h + 176559 h^{2} + 1185720 h^{3} + 1383585 h^{4} + 574416 h^{5} + 89964 h^{6} + 3456 h^{7}.
\]
(8 monomials, degree 7.)

\[
U_{20}(h)=-7620 - 32808 h + 176076 h^{2} + 356352 h^{3} + 156240 h^{4} + 15552 h^{5}.
\]
(6 monomials, degree 5.)

\[
U_{21}(h)=21780 - 117828 h - 283500 h^{2} + 1278504 h^{3} + 2796060 h^{4} + 1722456 h^{5} + 406728 h^{6} + 27648 h^{7}.
\]
(8 monomials, degree 7.)


The following direct bounds use only \(1/3\le h\le1/2\):
\[
U_{00}\ge11410>11000,\qquad U_{10}\ge30068>30000,
\qquad U_{20}\ge\frac{145792}{9}>16000.
\tag{3}
\]
For \(U_{00}\) and \(U_{10}\), substitute \(h=1/3\) in every positive
nonconstant term; their only negative terms are constants.
For \(U_{20}\), first use
\[
14673h^2-2734h=h(14673h-2734)\ge719.
\tag{4}
\]
The remaining nonconstant terms of \(U_{20}/12\) have positive coefficients,
so substituting \(h=1/3\) gives the third bound in (3).

Also \(U_{01}>0\), since \(126009h^2\ge14001>6440\).
For \(U_{11}\), the only negative term is absorbed by
\[
1185720h^3-91660h=h(1185720h^2-91660)>0.
\tag{5}
\]
For \(U_{21}/12\), the only negative terms are absorbed by
\[
\begin{aligned}
&233005h^4+106542h^3-23625h^2-9819h\\
&\quad=h\{233005h^3+h(106542h-23625)-9819\}\\
&\quad\ge h\left(\frac{233005}{27}+3963-9819\right)
       =\frac{74893}{27}h>0.
\end{aligned}
\tag{6}
\]
Thus all three \(U_{i1}\) are positive. The identities in (4)–(6) have,
respectively, two, two, and four monomials and degrees two, three, and four.

### The potentially negative second-degree coefficients

\[
U_{02}(h)=-2970 - 44298 h - 7488 h^{2} + 299416 h^{3} + 391735 h^{4} + 161532 h^{5} + 20664 h^{6}.
\]
(7 monomials, degree 6.)

\[
U_{12}(h)=-38280 - 134214 h - 385584 h^{2} + 522636 h^{3} + 3033505 h^{4} + 3485616 h^{5} + 1548659 h^{6} + 266160 h^{7} + 9720 h^{8}.
\]
(9 monomials, degree 8.)

\[
U_{22}(h)=-69330 - 77934 h - 402138 h^{2} - 112580 h^{3} + 4006850 h^{4} + 7087656 h^{5} + 4431434 h^{6} + 1132512 h^{7} + 76464 h^{8}.
\]
(9 monomials, degree 8.)

Their derivatives are the following small polynomials:

\[
V_0(h)=U_{02}^\prime(h)=-44298 - 14976 h + 898248 h^{2} + 1566940 h^{3} + 807660 h^{4} + 123984 h^{5}.
\]
(6 monomials, degree 5.)

\[
V_1(h)=U_{12}^\prime(h)=-134214 - 771168 h + 1567908 h^{2} + 12134020 h^{3} + 17428080 h^{4} + 9291954 h^{5} + 1863120 h^{6} + 77760 h^{7}.
\]
(8 monomials, degree 7.)

\[
V_2(h)=U_{22}^\prime(h)=-77934 - 804276 h - 337740 h^{2} + 16027400 h^{3} + 35438280 h^{4} + 26588604 h^{5} + 7927584 h^{6} + 611712 h^{7}.
\]
(8 monomials, degree 7.)


All terms omitted in the next lower bounds are positive:
\[
\begin{aligned}
V_0&\ge898248h^2-14976h-44298
      \ge\frac{151546}{3}>0,\\
V_1&\ge12134020h^3-771168h-134214
      \ge\frac{1569730}{27}>0,\\
V_2&\ge16027400h^3-337740h^2-804276h-77934
      \ge\frac{5164868}{27}>0.
\end{aligned}
\tag{7}
\]
For the first use \(h^2\ge h/3\). For the second use \(h^3\ge h/9\).
For the third also use \(h^2\le h/2\). Each remaining coefficient of \(h\)
is positive, so \(h\ge1/3\) gives the displayed constants.
Consequently each \(U_{i2}\) increases, and
\[
U_{02}\ge-\frac{157885}{81}>-2000,\qquad
U_{12}\ge-\frac{4249378}{81}>-60000,\qquad
U_{22}\ge-\frac{42950318}{729}>-60000.
\tag{8}
\]
These are evaluations at \(h=1/3\) of fully printed polynomials, not
coefficient minima.

### The third-degree coefficients

\[
U_{03}(h)=940 + 22636 h - 62763 h^{2} - 98500 h^{3} + 246285 h^{4} + 411198 h^{5} + 189938 h^{6} + 26112 h^{7}.
\]
(8 monomials, degree 7.)

\[
U_{13}(h)=-26090 + 140112 h + 591453 h^{2} + 1828 h^{3} - 32365 h^{4} + 2436774 h^{5} + 3431008 h^{6} + 1680080 h^{7} + 299376 h^{8}.
\]
(9 monomials, degree 8.)

\[
U_{23}(h)=- 71124 h + 1851753 h^{2} + 3007532 h^{3} + 290600 h^{4} + 1882758 h^{5} + 5886265 h^{6} + 4422400 h^{7} + 1195236 h^{8}.
\]
(8 monomials, degree 8.)

\[
V_3(h)=U_{03}^\prime(h)=22636 - 125526 h - 295500 h^{2} + 985140 h^{3} + 2055990 h^{4} + 1139628 h^{5} + 182784 h^{6}.
\]
(7 monomials, degree 6.)


To see \(V_3>0\), use
\[
985140h^3-295500h^2\ge10960h,\quad
2055990h^4\ge76000h,\quad1139628h^5\ge14000h.
\]
After discarding its remaining positive term, this gives
\[
V_3\ge22636-24566h\ge10353>0.
\tag{9}
\]
Hence \(U_{03}\ge697102/243>0\).

For \(U_{13}\), group its only negative nonconstant term as
\(h^4(2436774h-32365)\). This factor is positive and increasing on the
interval. All other nonconstant terms are positive monomials. Therefore
\[
U_{13}\ge U_{13}(1/3)=\frac{222083972}{2187}>100000.
\tag{10}
\]
For \(U_{23}\), all terms except its linear term are positive. Keep its
quadratic term to obtain
\[
U_{23}\ge h(1851753h-71124)\ge\frac{546127}{3}>100000.
\tag{11}
\]
The degrees of the sign polynomials in this subsection are at most eight.
The auxiliary product comparisons in (9)–(11) have at most three monomials
and degree at most five.

## 2. The positive higher coefficients

Here are the nine remaining sign polynomials. For each polynomial the next
line gives an explicit arithmetic lower bound, in the same increasing-power
order as its terms: a positive coefficient times \(h^m\) is bounded below
using \(h\ge1/3\); a negative one using \(h\le1/2\). Each resulting rational
is rounded downward to the displayed integer. These are elementary monomial
inequalities for the printed polynomials; no coefficient extraction or sign
program is a premise.

\[
P_{04}(h)=-4740 + 32320 h + 167472 h^{2} + 79352 h^{3} - 161270 h^{4} - 37452 h^{5} + 150402 h^{6} + 95872 h^{7} + 14472 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{04}(h)\ge -4740+10773+18608+2938-10080-1171+206+43+2=16579>0.
\]

\[
P_{05}(h)=-7920 + 49320 h + 219024 h^{2} + 173310 h^{3} - 91236 h^{4} - 135142 h^{5} - 18520 h^{6} + 16299 h^{7} + 3300 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{05}(h)\ge -7920+16440+24336+6418-5703-4224-290+7+0=29064>0.
\]

\[
P_{06}(h)=-1800 + 22880 h + 85600 h^{2} + 74208 h^{3} - 21406 h^{4} - 54080 h^{5} - 20259 h^{6} - 930 h^{7} + 198 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{06}(h)\ge -1800+7626+9511+2748-1338-1690-317-8+0=14732>0.
\]

\[
P_{14}(h)=-43340 + 797904 h + 2695200 h^{2} + 1720450 h^{3} - 1143300 h^{4} - 723828 h^{5} + 907456 h^{6} + 741762 h^{7} + 143640 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{14}(h)\ge -43340+265968+299466+63720-71457-22620+1244+339+21=493341>0.
\]

\[
P_{15}(h)=-22500 + 902928 h + 2853810 h^{2} + 2114988 h^{3} - 979839 h^{4} - 1677176 h^{5} - 444384 h^{6} + 77870 h^{7} + 26697 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{15}(h)\ge -22500+300976+317090+78332-61240-52412-6944+35+4=553341>0.
\]

\[
P_{16}(h)=9200 + 335700 h + 972216 h^{2} + 745612 h^{3} - 305240 h^{4} - 629073 h^{5} - 242050 h^{6} - 18227 h^{7} + 1368 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{16}(h)\ge 9200+111900+108024+27615-19078-19659-3783-143+0=214076>0.
\]

\[
P_{24}(h)=289722 + 5830096 h + 9460610 h^{2} + 499440 h^{3} - 5055736 h^{4} - 732864 h^{5} + 1501650 h^{6} + 514380 h^{7} + 24156 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{24}(h)\ge 289722+1943365+1051178+18497-315984-22902+2059+235+3=2966173>0.
\]

\[
P_{25}(h)=421584 + 5377950 h + 8558352 h^{2} + 457758 h^{3} - 5730288 h^{4} - 2865537 h^{5} - 131820 h^{6} + 74877 h^{7} + 1512 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{25}(h)\ge 421584+1792650+950928+16954-358143-89549-2060+34+0=2732398>0.
\]

\[
P_{26}(h)=189100 + 1673748 h + 2603272 h^{2} + 74704 h^{3} - 1916379 h^{4} - 1022300 h^{5} - 113157 h^{6} + 3024 h^{7}.
\]
(8 monomials, degree 7.)

\[
P_{26}(h)\ge 189100+557916+289252+2766-119774-31947-1769+1=885545>0.
\]


All nine polynomials have degree at most eight and at most nine monomials.
Their integer coefficients have at most seven digits. The corresponding
arithmetic comparisons involve only powers \(3^m\) and \(2^m\) for \(m\le8\).

## 3. The seventh-degree terms are uniformly bounded

\[
S_0(h)=150 + 120 h - 301 h^{2} - 240 h^{3} + 108 h^{4} + 100 h^{5} + 11 h^{6}.
\]
(7 monomials, degree 6.)

\[
S_1(h)=150 + 1500 h + 637 h^{2} - 3196 h^{3} - 1989 h^{4} + 1390 h^{5} + 1100 h^{6} + 126 h^{7}.
\]
(8 monomials, degree 7.)

\[
S_2(h)=2400 + 8029 h - 10048 h^{2} - 15570 h^{3} + 5940 h^{4} + 8261 h^{5} + 1128 h^{6}.
\]
(7 monomials, degree 6.)


Discard negative terms in each \(S_i\), then use \(h\le1/2\). This gives
\[
\begin{aligned}
S_0&\le\frac{11}{64}+\frac{100}{32}+\frac{108}{16}+60+150<221,\\
S_1&\le\frac{126}{128}+\frac{1100}{64}+\frac{1390}{32}
       +\frac{637}{4}+750+150<1121,\\
S_2&\le\frac{1128}{64}+\frac{8261}{32}+\frac{5940}{16}
       +\frac{8029}{2}+2400<7062.
\end{aligned}
\tag{12}
\]
These upper bounds do not require \(S_i\ge0\). Since \(h^4\le1/16\) and
\(h^5\le1/32\), all three coefficients of \(z^7\) in (2) are greater
than \(-2000\):
\[
-12h^4S_0>-2000,\qquad -12h^4S_1>-2000,\qquad -6h^5S_2>-2000.
\tag{13}
\]
The sign polynomials in this step are univariate of degrees six or seven.

## 4. Assemble the derivative signs

All factors discarded below are nonnegative by the preceding sections.
For \(0\le z\le1\), (2)–(13) give
\[
E_0\ge11000-2000z^2-2000z^7\ge7000,
\tag{14}
\]
\[
E_1\ge30000-60000z^2+100000z^3-2000z^7,
\qquad
E_2\ge16000-60000z^2+100000z^3-2000z^7.
\tag{15}
\]
The single small square identity
\[
100000z^3-60000z^2
=100000(z-2/5)^2(z+1/5)-3200\ge-3200
\quad(z\ge0)
\tag{16}
\]
has two monomials on its expanded polynomial side, total degree three,
and coefficients of at most six digits. Hence
\[
E_1\ge24800,\qquad E_2\ge10800.
\tag{17}
\]
Together with (14), division by two proves (1).

## 5. The caller and the expansion boundary

Substitution \(h=1/3\) in Appendix A gives the three \(a_i\) printed in
[the completed base-quadratic replacement](NONSHORT_LOW_RATIO.md).
Each of these three checks is a univariate identity in \(z\) of degree seven
and eight monomials. Integrating the positive derivative bounds, or using
the mean value theorem, gives
\[
\mathcal A_i(h,z)\ge a_i(z)
\quad(i=0,1,2;\ 1/3\le h\le1/2;\ 0\le z\le1).
\tag{18}
\]
These are precisely the monotonicity premises used by equation (15) of the
original low-ratio note. Combined with the base-quadratic replacement, they
make that quadratic positive with margin at least four.

To obtain (2) from Appendix A, differentiate one \(z\)-coefficient at a time.
For a factor \(h^r B(h)\), use
\[
\frac{d}{dh}(h^rB)=h^{r-1}\{rB+hB'\}.
\]
The bracket is a univariate polynomial of degree at most eight, regardless
of \(r\); keep the exterior power factored. For \(r=0\), differentiate
\(B\) directly. The four exceptional monomials in \(\mathcal A_1\) are
separated in its definition, so the power rule handles them without a
high-degree expansion. The two sides of every nontrivial coefficient
identity in this verification have at most nine monomials and degree at
most eight. The largest derivative coefficient printed here is 35,438,280.

The factored definitions themselves should be retained in Lean. Expanding
all exterior powers, all powers of \(z\), or the original \(P\) into one
ring identity would lose this budget. The
[fourth-derivative bridge](NONSHORT_LOW_RATIO_LINK.md) provides the required
link from the original residual \(G\) to these coefficient definitions
through small coefficient identities, with the verification order stated there.
No Lean verification or performance improvement is claimed here.

## Appendix A. Complete factored starting polynomials

These definitions specify every coefficient of \(\mathcal A_i\) while keeping
powers factored. All block polynomials \(B_{in}\) below have degree at most
eight and at most nine monomials.
\[
\begin{aligned}
2\mathcal A_0={}&B_{00}+zB_{01}+z^2B_{02}+z^3B_{03}
 +hz^4B_{04}+h^2z^5B_{05}+h^3z^6B_{06}+h^5z^7B_{07},\\
2\mathcal A_1={}&B_{10}+zB_{11}+z^2(1080h^9+B_{12})
 +hz^3(936h^9+B_{13})\\
 &+h^2z^4(288h^9+B_{14})+h^3z^5(18h^9+B_{15})
 +h^4z^6B_{16}+h^5z^7B_{17},\\
2\mathcal A_2={}&B_{20}+zB_{21}+hz^2B_{22}+h^2z^3B_{23}
 +h^3z^4B_{24}+h^4z^5B_{25}+h^5z^6B_{26}+h^6z^7B_{27}.
\end{aligned}
\tag{19}
\]

### Blocks for \(\mathcal A_0\)

\[
B_{00}(h)=-1860 + 2570 h + 9766 h^{2} + 6540 h^{3} + 1008 h^{4}.
\]
(5 monomials, degree 4.)

\[
B_{01}(h)=4020 - 6440 h + 3929 h^{2} + 42003 h^{3} + 38424 h^{4} + 11076 h^{5} + 1008 h^{6}.
\]
(7 monomials, degree 6.)

\[
B_{02}(h)=-4860 - 2970 h - 22149 h^{2} - 2496 h^{3} + 74854 h^{4} + 78347 h^{5} + 26922 h^{6} + 2952 h^{7}.
\]
(8 monomials, degree 7.)

\[
B_{03}(h)=-1380 + 940 h + 11318 h^{2} - 20921 h^{3} - 24625 h^{4} + 49257 h^{5} + 68533 h^{6} + 27134 h^{7} + 3264 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{04}(h)=-4740 + 16160 h + 55824 h^{2} + 19838 h^{3} - 32254 h^{4} - 6242 h^{5} + 21486 h^{6} + 11984 h^{7} + 1608 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{05}(h)=-3960 + 16440 h + 54756 h^{2} + 34662 h^{3} - 15206 h^{4} - 19306 h^{5} - 2315 h^{6} + 1811 h^{7} + 330 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{06}(h)=-600 + 5720 h + 17120 h^{2} + 12368 h^{3} - 3058 h^{4} - 6760 h^{5} - 2251 h^{6} - 93 h^{7} + 18 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{07}(h)=-360 - 240 h + 516 h^{2} + 360 h^{3} - 144 h^{4} - 120 h^{5} - 12 h^{6}.
\]
(7 monomials, degree 6.)


### Blocks for \(\mathcal A_1\)

\[
B_{10}(h)=-720 - 7780 h + 17094 h^{2} + 58240 h^{3} + 43434 h^{4} + 9612 h^{5} + 432 h^{6}.
\]
(7 monomials, degree 6.)

\[
B_{11}(h)=3000 + 1950 h - 45830 h^{2} + 58853 h^{3} + 296430 h^{4} + 276717 h^{5} + 95736 h^{6} + 12852 h^{7} + 432 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{12}(h)=-14760 - 38280 h - 67107 h^{2} - 128528 h^{3} + 130659 h^{4} + 606701 h^{5} + 580936 h^{6} + 221237 h^{7} + 33270 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{13}(h)=-26090 + 70056 h + 197151 h^{2} + 457 h^{3} - 6473 h^{4} + 406129 h^{5} + 490144 h^{6} + 210010 h^{7} + 33264 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{14}(h)=-21670 + 265968 h + 673800 h^{2} + 344090 h^{3} - 190550 h^{4} - 103404 h^{5} + 113432 h^{6} + 82418 h^{7} + 14364 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{15}(h)=-7500 + 225732 h + 570762 h^{2} + 352498 h^{3} - 139977 h^{4} - 209647 h^{5} - 49376 h^{6} + 7787 h^{7} + 2427 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{16}(h)=2300 + 67140 h + 162036 h^{2} + 106516 h^{3} - 38155 h^{4} - 69897 h^{5} - 24205 h^{6} - 1657 h^{7} + 114 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{17}(h)=-360 - 3000 h - 1092 h^{2} + 4794 h^{3} + 2652 h^{4} - 1668 h^{5} - 1200 h^{6} - 126 h^{7}.
\]
(8 monomials, degree 7.)


### Blocks for \(\mathcal A_2\)

\[
B_{20}(h)=4140 - 7620 h - 16404 h^{2} + 58692 h^{3} + 89088 h^{4} + 31248 h^{5} + 2592 h^{6}.
\]
(7 monomials, degree 6.)

\[
B_{21}(h)=-1020 + 21780 h - 58914 h^{2} - 94500 h^{3} + 319626 h^{4} + 559212 h^{5} + 287076 h^{6} + 58104 h^{7} + 3456 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{22}(h)=-69330 - 38967 h - 134046 h^{2} - 28145 h^{3} + 801370 h^{4} + 1181276 h^{5} + 633062 h^{6} + 141564 h^{7} + 8496 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{23}(h)=-35562 + 617251 h + 751883 h^{2} + 58120 h^{3} + 313793 h^{4} + 840895 h^{5} + 552800 h^{6} + 132804 h^{7} + 7272 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{24}(h)=96574 + 1457524 h + 1892122 h^{2} + 83240 h^{3} - 722248 h^{4} - 91608 h^{5} + 166850 h^{6} + 51438 h^{7} + 2196 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{25}(h)=105396 + 1075590 h + 1426392 h^{2} + 65394 h^{3} - 716286 h^{4} - 318393 h^{5} - 13182 h^{6} + 6807 h^{7} + 126 h^{8}.
\]
(9 monomials, degree 8.)

\[
B_{26}(h)=37820 + 278958 h + 371896 h^{2} + 9338 h^{3} - 212931 h^{4} - 102230 h^{5} - 10287 h^{6} + 252 h^{7}.
\]
(8 monomials, degree 7.)

\[
B_{27}(h)=-2400 - 6882 h + 7536 h^{2} + 10380 h^{3} - 3564 h^{4} - 4506 h^{5} - 564 h^{6}.
\]
(7 monomials, degree 6.)

