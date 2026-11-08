# A factored positive remainder for the low-ratio sign

Date: 2026-11-08.

**Scope and unresolved link.** This supplies small sign proofs for the
higher-gap coefficient functions \(C_3,\ldots,C_{10}\) of
[MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION](../../archive/notes/MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION.md).
Their complete factored forms are printed below. They have been checked
with exact symbolic arithmetic against the original coefficient definitions,
but **the original three-variable collection identity linking \(G\) to
\(P=\sum_{i=0}^{10}C_i j^i\) still needs a budget-compliant derivation**.
This note does not close that link or the full requested sign by itself.

The result for the displayed coefficient functions is
\[
\boxed{C_3>700,\quad C_4>3900,\quad C_5,C_6,C_7>0,
       \quad C_8,C_9,C_{10}\ge0}
\tag{1}
\]
for \(1/3\le h\le1/2\), \(0\le z\le1\). Consequently, for every \(j\ge0\),
\[
\boxed{\sum_{i=3}^{10}C_i(h,z)j^i\ge700j^3\ge0.}
\tag{2}
\]
The caller is the remainder estimate (16), used after (15), in the original
note. That caller needs only a nonnegative remainder. Thus (2) is sufficient;
no bound \(j\le h\) is needed by this replacement.

Unlike the original shifted-power negative-part estimate, the proof here
uses separate, explicitly printed univariate factors of degree at most
eight. All but two are positive by direct monomial bounds. The two remaining
factors have small negative lower bounds, absorbed by the positive constants
of \(C_3,C_4\). No subdivision, coefficient table, transcendental bound, or
external positivity calculation is a premise.

## 1. Domain and the factored coefficient functions

Put \(y=hz\), so \(0\le y\le h\le1/2\). Define
\(C_i(h,z)=\widetilde C_i(h,hz)\) by the following complete factored
expressions. Each \(P_{in}\) is a univariate polynomial in \(h\), printed
in Section 2. The powers of \(y\), and the factors \(h+1\) and \(1-h\),
remain factored; their nonnegativity needs no expansion.
\[
\begin{aligned}
\widetilde C_3(h,y)={}&2(h+1)^{2}P_{30}\\
&+y(h+1)P_{31}\\
&+\frac{1}{2}y^{2}(h+1)P_{32}\\
&+\frac{1}{2}y^{3}(h+1)P_{33}\\
&+y^{4}(h+1)P_{34}\\
&+\frac{1}{2}y^{5}(h+1)P_{35}\\
&+\frac{1}{2}y^{6}(h+1)P_{36}\\
&+3y^{7}(h+1)(1-h)P_{37} .
\end{aligned}
\]

\[
\begin{aligned}
\widetilde C_4(h,y)={}&(h+1)^{2}P_{40}\\
&+\frac{1}{2}y(h+1)P_{41}\\
&+\frac{1}{2}y^{2}(h+1)P_{42}\\
&+\frac{1}{2}y^{3}(h+1)P_{43}\\
&+y^{4}(h+1)P_{44}\\
&+\frac{1}{2}y^{5}(h+1)P_{45}\\
&+\frac{1}{2}y^{6}(h+1)P_{46}\\
&+3y^{7}(h+1)(1-h)P_{47} .
\end{aligned}
\]

\[
\begin{aligned}
\widetilde C_5(h,y)={}&3(h+1)^{2}P_{50}\\
&+\frac{3}{2}y(h+1)P_{51}\\
&+\frac{1}{2}y^{2}P_{52}\\
&+\frac{1}{2}y^{3}P_{53}\\
&+y^{4}P_{54}\\
&+\frac{3}{2}y^{5}P_{55}\\
&+\frac{3}{2}y^{6}P_{56}\\
&+3y^{7}(h+1)(1-h)P_{57} .
\end{aligned}
\]

\[
\begin{aligned}
\widetilde C_6(h,y)={}&12(h+1)^{2}P_{60}\\
&+6y(h+1)P_{61}\\
&+y^{2}P_{62}\\
&+\frac{1}{2}y^{3}P_{63}\\
&+y^{4}P_{64}\\
&+\frac{1}{2}y^{5}P_{65}\\
&+\frac{1}{2}y^{6}P_{66}\\
&+3y^{7}(h+1)(1-h)P_{67} .
\end{aligned}
\]

\[
\begin{aligned}
\widetilde C_7(h,y)={}&36(h+1)^{2}(1-h)P_{70}\\
&+3y(h+1)P_{71}\\
&+\frac{1}{2}y^{2}P_{72}\\
&+4y^{3}P_{73}\\
&+y^{4}P_{74}\\
&+\frac{1}{2}y^{5}P_{75}\\
&+\frac{1}{2}y^{6}P_{76}\\
&+3y^{7}(h+1)(1-h)P_{77} .
\end{aligned}
\]

\[
\begin{aligned}
\widetilde C_8(h,y)={}&24y(h+1)(1-h)P_{81}\\
&+4y^{2}P_{82}\\
&+2y^{3}P_{83}\\
&+y^{4}P_{84}\\
&+\frac{3}{2}y^{5}P_{85}\\
&+y^{6}(1-h)P_{86}\\
&+30y^{7}(h+1)(1-h) .
\end{aligned}
\]

\[
\begin{aligned}
\widetilde C_9(h,y)={}&36y(h+1)(1-h)P_{91}\\
&+6y^{2}(1-h)P_{92}\\
&+24y^{3}(1-h)P_{93}\\
&+y^{4}(1-h)P_{94}\\
&+6y^{5}(1-h)P_{95}\\
&+2y^{6}(1-h)P_{96} .
\end{aligned}
\]


The last coefficient needs only the visibly positive factorization
\[
\widetilde C_{10}(h,y)
=(1-h)\{432y^2+1080y^3+960y^4+300y^5\}\ge0.
\tag{3}
\]
If expanded, (3) has eight monomials, total degree six, and two variables.

## 2. Every univariate factor and its sign

For each printed polynomial, a positive term \(c h^m\) is at least
\(c/3^m\); a negative term is at least \(c/2^m\). The explicit integer sums
below follow by rounding each of these rational lower bounds downward,
in the same increasing-power order as the polynomial. Thus every displayed
lower bound can be checked directly from its adjacent polynomial.
No coefficient extraction or unexplained minimum is used.

### Factors for \(C_3\)

\[
P_{30}(h)=750 + 2735 h - 5619 h^{2} - 833 h^{3} + 18639 h^{4} + 11844 h^{5} + 1620 h^{6}.
\]
(7 monomials, degree 6.)

\[
P_{30}(h)\ge 750+911-1405-105+230+48+2=431>400.
\]

\[
P_{31}(h)=8705 + 32414 h - 38975 h^{2} - 51137 h^{3} + 231183 h^{4} + 424449 h^{5} + 268647 h^{6} + 72306 h^{7} + 6048 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{31}(h)\ge 8705+10804-9744-6393+2854+1746+368+33+0=8373>0.
\]

\[
P_{32}(h)=-72759 + 74553 h + 160411 h^{2} + 412787 h^{3} + 1338365 h^{4} + 1800478 h^{5} + 1148415 h^{6} + 338190 h^{7} + 29232 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{32}(h)\ge -72759+24851+17823+15288+16523+7409+1575+154+4=10868>0.
\]

\[
P_{33}(h)=225967 + 1979598 h + 2750577 h^{2} + 849874 h^{3} + 45928 h^{4} + 832220 h^{5} + 873028 h^{6} + 297504 h^{7} + 24696 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{33}(h)\ge 225967+659866+305619+31476+567+3424+1197+136+3=1228255>0.
\]

\[
P_{34}(h)=338793 + 2000238 h + 2548635 h^{2} + 261460 h^{3} - 1142100 h^{4} - 495097 h^{5} + 52254 h^{6} + 49671 h^{7} + 3654 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{34}(h)\ge 338793+666746+283181+9683-71382-15472+71+22+0=1211642>0.
\]

\[
P_{35}(h)=510006 + 2740780 h + 3366742 h^{2} + 73942 h^{3} - 1950176 h^{4} - 1012247 h^{5} - 124034 h^{6} + 7281 h^{7} + 378 h^{8}.
\]
(9 monomials, degree 8.)

\[
P_{35}(h)\ge 510006+913593+374082+2738-121886-31633-1939+3+0=1644964>0.
\]

\[
P_{36}(h)=135850 + 669914 h + 790444 h^{2} - 56276 h^{3} - 542205 h^{4} - 264504 h^{5} - 31721 h^{6} + 66 h^{7}.
\]
(8 monomials, degree 7.)

\[
P_{36}(h)\ge 135850+223304+87827-7035-33888-8266-496+0=397296>0.
\]

\[
P_{37}(h)=-919 - 1994 h + 1078 h^{2} + 3773 h^{3} + 1975 h^{4} + 235 h^{5}.
\]
(6 monomials, degree 5.)

\[
P_{37}(h)\ge -919-997+119+139+24+0=-1634>-2000.
\]


### Factors for \(C_4\)

\[
P_{40}(h)=5035 + 5478 h - 12439 h^{2} + 5742 h^{3} + 16992 h^{4} + 4320 h^{5}.
\]
(6 monomials, degree 5.)

\[
P_{40}(h)\ge 5035+1826-3110+212+209+17=4189>4000.
\]

\[
P_{41}(h)=63013 + 145269 h + 5447 h^{2} - 51105 h^{3} + 240828 h^{4} + 394548 h^{5} + 191808 h^{6} + 24192 h^{7}.
\]
(8 monomials, degree 7.)

\[
P_{41}(h)\ge 63013+48423+605-6389+2973+1623+263+11=110522>0.
\]

\[
P_{42}(h)=66595 + 595624 h + 709256 h^{2} + 304978 h^{3} + 397461 h^{4} + 727438 h^{5} + 428664 h^{6} + 57456 h^{7}.
\]
(8 monomials, degree 7.)

\[
P_{42}(h)\ge 66595+198541+78806+11295+4906+2993+588+26=363750>0.
\]

\[
P_{43}(h)=770791 + 3237631 h + 2512262 h^{2} - 671793 h^{3} - 1009965 h^{4} + 219446 h^{5} + 345204 h^{6} + 47880 h^{7}.
\]
(8 monomials, degree 7.)

\[
P_{43}(h)\ge 770791+1079210+279140-83975-63123+903+473+21=1983440>0.
\]

\[
P_{44}(h)=759057 + 2649927 h + 1602452 h^{2} - 1128401 h^{3} - 1229630 h^{4} - 224572 h^{5} + 42861 h^{6} + 6930 h^{7}.
\]
(8 monomials, degree 7.)

\[
P_{44}(h)\ge 759057+883309+178050-141051-76852-7018+58+3=1595556>0.
\]

\[
P_{45}(h)=1017184 + 3297010 h + 1674623 h^{2} - 1755821 h^{3} - 1635636 h^{4} - 347735 h^{5} - 7167 h^{6} + 630 h^{7}.
\]
(8 monomials, degree 7.)

\[
P_{45}(h)\ge 1017184+1099003+186069-219478-102228-10867-112+0=1969571>0.
\]

\[
P_{46}(h)=244734 + 742340 h + 292703 h^{2} - 488049 h^{3} - 369017 h^{4} - 58619 h^{5} - 780 h^{6}.
\]
(7 monomials, degree 6.)

\[
P_{46}(h)\ge 244734+247446+32522-61007-23064-1832-13=438786>0.
\]

\[
P_{47}(h)=-759 + 436 h + 3435 h^{2} + 2440 h^{3} + 360 h^{4}.
\]
(5 monomials, degree 4.)

\[
P_{47}(h)\ge -759+145+381+90+4=-139>-200.
\]


### Factors for \(C_5\)

\[
P_{50}(h)=2045 + 274 h - 2501 h^{2} + 1194 h^{3} + 1080 h^{4}.
\]
(5 monomials, degree 4.)

\[
P_{50}(h)\ge 2045+91-626+44+13=1567>0.
\]

\[
P_{51}(h)=33401 + 66473 h - 1933 h^{2} - 61825 h^{3} + 14408 h^{4} + 47196 h^{5} + 10080 h^{6}.
\]
(7 monomials, degree 6.)

\[
P_{51}(h)\ge 33401+22157-484-7729+177+194+13=47729>0.
\]

\[
P_{52}(h)=284044 + 1267299 h + 1354250 h^{2} - 231982 h^{3} - 767868 h^{4} + 134635 h^{5} + 359718 h^{6} + 70560 h^{7}.
\]
(8 monomials, degree 7.)

\[
P_{52}(h)\ge 284044+422433+150472-28998-47992+554+493+32=781038>0.
\]

\[
P_{53}(h)=1189999 + 4187845 h + 3415677 h^{2} - 1421207 h^{3} - 2664028 h^{4} - 604022 h^{5} + 239184 h^{6} + 57960 h^{7}.
\]
(8 monomials, degree 7.)

\[
P_{53}(h)\ge 1189999+1395948+379519-177651-166502-18876+328+26=2602791>0.
\]

\[
P_{54}(h)=943067 + 2881934 h + 1835589 h^{2} - 1373857 h^{3} - 1813517 h^{4} - 519067 h^{5} + 3549 h^{6} + 8190 h^{7}.
\]
(8 monomials, degree 7.)

\[
P_{54}(h)\ge 943067+960644+203954-171733-113345-16221+4+3=1806373>0.
\]

\[
P_{55}(h)=386159 + 1084357 h + 549849 h^{2} - 631562 h^{3} - 663211 h^{4} - 178757 h^{5} - 10645 h^{6} + 210 h^{7}.
\]
(8 monomials, degree 7.)

\[
P_{55}(h)\ge 386159+361452+61094-78946-41451-5587-167+0=682554>0.
\]

\[
P_{56}(h)=86727 + 221153 h + 72618 h^{2} - 162432 h^{3} - 126063 h^{4} - 23153 h^{5} - 594 h^{6}.
\]
(7 monomials, degree 6.)

\[
P_{56}(h)\ge 86727+73717+8068-20304-7879-724-10=139595>0.
\]

\[
P_{57}(h)=50 + 1639 h + 1776 h^{2} + 347 h^{3}.
\]
(4 monomials, degree 3.)

\[
P_{57}(h)\ge 50+546+197+12=805>0.
\]


### Factors for \(C_6\)

\[
P_{60}(h)=268 - 163 h - 156 h^{2} + 108 h^{3}.
\]
(4 monomials, degree 3.)

\[
P_{60}(h)\ge 268-82-39+4=151>0.
\]

\[
P_{61}(h)=7958 + 10532 h - 9131 h^{2} - 10567 h^{3} + 3762 h^{4} + 2016 h^{5}.
\]
(6 monomials, degree 5.)

\[
P_{61}(h)\ge 7958+3510-2283-1321+46+8=7918>0.
\]

\[
P_{62}(h)=195401 + 527630 h + 142618 h^{2} - 447188 h^{3} - 241443 h^{4} + 55950 h^{5} + 27720 h^{6}.
\]
(7 monomials, degree 6.)

\[
P_{62}(h)\ge 195401+175876+15846-55899-15091+230+38=316401>0.
\]

\[
P_{63}(h)=1128619 + 2548891 h + 400113 h^{2} - 2008759 h^{3} - 1111828 h^{4} + 3996 h^{5} + 44856 h^{6}.
\]
(7 monomials, degree 6.)

\[
P_{63}(h)\ge 1128619+849630+44457-251095-69490+16+61=1702198>0.
\]

\[
P_{64}(h)=738348 + 1419620 h + 15555 h^{2} - 1127405 h^{3} - 564117 h^{4} - 44415 h^{5} + 6174 h^{6}.
\]
(7 monomials, degree 6.)

\[
P_{64}(h)\ge 738348+473206+1728-140926-35258-1388+8=1035718>0.
\]

\[
P_{65}(h)=815314 + 1363151 h - 204114 h^{2} - 1124336 h^{3} - 476434 h^{4} - 46647 h^{5} + 378 h^{6}.
\]
(7 monomials, degree 6.)

\[
P_{65}(h)\ge 815314+454383-51029-140542-29778-1458+0=1046890>0.
\]

\[
P_{66}(h)=164589 + 220226 h - 104804 h^{2} - 198254 h^{3} - 51289 h^{4} - 1956 h^{5}.
\]
(6 monomials, degree 5.)

\[
P_{66}(h)\ge 164589+73408-26201-24782-3206-62=183746>0.
\]

\[
P_{67}(h)=321 + 707 h + 206 h^{2}.
\]
(3 monomials, degree 2.)

\[
P_{67}(h)\ge 321+235+22=578>0.
\]


### Factors for \(C_7\)

\[
P_{70}(h)=17 - 6 h.
\]
(2 monomials, degree 1.)

\[
P_{70}(h)\ge 17-3=14>0.
\]

\[
P_{71}(h)=9055 + 3222 h - 12343 h^{2} - 1350 h^{3} + 2016 h^{4}.
\]
(5 monomials, degree 4.)

\[
P_{71}(h)\ge 9055+1074-3086-169+24=6898>0.
\]

\[
P_{72}(h)=278995 + 384097 h - 232237 h^{2} - 375241 h^{3} - 29694 h^{4} + 27216 h^{5}.
\]
(6 monomials, degree 5.)

\[
P_{72}(h)\ge 278995+128032-58060-46906-1856+112=300317>0.
\]

\[
P_{73}(h)=83054 + 97195 h - 65819 h^{2} - 90166 h^{3} - 12429 h^{4} + 2709 h^{5}.
\]
(6 monomials, degree 5.)

\[
P_{73}(h)\ge 83054+32398-16455-11271-777+11=86960>0.
\]

\[
P_{74}(h)=366984 + 353231 h - 294555 h^{2} - 325325 h^{3} - 51465 h^{4} + 2898 h^{5}.
\]
(6 monomials, degree 5.)

\[
P_{74}(h)\ge 366984+117743-73639-40666-3217+11=367216>0.
\]

\[
P_{75}(h)=353458 + 264973 h - 295267 h^{2} - 250699 h^{3} - 38031 h^{4} + 126 h^{5}.
\]
(6 monomials, degree 5.)

\[
P_{75}(h)\ge 353458+88324-73817-31338-2377+0=334250>0.
\]

\[
P_{76}(h)=58723 + 21049 h - 54001 h^{2} - 23113 h^{3} - 1218 h^{4}.
\]
(5 monomials, degree 4.)

\[
P_{76}(h)\ge 58723+7016-13501-2890-77=49271>0.
\]

\[
P_{77}(h)=119 + 69 h.
\]
(2 monomials, degree 1.)

\[
P_{77}(h)\ge 119+23=142>0.
\]


### Factors for \(C_8\)

\[
P_{81}(h)=335 + 144 h - 72 h^{2}.
\]
(3 monomials, degree 2.)

\[
P_{81}(h)\ge 335+48-18=365>0.
\]

\[
P_{82}(h)=12812 + 4377 h - 13406 h^{2} - 4521 h^{3} + 954 h^{4}.
\]
(5 monomials, degree 4.)

\[
P_{82}(h)\ge 12812+1459-3352-566+11=10364>0.
\]

\[
P_{83}(h)=56167 + 13983 h - 53365 h^{2} - 17055 h^{3} + 1494 h^{4}.
\]
(5 monomials, degree 4.)

\[
P_{83}(h)\ge 56167+4661-13342-2132+18=45372>0.
\]

\[
P_{84}(h)=109011 + 15983 h - 95129 h^{2} - 28335 h^{3} + 774 h^{4}.
\]
(5 monomials, degree 4.)

\[
P_{84}(h)\ge 109011+5327-23783-3542+9=87022>0.
\]

\[
P_{85}(h)=29855 + 263 h - 23477 h^{2} - 6167 h^{3} + 6 h^{4}.
\]
(5 monomials, degree 4.)

\[
P_{85}(h)\ge 29855+87-5870-771+0=23301>0.
\]

\[
P_{86}(h)=5201 + 3072 h + 207 h^{2}.
\]
(3 monomials, degree 2.)

\[
P_{86}(h)\ge 5201+1024+23=6248>0.
\]


### Factors for \(C_9\)

\[
P_{91}(h)=25 - 6 h.
\]
(2 monomials, degree 1.)

\[
P_{91}(h)\ge 25-3=22>0.
\]

\[
P_{92}(h)=1417 + 787 h - 78 h^{2}.
\]
(3 monomials, degree 2.)

\[
P_{92}(h)\ge 1417+262-20=1659>0.
\]

\[
P_{93}(h)=783 + 397 h - 15 h^{2}.
\]
(3 monomials, degree 2.)

\[
P_{93}(h)\ge 783+132-4=911>0.
\]

\[
P_{94}(h)=16871 + 7989 h - 90 h^{2}.
\]
(3 monomials, degree 2.)

\[
P_{94}(h)\ge 16871+2663-23=19511>0.
\]

\[
P_{95}(h)=983 + 421 h.
\]
(2 monomials, degree 1.)

\[
P_{95}(h)\ge 983+140=1123>0.
\]

\[
P_{96}(h)=161 + 15 h.
\]
(2 monomials, degree 1.)

\[
P_{96}(h)\ge 161+5=166>0.
\]


Every factor has at most nine monomials and degree at most eight in one
variable. Every coefficient in these factors has at most seven digits.
In particular, the only factors that were not proved positive are
\[
P_{37}>-2000,\qquad P_{47}>-200.
\tag{4}
\]

## 3. Absorb the only possible negative contributions

All terms of \(\widetilde C_3\) except its last one are positive, and
its constant factor satisfies \(P_{30}>400\). Since
\(0\le y\le1/2\), \(0<1-h^2<1\), and \(h+1>1\),
\[
\begin{aligned}
\widetilde C_3
&>800-6000(1-h^2)y^7\\
&\ge800-\frac{6000}{128}
 =\frac{6025}{8}>700.
\end{aligned}
\tag{5}
\]
Here the only potentially negative summand is
\(3(1-h^2)y^7P_{37}\), and its sign is controlled by (4).
Likewise \(P_{40}>4000\) and the only potentially negative summand of
\(\widetilde C_4\) is \(3(1-h^2)y^7P_{47}\), so
\[
\widetilde C_4
>4000-\frac{600}{128}
 =\frac{63925}{16}>3900.
\tag{6}
\]
All factors of \(\widetilde C_5,\widetilde C_6,\widetilde C_7\) are positive,
and each has a positive constant term in \(y\). Hence these three coefficients
are positive even at \(y=0\). All factors of \(\widetilde C_8,\widetilde C_9\)
are nonnegative and their residual \(P\)'s are positive. These two coefficients
are nonnegative, including \(y=0\). Equation (3) proves the same for
\(\widetilde C_{10}\). This proves (1).

Multiplying each coefficient inequality by the nonnegative power \(j^i\)
and adding gives (2). The argument uses inequalities for positive products,
so there is no need to expand the full polynomial in \((h,z,j)\).

## 4. Budget and proof boundary

All nontrivial sign checks here are univariate, use at most nine monomials,
and have total degree at most eight. The termwise rational comparisons use
only denominators \(3^m\) or \(2^m\), with \(m\le8\); their numerators and
products have at most eleven digits. The factors and their numerical bounds
are all printed, so checking the signs requires elementary integer arithmetic
and the two endpoint inequalities \(1/3\le h\le1/2\).

The remaining task is to derive these factored \(C_i\) from the original
rational residual by small, staged coefficient identities. An instruction to
expand the original \(P\) as one three-variable polynomial would exceed the
requested budget and is **not** supplied as an acceptable link here. Exact
symbolic comparison was used to check the transcription of the displayed
factors; it is not offered as a substitute for that missing budget-compliant
link. No Lean or CI run, and no measured Lean speedup, is claimed.
