# Hand exclusion of the low-ratio nonshort forward successor

Date: 2026-11-08 UTC.

**Lighter replacement:** the complete unit-shape sign (10) now has a
[fourth-derivative proof](../../docs/lighter-proofs/NONSHORT_LOW_RATIO_LINK.md)
with the same conclusion and domain, no coefficient tables, and expanded
identities of degree at most eight with at most 41 monomials. That note and
its three companion proofs replace the large sign argument below for the
requested hand-proof standard. The original argument is retained here as
the historical source. Existing Lean sources have not been changed or run.

This note completes the scalar sign left open in
[MIXED_NONSHORT_FORWARD_RATIO_REDUCTION](MIXED_NONSHORT_FORWARD_RATIO_REDUCTION.md),
with the sharper integral secant majorant from
[MIXED_NONSHORT_POSITIVE_INTEGRAL_SECANT_BOUND](MIXED_NONSHORT_POSITIVE_INTEGRAL_SECANT_BOUND.md).
Its conclusion is
\[
\boxed{t>\frac13}
\tag{1}
\]
for an eligible actual smaller-nonshort forward-successor boundary point.
It does not by itself exclude all such points.

The sign proof has three parts: remove the shape variable by the already
proved monotonicity; isolate a quadratic in the gap variable; and bound
its higher-order remainder by a single elementary coefficient sum. The
coefficient identities used in the last two parts are displayed below,
including the negative contributions and their rational bounds. No
subdivision, executable certificate, numerical minimum or omitted
positivity test is a premise.

## 1. The sharper substitution preserves the actual scalar inequalities

Suppose that an eligible actual point has \(t\le1/3\). The cited ratio
reduction already proves
\[
\frac14\le t\le\frac13,\qquad
1-2t\le x\le1,\qquad 1\le k\le2t+x,
\qquad1\le q\le\frac{1+x}{2t+x}.
\tag{2}
\]
Write
\[
c=1-t,\quad p=t+x,\quad W=1+x,\quad X=2+x,
\quad R=x^2+10x+15.
\]
The actual incoming norm is \(v\), and its floor is
\(F_{p/W}(q)\le v\). Define
\[
V=1-\frac{cp}{W^2}
 +\frac{cx}{W^2}\left(\frac{90-19x^2}{12R}-t\right),
\tag{3}
\]
\[
L=\frac{(q-1)(q^2+10q+1)}{6q(q+1)},\qquad
F_\ell=1+\frac{p^2q}{W^2}
 -\frac pW\frac{q^2+10q+1}{6(q+1)},
\]
\[
\rho=\frac34(q+2t+x-1),\qquad
\widehat v=V+\rho(V-F_\ell),\qquad
\widehat G=F(\widehat v,L).
\tag{4}
\]
Here \(F\) is precisely the combined residual in equations (4)--(5)
of the cited ratio reduction; it is not a new boundary comparison.

The positive integral lemma gives \(V>v\). Also \(L>\log q\) and
\(F_\ell<F_{p/W}(q)\le v\) for actual \(q>1\).
Since the already proved coefficients satisfy
\(F_v<0\) and \(F_{\log q}<0\), actual eligibility implies
\[
\widehat G<0.
\tag{5}
\]
The strict statement has its usual continuous endpoint interpretation
at \(q=1\); actual durations are positive.

Let \(v_3\) be the three-term secant majorant in the ratio reduction.
There is the exact identity
\[
v_3-V=
\frac{cx^6(31x^2+82x+46)}{60W^2X^5R}>0.
\tag{6}
\]
Consequently
\(\widehat v<v_3+\rho(v_3-F_\ell)<U(t)\) throughout (2).
The proof of \(G_k>0\) in Section 5 of the ratio reduction uses only
this ceiling, independence of \(k\), and the already proved signs
\(F_{kv}<0,F_{k,\log q}<0\). It therefore applies verbatim:
\[
\widehat G_k>0.
\tag{7}
\]
Lowering the shape to \(k=1\) in (5) would give
\[
\widehat G(t,x,q,1)<0.
\tag{8}
\]
This use of monotonicity is made at the original \((t,x,q)\), where (2)
holds. No floor or Casimir constraint is asserted at another geometry.

## 2. An enlarged unit-shape polynomial

Set
\[
h=1-2t,\qquad j=2t+x-1.
\]
The common order and duration bounds, together with the quantitative
swap bound, give
\[
\frac13\le h\le\frac12,\qquad0\le j\le h,
\qquad q-1\le\frac{h-j}{1+2j}\le h.
\]
For the remaining polynomial sign it is enough to enlarge this to
\[
 t=\frac{1-h}{2},\quad x=h+j,\quad q=1+hz,\quad k=1,
\qquad \frac13\le h\le\frac12,\ 0\le j\le h,\ 0\le z\le1.
\tag{9}
\]
Define
\[
P(h,j,z)=192q(q+1)W^3R\,\widehat G(t,x,q,1).
\tag{10}
\]
All factors multiplying \(\widehat G\) are positive. The denominators
in (3)--(4) cancel, so (10) is a polynomial. Write
\[
P=\sum_{i=0}^{10}C_i(h,z)j^i.
\tag{11}
\]
An explicit compact specification for this polynomial, useful for
checking every subsequent identity, is given in Section 6.

The first three coefficients have the factors
\[
C_0=h^3(h+1)^3A_0(h,z),\qquad
C_1=h^2(h+1)^2A_1(h,z),\qquad
C_2=h(h+1)^2A_2(h,z).
\tag{12}
\]
The quotients \(A_i\) are polynomials of degree at most seven in \(z\).
We will prove
\[
\partial_hA_i>0\quad(i=0,1,2),
\tag{13}
\]
and put \(a_i(z)=A_i(1/3,z)\).

The key one-variable sign is
\[
a_0>0,\qquad a_2>0,\qquad
\Delta(z):=\frac{16}{3}a_0a_2-a_1^2>0
\quad(0\le z\le1).
\tag{14}
\]
Once (13)--(14) hold, let \(\beta=j/[h(h+1)]\ge0\). Then
\[
\frac{C_0+C_1j+C_2j^2}{h^3(h+1)^3}
=A_0+\beta A_1+(h+1)\beta^2A_2
\ge a_0+\beta a_1+\frac43\beta^2a_2>0.
\tag{15}
\]
The last inequality is the positive-leading-coefficient quadratic
criterion, since its discriminant is \(-\Delta\).

The remainder has the separate elementary bound
\[
\sum_{i=3}^{10}C_i(h,z)j^i
\ge j^3\left(\frac{370816}{81}-\frac{72713}{64}\right)\ge0.
\tag{16}
\]
Sections 3--5 prove (13), (14) and (16). Equations (15)--(16) imply
\(P>0\) throughout (9), contradicting (8). This proves (1).

## 3. The quadratic coefficients increase with \(h\)

Here is a small coefficient estimate used both here and for the
remainder. If
\[
Q(u,z)=\sum_{m,n}q_{mn}u^mz^n,\qquad0\le u\le1/6,
\quad0\le z\le1,
\]
then each negative term is at least
\(-|q_{mn}|(1/6)^m\), and every nonnegative term may be discarded
in a lower bound. In particular, if the terms with \(m=0\) are kept
as the polynomial \(Q(0,z)\), then
\[
Q(u,z)\ge Q(0,z)-\sum_{m\ge1,n:q_{mn}<0}|q_{mn}|(1/6)^m.
\tag{17}
\]
This is just \(u^m\le6^{-m}\), \(z^n\le1\), applied to displayed
finite polynomials.

Put \(u=h-1/3\), and let
\(D_i(u,z)=\partial_hA_i(1/3+u,z)\).
The coefficients of \(D_i(0,z)\) in the basis
\(z^m(1-z)^{7-m}\) are as follows. The binomial coefficient is not
included in the table.

| \(m\) | \(D_0(0,z)\) | \(D_1(0,z)\) | \(D_2(0,z)\) |
| ---: | ---: | ---: | ---: |
| 0 | \(5705\) | \(15034\) | \(\frac{72896}{9}\) |
| 1 | \(\frac{2604187}{54}\) | \(\frac{10731529}{81}\) | \(\frac{6234080}{81}\) |
| 2 | \(\frac{27309071}{162}\) | \(\frac{36691651}{81}\) | \(\frac{191169065}{729}\) |
| 3 | \(\frac{77904986}{243}\) | \(\frac{1868923676}{2187}\) | \(\frac{1307221747}{2187}\) |
| 4 | \(\frac{818646482}{2187}\) | \(\frac{7263244340}{6561}\) | \(\frac{877950949}{729}\) |
| 5 | \(\frac{1888382344}{6561}\) | \(\frac{7140439360}{6561}\) | \(\frac{33894116407}{19683}\) |
| 6 | \(\frac{935441456}{6561}\) | \(\frac{41521930448}{59049}\) | \(\frac{26022527212}{19683}\) |
| 7 | \(\frac{679591424}{19683}\) | \(\frac{11976348224}{59049}\) | \(\frac{2624449664}{6561}\) |

Comparing each column with the coefficients
\(\binom7m\) of \(1=(z+(1-z))^7\) gives
\[
D_0(0,z)\ge5705,\qquad
D_1(0,z)\ge15034,\qquad
D_2(0,z)\ge\frac{72896}{9}.
\tag{18}
\]
For completeness, the sums of the absolute values of the negative
coefficients with each fixed positive power of \(u\) are the following
three polynomials. Thus the term of degree \(m\) in \(R_i\) is
\(u^m\sum_{n:d_{imn}<0}|d_{imn}|\), omitting \(m=0\).
Their displayed form is also a direct way to check the negative part
of the coefficient expansion; no sign test is left implicit.

\[
R_0(u)=66 u^{10} + 955 u^{9} + \frac{27615 u^{8}}{2} + \frac{175360 u^{7}}{3} + \frac{495572 u^{6}}{3} + \frac{755768 u^{5}}{3} + \frac{2864665 u^{4}}{27} + \frac{2629504 u^{3}}{243} + \frac{107648 u^{2}}{243} + \frac{804280 u}{6561} .
\]

\[
R_1(u)=756 u^{11} + \frac{31955 u^{10}}{2} + \frac{546550 u^{9}}{3} + \frac{1615379 u^{8}}{2} + \frac{24692116 u^{7}}{9} + \frac{234503633 u^{6}}{54} + \frac{20388745 u^{5}}{9} + \frac{1053916 u^{3}}{243} + \frac{1975750 u^{2}}{729} + \frac{3742444 u}{6561} .
\]

\[
R_2(u)=3384 u^{11} + \frac{176451 u^{10}}{2} + 811615 u^{9} + 4355323 u^{8} + 11628256 u^{7} + \frac{43686979 u^{6}}{3} + \frac{78070060 u^{5}}{9} + \frac{449620 u^{3}}{81} + \frac{7000324 u^{2}}{2187} + \frac{4045108 u}{6561} .
\]

Substitution of \(u=1/6\) gives the small rational bounds
\[
R_0(1/6)=\frac{2024155555}{10077696}<201,
\]
\[
R_1(1/6)=\frac{7862531755}{13436928}<586,
\qquad
R_2(1/6)=\frac{68094787741}{40310784}<1690.
\tag{19}
\]
Combining (17)--(19), the three derivatives are respectively greater
than \(5705-201\), \(15034-586\), and \(72896/9-1690\).
All are positive, proving (13).

## 4. The base quadratic is positive

The three base polynomials in (14), in increasing-power form, are

\[
a_0(z)=- \frac{45152 z^{7}}{59049} + \frac{437189 z^{6}}{6561} + \frac{9424115 z^{5}}{19683} + \frac{7868156 z^{4}}{6561} - \frac{632434 z^{3}}{2187} - \frac{864913 z^{2}}{243} + \frac{19741 z}{9} + \frac{1514}{9} .
\]

\[
a_1(z)=- \frac{51824 z^{7}}{19683} + \frac{50122106 z^{6}}{177147} + \frac{51599650 z^{5}}{19683} + \frac{166227560 z^{4}}{19683} + \frac{7854788 z^{3}}{2187} - \frac{37970326 z^{2}}{2187} + \frac{689290 z}{243} + \frac{17812}{27} .
\]

\[
a_2(z)=- \frac{429568 z^{7}}{177147} + \frac{20583334 z^{6}}{59049} + \frac{24894044 z^{5}}{6561} + \frac{286749662 z^{4}}{19683} + \frac{3564514 z^{3}}{243} - \frac{30095420 z^{2}}{2187} + \frac{115918 z}{81} + \frac{14324}{9} .
\]

A particularly short sign argument for their discriminant is its
positive sum expansion
\[
\Delta(z)=\frac4{31381059609}
\sum_{m=0}^{14}d_mz^m(1-z)^{14-m},
\tag{20}
\]
where the coefficients are

| \(m\) | \(d_m\) | \(m\) | \(d_m\) | \(m\) | \(d_m\) |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 7788081465886716 | 5 | 60730972445626746336 | 10 | 5411896812314986176 |
| 1 | 235812193534894788 | 6 | 78015463740103117752 | 11 | 1848816854673942528 |
| 2 | 2270888689925466891 | 7 | 69668317358363112192 | 12 | 1619765580689088512 |
| 3 | 11035648754889615450 | 8 | 43547441542788954816 | 13 | 1001010298535772160 |
| 4 | 32108535751409315199 | 9 | 18695679419176727040 | 14 | 234477149301440512 |

Equation (20) is a polynomial identity: expand each \((1-z)^{14-m}\)
and use the three displayed \(a_i\). Every summand is nonnegative on
\([0,1]\); at either endpoint the surviving coefficient is positive,
and in the interior all summands are positive. Thus \(\Delta>0\).
It follows that \(a_0a_2>0\) everywhere. At \(z=0\),
\(a_0=1514/9>0\) and \(a_2=14324/9>0\). Neither polynomial can vanish
because their product is strictly positive. Continuity therefore gives
\(a_0>0,a_2>0\) on the entire interval. This proves (14).

## 5. The higher powers of \(j\) cannot change the sign

For \(i=3,\ldots,10\), expand
\[
C_i(1/3+u,z)=\sum_{m,n}c_{imn}u^mz^n,
\]
and set
\[
S_i(u)=\sum_{m,n:c_{imn}<0}|c_{imn}|u^m.
\tag{21}
\]
Unlike the derivative estimate, the index \(m=0\) is included here.
The following is the entire negative part, collected only by powers
of \(u\):

\[
S_3(u)=705 u^{14} + \frac{49777 u^{13}}{2} + 299653 u^{12} + \frac{17991542 u^{11}}{9} + \frac{191790206 u^{10}}{27} + \frac{48952703 u^{9}}{3} + \frac{1819632836 u^{8}}{81} + \frac{113827469 u^{7}}{9} + \frac{25098989 u^{4}}{19683} + \frac{59719102 u^{3}}{59049} + \frac{45671032 u^{2}}{177147} + \frac{16855280 u}{531441} + \frac{2524864}{1594323} .
\]

\[
S_4(u)=1470 u^{13} + 45293 u^{12} + 571656 u^{11} + \frac{57426557 u^{10}}{18} + \frac{592916371 u^{9}}{54} + \frac{131505655 u^{8}}{6} + \frac{3750175795 u^{7}}{162} + \frac{653217754 u^{6}}{81} + \frac{29632}{177147} .
\]

\[
S_5(u)=1932 u^{12} + 62493 u^{11} + 678389 u^{10} + \frac{64494793 u^{9}}{18} + \frac{62964409 u^{8}}{6} + \frac{162443486 u^{7}}{9} + \frac{874911391 u^{6}}{54} + \frac{128062691 u^{5}}{27} + \frac{2033 u^{3}}{3} + \frac{12196 u^{2}}{3} .
\]

\[
S_6(u)=1596 u^{11} + 56248 u^{10} + 540419 u^{9} + \frac{7668154 u^{8}}{3} + \frac{58054858 u^{7}}{9} + \frac{488685467 u^{6}}{54} + \frac{337465099 u^{5}}{54} + \frac{96917099 u^{4}}{54} + 165642 u^{3} + 6012 u^{2} .
\]

\[
S_7(u)=816 u^{10} + 33439 u^{9} + 291466 u^{8} + \frac{3423967 u^{7}}{3} + \frac{21388046 u^{6}}{9} + \frac{68935735 u^{5}}{27} + \frac{10528160 u^{4}}{9} + \frac{1511425 u^{3}}{6} + 17138 u^{2} + 256 u .
\]

\[
S_8(u)=237 u^{9} + \frac{25599 u^{8}}{2} + \frac{193611 u^{7}}{2} + \frac{917543 u^{6}}{3} + \frac{4264333 u^{5}}{9} + \frac{1019504 u^{4}}{3} + \frac{251140 u^{3}}{3} + 7976 u^{2} .
\]

\[
S_9(u)=30 u^{8} + 2898 u^{7} + \frac{52763 u^{6}}{3} + \frac{367538 u^{5}}{9} + \frac{122504 u^{4}}{3} + 15072 u^{3} + 972 u^{2} .
\]

\[
S_10(u)=300 u^{6} + 1260 u^{5} + 1720 u^{4} + 792 u^{3} .
\]

Every coefficient of every \(S_i\) is positive. At \(u=1/6\), their
values have these simple strict upper bounds:

| \(i\) | \(S_i(1/6)\) | upper bound \(b_i\) |
| ---: | ---: | ---: |
| 3 | \(\frac{87065188259}{1088391168}\) | 80 |
| 4 | \(\frac{12240024959}{45349632}\) | 270 |
| 5 | \(\frac{5125662803}{4478976}\) | 1145 |
| 6 | \(\frac{623504453}{186624}\) | 3341 |
| 7 | \(\frac{29941794263}{10077696}\) | 2972 |
| 8 | \(\frac{394364261}{419904}\) | 940 |
| 9 | \(\frac{37490453}{279936}\) | 134 |
| 10 | \(\frac{20071}{3888}\) | 6 |

The constant coefficients of \(C_i(1/3+u,z)\) for \(i=3,\ldots,10\)
are, respectively,
\[
\frac{370816}{81},\quad\frac{852352}{81},\quad
\frac{30656}{3},\quad\frac{38464}{9},\quad640,\quad0,\quad0,\quad0.
\]
In particular all are nonnegative. Keeping the first of these and
discarding the remaining nonnegative terms gives, for \(j>0\),
\[
\begin{aligned}
\frac1{j^3}\sum_{i=3}^{10}C_i(h,z)j^i
&\ge\frac{370816}{81}-\sum_{i=3}^{10}b_i j^{i-3}\\
&\ge\frac{370816}{81}-
\left(80+\frac{270}{2}+\frac{1145}{4}+\frac{3341}{8}
+\frac{2972}{16}+\frac{940}{32}+\frac{134}{64}+\frac6{128}\right)\\
&=\frac{370816}{81}-\frac{72713}{64}>0.
\end{aligned}
\tag{22}
\]
Here \(j\le h\le1/2\). At \(j=0\), the remainder is zero.
This proves (16), with a large margin: the retained positive constant
is greater than \(4500\), while the entire subtracted sum is less
than \(1200\).

## 6. Compact algebraic specification of all coefficient identities

This section makes the coefficient checks above self-contained without
printing the full expanded polynomial \(P\). Use \(k=1\), and put
\[
B=1+2tx+x^2,\quad Y=x(x+2),\quad J=t+Y,
\]
\[
H=tH_U=\widehat v-1+t^2+t^2(2-t),
\]
\[
M=tB^2w_U=t(1-t+t^2)+HY+t\widehat vY^2,
\qquad E_0=q^2B+W^2-2pqW.
\]
In the following formula, \(\widehat v,L\) are exactly (3)--(4):
\[
\begin{aligned}
N={}&tBqWc+tq^2B^2-tBqp^2-tp^2W^2+tqWp^3\\
 &-tBqWpL-tBqW^2\widehat v-q^2M+qWp(H+2t\widehat vY).
\end{aligned}
\tag{23}
\]
Then the single compact polynomial specification is
\[
\begin{aligned}
P=48(q+1)WR\bigl[&4q(7W^2-Jq^2)N\\
&+(qJ-pW)\{3tE_0^2-4t\widehat vW^4
 +4q^2W^2(H+2t\widehat vY)-4q^4M\}\bigr],
\end{aligned}
\tag{24}
\]
followed by \(t=(1-h)/2,x=h+j,q=1+hz\).
The bracket is \(4qW^2F\), by the exact residual/transport identity,
so (24) agrees with (10).

For a direct check of any number above, multiply the rational
expressions in (24); its factors \(48(q+1)WR\) cancel all denominators.
Collect powers of \(j\) to obtain \(C_i\), and divide the first three
by the displayed factors in (12). Substitution of \(h=1/3\) yields
Section 4; differentiation and substitution of \(h=1/3+u\) yields
Section 3; the remaining \(j\)-coefficients yield Section 5.
For an ordinary polynomial \(f(z)=\sum_{r=0}^nf_rz^r\), the coefficient
of \(z^m(1-z)^{n-m}\) in its positive-basis expansion is exactly
\[
\sum_{r=0}^m\binom{n-r}{m-r}f_r.
\tag{25}
\]
This follows at once by inserting
\(z^r=z^r(z+(1-z))^{n-r}\), and specifies the coefficient convention
in both tables. Thus the signs use only explicit polynomial identities,
the elementary inequalities (17) and (22), and the quadratic
criterion (15).

## 7. Actual-boundary conclusion

The hypothetical low-ratio point forced the strict negative scalar
comparison (8). The proved positive polynomial sign gives the opposite
strict sign at those same \((t,x,q)\) after the allowed lowering of
\(k\). The contradiction establishes \(t>1/3\) for the actual eligible
forward-successor boundary alternative. All incoming floors and next
norm assumptions were used at their original actual coordinates before
this purely scalar comparison. The common costate and twisted seam
remain the ones in the accepted boundary reduction.
