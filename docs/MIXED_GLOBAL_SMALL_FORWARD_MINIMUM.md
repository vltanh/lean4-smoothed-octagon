# A small forward minimum cannot occur in a normal period

Date: 2026-11-07 UTC. Hand inequalities with a supplementary exact
certificate. No Lean, Lake, typechecking, or CI.

## Statement and scope

Consider an actual finite normal closed period in the state-closed
active-margin coordinates of
[MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md). Suppose five consecutive active
margins are `(p,b,a,c,d)` and the four switches between them are forward.
The three interior indices are distinct. The coordinates and the common
normal multiplier use the actual twisted seam; a local prefix-frame
change conjugates that same multiplier. Assume

\[
0<a\le\min(p,b,c,d),\qquad a^2\le\frac43.
\tag{1}
\]

Then the normal PMP conditions are incompatible with positive durations
of the three interior arcs. The argument uses the same actual primary
multiplier throughout. It uses neither endpoint-rank inversion nor an
implicit-function assertion, and it does not need a Casimir bound.

For the remaining pure-forward problem the active indices satisfy the
stated distinctness condition. For a mixed period, the already proved
minimum structure places a global minimum either at four consecutive
forward switches or at a strict reverse centre. Since every mixed period
has some reverse centre with active square below `4/3`, the theorem
forces every mixed global minimum to occur at a reverse centre. This
necessary whole-period statement does not by itself close M2.

## 1. The common normal stationarity equations

Put

\[
K=a^2+4,\quad K_b=b^2+4,\quad K_c=c^2+4,
\quad s=a+b,\quad t=a+c,
\]
\[
h=\frac{(p+b)s}{K_b},\qquad
q=\frac{st}{K},\qquad
k=\frac{t(c+d)}{K_c}.
\tag{2}
\]

All three factors exceed one. The strict-star state inequalities give
`ab<4`, `ac<4`, and also `pb<4`, `cd<4` at the two
exterior switches. Substituting (2) in those last two inequalities gives

\[
h<\frac{a+b}{b},\qquad k<\frac{a+c}{c}.
\tag{2a}
\]

The exterior minimum conditions give

\[
h\ge\max\left(1,\frac{s^2}{K_b}\right),\qquad
k\ge\max\left(1,\frac{t^2}{K_c}\right),
\tag{3}
\]

where `h,k>1` are still strict. Define

\[
\begin{aligned}
A={}&b+a+c-a^2(s^{-1}+t^{-1})+a^3/K-a\log q,\\
B={}&hK_b/s+a-b^2\left(s/(hK_b)+s^{-1}\right)
       +b^3/K_b-b\log h,\\
C={}&a+kK_c/t-c^2\left(t^{-1}+t/(kK_c)\right)
       +c^3/K_c-c\log k.
\end{aligned}
\tag{4}
\]

These are four times the three corresponding derivatives of the common
normalized cyclic action. Use the central arc's prefix frame, and write
the actual normalized primary multiplier as

\[
U_a=\begin{pmatrix}
KE/16&-s^2u/8\\ K^2v/(8s^2)&-KE/16
\end{pmatrix}.
\tag{5}
\]

Here `u,v,E` are real coordinates; no positive-definiteness assumption
is needed in this proof. The established normal stationarity identity
is `tr(U_i W_i)=partial_i J`. In particular,

\[
su+tv-aE=A.
\tag{6}
\]

The other two identities, after eliminating `E` using (6), read

\[
M_{11}u+M_{12}v=R_L,\qquad
M_{21}u+M_{22}v=R_R,
\tag{7}
\]

where

\[
\begin{aligned}
M_{11}&=\frac{s^2(4-ab)(h-1)}{aK_b},\\
M_{12}&=\frac{K^2\{a(q-1)+(h-1)(sq-a)\}}{asK_b},\\
R_L&=\frac{K(hs-b)}{aK_b}A-B.
\end{aligned}
\tag{8}
\]

The right row is obtained by exchanging `(b,h,s,u)` with `(c,k,t,v)`.
Every coefficient `M_ij` is positive. We will use only one row after
choosing the smaller of `b,c`; thus no division by `det M` is involved.

For a direct check of the common-covector interface, let

\[
T(z)=\operatorname{diag}(z,z^{-1}),\qquad
R=\begin{pmatrix}1&-1\\1&0\end{pmatrix},\qquad
U_b=T(h)R U_a R^{-1}T(h)^{-1},
\]
\[
W_b=2\begin{pmatrix}-b/K_b&h^2/s\\-s/(hK_b)&b/K_b\end{pmatrix}.
\]

With `H_a=su+tv-aE-A` and `H_b=4 tr(U_b W_b)-B`, direct matrix
multiplication gives

\[
H_b+(M_{11}u+M_{12}v-R_L)
=\frac{K(hs-b)}{aK_b}H_a.
\tag{9}
\]

Thus (7) is an identity for the actual same-lift stationarity equations,
not a choice of an independently fitted edge multiplier.

## 2. The two genuine exterior switches supply stronger floors

For `1/2<=x<1` and `z>1`, define

\[
F_x(z)=1+x^2z-\frac{xz\log z}{z-1},\qquad
F_x(1)=1-x+x^2.
\tag{10}
\]

The two missing-control inequalities at the actual exterior switches
imply

\[
u\ge F_{b/s}(h),\qquad v\ge F_{c/t}(k).
\tag{11}
\]

For example, put `s_0=p+b=hK_b/s`. Rotate the new control at this
forward switch to label 0. In the first interior arc's frame define

\[
G_L=4b s_0(U_b)_{11}+2K_b(U_b)_{12}
 -2s_0^2(U_b)_{21}+p s_0+K_b.
\]

The two incident maximizing Hamiltonians vanish. Solving those two
ties in the common normal normalization gives the missing Hamiltonian

\[
H_1=-\frac{4\sqrt3}{(p+b)(4-pb)}G_L.
\tag{11a}
\]

The denominator is positive by the actual exterior strict-star
inequality, so PMP gives `G_L>=0`. The exact identity

\[
G_L=-\frac{hK_b^2}{4s}H_b
 +\frac{K_b^2(h-1)}4\{u-F_{b/s}(h)\}
\tag{12}
\]

proves the first floor, since `H_b=0`. The reflected matrix identity
proves the second. This calculation retains equality at a missing-control
triple tie; strictness of an inactive gap is not assumed.

The elementary derivative formulas are

\[
\partial_z F_x=x^2-x\frac{z-1-\log z}{(z-1)^2}>0,
\qquad
\partial_x F_x=z\left(2x-\frac{\log z}{z-1}\right)>0.
\tag{13}
\]

Indeed, `log z<z-1` and
`z-1-log z<(z-1)^2/2`, the latter by differentiation from `z=1`.
The strict inequalities hold also at `x=1/2,z>1`.

Define the minimum-aware opposite floor

\[
V(a,c)=F_{c/(a+c)}\left(\max\left\{1,
\frac{(a+c)^2}{c^2+4}\right\}\right).
\tag{14}
\]

It is continuous and nondecreasing in `c>=a` on `ac<4`. To see this,
the ratio `c/(a+c)` increases, and the nonconstant factor in (14) has
positive derivative

\[
\frac{d}{dc}\frac{(a+c)^2}{c^2+4}
=\frac{2(a+c)(4-ac)}{(c^2+4)^2}>0.
\]

Also `V(a,c)>=U(a/(a+c))`, where `U(r)=1-r+r^2`.
By (3), (11), and positivity of the first row of (7), necessarily

\[
\mathcal E(a,b,c,h):=
R_L-M_{11}F_{b/s}(h)-M_{12}V(a,c)\ge0.
\tag{15}
\]

## 3. Reduce the larger neighboring margin

Exchange the two reflected scalar rows if necessary, so that `b<=c`.
No new trajectory or new multiplier is introduced. Put

\[
\alpha=\frac{K(hs-b)}{aK_b},\qquad
\beta=\frac{K^2h}{sK_b}.
\]

Then `R_L=alpha A-B`, `M12=alpha(a+c)-beta`, and
`partial_c A=U(a/(a+c))`. At every differentiability point of `V`,

\[
\partial_c\mathcal E
=\alpha\{U(a/(a+c))-V(a,c)\}-M_{12}\partial_cV\le0.
\tag{16}
\]

Continuity handles the single transition in the max in (14). Decrease
`c` until either `c=b` or `q=1`. The same strict-star bound remains valid,
`h` and its minimum restriction are unchanged, and `M12` remains
positive, including at `q=1` because `h>1`. This is a scalar comparison,
not a deformation through PMP trajectories. It proves that the original
residual is no larger than its value on one of the following faces:

1. `q=1`, with `(a+b)^2<=K` and `c=K/(a+b)-a>=b`;
2. `c=b`, with `(a+b)^2>=K`.

It remains to show a strictly negative residual on these faces.

## 4. The zero-central-factor comparison face

On `q=1`, one has

\[
\frac{(a+c)^2}{K_c}\le1,
\]

because the numerator of its difference from one is
`K(a-b)/(a+b)<=0`. Therefore `V=U`, and direct substitution gives

\[
\mathcal E(1)=\mathcal E_h(1)=0.
\tag{17}
\]

For either boundary face, with the opposite floor held fixed, the
second derivative with respect to `h` is

\[
\mathcal E_{hh}
=-\frac{b\,P(h)}{aK_bh^3},
\quad
P(h)=(4-ab)h^2(2bh-a-b)+aK_bh-2ab(a+b).
\tag{18}
\]

Moreover

\[
P'(h)=2(4-ab)h(3bh-a-b)+aK_b>0\qquad(h\ge1),
\]
\[
P(1)=b(4-a^2-2ab)\ge b(b^2-a^2)\ge0,
\]

where `(a+b)^2<=K` and `b>=a` give the last line. Hence
`mathcal E_hh<0` for `h>1`. Together with (17), this proves
`mathcal E(h)<0` at every actual positive factor.

## 5. Equal neighboring margins when the exterior minimum factor is one

Now let `c=b`, `s=a+b`, `q=s^2/K>=1`, and suppose
`H=s^2/Kb<=1`. Write `r=a/s<=1/2`, and put

\[
F(q)=r(q-1)+(1-r)(1-q^{-1})-\log q.
\]

Direct differentiation gives

\[
F'(q)=\frac{(q-1)\{rq-(1-r)\}}{q^2}.
\tag{19}
\]

The restriction `H<=1` is `a^2+2ab<=4`, and implies
`q<=1/(2r)<=(1-r)/r`. Thus `F(q)<=0`, strictly when `q>1`.
The exact initial residual and slope are

\[
\mathcal E(1)=\frac{aK}{K_b}F(q),
\]
\[
\mathcal E_h(1)=\frac{sK}{K_b}
\left[F(q)+\frac{(1-r)(q-1)\{rq-(1-r)\}}q\right]\le0.
\tag{20}
\]

Here `P(1)>=0`, so (18) is strictly negative for `h>1`. This gives
`mathcal E(h)<0`, also in the possible `q=1` equality case.

## 6. The hard symmetric face: a finite exact sign certificate

Let \(0<a\le b\), \(a^2\le4/3\), and \(ab<4\). This subsection covers
the remaining symmetric face

\[
H=\frac{(a+b)^2}{b^2+4}>1,
\qquad H\le h<\frac{a+b}{b}.
\]

Both exterior switching conditions are retained: the opposite norm floor
is \(F_x(H)\), not merely its limiting value at \(H=1\). No monotonicity
in \(h\) is asserted or needed.

Set

\[
u=\frac4{a^2},\quad z=\frac ba,\quad
t=\frac1{1+z},\quad x=\frac z{1+z},\quad
q=\frac{(1+z)^2}{1+u},\quad H=\frac{(1+z)^2}{u+z^2}.
\]

The full domain is

\[
u\ge3,\qquad \frac{u-1}{2}<z<u,
\qquad H\le h<\frac{1+z}{z}.
\tag{H1}
\]

Define

\[
\begin{aligned}
\widetilde A&=2-t-2t^2+t^3q-t\log q,\\
\widetilde B&=h/H+t-x^2H/h-x^2+x^3H-x\log h,\\
F_x(v)&=1+x^2v-\frac{xv}{v-1}\log v.
\end{aligned}
\]

The original residual divided by the positive number \(a+b\),
\(\mathscr E=\mathcal E/(a+b)\), is

\[
\begin{aligned}
\mathscr E={}&\frac{H(h-x)}{tq}\widetilde A-\widetilde B
 -\frac{H(1-tq)(h-1)}{tq}F_x(h)\\
&-\frac{H[t(q-1)+(h-1)(q-t)]}{tq^2}F_x(H).
\end{aligned}
\tag{H2}
\]

We prove \(\mathscr E<0\) throughout (H1), including \(a^2=4/3\) and
\(h=H\).

### Rational bounds for the three logarithms

For \(v\ge1\), put \(w=(v-1)/(v+1)\) and define

\[
L(v)=2w+\frac23w^3,
\qquad U(v)=2w+\frac{2w^3}{3(1-w^2)}.
\]

Then \(L(v)\le\log v\le U(v)\). Indeed, both comparisons are equality
at \(v=1\), and

\[
\frac1v-L'(v)=\frac{(v-1)^4}{v(v+1)^4}\ge0,
\qquad U'(v)-\frac1v=\frac{(v-1)^4}{6v^2(v+1)^2}\ge0.
\tag{H3}
\]

In (H2), the coefficient of \(\log q\) is negative. The coefficient of
\(\log h\) is positive because \(1-tq>0\), and the coefficient of
\(\log H\) is positive because \(q>1\), \(h>1\), and \(q>t\).
Thus the replacements

\[
\log q\mapsto L(q),\qquad
\log h\mapsto U(h),\qquad
\log H\mapsto U(H)
\]

give a rational upper bound \(\widehat{\mathscr E}\) for \(\mathscr E\).

### A polynomial identity on the whole domain

The positive denominator

\[
\mathcal D(u,z,h)=6h(h+1)(u+z^2)^2(z+1)^3
 (u+z^2+2z+2)^3(u+2z^2+2z+1)
\]

clears this rational upper bound. Let \(N=\mathcal D\widehat{\mathscr E}\).
This is a polynomial of degrees \((7,15,4)\) in \((u,z,h)\).

Parameterize the entire domain (H1) by

\[
u=3+Y,\qquad
z=\frac{(2+Y)+(6+2Y)R}{2(1+R)},\qquad
h=\frac{H+T(1+z)/z}{1+T},
\quad Y\ge0,\quad R>0,\quad T\ge0.
\tag{H4}
\]

The inverse formulas are

\[
R=\frac{2z+1-u}{2(u-z)}>0,
\qquad T=\frac{h-H}{(1+z)/z-h}\ge0.
\]

For clarity about denominator clearing, put

\[
h_n=(1+z)^2z+T(1+z)(z^2+u),\qquad
h_d=z(z^2+u)(1+T)>0,
\]

so that \(h=h_n/h_d\). Define the polynomial

\[
N_h(u,z,T)=h_d^4N(u,z,h_n/h_d).
\]

It has degree twenty-five in \(z\). Use the following short positive
polynomials:

\[
\begin{aligned}
\mathcal A&=2RY+6R+Y+2,\\
\mathcal B&=4R^2Y+12R^2+4RY+12R+Y+4,\\
\mathcal C&=4R^2Y+14R^2+4RY+14R+Y+4.
\end{aligned}
\]

The exact finite identity is

\[
\begin{aligned}
&[2(1+R)]^{25}
N_h\!\left(3+Y,\frac{(2+Y)+(6+2Y)R}{2(1+R)},T\right)\\
&\quad=-8(2R+1)^2(Y+4)^{12}\Bigl[
\mathcal A^4\mathcal B\mathcal C Q_0
+T\mathcal A^3\mathcal B Q_1
+T^2\mathcal A^2\mathcal B^2Q_2\\
&\hspace{49mm}
+T^3\mathcal A\mathcal B^3Q_3
+T^4\mathcal A\mathcal B^4Q_4\Bigr].
\end{aligned}
\tag{H5}
\]

The five polynomials \(Q_j(Y,R)\) are specified completely by the tables
below. For each table row, multiply the listed polynomial in \(Y\) by
the row factor and by the indicated power of \(R\), then sum the rows.
All entries are exact integers. Their nonzero coefficients are positive.
The polynomial \(Q_0\) contains \(1966080R^3\), so the first term in
brackets in (H5) is strictly positive even when \(Y=T=0\).
All other bracketed terms are nonnegative. Every denominator cleared in
(H5) is positive, proving \(\widehat{\mathscr E}<0\), hence
\(\mathscr E<0\), on the whole domain (H1).

Identity (H5) is a finite polynomial identity: multiply the displayed
rational expressions (H2) after (H3), clear the displayed denominators,
and collect powers. The full coefficient tables are part of the hand
certificate; a coefficient count alone is not used as proof.
The supplementary exact checker verifies the normalization, all three
logarithm signs, the domain changes, and (H5) against these fixed tables.

### Coefficients of Q_0

| R power | row factor | Y^0 | Y^1 | Y^2 | Y^3 | Y^4 | Y^5 | Y^6 | Y^7 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 1 | 0 | 0 | 0 | 4096 | 3328 | 1008 | 136 | 7 |
| 1 | 2 | 0 | 0 | 61440 | 112128 | 66368 | 17796 | 2265 | 113 |
| 2 | 2 | 0 | 507904 | 2002944 | 2307072 | 1148288 | 283468 | 34543 | 1681 |
| 3 | 4 | 491520 | 6033408 | 14275072 | 13136192 | 5851240 | 1360984 | 160409 | 7651 |
| 4 | 4 | 9601024 | 65564672 | 120309760 | 96501696 | 39790248 | 8852126 | 1016467 | 47696 |
| 5 | 8 | 42868736 | 215851008 | 338471808 | 247301440 | 96370908 | 20718879 | 2330279 | 107888 |
| 6 | 16 | 115601408 | 480402432 | 676590656 | 462188624 | 172591616 | 36125985 | 3995975 | 182974 |
| 7 | 32 | 209413120 | 762946432 | 994406848 | 646025016 | 233439695 | 47837898 | 5220507 | 236874 |
| 8 | 128 | 133984256 | 444304320 | 546727784 | 341871894 | 120411761 | 24262836 | 2618943 | 117942 |
| 9 | 256 | 123841728 | 383563352 | 452095826 | 274570008 | 94799928 | 18848637 | 2016677 | 90266 |
| 10 | 512 | 82961632 | 244710444 | 279439433 | 166039412 | 56464287 | 11111151 | 1180638 | 52591 |
| 11 | 1024 | 39711672 | 113410668 | 126715789 | 74142885 | 24941037 | 4871368 | 515020 | 22861 |
| 12 | 1024 | 26195752 | 73632570 | 81305115 | 47154964 | 15761334 | 3064802 | 323071 | 14312 |
| 13 | 2048 | 5532764 | 15631669 | 17269597 | 10007932 | 3341972 | 649439 | 68443 | 3032 |
| 14 | 4096 | 641328 | 1890821 | 2132191 | 1249912 | 420418 | 82113 | 8687 | 386 |
| 15 | 8192 | 26829 | 91866 | 110657 | 67266 | 23143 | 4590 | 491 | 22 |

### Coefficients of Q_1

| R power | row factor | Y^0 | Y^1 | Y^2 | Y^3 | Y^4 | Y^5 | Y^6 | Y^7 | Y^8 | Y^9 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 1 | 0 | 0 | 196608 | 565248 | 555008 | 272320 | 75344 | 12020 | 1039 | 38 |
| 1 | 1 | 0 | 2359296 | 16515072 | 30097408 | 24749056 | 11116384 | 2929376 | 454510 | 38671 | 1402 |
| 2 | 2 | 2097152 | 61931520 | 236412928 | 339926016 | 248509312 | 104555968 | 26518272 | 4022434 | 337773 | 12155 |
| 3 | 2 | 102236160 | 1278509056 | 3626479616 | 4495882752 | 3023371392 | 1210018224 | 297653344 | 44318333 | 3680825 | 131618 |
| 4 | 4 | 912326656 | 7520051200 | 17787894784 | 19913354880 | 12584499712 | 4843279016 | 1162243282 | 170402661 | 14022126 | 498670 |
| 5 | 4 | 9121300480 | 58480410624 | 122240700416 | 127026416896 | 76533102112 | 28548906896 | 6713068848 | 971630691 | 79326834 | 2807812 |
| 6 | 8 | 29964419072 | 162387701760 | 310336569088 | 304759196032 | 176842914432 | 64319051192 | 14871623071 | 2129197067 | 172665844 | 6086444 |
| 7 | 16 | 70056484864 | 336864277504 | 601670356480 | 565353557120 | 318319694512 | 113397797656 | 25852967771 | 3667358225 | 295674314 | 10384660 |
| 8 | 32 | 121913436160 | 536563261696 | 909398938368 | 825030604608 | 453292523924 | 158730253249 | 35761656132 | 5032959107 | 403718172 | 14133548 |
| 9 | 64 | 162058930176 | 666909552000 | 1084540829568 | 956482489672 | 515068013326 | 177798739319 | 39657717240 | 5543367324 | 442681954 | 15452580 |
| 10 | 128 | 166839799552 | 651977017216 | 1025961611136 | 884308134176 | 468392999795 | 159763999135 | 35332841918 | 4909848922 | 390550732 | 13597012 |
| 11 | 256 | 133637830912 | 501802267936 | 769286215376 | 650887388330 | 340108558139 | 114857319293 | 25219054122 | 3486710764 | 276388086 | 9599564 |
| 12 | 512 | 82976894080 | 302272783632 | 454037175724 | 378526552395 | 195632163784 | 65528199841 | 14301675776 | 1968798352 | 155594452 | 5392660 |
| 13 | 1024 | 39433581280 | 140545523632 | 207923351136 | 171401455896 | 87831347500 | 29229726775 | 6348623012 | 870874491 | 68651094 | 2374988 |
| 14 | 2048 | 13998133952 | 49221663328 | 72096483274 | 58976918088 | 30040142847 | 9950457577 | 2153490351 | 294617727 | 23179452 | 800740 |
| 15 | 4096 | 3558270528 | 12464227516 | 18185975328 | 14823787436 | 7527296147 | 2486948119 | 537128947 | 73369241 | 5765710 | 199004 |
| 16 | 8192 | 601287204 | 2127310366 | 3117844074 | 2546595505 | 1294221446 | 427722682 | 92384480 | 12619187 | 991676 | 34228 |
| 17 | 32768 | 29197503 | 106981911 | 159737418 | 131912781 | 67509660 | 22415611 | 4857534 | 665119 | 52365 | 1810 |
| 18 | 131072 | 563409 | 2277963 | 3571713 | 3034859 | 1581775 | 531781 | 116267 | 16025 | 1268 | 44 |

### Coefficients of Q_2

| R power | row factor | Y^0 | Y^1 | Y^2 | Y^3 | Y^4 | Y^5 | Y^6 | Y^7 | Y^8 | Y^9 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 1 | 0 | 0 | 442368 | 1083392 | 1015040 | 492768 | 136880 | 22070 | 1935 | 72 |
| 1 | 3 | 524288 | 2883584 | 11018240 | 17486848 | 13820928 | 6163280 | 1633788 | 256506 | 22151 | 817 |
| 2 | 2 | 23592960 | 147046400 | 408803328 | 535852800 | 381009056 | 159783152 | 40829186 | 6270939 | 534561 | 19563 |
| 3 | 2 | 375521280 | 2319679488 | 5492862976 | 6415995392 | 4238949472 | 1696752056 | 420968618 | 63479511 | 5350998 | 194466 |
| 4 | 4 | 1949794304 | 11232796672 | 23880942080 | 25753210112 | 16111955968 | 6217665872 | 1505820207 | 223564881 | 18662199 | 673974 |
| 5 | 4 | 14126317568 | 74701230080 | 146491484160 | 148820296448 | 89250149552 | 33442612660 | 7938248398 | 1162982361 | 96248772 | 3456180 |
| 6 | 32 | 9286215680 | 45230442752 | 83227805760 | 80690954352 | 46781576900 | 17110471513 | 3993315913 | 578334095 | 47498010 | 1696695 |
| 7 | 16 | 72915263488 | 330349184000 | 577358642176 | 539080397440 | 304009009016 | 108970882477 | 25067510793 | 3594052557 | 293152596 | 10421268 |
| 8 | 32 | 108925047808 | 464101335808 | 777569014080 | 703937497408 | 387963776398 | 136715801847 | 31061396400 | 4414097604 | 357804282 | 12662364 |
| 9 | 128 | 62621976576 | 253528327072 | 410218045000 | 361988846108 | 195701655876 | 67972212907 | 15277635857 | 2154082412 | 173620458 | 6118398 |
| 10 | 128 | 111286689920 | 432098410624 | 679371045560 | 586894539860 | 312204782281 | 107106036365 | 23849399136 | 3339263052 | 267756324 | 9398532 |
| 11 | 512 | 38074360992 | 142969880840 | 219606536846 | 186426307313 | 97843415522 | 33217085764 | 7336981165 | 1020963672 | 81481242 | 2849574 |
| 12 | 512 | 39639078208 | 145089189872 | 218825885962 | 183185014391 | 95092261956 | 32003886545 | 7020781246 | 971743026 | 77228610 | 2691780 |
| 13 | 1024 | 15329660912 | 55140090172 | 82079480264 | 67999502939 | 35002744990 | 11700026900 | 2552492694 | 351719457 | 27852636 | 967932 |
| 14 | 2048 | 4225806000 | 15080440332 | 22288982267 | 18349617545 | 9393810045 | 3125239255 | 679098820 | 93265212 | 7365168 | 255348 |
| 15 | 4096 | 771669432 | 2769330075 | 4097509279 | 3370589797 | 1722762940 | 572076159 | 124075633 | 17010101 | 1341132 | 46428 |
| 16 | 49152 | 13475979 | 49825554 | 74811226 | 62025068 | 31840544 | 10598856 | 2301734 | 315756 | 24901 | 862 |
| 17 | 98304 | 563409 | 2277963 | 3571713 | 3034859 | 1581775 | 531781 | 116267 | 16025 | 1268 | 44 |

### Coefficients of Q_3

| R power | row factor | Y^0 | Y^1 | Y^2 | Y^3 | Y^4 | Y^5 | Y^6 | Y^7 | Y^8 | Y^9 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 2 | 262144 | 589824 | 708608 | 658944 | 445056 | 194928 | 52864 | 8565 | 763 | 29 |
| 1 | 1 | 14548992 | 35897344 | 49588224 | 48436992 | 31783680 | 13326512 | 3490128 | 552272 | 48467 | 1824 |
| 2 | 1 | 189595648 | 533651456 | 821244928 | 816488064 | 520070624 | 210326904 | 53513816 | 8299152 | 718761 | 26806 |
| 3 | 4 | 396886016 | 1284214784 | 2117427712 | 2100686208 | 1299889176 | 509875412 | 126600166 | 19294880 | 1651462 | 61079 |
| 4 | 2 | 4877402112 | 17737367552 | 30254511872 | 29609786752 | 17828362352 | 6811466536 | 1656197732 | 248599139 | 21052602 | 772616 |
| 5 | 8 | 5855473664 | 22995355136 | 39537965056 | 37945254560 | 22275068496 | 8317346206 | 1985820271 | 294077799 | 24663887 | 898612 |
| 6 | 8 | 22485710848 | 91556007680 | 156080998912 | 146519353056 | 84032948148 | 30750173871 | 7224981140 | 1057083493 | 87870728 | 3179748 |
| 7 | 16 | 34573492224 | 141510243840 | 237006233216 | 217529964816 | 122145112566 | 43904370017 | 10169790490 | 1471787546 | 121340054 | 4362644 |
| 8 | 32 | 42254445824 | 170596730240 | 279557311840 | 251071532376 | 138307880813 | 48929902141 | 11190590566 | 1603542402 | 131193876 | 4688112 |
| 9 | 64 | 40617906176 | 160287609344 | 256775526832 | 226007998512 | 122387131415 | 42690003785 | 9652853994 | 1370756796 | 111351064 | 3955952 |
| 10 | 128 | 30309873216 | 116614813936 | 182838832744 | 158040430825 | 84296353428 | 29038628145 | 6499594402 | 915431018 | 73872194 | 2610036 |
| 11 | 256 | 17245988896 | 64801759392 | 99692721088 | 84830471637 | 44659938468 | 15218373357 | 3375829506 | 471970980 | 37855332 | 1330628 |
| 12 | 512 | 7284098928 | 26856222096 | 40689848599 | 34184546518 | 17803765113 | 6011765759 | 1323359858 | 183826967 | 14664082 | 513032 |
| 13 | 1024 | 2187993264 | 7976454236 | 11962849047 | 9959455663 | 5145507399 | 1725270643 | 377458192 | 52154582 | 4141278 | 144296 |
| 14 | 2048 | 434310612 | 1584872756 | 2370720608 | 1965959335 | 1011324198 | 337641304 | 73570482 | 10127457 | 801412 | 27836 |
| 15 | 8192 | 24706413 | 92320305 | 139507486 | 116187491 | 59852516 | 19979813 | 4349402 | 597905 | 47239 | 1638 |
| 16 | 32768 | 563409 | 2277963 | 3571713 | 3034859 | 1581775 | 531781 | 116267 | 16025 | 1268 | 44 |

### Coefficients of Q_4

| R power | row factor | Y^0 | Y^1 | Y^2 | Y^3 | Y^4 | Y^5 | Y^6 | Y^7 | Y^8 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 0 | 1 | 196608 | 360448 | 301056 | 173568 | 75312 | 22328 | 4059 | 404 | 17 |
| 1 | 1 | 4161536 | 7905280 | 7343104 | 4690688 | 2115992 | 624998 | 112028 | 11015 | 459 |
| 2 | 1 | 40435712 | 82976768 | 86620160 | 59873024 | 27567632 | 8076726 | 1428193 | 138853 | 5734 |
| 3 | 2 | 121946112 | 280031232 | 326068736 | 237594496 | 110158436 | 31927943 | 5572935 | 536179 | 21956 |
| 4 | 2 | 522403840 | 1367136256 | 1735699968 | 1302336928 | 602429436 | 172484969 | 29737207 | 2833206 | 115104 |
| 5 | 4 | 860123136 | 2546169856 | 3421107136 | 2595626752 | 1190938540 | 336639809 | 57363090 | 5415254 | 218372 |
| 6 | 8 | 1136367616 | 3689985536 | 5101643872 | 3865446072 | 1753319453 | 489280357 | 82457657 | 7717140 | 309012 |
| 7 | 16 | 1217224704 | 4165602560 | 5801304448 | 4356513172 | 1950450779 | 537548593 | 89659180 | 8322972 | 331056 |
| 8 | 32 | 1041396864 | 3628790304 | 5022942144 | 3724043228 | 1645152273 | 448098711 | 74024006 | 6819276 | 269544 |
| 9 | 64 | 690905056 | 2398259560 | 3277467680 | 2396158079 | 1045102670 | 281598255 | 46111444 | 4217992 | 165748 |
| 10 | 128 | 342035200 | 1171557148 | 1578122630 | 1138602253 | 490970008 | 131034115 | 21289948 | 1935122 | 75636 |
| 11 | 256 | 120087224 | 406080510 | 540406051 | 385725823 | 164793751 | 43639365 | 7044390 | 636830 | 24776 |
| 12 | 512 | 27661164 | 93224731 | 123329868 | 87476775 | 37151209 | 9785756 | 1572299 | 141566 | 5488 |
| 13 | 2048 | 1809138 | 6215872 | 8275189 | 5878227 | 2495046 | 656250 | 105253 | 9459 | 366 |
| 14 | 2048 | 187803 | 696720 | 958331 | 692176 | 296533 | 78416 | 12617 | 1136 | 44 |


## 7. Whole-period consequences

Every comparison face now has a negative upper residual, contradicting
(15). This proves the theorem, including every equality in (1) and
weak missing-control tie in (11). The positive factors remain strict,
as required for the actual three complete arcs.

For a pure-forward competitive period beyond the retained through-five
cases, a global minimum `m` must therefore satisfy `m^2>4/3`. For a
mixed period, the presence of a reverse centre gives `m^2<4/3`; its
minimum cannot be a forward site. The existing
[MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md)
theorem then forces it to be a strict reverse centre.

This conclusion does not assert that the global minimum borders a long
forward run. A reverse minimum may lie inside a chain of short bridges;
that propagation issue is a separate remaining M2 obligation.

## Exact verification and independent audit

The supplementary exact interface checker is
[mixed_global_small_forward_minimum_certificate.py](../explorations/mixed_global_small_forward_minimum_certificate.py).
Its 28 identities cover the actual common-covector stationarity,
both genuine exterior needle floors, both easy comparison faces,
and the normalization of the full hard face.

The complete hard-face polynomial identity and the fixed integer tables
are checked by
[global_structure_forward_small_minimum_certificate.py](../explorations/global_structure_forward_small_minimum_certificate.py).
Its 199 exact identities and integer sign checks pass.
The displayed coefficient tables are part of the proof; no numerical
sampling or unlisted positivity oracle is used. The scalar comparisons,
actual PMP normalization, and whole-period application are established
in the prose above.

See [MIXED_GLOBAL_SMALL_FORWARD_MINIMUM_AUDIT](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM_AUDIT.md)
for the independent audit of the physical signs, domain reductions,
and the full fixed-table polynomial identity.
