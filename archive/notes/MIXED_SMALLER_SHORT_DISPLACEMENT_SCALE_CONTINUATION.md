# Increasing the displacement-weighted residual along the tau-two face

Date: 2026-11-08 UTC. This is a hand proof of the scale-continuation
step for the displacement-adapted weight. It uses four explicitly
displayed polynomials, with their signs obtained by termwise
domination. It does not assume the terminal displacement boundary
signs.

Use the notation of
[the displacement weight reduction](MIXED_SMALLER_SHORT_DISPLACEMENT_WEIGHT_REDUCTION.md).
In particular, retain the original incoming norm while making this
scale comparison. The domain needed here is

\[
\frac{11}{10}\le a:=\alpha\le\frac{13}{6},\quad
3\le S:=1+x\le\frac{19}{6},\quad
\frac13\le p:=r_A\le\frac{a}{a+2},\quad
\frac34\le u\le\frac{19}{25},\quad
0<\Delta:=\frac D{a^2}<3.
\tag{1}
\]

The actual candidate excluded shape has these properties: the weight
reduction proves all of them except the displayed upper bound on
\(p\), which follows immediately from \(\beta\ge x\ge2\).
The letters \(p\) and \(S\) in this note are fixed geometric
parameters; the variable being increased is \(q\).

## 1. The exact derivative and its four coefficients

Put

\[
k=5a-1,\quad M=16/k,\quad N=24/(kp).
\]

At \(\tau=2\), the weight is \(m=M-Nq\), and the normalized
identities give

\[
q(G_2^*)'(q)=1-K_1q+K_2q^2-3NA_2q^3,
\]
\[
K_1=(2+M)A_1+1+A_3+N/4,\qquad
K_2=(4+2M)A_2+2NA_1.
\tag{2}
\]

For \(Y=7q\), this cubic equals

\[
(1-Y)^3+3B_1Y(1-Y)^2+3B_2Y^2(1-Y)+B_3Y^3,
\tag{3}
\]

where

\[
B_1=1-K_1/21,\quad
B_2=1-2K_1/21+K_2/147,
\]
\[
B_3=1-K_1/7+K_2/49-3NA_2/343.
\tag{4}
\]

We prove all three coefficients positive on (1). This proves

\[
\boxed{(G_2^*)'(q)>0\qquad(0<q\le1/7).}
\tag{5}
\]

## 2. A direct bound for the first coefficient

For the rest of the proof set

\[
b=a^{-2},\quad e=1-b,\quad H=S(1-u)-1/S,
\]
\[
B=2e+Sb,\quad A=e^2+eSb+S^2b^2,
\quad K=eH+(2S-1)b.
\tag{6}
\]

The exact normalized coefficients are

\[
A_1=B-\Delta H,\quad
A_2=A-\Delta K+u\Delta^2,\quad
A_3=2u\Delta-K.
\tag{7}
\]

On (1),

\[
\frac{36}{169}\le b\le\frac{100}{121},\quad
k\ge\frac92,\quad
\frac{29}{75}\le H\le\frac{217}{456}.
\tag{8}
\]

Since \(N/4\le18/k\), substitution into \(K_1\) gives

\[
K_1\le5+\frac{50}{k}
 +b\left[-3+\frac{16(S-2)}k\right]-eH
 +\Delta[2u-(2+M)H].
\]

The bracket multiplying \(b\) is at most \(31/27\), and
\(2u-(2+M)H\le2u-2H\le56/75\). Thus

\[
K_1\le5+\frac{100}{9}+\frac{3100}{3267}+\frac{56}{25}
=\frac{1576327}{81675}<21.
\]

In particular \(B_1\ge138848/1715175>0\).

## 3. Completing the square for the other two coefficients

Write \(B_i=c_0+c_1A_1+c_2A_2+c_3A_3\), with the following
coefficients:

| \(i\) | \(c_0\) | \(c_1\) | \(c_2\) | \(c_3\) |
|---|---|---|---|---|
| \(2\) | \(1-2(1+N/4)/21\) | \(-2(2+M)/21+2N/147\) | \((4+2M)/147\) | \(-2/21\) |
| \(3\) | \(1-(1+N/4)/7\) | \(-(2+M)/7+2N/49\) | \((4+2M)/49-3N/343\) | \(-1/7\) |

Both values of \(c_2\) are positive. For the second row,

\[
343kc_2=28k+224-72/p\ge28k+8>0.
\tag{9}
\]

By (7), completing the square in \(\Delta\) gives

\[
B_i\ge F_i:=c_0+c_1B+c_2A-c_3K
 -\frac{(-c_1H-c_2K+2uc_3)^2}{4c_2u}.
\tag{10}
\]

This inequality holds for every real \(\Delta\), so no movement
of the physical shape is involved.

For fixed \(a,S,u\), the function \(F_i\) is concave in
\(v=1/p\). Indeed, each \(c_j\) is affine in \(v\), and its
only nonlinear term is a negative quadratic divided by a positive
affine function. Explicitly, for affine functions \(f,g\) with
\(g>0\),

\[
\left(\frac{f^2}{g}\right)''
=\frac{2(f'g-fg')^2}{g^3}\ge0.
\]

Consequently it suffices to consider the two endpoints

\[
p=1/3,\qquad p=a/(a+2).
\tag{11}
\]

## 4. An elementary monotonicity removes the incoming-norm variable

In fact \(F_i\) decreases with \(u\) throughout (1). Here is a
proof that avoids doubling the number of endpoint polynomials.
Set

\[
t=-c_1/c_2,\quad r=-c_3/c_2,\quad
L=(t-e)S+2r,\quad
J_0=(t-e)(S-1/S)-(2S-1)b.
\]

Differentiating (10), with \(a,S,p\) fixed, gives the identity

\[
\frac{(F_i)_u}{c_2}
=-reS-\frac14\left(L^2-\frac{J_0^2}{u^2}\right).
\tag{12}
\]

For completeness the bounds on \(t,r\) follow from the single
quantity

\[
j=\frac{12}{p(5a+7)},\qquad
1<\frac{1800}{1391}\le j\le\frac{72}{25}.
\]

For \(i=2\),

\[
t=7-j,\qquad r=\frac{7}{2(1+8/k)},\qquad
\frac{78}{25}<t-e<6,\quad r\ge\frac{63}{50}.
\tag{13}
\]

For \(i=3\),

\[
t=\frac{7(7-2j)}{14-3j},\qquad
r=\frac{49}{28+224/k-72/(kp)},\qquad
\frac45<t-e<4,\quad r>1.
\tag{14}
\]

To check the two non-immediate bounds in (14), the displayed
function of \(j\) is decreasing, so

\[
t-e\ge\frac{217}{134}-\frac{133}{169}
=\frac45+\frac{3671}{113230}.
\]

Also \(p\le13/25\) and \(1/k\le2/9\) give

\[
28+224/k-72/(kp)\le28+\frac{1112}{13k}
\le\frac{5500}{117}<49.
\]

Now

\[
uL-J_0=-(t-e)H+2ur+(2S-1)b,
\]
\[
uL+J_0=(t-e)((1+u)S-1/S)+2ur-(2S-1)b.
\tag{15}
\]

Use (8), \((1+u)S-1/S\ge59/12\), and
\(180/169\le(2S-1)b\le1600/363\). The four lower bounds in
(15) are respectively

\[
\begin{array}{c|cc}
&uL-J_0&uL+J_0\\ \hline
i=2&16027/160550&465449/36300\\
i=3&6373/9633&1241/1210
\end{array}
\tag{16}
\]

For example the first is
\(-6(217/456)+(3/2)(63/50)+180/169\); the other three use the
corresponding bounds from (13)--(14). All are strictly positive.
Thus \(uL>|J_0|\), and (12) proves \((F_i)_u<0\). It remains
to prove the four endpoint signs from (11) at \(u=19/25\).

## 5. Four fully displayed polynomial signs

Put \(h=S-3\) and \(z=a-1\). In the domain (1),
\(0\le h\le1/6\) and \(z\ge1/10\). For each of the four
cases, direct substitution into the rational expression (10)
gives the exact identity

\[
F_i=\frac{P(h,z)}{\mathcal D},\qquad
P(h,z)=C_0(z)+hC_1(z)+h^2C_2(z)+h^3C_3(z)+h^4C_4(z).
\tag{17}
\]

The positive denominators, still written in \(S,a\), are:

| Case | \(i\) | \(p\) | \(\mathcal D\) |
|---|---|---|---|
| A | 2 | \(1/3\) | \(69825S^2a^4(5a-1)(5a+7)\) |
| B | 2 | \(a/(a+2)\) | \(69825S^2a^4(5a-1)(5a+7)\) |
| C | 3 | \(1/3\) | \(3258500S^2a^4(5a-1)(7a-1)\) |
| D | 3 | \(a/(a+2)\) | \(651700S^2a^5(5a-1)(35a^2+31a-36)\) |

The last additional factor is positive because it increases for
\(a\ge1\) and has value \(30\) at \(a=1\).
In each table below a row \((d_0,\ldots,d_n)\) denotes precisely
the polynomial \(\sum_{j=0}^n d_jz^j\); all coefficients are
printed. Thus (17) can be checked by multiplication and collection,
without a coefficient search or a numerical sign certificate.

### Case A

| Polynomial | Coefficients in ascending powers of \(z\) |
|---|---|
| \(C_0\) | \(-786816,16087260,81257528,147238728,126952752,52068060,7969800\) |
| \(C_1\) | \(5103168,35269544,101336150,150677368,120496952,48609720,7616050\) |
| \(C_2\) | \(4585088,18354348,32837789,35480560,24440220,9590220,1553750\) |
| \(C_3\) | \(1514304,4450704,3934032,62640,-1596600,-764640,-109500\) |
| \(C_4\) | \(176256,472608,253260,-339264,-472896,-207360,-32400\) |

### Case B

| Polynomial | Coefficients in ascending powers of \(z\) |
|---|---|
| \(C_0\) | \(-786816,16479228,81648608,148396608,129164520,53121060,7969800\) |
| \(C_1\) | \(5103168,37298024,102558278,149786536,121436792,49634040,7616050\) |
| \(C_2\) | \(4585088,19811916,30723797,27962008,19792548,8889540,1553750\) |
| \(C_3\) | \(1514304,5048592,3162288,-3010224,-3730392,-1195200,-109500\) |
| \(C_4\) | \(176256,562464,209484,-659520,-711360,-259200,-32400\) |

### Case C

| Polynomial | Coefficients in ascending powers of \(z\) |
|---|---|
| \(C_0\) | \(-26637696,198713856,1392715664,3069730816,3244093744,1696449440,354720800\) |
| \(C_1\) | \(42453600,644042360,2440857580,4237268240,3885845380,1857755760,369901000\) |
| \(C_2\) | \(38087888,385441312,1170034963,1655412252,1245247298,505583260,93049775\) |
| \(C_3\) | \(8985600,87211200,226261460,239623120,104953160,13834800,455700\) |
| \(C_4\) | \(609984,7263936,17477484,13059696,-1377336,-4712400,-1102500\) |

### Case D

| Polynomial | Coefficients in ascending powers of \(z\) |
|---|---|
| \(C_0\) | \(-26637696,138565632,1554453776,5349435296,10120506752,11470660160,7577413072,2621878560,354720800\) |
| \(C_1\) | \(42453600,1047777272,5374150028,12706281168,17645679936,15794649688,8963615852,2847548480,369901000\) |
| \(C_2\) | \(38087888,731343488,3352537139,6650234034,7206707853,4973412092,2374822713,711091850,93049775\) |
| \(C_3\) | \(8985600,186244032,828109652,1408119992,1050658044,307702352,6771452,-6401640,455700\) |
| \(C_4\) | \(609984,16992576,77912556,120816456,57882132,-23578320,-31501884,-10243800,-1102500\) |

Here is the elementary sign argument for the four complete
polynomials. In every case, \(C_1\) has strictly positive
coefficients. All coefficients of \(C_0\) except the constant
are positive. Retaining only its constant, linear and quadratic
terms and using \(z\ge1/10\) gives the following explicit lower
bounds:

\[
C_0\ge
\begin{cases}
40862132/25&\text{in A},\\
41939822/25&\text{in B},\\
179021156/25&\text{in C},\\
69085124/25&\text{in D}.
\end{cases}
\tag{18}
\]

For a polynomial \(C\), let \(C^-\) denote the sum of the
absolute values of its negative-coefficient terms. The following
table prints every coefficient of
\(V=C_2-C_3^--C_4^-\):

| Case | Coefficients of \(V\), in ascending powers of \(z\) |
|---|---|
| A | \(4585088,18354348,32837789,35141296,22370724,8618220,1411850\) |
| B | \(4585088,19811916,30723797,24292264,15350796,7435140,1411850\) |
| C | \(38087888,385441312,1170034963,1655412252,1243869962,500870860,91947275\) |
| D | \(38087888,731343488,3352537139,6650234034,7206707853,4949833772,2343320829,694446410,91947275\) |

Every entry is positive. Since \(0\le h\le1/6<1\) and
\(z\ge0\),

\[
C_2+hC_3+h^2C_4
\ge C_2-C_3^--C_4^-=V>0.
\tag{19}
\]

Equations (17)--(19) prove the four endpoint signs. Section 4
extends them to every incoming norm in (1), and the concavity in
Section 3 extends them to every allowed \(p\). Equation (10)
then proves \(B_2>0\) and \(B_3>0\). Together with Section 2,
this proves (5).

## 6. The continuation supplied by the lemma

Suppose fixed-normalized-duration convexity has selected the face
\(q=p_0/2\), where \(p_0=\tau q\) was held fixed in that
comparison. At this endpoint the duration is \(\tau=2\).
Now fix the geometry and increase \(q\) on that face. By (5),
the value of \(G_2^*\) strictly increases until

\[
q=\min\{q_c,1/7\}.
\]

The full interval remains admissible for the scalar formula:
\(r_A>1/3>2/7\) implies \(2<T=r_A/q\) whenever
\(q\le1/7\). Hence this step removes the extra tau-two scale
endpoint. It does not assert that the endpoint is an actual
trajectory, or that an outgoing norm floor survives separately.
The positivity being transported is solely the scalar weighted
residual established at the original root.
