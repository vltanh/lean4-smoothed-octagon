# Two small positive polynomials for the low-t maximum-duration face

Date: 2026-11-08.

**Scope.** This proves the two auxiliary signs
\[
\mathcal M(h,j)>0\quad
 (1/4\le h\le1/3,\quad1/30\le j\le3h/4),
\tag{1}
\]
and
\[
\mathcal B(h)>39\quad(1/4\le h\le1/3).
\tag{2}
\]
The complete polynomials are printed below. Their intended caller is the
maximum-duration face \(q=(1+h+j)/(1+2j)\) of the new residual in
[the low-t shape note](NONSHORT_LOW_T_SHAPE.md).
The [complete face proof](NONSHORT_LOW_T_QMAX.md) establishes the
source-to-auxiliary comparisons in Section 5 through small divided-derivative
identities and zero jets, then combines the results to close that face.
This note supplies its two subordinate sign claims; the separate reduction
from the full low-t domain to the comparison faces remains outside its scope.

## 1. The derivative lower polynomial

The polynomial \(\mathcal M\) has 43 monomials and total degree eight
in \((h,j)\). Its largest absolute coefficient is 1,018,180.
\[
\begin{aligned}
\mathcal M={}&- 28629 h^{8} - 13039 h^{7} j - 4907 h^{7} + 517202 h^{6} j^{2}\\
 &+ 104683 h^{6} j + 8268 h^{6} + 926841 h^{5} j^{3} + 320192 h^{5} j^{2}\\
 &+ 82723 h^{5} j + 7539 h^{5} - 358391 h^{4} j^{4} - 254988 h^{4} j^{3}\\
 &- 34503 h^{4} j^{2} + 10738 h^{4} j + 1890 h^{4} - 1018180 h^{3} j^{5}\\
 &- 747741 h^{3} j^{4} - 416497 h^{3} j^{3} - 108100 h^{3} j^{2} - 8222 h^{3} j\\
 &+ 195 h^{3} + 484321 h^{2} j^{6} + 500497 h^{2} j^{5} + 129038 h^{2} j^{4}\\
 &- 18104 h^{2} j^{3} - 11138 h^{2} j^{2} + 248 h^{2} j + 221 h^{2}\\
 &+ 455425 h j^{7} + 522510 h j^{6} + 442505 h j^{5} + 200524 h j^{4}\\
 &+ 44472 h j^{3} + 3422 h j^{2} - 86 h j - 5 h\\
 &- 336381 j^{8} - 381694 j^{7} - 256003 j^{6} - 105439 j^{5}\\
 &- 26431 j^{4} - 3836 j^{3} - 257 j^{2}
\end{aligned}
\tag{3}
\]
We first prove the separate, stronger monotonicity claim
\[
\partial_h\mathcal M>11
\quad(1/4\le h\le1/3,\quad0\le j\le1/4).
\tag{4}
\]
Put \(u=4h-1\in[0,1/3]\), \(v=4j\in[0,1]\).
The exact derivative identity is
\[
\partial_h\mathcal M=\sum_{i=0}^7 A_i(v)u^i,
\tag{5}
\]
where all eight univariate polynomials are
\[
16384A_0(v)=455425 v^{7} + 3058682 v^{6} + 8029516 v^{5} + 6556296 v^{4} - 10369939 v^{3} - 15654868 v^{2} + 5629039 v + 7102692.
\]

\[
8192A_1(v)=484321 v^{6} - 1052552 v^{5} - 9058630 v^{4} - 18001814 v^{3} - 6353106 v^{2} + 17305689 v + 10002776.
\]

\[
16384A_2(v)=- 3054540 v^{5} - 13273584 v^{4} - 4426050 v^{3} + 42075384 v^{2} + 65394153 v + 21946668.
\]

\[
4096A_3(v)=- 358391 v^{4} + 3614253 v^{3} + 13609822 v^{2} + 13129687 v + 2189630.
\]

\[
16384A_4(v)=4634205 v^{3} + 21919900 v^{2} + 17810705 v - 3695940.
\]

\[
8192A_5(v)=1551606 v^{2} + 982377 v - 2420160.
\]

\[
16384A_6(v)=- 91273 v - 1740620.
\]

\[
2048A_7(v)=-28629.
\]

Identity (5) has 36 monomials and total degree seven in \((u,v)\).
After clearing the denominator 16384, its largest coefficient is 65,394,153.
The eight coefficient polynomials have 8, 7, 6, 5, 4, 3, 2, and 1 monomials,
respectively, and degrees seven down to zero.

### The only square completion

We prove \(A_0>140\). The following is an exact degree-seven identity
with eight expanded monomials and coefficients of at most eleven digits:
\[
51200000(A_0(v)-140)
 =(5v-4)^2 Q(v)-8149898997v+7137213684,
\tag{6}
\]
where the complete positive-coefficient factor is
\[
\begin{aligned}
Q(v)={}&56928125v^5+473420250v^4+1724727900v^3\\
 &+3276112680v^2+2841712057v+493168676.
\end{aligned}
\tag{7}
\]
It has six monomials and degree five. If \(0\le v\le4/5\), the linear
part in (6) is at least \(3086472432/5>0\).
If \(4/5\le v\le1\), the first four terms of \(Q\) in increasing order
already give
\[
Q(v)>493000000+2273000000+2096000000+883000000>5000000000.
\]
Each bound is a direct substitution of \(v\ge4/5\) into one positive term.
Put \(d=5v-4\in[0,1]\). The right side of (6) is greater than
\[
5000000000d^2-1630000000d+617000000
=5000000000(d-1/6)^2+\frac{110000000}{3}d
 +\frac{4303000000}{9}>0.
\tag{8}
\]
This final identity is quadratic with three monomials. Thus \(A_0>140\)
on the whole interval; the only split is at \(4/5\).

### The remaining seven coefficients

For \(A_1\), direct differentiation gives
\[
4096A_1''=7264815v^4-10525520v^3-54351780v^2
 -54005442v-6353106<0.
\tag{9}
\]
There are five monomials and degree four. Since \(v^4\le v^2\), its first
positive term is absorbed by the displayed negative quadratic term.
Concavity and the endpoint values
\[
A_1(0)=1250347/1024,
\qquad A_1(1)=-1668329/2048>-816
\]
give \(A_1>-816\).

For \(A_2\), factor 3 from the displayed numerator and use
\(v^3,v^4,v^5\le v^2\). The residual quadratic
coefficient is
\[
14025128-1018180-4424528-1475350=7107070>0.
\]
Therefore \(A_2\ge5486667/4096>1338\).
For \(A_3\), its single negative quartic term is absorbed by its positive
cubic term because \(v^4\le v^3\); hence \(A_3>0\).
The last four printed polynomials immediately give
\[
A_4>-226,\qquad A_5>-296,\qquad A_6>-112,\qquad A_7>-14.
\tag{10}
\]
For \(A_6\) use \(v\le1\); the other three bounds discard positive terms.

Combining these estimates and \(u\le1/3\) gives
\[
\begin{aligned}
\partial_h\mathcal M
&>140-816u+1338u^2-226u^4-296u^5-112u^6-14u^7\\
&\ge1338(u-3/10)^2+\frac{759}{50}-\frac{9116}{2187}>11.
\end{aligned}
\tag{11}
\]
The quadratic completion is
\(140-816u+1338u^2=1338(u-3/10)^2-66u/5+979/50\).
The discarded higher powers sum to at most
\(226/81+296/243+112/729+14/2187=9116/2187\).
This proves (4).

## 2. The first endpoint: \(h=1/4\)

For \(1/30\le j\le3/16\), put \(v=4j\in[2/15,3/4]\).
The exact identity
\[
65536\mathcal M(1/4,j)=F(v)
\tag{12}
\]
has nine monomials and degree eight, where
\[
\begin{aligned}
F(v)={}&-336381v^8-1071351v^7-1521687v^6+1315792v^5\\
 &+4782453v^4-458951v^3-6072350v^2+213357v+2073343.
\end{aligned}
\tag{13}
\]
We prove \(F'<0\) on this interval. Its derivative is
\[
\begin{aligned}
F'(v)={}&213357+v\bigl[-12144700-1376853v+19129812v^2\\
 &+6578960v^3-9130122v^4-7499457v^5-2691048v^6\bigr].
\end{aligned}
\tag{14}
\]
This has eight monomials and degree seven. Use \(v\le3/4\),
\(1376853v>183000\), and discard the negative fifth and sixth powers
inside the brackets. The bracket is less than
\[
-12144700-183000+R(v^2),
\qquad R(s)=24064032s-9130122s^2.
\tag{15}
\]
The two-term quadratic \(R\) increases on \([0,9/16]\), since
\(R'=24064032-18260244s>0\) there. Its endpoint value is less than
10648000. Thus the bracket in (14) is less than \(-1670000\), and
\[
F'(v)<213357-1670000\cdot\frac2{15}<0.
\]
Finally
\[
F(3/4)=129353599/65536>0.
\tag{16}
\]
Consequently \(\mathcal M(1/4,j)>0\) on the required first interval.

## 3. The second endpoint: \(j=3h/4\)

The exact identity is
\[
65536\mathcal M(h,3h/4)=hT(h),
\tag{17}
\]
where the eight-monomial, degree-seven factor is
\[
\begin{aligned}
T(h)={}&26334162591h^7+4611512824h^6-1607824368h^5\\
 &-945389376h^4-9367296h^3+45060096h^2+782336h-327680.
\end{aligned}
\tag{18}
\]
Identity (17) has eight monomials, degree eight, and coefficients of at most
eleven digits. Write its eight positive magnitudes as
\(a,b,c,d,e,f,g,\ell\), in the order displayed. Then
\[
\begin{aligned}
T'={}&184339138137h^6+27669076944h^5-8039121840h^4\\
 &-3781557504h^3-28101888h^2+90120192h+782336,\\
\tfrac12T''={}&553017414411h^5+69172692360h^4-16078243680h^3\\
 &-5672336256h^2-28101888h+45060096\\
={}&21ah^5+15bh^4-10ch^3-6dh^2-3eh+f.
\end{aligned}
\tag{19}
\]
These have seven and six monomials and degrees six and five. The largest
coefficient is 553017414411, twelve digits.
For \(h\ge1/4\), group the first and third terms, then the second and fourth:
\[
\begin{aligned}
\tfrac12T''
&\ge(21a/16-10c)h^3+(15b/16-6d)h^2-3eh+f\\
&\ge\frac{21a-160c+60b-384d-768e}{256}\,h+f\\
&=\frac{202232681259}{256}\,h+45060096>0.
\end{aligned}
\tag{20}
\]
The second line uses \(h^3\ge h^2/4\) and \(h^2\ge h/4\).
The two coefficients to which those inequalities are applied are positive:
\(21a-160c=295765515531>0\), and
\(21a-160c+60b-384d>202232681259>0\).
Also
\[
T(1/4)=129353599/16384>0,\qquad
T'(1/4)=12663257753/4096>0.
\tag{21}
\]
Thus \(T'>0\), and then \(T>0\), for every \(h\ge1/4\).
This proves the second endpoint sign.

For a point in (1), if \(j\le3/16\), lower \(h\) to \(1/4\) using (4)
and apply Section 2. Otherwise lower it to \(h_0=4j/3\in[1/4,h]\)
and apply Section 3. Throughout each comparison \(j\le1/4\), so (4)
applies. This completes the proof of (1).

## 4. The low-degree lower polynomial on the minimum-gap face

The complete polynomial in (2) is
\[
\begin{aligned}
\mathcal B(h)={}&- 3151454 h^{8} - 653470 h^{7} + 286042 h^{6}\\
 &+ 230929 h^{5} - 4078 h^{4} - 22536 h^{3}\\
 &+ 3694 h^{2} - 78 h -11.
\end{aligned}
\tag{22}
\]
It has nine monomials and degree eight, with coefficients of at most seven
digits. Its third and fourth derivatives are
\[
\mathcal B'''=-12(88240712h^5+11435725h^4-2860420h^3
 -1154645h^2+8156h+11268),
\tag{23}
\]
\[
\frac1{24}\mathcal B''''=-220601780h^4-22871450h^3
 +4290630h^2+1154645h-4078.
\tag{24}
\]
These have six and five monomials, and degrees five and four.
On \([1/4,1/3]\), bound positive terms of (24) at \(1/3\), and negative
terms at \(1/4\). The resulting upper bound is
\(-69417941/192<0\). Also
\[
\mathcal B'''(1/4)=-20959485/64<0.
\]
Hence \(\mathcal B'''<0\), so \(\mathcal B'\) is concave.
Its left endpoint is positive:
\[
\mathcal B'(1/4)=1678169/2048>0.
\]
A differentiable function whose derivative is concave and positive at the
left endpoint takes its minimum at an endpoint. Indeed, at any interior
zero of the derivative, concavity forces the derivative to be positive
between the left endpoint and that zero; such a point cannot be a minimum
below the left endpoint value. Applying this elementary observation gives
\[
\mathcal B(h)\ge\min\{\mathcal B(1/4),\mathcal B(1/3)\}
 =\min\{1300869/32768,341200/6561\}>39.
\tag{25}
\]
This proves (2).

## 5. Exact caller and the source comparisons

Let \(G_n\) be the unit-shape residual of the linked shape note, put
\(t=(1-h)/2\), \(x=h+j\), and on this face set
\[
q=\frac{1+h+j}{1+2j},\quad
W=1+h+j,\quad d=1+2j,\quad Z=h+3j+2,\quad R=17h+17j+76.
\]
The natural cleared numerator is
\[
P(h,j)=576d^4W^2ZR\,G_n(t,x,q,1).
\tag{26}
\]
All denominator factors are positive on the original face
\(1/4\le h\le1/3\), \(1/30\le j\le5h/7\).
The complete face proof establishes the two comparisons
\[
\partial_jP\ge500\mathcal M(h,j),
\qquad P(h,1/30)\ge\mathcal B(h).
\tag{27}
\]
Given (27), the enlarged bound \(j\le5h/7<3h/4\), (1), and the mean value
theorem imply
\(P(h,j)\ge P(h,1/30)\ge\mathcal B(h)>39\), which closes the exact
maximum-duration face without weakening its domain.

The signs (1)--(2), their derivative reductions, and their displayed
identities are proved here independently of (27). The linked face proof
derives the first comparison from an explicit positive-product identity,
verified by a sixth derivative and small zero jets. It obtains the second
by integrating the first comparison from zero to \(1/30\), with a separately
verified zero-gap value. No high-degree coefficient table is a premise.
The full numerator has degree fourteen in two variables; globally expanding
it or its degree-thirteen derivative is outside that verification interface.
No Lean compilation, CI run, or measured speedup is claimed.
