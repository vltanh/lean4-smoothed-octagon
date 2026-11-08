# S1 outer-scale large ratio by shape reduction

This proves all three strict inequalities (7) of
[the archived outer-scale large-ratio lemma](../../archive/notes/MIXED_SMALLER_SHORT_OUTER_SCALE_LARGE_RATIO_SIGN.md)
on its unchanged closed scalar domain. The proof first splits the shape
at a simple affine curve. On the larger side, a cubic comparison in beta
leaves twelve degree-eight polynomials with one sign change in the shape
variable. On the narrow boundary strip, beta convexity and two shape
derivatives reduce every sign to a single rational evaluation.

The full polynomial identities are in the
[large-shape appendix](SHORT_SCALE_OUTER_LARGE_SHAPES_ALGEBRA.md) and
[boundary-strip appendix](SHORT_SCALE_OUTER_BOUNDARY_ALGEBRA.md).
No archived coefficient table is used as a premise.

## 1. Exact source and caller

Write \(a=\alpha,b=\beta\). Assume
\[
\frac{12}{5}\le x\le9,\qquad
 a_f(x):=\frac{22x+20}{55}\le a\le x,
\tag{1}
\]
\[
 x+\frac{4x}{5x+4}(a-1)\le b\le x+c_0(x)(a-1),
 \qquad c_0(x)=\frac{x(7x+1)}{4x^2+11x+1}.
\tag{2}
\]
Put \(S=x+1,M=35x+13,B=a+b\), and, for an independent incoming norm \(u\), set
\[
\begin{gathered}
 M_0=6a^2+1,\quad D=a^2+2ab+1+2x-2bx,\\
 N_0=M_0\{S(u-1)+S^{-1}\}+2S-1,\\
 w=\frac{M_0^2-M_0S+S^2+D^2u-DN_0}{49a^4},
 \qquad E_L=\frac{2Du-N_0}{7a^2},\qquad T=\frac{7a}{B},\\
 F(\tau,\ell;u)=(w-1)\tau+\tau^{-1}
 +(u-1)B/a+a/B+6/7-E_L+\ell+\frac12(w-3/4).
\end{gathered}
\tag{3}
\]
These are exactly the source's transport formulas at \(q=1/7\).
Use labels \(i=T,8,2\) for
\[
 F_T(u)=F(T,0;u),\quad F_8(u)=F(8T/9,-1/9;u),\quad
 F_2(u)=F(2,5/(2T)-11/9;u).
\tag{4}
\]
The incoming ceiling in the source is
\[
 \bar u=\frac34+
 \frac{2(x-1)^3/(SM)+(b-x)^3/(48x^2)}{b-1}.
\tag{5}
\]
We prove \(F_i(\bar u)<0\) for all three labels on (1)--(2).

The exact caller is the outer face in the
[floor-weighted envelope reduction](../../archive/notes/MIXED_SMALLER_SHORT_FLOOR_WEIGHTED_ENVELOPE.md),
including the endpoint used by the
[tau-two scale reduction](../../archive/notes/MIXED_SMALLER_SHORT_ROOT_FLOOR_TAU_TWO_SCALE.md).
The elementary two tangent lines and convexity in duration in Section 2
of the source then give its unchanged uniform conclusion on \(2\le\tau\le T\).
The accepted [source audit](../../archive/notes/MIXED_SMALLER_SHORT_OUTER_SCALE_LARGE_RATIO_AUDIT.md)
identifies that same domain and caller. The corrections in
[HS_ERRATA](HS_ERRATA.md) remain in force.

We use incoming-norm monotonicity only at the original shape (1)--(2).
Here \(b\ge4a/3\): the difference between the lower endpoint in (2)
and \(4a/3\) decreases with \(a\), and its value at \(a=x\) is
\(x(7x-16)/(3(5x+4))>0\). Thus all hypotheses of Section 4 of the
floor-weighted envelope reduction hold. Its coefficient of \(u\) is
strictly positive at \(T,8T/9\), and also at \(2\), including when a
later scalar scale comparison passes \(T=2\). Consequently any proved
upper bound for (5) may be substituted before the subsequent shape
comparisons. Those later comparisons use the explicit rational
functions (3); they impose no outgoing floor at their new endpoints.

## 2. Two incoming majorants

Put
\[
 v=\frac{2(x-1)^2}{SM},\qquad m(x)=\frac{2x+3}{5}.
\]
On the entire source domain,
\[
 \bar u\le\frac34+v\le u_b:=\frac{x+74}{100}.
\tag{6}
\]
For the first inequality put \(\delta=b-x\ge0\). As \(a\le x\),
\(\delta\le c_0(x)(x-1)\); after cancelling nonnegative factors,
the required estimate is \(\delta^2SM\le96x^2(x-1)^2\).
The explicit polynomial
\[
96(4x^2+11x+1)^2-(7x+1)^2SM
 =-179x^4+5606x^3+11040x^2+1882x+83>0
\tag{7}
\]
proves it, since \(5606-179x>0\) for \(x\le9\).
The second inequality is \(35x^2-152x+213>0\), whose discriminant
is \(-6716\). Both identities have at most five monomials and degree four.

On the boundary strip \(a_f\le a\le m\), use the sharper bound
\[
 \bar u\le u_s:=\frac34+\frac{v(x-1+(b-x)/8)}{b-1}
 =\frac34+\frac{(x-1)^2(b+7x-8)}{4SM(b-1)}.
\tag{8}
\]
Indeed \(a-1\le2(x-1)/5\), so the needed inequality
\(\delta^2SM\le12x^2(x-1)^2\) follows from
\[
 p(x):=75(4x^2+11x+1)^2-(7x+1)^2SM
 =-515x^4+3758x^3+8331x^2+1420x+62>0.
\tag{9}
\]
To verify the last sign without subdivision, note that
\(p'= -2060x^3+11274x^2+16662x+1420\).
For \(x>0\), \(p'/x^2=-2060x+11274+16662/x+1420/x^2\)
is strictly decreasing. Thus \(p\) first increases and then decreases;
its minimum on \([0,9]\) is at an endpoint. Both values are positive:
\(p(0)=62\), \(p(9)=48320\). These displayed polynomials have five
and four monomials, of degrees four and three.

## 3. The larger shapes: a cubic comparison and one sign change

Assume \(m\le a\le x\), and substitute \(u_b\) from (6).
The source beta interval is contained in
\[
 b=x+c(a-1),\qquad 3/5\le c\le3/2.
\tag{10}
\]
The lower bound follows from \(x\ge12/5\). For the upper bound,
\(3(4x^2+11x+1)-2x(7x+1)=-2x^2+31x+3>0\) on \([0,9]\),
as is seen at both endpoints of this concave quadratic.

For this section only define
\[
 \mathcal N_i(c)=-d_i a^4SB F_i(u_b),\qquad
 d_T=9800,\quad d_8=d_2=88200,
\tag{11}
\]
with \(b=x+c(a-1)\). At fixed \(x,a\), this is a cubic in \(c\).
This degree follows directly from (3): \(w\) is quadratic in \(b\),
\(E_L\) is affine, and multiplication by \(B\) removes the sole pole.
Let \(c_-=3/5,c_+=3/2\), and form the four scalar coefficients
\[
\begin{aligned}
 C_{i0}&=\mathcal N_i(c_-),&
 C_{i1}&=\mathcal N_i(c_-)+\frac3{10}\mathcal N_i'(c_-),\\
 C_{i2}&=\mathcal N_i(c_+)-\frac3{10}\mathcal N_i'(c_+),&
 C_{i3}&=\mathcal N_i(c_+).
\end{aligned}
\tag{12}
\]
Primes here mean differentiation in the single variable \(c\), with
\(x,a\) fixed. For \(z=(c-c_-)/(c_+-c_-)\), the elementary cubic identity is
\[
 \mathcal N_i(c)=\sum_{j=0}^3\binom3j z^j(1-z)^{3-j}C_{ij}.
\tag{13}
\]
Its four weights are nonnegative and sum to one.

Only after this univariate reduction do we expand the twelve
coefficient functions, now in two variables:
\[
 C_{ij}=s_{ij}P_{ij}(A,X),\qquad
 A=a-m(x),\quad X=x-2.
\tag{14}
\]
The complete \(P_{ij}\) are in the large-shape appendix. Each has
39 monomials, total degree eight, and coefficient numerators of at most
twelve digits. The following table supplies their positive scale
factors and the sign cutoff \(r\) used below. It also gives the factor
\(e_{ij}\) in the endpoint identity (16).

| i,j | sij | r | eij |
|---|---:|---:|---:|
| T0 | 1/125 | 2 | 5 |
| T1 | 1/50 | 2 | 1 |
| T2 | 1/10 | 2 | 1 |
| T3 | 1/2 | 2 | 1 |
| 80 | 1/125 | 2 | 5 |
| 81 | 1/50 | 2 | 1 |
| 82 | 1/20 | 2 | 1 |
| 83 | 1/4 | 3 | 1 |
| 20 | 1/25 | 4 | 1 |
| 21 | 1/50 | 3 | 1 |
| 22 | 1/10 | 3 | 1 |
| 23 | 1/2 | 3 | 1 |
For \(2/5\le X\le7\), the coefficients of \(A^0,\ldots,A^r\)
in each \(P_{ij}\) are positive, and those of \(A^{r+2},\ldots,A^5\)
are negative. The intervening coefficient may have either sign.
Here is a direct check using only the printed polynomials. Working
from the largest power downwards in any coefficient polynomial in
\(X\), replace a negative term \(tX^k\), \(k\ge1\), by the lower
bound \(7tX^{k-1}\). For a required negative coefficient apply the
same procedure to its negative. Every resulting coefficient is
nonnegative, except for two constant terms. In those cases the
remaining lower bounds include respectively
\[
 [A^2]P_{T0}\ge\frac{343748133X-95134102}{25}>0,
 \qquad [A^4]P_{20}\ge4205907X-254421>0,
\tag{15}
\]
using \(X\ge2/5\). All unused terms in these two lower bounds are
nonnegative. The coefficient signs are therefore checked by a
single fixed monomial rule, with no root isolation or box cover.

For each row the appendix also prints the complete degree-seven
polynomial \(E_{ij}\), with eight monomials, such that
\[
 P_{ij}(3(x-1)/5,x-2)=e_{ij}\,xE_{ij}(x-2).
\tag{16}
\]
The same negative-term rule with \(X\le7\) turns each \(E_{ij}\)
into a polynomial with nonnegative coefficients and a positive
constant. Hence every right endpoint (16) is positive.

A polynomial whose coefficients start positive and then become
negative, with at most one intervening coefficient of unspecified
sign, has at most one positive zero and can cross only from positive
to negative. To see this, divide by the power at the last positive
coefficient: every positive lower power is nonincreasing, and every
negative higher power is nonincreasing. The quotient is strictly
decreasing whenever both blocks occur. A polynomial with only the
positive block is already positive. Thus positivity at zero and at
the right endpoint implies positivity throughout that interval.
Apply this to each \(P_{ij}\) on \(0\le A\le3(x-1)/5\).
Equations (13)--(16) prove \(\mathcal N_i>0\), hence all three
\(F_i(u_b)<0\) for the larger shapes.

## 4. The boundary strip: elementary beta convexity

Now let \(a_f\le a\le m\), use \(u_s\), and enlarge beta only to
\(x\le b\le x+3(a-1)/2\). In this strip \(B\le2x\).
At fixed \(x,a\), write
\[
 u_s=u_\infty+\frac{J_0}{b-1},\qquad
 u_\infty=\frac34+\frac v8,\qquad
 J_0=\frac{7(x-1)^3}{4SM}>0.
\tag{17}
\]
Each \(F_i(u_s)\) is a quadratic in \(b\), plus simple poles at
\(b=1\) and \(b=-a\). Its quadratic coefficient is respectively
\(q_0,q_0,5q_0\), where
\[
 q_0=\frac{2(x-a)^2u_\infty}{49a^4}\ge0.
\]
The residue at \(b=1\) is \(J_0U_i\), where \(U_i=(F_i)_u\vert_{b=1}\).
In particular
\[
\begin{aligned}
98a^4U_T={}&-6a^4x+79a^4-96a^3x-8a^3-7a^2x+13a^2-16ax+2a-x,\\
98a^4U_2={}&54a^4x+129a^4-60a^3x+2a^3-21a^2x-19a^2-10ax+10a-5x.
\end{aligned}
\tag{18}
\]
Both have nine monomials and total degree five. Also \(U_8\ge U_T\):
at \(b=1\), \(D=(a+1)^2\), and the coefficient of \(u\) in \(w\)
is \(D(D-M_0S)/(49a^4)<0\). Reducing \(T\) to \(8T/9\) therefore
increases the incoming coefficient.

Let \(R_i\) be the residues at \(b=-a\), and put
\(w_-=w(x,a,-a,u_s(-a))\). Then
\[
 R_T=a(7w_--6),\qquad R_8=\frac89R_T+\frac a9,
 \qquad R_2=a.
\tag{19}
\]
We will prove
\[
 U_T>-5/2,\qquad U_2>0,\qquad R_T>x^2/3.
\tag{20}
\]
It then follows, since \(b-1\ge x-1\) and \(B\le2x\), that
\[
\begin{aligned}
\frac12(F_T(u_s))_{bb}&>q_0-\frac{35}{8SM}+\frac1{24x}>0,\\
\frac12(F_8(u_s))_{bb}&>q_0-\frac{35}{8SM}+\frac1{27x}>0,\\
\frac12(F_2(u_s))_{bb}&=5q_0+\frac{J_0U_2}{(b-1)^3}+\frac a{B^3}>0.
\end{aligned}
\tag{21}
\]
For the middle strict sign it suffices that
\(8SM-945x=280x^2-561x+104>0\).
This quadratic is increasing for \(x\ge12/5\), and its value there
is \(1852/5>0\). The first sign has a still larger positive term.

Here are small explicit verifications of (20). Put
\[
 A=a-1,\qquad J=x-(5a-3)/2.
\]
The strip gives \(8/25<A\le16/5\), \(0\le J\le13/22\).
Define the following three polynomials:
\[
\begin{aligned}
 Q_T={}&-15A^5-6A^4J+18A^4-120A^3J+681A^3/2\\
 &-331A^2J+747A^2-342AJ+643A-126J+205,\\
 Q_2={}&135A^5+54A^4J+573A^4+156A^3J+1963A^3/2\\
 &+123A^2J+844A^2-16AJ+373A-42J+80,\\
 Q_R={}&25A^6/2+60A^5J+1825A^5/2+42A^4J^2
 +1465A^4J+5753A^4/2\\
 &+8A^3J^3+680A^3J^2+8567A^3J/2+6141A^3/2\\
 &+96A^2J^3+1728A^2J^2+4611A^2J+956A^2\\
 &+198AJ^3+1542AJ^2+1924AJ-284A+116J^3+440J^2+184J-128.
\end{aligned}
\tag{22}
\]
Their exact identities are
\[
 Q_T=98a^4(U_T+5/2),\qquad Q_2=98a^4U_2,
\]
\[
 Q_R=84a^3S\{a[7w(x,a,-a,3/4)-6]-x^2/3\}.
\tag{23}
\]
The first two polynomials have eleven monomials and degree five;
the third has 22 monomials and degree six. Their coefficient
numerators have at most four digits.

For \(Q_T\), discard positive terms involving \(J\) and use
\(J\le13/22\) in negative ones. This gives
\[
 Q_T\ge-15A^5+\frac{159}{11}A^4+\frac{5931}{22}A^3
       +\frac{12131}{22}A^2+\frac{4850}{11}A+\frac{1436}{11}
\]
\[
 \ge\frac{17847}{110}A^3+\frac{12131}{22}A^2
       +\frac{4850}{11}A+\frac{1436}{11}>0.
\tag{24}
\]
The second step twice uses \(A\le16/5\) on a negative highest
power. Likewise
\[
 Q_2\ge135A^5+573A^4+\frac{1963}{2}A^3+844A^2
          +\frac{3999}{11}A+\frac{607}{11}>0.
\tag{25}
\]
All \(J\)-terms in \(Q_R\) are nonnegative, and hence
\[
 Q_R\ge q_R(A):=\frac{25}{2}A^6+\frac{1825}{2}A^5
 +\frac{5753}{2}A^4+\frac{6141}{2}A^3+956A^2-284A-128>0.
\tag{26}
\]
Indeed \(q_R(A)/A\) is strictly increasing for \(A>0\), and
\(q_R(8/25)=125645472/9765625>12\).

Finally \(u_s(-a)<3/4\), because \(7x-a-8>0\).
At that point \(D=S^2-(x-a)^2>0\), while
\(D-M_0S=x(1+2a-6a^2)-7a^2<0\).
Thus \(w_u<0\) there, and
\(R_T\ge a[7w(x,a,-a,3/4)-6]>x^2/3\) by (23)--(26).
This completes the beta-convexity proof.

## 5. The boundary strip: five fixed beta faces

The lower slope in (2) is at least \(3/5\). For the upper slope,
use the following four intervals. Row 0 is the common lower face.

| j | x interval [lj,uj] | cj | Aj=af(lj)-1 |
|---:|---|---:|---:|
| 0 | [12/5,9] | 3/5 | 89/275 |
| 1 | [12/5,5/2] | 7/8 | 89/275 |
| 2 | [5/2,14/5] | 11/12 | 4/11 |
| 3 | [14/5,4] | 13/12 | 133/275 |
| 4 | [4,9] | 3/2 | 53/55 |

For completeness,
\[
 c_0'(x)=\frac{73x^2+14x+1}{(4x^2+11x+1)^2}>0.
\tag{27}
\]
At the four right endpoints its values are respectively
\(185/214,1442/1579,116/109,72/53\), strictly below the
four listed upper slopes. Beta convexity (21) therefore reduces
all source values to these five fixed faces.

For \(c_j=p_j/q_j\) in lowest terms put
\[
 L_j=p_ja+q_jx-p_j-q_j=q_j(b-1),\qquad
 V_j=(p_j+q_j)a+q_jx-p_j=q_jB,
\]
\[
 N_{ji}(x,a)=-\Delta_{ji} F_i(u_s),\qquad
 \Delta_{ji}=d_{ji}a^4SM L_jV_j>0,
 \quad b=x+c_j(a-1).
\tag{28}
\]
The exact small normalizations and derivative factors are as follows.

| j,i | dji | gji | hji | initial Nji(lj,af(lj)) > |
|---|---:|---:|---:|---:|
| 0T | 9800 | 1 | 1/2 | 4290 × 10^4 |
| 08 | 88200 | 1 | 1/2 | 1715 × 10^5 |
| 02 | 17640 | 1 | 1/2 | 3728 × 10^4 |
| 1T | 3136 | 2 | 1/2 | 2237 × 10^4 |
| 18 | 28224 | 1 | 1/2 | 5346 × 10^3 |
| 12 | 28224 | 2 | 1/2 | 1450 × 10^4 |
| 2T | 7056 | 2 | 1/2 | 1782 × 10^5 |
| 28 | 42336 | 1 | 1 | 6970 × 10^4 |
| 22 | 7056 | 2 | 1/2 | 1382 × 10^4 |
| 3T | 7056 | 2 | 1/2 | 5449 × 10^5 |
| 38 | 42336 | 1 | 1 | 1275 × 10^5 |
| 32 | 7056 | 2 | 1/2 | 1685 × 10^4 |
| 4T | 392 | 2 | 1 | 5360 × 10^4 |
| 48 | 7056 | 1 | 1 | 5044 × 10^5 |
| 42 | 3528 | 2 | 1 | 3502 × 10^5 |
The rational initial bounds in the final column use (3),(8),(28)
directly at the displayed rational arguments.

The boundary appendix prints, in full, the two identities
\[
 (N_{ji})_a=g_{ji}P_{ji}(A,H),\qquad
 (N_{ji})_a+\frac52(N_{ji})_x=h_{ji}R_{ji}(A,H),
\tag{29}
\]
where \(A=a-1\), \(H=x-2a+1\). Each of the thirty identities has
44 monomials and total degree eight, with integer coefficients of
at most twelve digits. Differentiation is done before expanding;
no degree-nine numerator expansion is a premise of the proof.

For the source arithmetic, first collect the affine dependence on the
incoming norm, using
\[
 F_i(u_s)=F_i(3/4)+(u_s-3/4)C_i,\qquad
 C_i=\frac Ba+\lambda S-2d+(\tau_i+1/2)d(d-\lambda S),
\]
\[
 \lambda=\frac{6a^2+1}{7a^2},\qquad d=\frac{D}{7a^2}.
\tag{30a}
\]
Here \(\tau_i\) is the duration in (4); its logarithmic tangent value
is independent of \(u\). For each of the two summands, multiply by
\(-\Delta_{ji}\), differentiate as in (29), then substitute \(A,H\)
and expand. All sixty individual contributions already have at most
44 monomials, degree eight, and twelve-digit coefficient numerators
before their pairwise addition. This specifies a budget-compliant
order of operations for reconstructing (29), without separately
expanding larger cancelling transport terms or the degree-nine parent.
The same affine grouping with \(u_b\) in Section 3 gives twenty-four
individual contributions to (14); each already has at most 39
monomials, degree eight, and twelve-digit coefficient numerators
before addition.

Here is the complete rule for reading the lower polynomials printed
in that appendix. In the strip,
\[
 A\ge A_j>0,\qquad A/2\le H\le A/2+13/22.
\tag{30}
\]
For the shape derivative \(P\), a term \(tA^kH^l\) is bounded
below by \(tA^k(A/2)^l\) when \(t\ge0\), and by
\(tA^k(A/2+13/22)^l\) when \(t<0\).
For the boundary derivative \(R\), use the exact boundary value
\(H=A/2+13/22\). The appendix's explicitly printed polynomial
\(L(A)=\sum_{k=0}^8l_kA^k\) then gives respectively
\[
 P_{ji}(A,H)\ge10^eL(A),\qquad
 R_{ji}(A,A/2+13/22)\ge10^eL(A).
\tag{31}
\]
Every coefficient in these lower polynomials is a downward integer
rounding after division by the listed \(10^e\). Some positive
coefficients below the last negative power are discarded. Thus these
bounds require only termwise substitution into the already printed
44-term identities and addition of rational numbers. No unlisted
sign table or executable certificate is required.

Every printed \(L\) is either coefficientwise nonnegative or has
all its nonpositive coefficients first and its nonnegative
coefficients last. Let \(r\) be its last negative exponent.
Then \(L(A)/A^r\) is increasing for \(A>0\): negative lower
powers and positive higher powers both have nonnegative derivative.
The appendix prints a strictly positive lower bound for \(L(A_j)\)
in each row. Consequently (31) is positive for all \(A\ge A_j\).
If all coefficients are nonnegative the conclusion is immediate.

It follows that \(N_{ji}(x,a)\) increases with \(a\) throughout
the strip. Hence
\[
 N_{ji}(x,a)\ge N_{ji}(x,a_f(x)).
\tag{32}
\]
Along that boundary, write \(a=1+A\) and
\(x=(5/2)(1+A)-10/11\). Its derivative with respect to \(A\)
is exactly the second expression in (29); it is positive by (31).
The positive initial values in the table therefore imply
\(N_{ji}(x,a)>0\) on every listed face. Equations (28) and (21)
give \(F_i(u_s)<0\) throughout the original boundary strip.

## 6. Closure and size audit

The two shape intervals \([a_f,m]\) and \([m,x]\) cover (1);
\(m-a_f=13/55>0\), and \(m\le x\) for \(x\ge1\).
Section 3 proves all three signs using the majorant \(u_b\), and
Sections 4--5 prove all three using \(u_s\). Incoming monotonicity
from Section 1 and the two comparisons (6),(8) finally give
\[
 \boxed{F_T(\bar u)<0,\qquad F_8(\bar u)<0,
              \qquad F_2(\bar u)<0}
\]
on exactly (1)--(2). This is the full original outer-scale lemma,
including all three logarithmic tangent tests and both closed endpoints
of the ratio range. Its original duration and scale callers therefore
remain valid.

The largest expanded identities are the thirty boundary derivatives:
44 monomials, two variables, total degree eight. The twelve larger-shape
coefficient identities have 39 monomials and degree eight; their twelve
endpoint polynomials have eight monomials and degree seven. The thirty
explicit lower polynomials have at most nine monomials and degree eight.
All other displayed polynomials have at most 22 monomials and degree six.
Every expanded coefficient numerator has at most twelve digits.
There are four fixed rational beta-slope intervals and one affine shape
split; the lower face is common to all four intervals.

The symbolic calculations used to transcribe these identities are not
premises. The proof consists of the displayed transport formulas, norm
comparisons, the four-term cubic identity, beta convexity, one-sign-change
arguments, and explicit rational inequalities. No Lean source or Lean
verification is part of this hand replacement.
