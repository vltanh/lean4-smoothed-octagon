# Hand substitution signs for the large-gap forward residual

Date: 2026-11-08 UTC. This note proves the substitution signs and shape
endpoint reduction for one explicit residual. The final rational sign
at the shape endpoints is a separate obligation; it is not asserted
here.

Use the unchanged common nonshort normalized data and the definitions
of N, the upper-envelope transported norm \(\mathcal T_U\), and the
solved-boundary transported norm \(\mathcal T_*\) from
[MIXED_NONSHORT_FORWARD_RATIO_REDUCTION](MIXED_NONSHORT_FORWARD_RATIO_REDUCTION.md).
Thus
\[
c=1-t,\quad p=t+x,\quad W=1+x,\quad Y=x(x+2),\quad J=t+Y,
\]
\[
B=k-t^2+p^2,\quad e=q/W,\quad D=eJ-p,\quad
E=e^2B+1-2pe,\quad C_*=tW^2DE^2/e>0.
\]
The original incoming secant is denoted by v. Actual eligibility gives
\[
N<0,\qquad \mathcal T_*\ge3/4,\qquad F_{p/W}(q)\le v.
\tag{1}
\]
All three inequalities refer to the retained actual comparison
coordinates, as justified in the ratio reduction.

We consider the possible large-gap case
\[
\frac13\le t<\frac25,\quad h=1-2t,\quad
j=x-h\ge\frac1{30}.
\tag{2}
\]

## 1. A smaller domain from the original incoming derivative floor

The exact incoming identity and the positive-integral bound give
\[
t<T_0(x)<T_G(x),\qquad
T_G(x)=\frac{90-19x^2}{12(x^2+10x+15)}.
\]
The first strict inequality is the original incoming derivative floor
\(v>1-cp/W^2\); the second is proved in
[MIXED_NONSHORT_POSITIVE_INTEGRAL_SECANT_BOUND](MIXED_NONSHORT_POSITIVE_INTEGRAL_SECANT_BOUND.md).
Direct differentiation gives
\[
T_G'(x)=-\frac{5(19x^2+75x+90)}{6(x^2+10x+15)^2}<0,
\qquad T_G(3/5)=\frac{231}{712}<\frac13.
\]
Consequently \(x<3/5\). On this interval,
\[
\frac12-\frac{7x}{24}-T_G(x)
=\frac{x(15-20x-7x^2)}{24(x^2+10x+15)}>0,
\]
since \(15-20x-7x^2>15-12-63/25=12/25>0\).
It follows that \(x<12h/7\), or
\[
\boxed{\frac1{30}\le j<\frac{5h}{7}.}
\tag{3}
\]

For the remaining estimates we use the closed enlarged domain
\[
\frac15\le h\le\frac13,\quad \frac1{30}\le j\le\frac{5h}{7},
\quad x=h+j,\quad
1\le q\le\frac{W}{1+2j},\quad 1\le k\le1+j.
\tag{4}
\]
The q bound is the retained quantitative swap inequality; the k bound
is the common-order inequality. Actual q is strictly greater than one.
In particular \(j\le5/21<1/4\).

## 2. The explicit positive multipliers

Put
\[
u=15(t-1/3)=\frac{5-15h}{2},\qquad y=q-1,
\]
\[
\boxed{\alpha=\frac{27}{4}-3u-24y+16j,
\qquad M=\frac14-u+6y+24j.}
\tag{5}
\]
Both are strictly positive on (4). Indeed \(0\le u\le1\), and
\[
0\le y\le\frac{h-j}{1+2j}\le\frac{15}{16}(h-j).
\]
Therefore
\[
\alpha=-\frac34+\frac{45}{2}h-24y+16j
\ge-\frac34+\frac{77}{2}j\ge\frac8{15},
\qquad M\ge\frac14-1+\frac{24}{30}=\frac1{20}.
\tag{6}
\]

For fixed t,x,q,k, temporarily regard v and \(\ell=\log q\) as
independent scalar arguments. Write
\[
F_\eta(q,\ell)=1+\eta^2q-\frac{\eta q\ell}{q-1},
\qquad\eta=p/W.
\]
Define the combined residual
\[
\mathcal H(v,\ell)
=\alpha N+C_*(3/4-\mathcal T_*)
       +M\{F_\eta(q,\ell)-v\}.
\tag{7}
\]
At actual eligible data, (1) and (6) give \(\mathcal H<0\).
The exact transported-norm identity from the ratio reduction gives
\[
\boxed{\mathcal H(v,\ell)
=(\alpha+1-Je^2)N+C_*(3/4-\mathcal T_U)
       +M\{F_\eta(q,\ell)-v\}.}
\tag{8}
\]
This identity will permit rational substitution without solving a new
switch or assigning a cost cap to the boundary comparison.

## 3. Three elementary geometric estimates

We first record
\[
\boxed{Je^2<\frac{17}{16},\qquad
        \frac{WD}{x}\le\frac{41}{24},\qquad
        W^2Dek<3h.}
\tag{9}
\]

For the first, J increases with h at fixed j, because
\(J=(1-h)/2+(h+j)(h+j+2)\). Thus
\[
J\le\frac{10}{9}+\frac83j+j^2.
\]
Since \(e\le1/(1+2j)\), the desired comparison follows from
\[
\frac{17}{16}(1+2j)^2
-\left(\frac{10}{9}+\frac83j+j^2\right)
=-\frac7{144}+\frac{19}{12}j+\frac{13}{4}j^2
\ge\frac7{900}>0.
\]

For the second, direct subtraction gives
\[
J-p(1+2j)=hW-j^2<x(1+h).
\]
Therefore
\[
\frac{WD}{x}\le\frac{W(1+h)}{1+2j}
\le\frac43\frac{4/3+j}{1+2j}\le\frac{41}{24}.
\]
The last fraction decreases with j, so its largest value occurs at
\(j=1/30\).

For the third, use \(D\le hW/(1+2j)\),
\(e\le1/(1+2j)\), and \(k\le1+j\). This yields
\[
W^2Dek\le h\frac{W^3(1+j)}{(1+2j)^2}
\le h\frac{(4/3+j)^3(1+j)}{(1+2j)^2}<3h.
\]
The strict final sign is the elementary identity
\[
3(1+2j)^2-(4/3+j)^3(1+j)
=\frac{17}{27}+\frac{116}{27}j
 +\left(\frac83-5j-j^2\right)j^2>0.
\]
Indeed \(0\le j<1/4\) makes the parenthesis at least \(65/48\).

## 4. Both substitution coefficients are strictly negative

The residual coefficient from the ratio reduction is
\[
A:=-N_v=xq\{I_0+I_1(q-1)\}\ge xeWk>0,
\]
\[
I_0=k+tx+tW(k-2t),\qquad
I_1=k(x+2)+tx(x+2)^2.
\tag{10}
\]
Here \(k\ge1>2t\). From the explicit upper-envelope transport,
\[
(\mathcal T_U)_v
=\frac{(1-e^2Y)\{1-e^2(Y+k/t)\}}{E^2}.
\]
Consequently
\[
\mathcal H_v
=-(\alpha+1-Je^2)A
-\frac{tW^2D}{e}(1-e^2Y)\{1-e^2(Y+k/t)\}-M.
\tag{11}
\]

If the product of the two parenthesized factors is nonnegative,
its contribution in (11) is nonpositive. If it is negative, put
\(a=e^2Y\), \(b=e^2k/t>0\). Negativity then forces
\(0<1-a<1\), and
\[
-(1-a)(1-a-b)=(1-a)(a+b-1)<b.
\]
Thus in either case its possible positive contribution is less than
\(W^2Dek\). Equations (6) and (9) also give
\[
\alpha+1-Je^2>\frac8{15}-\frac1{16}
=\frac{113}{240}>0.
\tag{12}
\]

If \(\alpha\ge2\), (9)--(11) imply
\[
\mathcal H_v
< -\frac{31}{16}A+W^2Dek-M
\le-\left(\frac{31}{16}-\frac{41}{24}\right)A-M
=-\frac{11}{48}A-M<0.
\tag{13}
\]
We used \(W^2Dek\le(WD/x)A\), which follows from (10).

If \(\alpha<2\), (5) gives
\[
6y>\frac{19}{16}-\frac34u+4j,
\qquad M>\frac{23}{16}-\frac74u+28j
\ge\frac{569}{240}-\frac74u.
\]
Since \(3h=1-2u/5\) and \(u\le1\),
\[
M-3h>\frac{329}{240}-\frac{27}{20}u
\ge\frac1{48}.
\]
Using (9), (11), and (12), we again obtain
\[
\mathcal H_v<W^2Dek-M<3h-M<-\frac1{48}<0.
\tag{14}
\]
Together (13) and (14) prove \(\mathcal H_v<0\) on the entire
closed parameter domain, independently of the scalar values of v and
\(\ell\).

For \(q>1\), the logarithm coefficient is even simpler:
\[
\mathcal H_\ell
=(\alpha+1-Je^2)N_\ell
 -M\frac{\eta q}{q-1}<0,
\quad N_\ell=-tpBqW<0,
\tag{15}
\]
by (6) and (12).

## 5. The resulting rational necessary condition

Retain the proved bounds
\[
v<v_G:=1-\frac{cp}{W^2}
 +\frac{cx}{W^2}\{T_G(x)-t\},
\qquad
\log q<L_+(q):=\frac{(q-1)(q^2+10q+1)}{6q(q+1)}.
\]
Set
\[
F_\ell=1+\frac{p^2q}{W^2}
-\frac pW\frac{q^2+10q+1}{6(q+1)}.
\]
Equations (13)--(15) prove that the rational function
\[
\boxed{G=(\alpha+1-Je^2)N(v_G,L_+)
 +C_*(3/4-\mathcal T_U(v_G))+M(F_\ell-v_G)}
\tag{16}
\]
satisfies \(G<\mathcal H(v,\log q)<0\) at every actual eligible
point in the large-gap case. The expression (16) extends continuously
to q=1. No floor is asserted for the artificially increased norm v_G;
only the two proved scalar coefficient signs are used.

At fixed t,x,q, G is a concave quadratic in k, with quadratic
coefficient
\[
\boxed{-\frac{tW^2De^3}{4}<0.}
\tag{17}
\]
Indeed the coefficient is already computed for the combination with
\(\alpha=6\) in the ratio reduction. Changing \(\alpha\) adds a
multiple of N, which is affine in k; the independent floor term is
constant in k. Rational substitution does not change this conclusion.

The common scale inequality supplies \(k>29t^2/4\). Thus an actual
point lies in the interval
\[
\max(1,29t^2/4)\le k\le1+j.
\]
By concavity, proving G positive at its two endpoints would prove it
positive throughout that interval, contradicting (16). Only nonempty
intervals need be considered. The required endpoint signs are the
remaining algebraic obligation; all domain bounds and substitutions
in this reduction have been proved above.
