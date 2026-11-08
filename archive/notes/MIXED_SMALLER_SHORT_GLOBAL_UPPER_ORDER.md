# A global upper order bound for the exact short secants

Date: 2026-11-08 UTC. Hand lemma, accepted in the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md),
Section 9.
No root, scale, norm-floor or Casimir hypothesis is used.

Suppose

\[
1<x,\qquad 1\le\alpha<x\le\beta\le\alpha x,
\qquad
u=\operatorname{Sec}(1,x,\beta)
 =\operatorname{Sec}(\alpha,\beta,x).
\tag{1}
\]

Then

\[
\boxed{\alpha\le\frac\beta x+\frac54(\beta-x).}
\tag{2}
\]

The inequality is strict for beta>x. If additionally x<=5, the
stronger bound

\[
\boxed{\alpha\le\frac\beta x+\frac98(\beta-x)}
\tag{3}
\]

holds, again strictly for beta>x.

These bounds complement the
[strong lower-order inequality](MIXED_SMALLER_SHORT_STRONG_ORDER.md).
For example, (2) gives the necessary rational strip

\[
x+\frac{4x(\alpha-1)}{5x+4}\le\beta
 \le x+\frac{x(7x+1)(\alpha-1)}{4x^2+11x+1}.
\tag{4}
\]

## 1. An elementary upper estimate for the secant-gap ratio

Use the exact equal-secant continuation and derivative formula stated
in Section 2 of the strong lower-order note. At a point on the branch,
write

\[
p=\frac\alpha\beta<q=\frac x\beta\le1,
\qquad g(s)=1-\frac{s}{(1+s)^2},
\]
\[
\eta=u-g(q)>0,\qquad \xi=g(p)-u>0,
\qquad
\alpha_\beta=p+\frac\eta\xi M,
\quad M=\frac{(2q-p)x-q^2}{x-q}>0.
\tag{5}
\]

The second secant is the average of g on [p,q]. Make the substitution

\[
z=\frac{1-s}{1+s},\qquad
z_q=\frac{1-q}{1+q}<z_p=\frac{1-p}{1+p}.
\]

Then g(s)=3/4+z^2/4, and the averaging weight in z is
2/(1+z)^2. Since z^2 strictly increases and the weight strictly
decreases, its weighted mean is strictly less than its unweighted
mean. This familiar integral comparison follows directly by integrating
the strictly negative product
(z^2-w^2)[(1+z)^(-2)-(1+w)^(-2)] over the square of the interval.
Consequently

\[
u-\frac34<\frac{z_p^2+z_pz_q+z_q^2}{12}.
\tag{6}
\]

The right side lies strictly between z_q^2/4 and z_p^2/4.
The ratio (u-g(q))/(g(p)-u) increases with u. Applying (6) gives

\[
\frac\eta\xi
 <\frac{z_p+2z_q}{2z_p+z_q}
 =\frac{3+p-q-3pq}{3-p+q-3pq}.
\tag{7}
\]

Both numerator and denominator are positive; this also follows from
their expression in z_p,z_q. Estimate (7) is an analytic integral
inequality, with no quadrature or numerical sign premise.

## 2. A finite derivative test for an affine upper barrier

Fix k>1 and consider

\[
\overline\alpha(\beta)=\frac\beta x+k(\beta-x).
\]

At a contact with the branch,

\[
p=\frac1x+k(1-q),\qquad
\overline\alpha_\beta=p+kq.
\tag{8}
\]

The contact condition p<=q restricts q to

\[
q_m\le q\le1,\qquad
q_m=\frac{1+kx}{(1+k)x}<1.
\tag{9}
\]

Put N=3+p-q-3pq and Z=3-p+q-3pq. Clearing the positive denominator
Z(x-q), the desired strict derivative inequality follows from

\[
F_k(q,x):=kqZ(x-q)-N\{(2q-p)x-q^2\}>0,
\quad p=\frac1x+k(1-q).
\tag{10}
\]

Indeed (10), then (7), imply (eta/xi)M<kq; equation (5) is therefore
strictly below the barrier derivative in (8).

## 3. The coefficient 5/4 works for every x>1

Take k=5/4, so q_m=(5x+4)/(9x), and put

\[
q=q_m+(1-q_m)v,\qquad 0\le v\le1.
\]

The following is a complete quartic identity:

\[
\boxed{
\frac{8748x^4}{(x-1)^2}F_{5/4}(q,x)
 =\sum_{i=0}^4\binom4i B_i(x)v^i(1-v)^{4-i},}
\tag{11}
\]

where

\[
\begin{array}{c|l}
i&B_i(x)\\ \hline
0&8(5x+4)(7x+2)(9x+4)\\
1&9(x+4)(142x^2+61x+4)\\
2&54x(53x^2+102x+24)\\
3&729x^2(8x+5)\\
4&8748x^3.
\end{array}
\tag{12}
\]

Each displayed coefficient is strictly positive for x>1. Since the
five nonnegative basis functions in (11) sum to one, (11) proves the
strict sign (10) on the entire contact interval.

For direct verification of the identity, substitution in (10) gives

\[
\begin{split}
16xF_{5/4}={}&-15xq^4
 -(120x^2+66x-12)q^3\\
 &+(357x^2+189x+36)q^2
 -(306x^2+228x+48)q\\
 &+85x^2+88x+16.
\end{split}
\tag{13}
\]

Inserting q=(5x+4)/(9x)+4(x-1)v/(9x), and collecting the degree-four
Bernstein basis, gives exactly (11)--(12). This is a small displayed
identity, not an unspecified coefficient test.

## 4. The coefficient 9/8 works for 1<x<=5

For this additional statement use k=9/8 and q_m=(9x+8)/(17x), with
the same parameter v=(q-q_m)/(1-q_m). The corresponding exact identity
is

\[
\boxed{
\frac{2004504x^4}{(x-1)^2}F_{9/8}(q,x)
 =\sum_{i=0}^4\binom4i C_i(x)v^i(1-v)^{4-i},}
\tag{14}
\]

with the complete coefficient list

\[
\begin{array}{c|l}
i&C_i(x)\\ \hline
0&144(9x+8)(13x+4)(17x+8)\\
1&51(-3237x^3+17062x^2+7840x+384)\\
2&578x(67x^2+1500x+416)\\
3&14739x^2(37x+38)\\
4&1002252x^3.
\end{array}
\tag{15}
\]

Four entries are visibly positive. For the remaining one, x<=5 gives

\[
17062x^2-3237x^3\ge877x^2>0.
\]

Thus (14) proves (10) for k=9/8 on this range as well.

## 5. Complete the upper-barrier comparison

The exact continuation starts at beta=x,alpha=1, where either barrier
also equals one. The derivative test is strict at this initial point,
since p=1/x<q=1 and (11) or (14) is strictly positive there.
Consequently the exact branch initially lies below the barrier.

A first later contact from below would require the branch derivative
to be at least the barrier derivative. Equations (5), (7) and (10)
give the opposite strict inequality at every possible contact.
If the barrier has already reached x, the original branch remains
strictly below it by alpha<x, so no additional contact interval is
needed. This proves (2), and proves (3) on its stated range.

Only the original two equal secants and their ordered continuation were
used. These upper bounds place no restriction on a changed or artificial
scale and do not themselves prove any remaining root or cost sign.
