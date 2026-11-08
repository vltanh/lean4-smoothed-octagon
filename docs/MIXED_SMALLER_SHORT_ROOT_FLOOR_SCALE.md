# Scale endpoints for a combined short residual and norm-floor test

Date: 2026-11-08 UTC. Hand reduction, accepted in the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md),
Section 7. The signs at the resulting endpoints remain separate tasks.

Use the coefficients and normalized root parameter of
[the envelope scale theorem](MIXED_SMALLER_SHORT_ENVELOPE_SCALE_MONOTONICITY.md):
\[
S=1+x,\quad q=\rho_A,\quad p=\tau q,\quad
R_{p/q}^*(q)=C(p)+qL(p),\quad
w_*(q)=1-qA_1+q^2A_2.
\]
Consider the scalar combination
\[
\mathcal G(q):=R_{p/q}^*(q)+\frac12[w_*(q)-3/4]
 =C(p)+\frac18+q\left[L(p)-\frac{A_1}{2}\right]
              +\frac{q^2A_2}{2}.
\tag{1}
\]
Its value at q=0 is the continuous extension of this last polynomial;
it is not asserted to describe a physical reverse arc.

## 1. Statement

Assume
\[
\frac{12}{5}\le x\le9,\qquad
1\le\alpha\le x\le\beta,\qquad
\frac34\le u\le\frac{13}{16},
\]
\[
0<p\le r_A=\frac{\alpha}{\alpha+\beta}\le\frac12,
\qquad 0\le q\le q_{\max}\le\frac p2.
\tag{2}
\]
The fixed shape has
\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x.
\]
Then
\[
\boxed{\mathcal G(q)\le
 \max\{\mathcal G(0),\mathcal G(q_{\max})\}.}
\tag{3}
\]
More precisely, if A_2>=0, the assertion follows from convexity in q.
If A_2<0, then
\[
\boxed{\mathcal G'(q)>\frac1{10}>0.}
\tag{4}
\]
For the intended root domain one can take
\[
q_{\max}=\min\left\{
 \frac{\alpha^2}{S^2+\alpha^2-1},\frac17,\frac p2\right\}.
\]
Thus this combined test has only its q=0 value and the same three
positive-scale faces as the original residual. Proving the actual
root supplies a positive combined test, and proving signs on these
faces, are not premises established by this note.

## 2. Useful coefficient identities

Put
\[
a=\alpha^{-2},\quad \varepsilon=1-a,\quad
\delta=D/\alpha^2,\quad
H=-E_0=S(1-u)-S^{-1}>0,
\]
\[
A=\varepsilon^2+\varepsilon Sa+S^2a^2,
\quad K=\varepsilon H+(2S-1)a>0,
\quad b=2u-H/2.
\tag{5}
\]
The scale coefficients take the form
\[
A_1=2\varepsilon+Sa-\delta H,\quad
A_2=A-\delta K+u\delta^2,\quad
A_3=2u\delta-K.
\tag{6}
\]
These follow directly from their definitions in the cited scale
theorem. In particular A_2<0 implies delta>0: for delta<=0 all
three terms in A-delta*K+u*delta^2 are nonnegative and A>0.

## 3. A negative A_2 forces a large shape and small a

First, for any D>0 in (2),
\[
\boxed{(x-1)^2<2\alpha^2.}
\tag{7}
\]
Indeed, beta>=x and alpha<=x give
\[
D\le\alpha^2+2\alpha x+1+2x-2x^2.
\]
If instead 2alpha^2<=(x-1)^2, then alpha>=1 forces
x>=1+sqrt(2). The last upper bound increases with alpha. Substituting
alpha=(x-1)/sqrt(2) bounds it above by
\[
\left(\sqrt2-\frac32\right)
 (x+3+3\sqrt2)(x-1-\sqrt2)\le0,
\]
contradicting D>0. This proves (7).

Now suppose A_2<0. Then delta>0 and (7) applies. Define
\[
\overline H=\frac S4-\frac1S,\qquad
\overline K=\varepsilon\overline H+(2S-1)a,
\qquad z=(S-2)^2a<2.
\]
Since u>=3/4, H<=Hbar and K<=Kbar. Completing the square in delta,
\[
A_2\ge A-\delta\overline K+\frac34\delta^2
       \ge A-\frac{\overline K^2}{3}.
\tag{8}
\]
The following identity displays its discriminant explicitly:
\[
\overline K^2-3A
 =\frac{S^4-56S^2+16+2(7S^2-4)z+z^2}{16S^2}.
\tag{9}
\]
If S<=5, the numerator is bounded above by
\[
S^4-28S^2+4\le4-3S^2<0.
\]
Here z<2 and S>=17/5 were used. Equations (8)--(9) would then give
A_2>0. Therefore A_2<0 forces
\[
\boxed{5<S\le10,\qquad 0<a<\frac29.}
\tag{10}
\]
The second inequality follows from (7) and S-2>3.

## 4. Reduce the derivative to a completed square

Assume A_2<0 from now on. Since q<=p/2, differentiating (1) gives
\[
\mathcal G'(q)
=(p+q)A_2+p^{-1}-1-A_3-A_1/2
\ge T(p):=\frac{3p}{2}A_2+p^{-1}-1-A_3-A_1/2.
\tag{11}
\]
Put m=3p/2. Substituting (6), then completing the square in delta,
\[
\begin{aligned}
T(p)={}&mA+p^{-1}-1-\varepsilon(1-H)
 +(3S/2-1)a+mu\delta^2-(mK+b)\delta\\
\ge F(p,a):={}&mA+p^{-1}-1-\varepsilon(1-H)
 +(3S/2-1)a-\frac{(mK+b)^2}{4mu}.
\end{aligned}
\tag{12}
\]
We will prove F>1/10 on the enlarged closed domain
\[
5\le S\le10,\quad \frac34\le u\le\frac{13}{16},\quad
0\le a\le\frac29,\quad 0<p\le\frac12.
\tag{13}
\]
On this domain
\[
\frac{59}{80}\le H\le\frac{12}{5},\qquad
\frac3{10}\le b\le2u.
\tag{14}
\]
These follow by taking the endpoints in H=S(1-u)-1/S.

## 5. F decreases with p

At fixed S,u, the quadratic A-K^2/(4u) is concave in a. Its quadratic
coefficient is
\[
-\frac{S^2[u-U(1/S)]^2}{4u}\le0,
\tag{15}
\]
because
\(2S-1-H=S[u+U(1/S)]\) and
\(S^2-S+1=S^2U(1/S)\).

Its derivative at a=0 is
\[
Q_1=S-2-\frac{H(2S-1-H)}{2u}<0.
\tag{16}
\]
For a direct verification, substitute H=S(1-u)-1/S to obtain
\[
2uQ_1
=S(1+u)[1-S(1-u)]-2u-S^{-1}+S^{-2}.
\]
Since 1-u>=3/16 and S>=5,
\[
S[1-S(1-u)]\le S(1-3S/16)\le\frac5{16}.
\]
Thus the last expression is strictly smaller than
\(145/256-3/2<0\). Concavity and (16) show
\[
A-\frac{K^2}{4u}\le1-\frac{H^2}{4u}\le1.
\tag{17}
\]

Expanding only the square in (12) gives
\[
F_p=\frac32\left(A-\frac{K^2}{4u}\right)
 -\frac{1-b^2/(6u)}{p^2}.
\]
By (14),
\(1-b^2/(6u)\ge1-2u/3\ge11/24\). Therefore
\[
\boxed{F_p\le\frac32-4\frac{11}{24}=-\frac13<0.}
\tag{18}
\]
It suffices to bound F(1/2,a).

## 6. The two a endpoints

For fixed S,u,p, the coefficient of a^2 in F is m times (15).
Consequently F is concave in a; its minimum on [0,2/9] occurs at an
endpoint.

At a=0 and p=1/2, (12) simplifies to
\[
F(1/2,0)=\frac34-\frac{4u}{3}+\frac{2H}{3}
                         -\frac{H^2}{48u}.
\tag{19}
\]
This expression increases with H and decreases with u on the rectangle
in (13)--(14): its respective partial derivatives are at least 8/15
and at most -28/25. Hence
\[
F(1/2,0)\ge
\left[\frac34-\frac{4u}{3}+\frac{2H}{3}
                         -\frac{H^2}{48u}\right]_{u=13/16,H=59/80}
=\frac{12013}{83200}>\frac1{10}.
\tag{20}
\]

At a=2/9 and p=1/2, F is concave as a function of u. To see this
without an expansion, note that all its terms outside the completed
square are affine in u, while that square divided by u has the form
\((c_1u+c_0)^2/u\). Its negative is concave for u>0.
It therefore suffices to check u=3/4 and u=13/16. Substitution gives
\[
F(1/2,2/9)\big|_{u=3/4}
=\frac{-97S^4+1232S^3-1608S^2-3520S-16}{5184S^2},
\tag{21}
\]
\[
F(1/2,2/9)\big|_{u=13/16}
=\frac{-1161S^4+17184S^3-35488S^2-60928S-256}{89856S^2}.
\tag{22}
\]
Each of these functions is strictly concave for S>0. After division
by S^2, its numerator has the form
\(-c_2S^2+c_1S-c_0-c_{-1}/S-c_{-2}/S^2\), with all four
coefficients relevant to its second derivative positive. Its minimum
on [5,10] is therefore at an endpoint. The four values are
\[
\frac{439}{1600},\quad\frac{1031}{8100},\quad
\frac{230279}{2246400},\quad\frac{3277}{20800},
\tag{23}
\]
in the order (21) at 5 and 10, then (22) at 5 and 10.
All are strictly greater than 1/10.

Equations (18)--(23) prove F>1/10 on (13). Equations (11)--(12)
then prove (4).

## 7. Complete the endpoint alternative

When A_2>=0, (1) is convex in q, proving (3) directly from its two
endpoint values. When A_2<0, (4) shows that its maximum is at
q=q_max, again proving (3).

The proof uses only elementary completed squares, short-order bounds,
concavity and explicitly evaluated rational endpoints. In particular
it does not use an executable sign check. It transports only the
combined scalar expression (1); no Casimir cap, physical cost or
separate norm floor is asserted at the artificial endpoints.
