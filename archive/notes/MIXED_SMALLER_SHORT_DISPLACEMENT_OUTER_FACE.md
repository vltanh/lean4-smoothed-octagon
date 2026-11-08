# The outer displacement face is strictly negative

**Replacement status, 2026-11-08:** the [new outer displacement assembly](../../docs/lighter-proofs/SHORT_DISPLACEMENT_OUTER_COMPLETE.md)
replaces the large signs (7)--(21) for the original actual caller.
It retains the lower beta order, covers both signs of the continued
norm residual, and uses reciprocal-shape convexity with three terminal
families. Every expanded identity has degree at most eight and at most
39 monomials; the original duration and scale conclusion is preserved.

Date: 2026-11-08 UTC. Conditional scalar hand theorem for the terminal
scale \(q=1/7\). The proof below specifies both rational numerators
completely, reduces a degree-six or degree-five variable by the
binomial identity, and gives explicit polynomial majorants for all
remaining adverse coefficients. There is no box subdivision or
coefficient-minimum premise.

Combine this note with
[the displacement weight reduction](MIXED_SMALLER_SHORT_DISPLACEMENT_WEIGHT_REDUCTION.md),
its [zero-scale sign](MIXED_SMALLER_SHORT_DISPLACEMENT_ZERO_SCALE.md),
and its [tau-two continuation](MIXED_SMALLER_SHORT_DISPLACEMENT_SCALE_CONTINUATION.md).
It concerns an actual candidate with
\(2\le x\le13/6\) and \(\delta=\beta/x-1\ge1/19\).
The ratio hypotheses and the central terminal face are separate
inputs.

## 1. A simple enclosing shape domain

Write \(a=\alpha\). The outer scale is selected only when
\(q_c\ge1/7\), so

\[
a^2\ge x(x+2)/6.
\]

Set

\[
a_0(x)=\frac{100x+77}{240}.
\]

For \(h=x-2\in[0,1/6]\),

\[
\frac{x(x+2)}6-a_0(x)^2
=\frac{71+2200h-400h^2}{57600}>0.
\tag{1}
\]

Consequently the unchanged actual shape lies in

\[
a_0(x)\le a\le x,
\qquad \beta=x[1+g(a-1)],
\qquad \frac14\le g\le\frac{115}{304}.
\tag{2}
\]

Indeed the upper short-order bound gives
\(g\ge8/(9x+8)\ge16/55>1/4\). The
[rational quadratic order](MIXED_SMALLER_SHORT_RATIONAL_QUADRATIC_ORDER.md)
gives \(a>1+[c(x)+1/23]\delta\); since
\(c(x)\ge13/5\), it implies
\(g<1/(13/5+1/23)=115/304\). These are necessary shape
restrictions. The extra points in (2) are used only to bound explicit
rational functions.

## 2. The incoming ceiling and the two rational upper tests

The incoming ceiling used here is

\[
\bar u=\frac34+
\frac{(x-1)^2(x+\beta-2)}{(\beta-1)(x+1)(35x+13)}.
\tag{3}
\]

It bounds the original incoming norm on (2). To see this, use the
accepted [incoming integral bound](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md):

\[
u\le\frac34+\frac1{\beta-1}
 \left[\frac{2(x-1)^3}{(x+1)(35x+13)}
             +\frac{(\beta-x)^3}{48x^2}\right].
\]

Here \(\beta-x\le(5/13)x(x-1)\). Also

\[
(x+1)(35x+13)\le\frac{10127}{36}
<\frac{8112}{25}=48(13/5)^2.
\]

Thus the cubic tail is at most
\((x-1)^2(\beta-x)/[(x+1)(35x+13)]\). Combining the two
terms proves (3).

Use \(u=\bar u\) in the rest of this note. The positive incoming
coefficient in the weight reduction permits this substitution at the
actual shape after all scale comparisons have been completed. Define

\[
S=1+x,\quad r=\frac a{a+\beta},\quad T=7r,\quad y=2/T,
\quad k=5a-1,\quad E_0=S(u-1)+1/S,
\]
\[
e=1-a^{-2},\quad n=S/a^2,\quad
\Delta=\frac{a^2+2a\beta+1+2x-2\beta x}{a^2},
\]
\[
A_1=2e+n+\Delta E_0,
\]
\[
A_2=e^2+en+n^2+\Delta^2u+\Delta eE_0
                                  -\Delta(2S-1)/a^2,
\]
\[
A_3=2\Delta u+eE_0-(2S-1)/a^2,
\quad w=1-A_1/7+A_2/49,
\quad E_L=-E_0+A_3/7.
\tag{4}
\]

At the actual shape, \(\beta<2a\) gives \(0<y<6/7\).
The elementary logarithm bound proved in the
[central-face note](MIXED_SMALLER_SHORT_DISPLACEMENT_CENTRAL_FACE.md),
Section 3, therefore gives

\[
\log y\le-\frac{40153}{180000}
                +\frac{2(5y-4)}{5y+4}
=\frac{319847}{180000}-\frac{56a}{19a+5\beta}
=:\ell.
\tag{5}
\]

Replace the logarithm at this point, before enlarging the shape domain
to (2). No logarithm comparison is needed at any extra shape. Put

\[
J=(u-1)/r+r+1-1/7-E_L+\ell,
\]
\[
n_0=2+\frac{16-24/T}{k},\qquad n_1=T+4/k,
\qquad \overline F_i=J+n_i(w-3/4).
\tag{6}
\]

These are rational upper bounds for the two duration tests. We prove
both strictly negative on all of (2).

## 3. Complete polynomial specifications

Use the positive clearing factors

\[
\mathcal D_0=61740000a^5(a+\beta)k(19a+5\beta)
                       (\beta-1)S(35x+13),
\]
\[
\mathcal D_1=8820000a^4(a+\beta)k(19a+5\beta)
                       (\beta-1)S(35x+13).
\tag{7}
\]

Define ordinary polynomials by the exact algebraic formulas

\[
N_i(h,v,t):=-\mathcal D_i\overline F_i,
\tag{8}
\]

where (3)--(7) are substituted and

\[
x=2+h,\quad
a=\frac{100x+77+(140x-77)v}{240},\quad
\beta=x\left[1+\left(\frac{115}{304}-t\right)(a-1)\right].
\tag{9}
\]

Thus \(0\le h\le1/6\), \(0\le v\le1\), and
\(0\le t\le b:=39/304\). The degrees in \((h,v,t)\) are
at most \((16,9,6)\) and \((14,8,5)\), respectively. Formulas
(3)--(9), involving only rational operations, specify every
coefficient of both polynomials; (7) cancels every denominator.

The following finite binomial identity is useful. For a polynomial
\(P(t)\) of degree at most \(m\), define

\[
\mathcal B_j[P]=
\sum_{l=0}^j
 \frac{\binom jl}{\binom ml}\frac{b^l}{l!}P^{(l)}(0)
\qquad(0\le j\le m).
\tag{10}
\]

Expanding \((1-s)^{m-j}\) verifies

\[
P(bs)=\sum_{j=0}^m\binom mj s^j(1-s)^{m-j}
                      \mathcal B_j[P].
\tag{11}
\]

All weights are nonnegative for \(0\le s\le1\), and their sum
is one. Apply this identity in the variable \(t\), setting

\[
B_{ij}(h,v)=\mathcal B_j[N_i(h,v,\cdot)],
\qquad m=6-i.
\tag{12}
\]

This formula explicitly defines the seven and six coefficient
polynomials to be compared below. No numerical endpoint value or
coefficient minimum is required.

## 4. A single adverse-term bound proves the first test

Normalize by the positive exact value

\[
c_0=N_0(0,0,0)=
\frac{7768604474750411439005709941213826217409}
     {282820069062612803911680000000}.
\tag{13}
\]

Write \(P\succeq Q\) when every ordinary coefficient of
\(P-Q\) is nonnegative. For each \(0\le j\le6\), multiplication
and collection of the completely specified polynomials (8)--(12)
gives

\[
\boxed{\frac{B_{0j}(h,v)}{c_0}
\succeq(1+v)^9[1-15h^8(1+h)^8].}
\tag{14}
\]

Here is the full coefficient comparison expressed without an
executable table. For powers \(h^rv^l\), the coefficient at
\(r=0\) is at least \(\binom9l\); coefficients for
\(1\le r\le7\) are nonnegative; and for \(8\le r\le16\)
the adverse coefficient is at most

\[
15\binom8{r-8}\binom9l.
\tag{15}
\]

These are comparisons of rational coefficients in (8)--(12).
Binomial coefficients outside their indicated ranges are zero.
Equations (14)--(15) specify one product majorant for every adverse
term, rather than an aggregate minimum of unprinted coefficients.

On \(0\le h\le1/6\),

\[
15h^8(1+h)^8\le\frac{15}{6^8}(7/6)^8
<\frac{60}{6^8}<\frac1{20000}.
\tag{16}
\]

Thus every \(B_{0j}\) is positive. The binomial identity (11)
proves \(N_0>0\), and hence \(\overline F_0<0\).

## 5. A five-term adverse bound proves the second test

The positive normalizing constant for the second test is

\[
c_1=N_1(0,0,0)=
\frac{33788202939258683901707399863924979}
     {10336990828311871488000000}.
\tag{17}
\]

For \(0\le j\le5\), define the nine univariate polynomials
\(A_{jl}(h)\), of degree at most fourteen, by the identity

\[
B_{1j}(h,v)=\sum_{l=0}^8 A_{jl}(h)v^l,
\qquad R_j(h)=\sum_{l=0}^3 A_{jl}(h).
\tag{18}
\]

Equations (8)--(12) and (18) are full algebraic specifications of
these polynomials. The following ordinary coefficient comparisons
give a common bound for all six values of \(j\):

\[
A_{j0}\succeq c_1,\qquad
A_{j1}\succeq0,\quad A_{j2}\succeq0,\quad A_{j3}\succeq0,
\tag{19}
\]

\[
\begin{array}{c|ccccc}
l&4&5&6&7&8\\ \hline
d_l&8/25&2/5&3/16&1/20&1/40
\end{array}
\qquad
\boxed{A_{jl}+d_lR_j\succeq0\quad(4\le l\le8).}
\tag{20}
\]

These inequalities are checked by direct multiplication and
collection of the rational formulas (3)--(12). They are explicit
univariate polynomial comparisons. In particular, each adverse
coefficient of degree \(h^r\) in \(A_{jl}\) is bounded by the
same displayed rational multiple \(d_l\) of the degree-\(h^r\)
coefficient in \(R_j\). There is no minimum over a parameter box
and no unspecified adverse polynomial.

The sign now follows by an elementary bound in \(v\). Put

\[
V(v)=\frac{128v^4+160v^5+75v^6+20v^7+10v^8}{400}.
\]

For \(0\le v\le1\),

\[
V(v)\le\frac{393}{400}v^3,
\]

and (19)--(20) give

\[
\begin{aligned}
B_{1j}(h,v)
&\ge\sum_{l=0}^3A_{jl}(h)v^l-R_j(h)V(v)\\
&\ge A_{j0}(h)(1-v^3)+R_j(h)[v^3-V(v)]\\
&\ge c_1\left(1-v^3+\frac7{400}v^3\right)
\ge\frac7{400}c_1>0.
\end{aligned}
\tag{21}
\]

The middle inequality uses \(v^l\ge v^3\) for \(1\le l\le3\).
The last uses \(R_j\ge A_{j0}\ge c_1\). The binomial identity
(11) proves \(N_1>0\), so \(\overline F_1<0\).

## 6. The terminal outer face is excluded

The original incident norm survives the scale comparisons. At the
actual terminal shape it can then be raised to (3), using the proved
positive incoming coefficient, and the exact logarithm can be raised
to (5). The two resulting rational functions are exactly (6).
Sections 3--5 prove both strictly negative on the enclosing domain
(2), which contains the unchanged actual shape. Thus neither duration
alternative can carry a positive weighted residual on the outer face.

This argument moves no physical root, common covector, Casimir cap,
outgoing norm floor, or cost to an enlarged shape. It is solely a
uniform sign theorem for the explicit terminal scalar bounds.
