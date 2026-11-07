# An exact stationary minimum obstructs the same-word L1 strategy

Date: 2026-11-06. **L1 itself remains open.** This note gives an exact,
strict-star, competitive, sector-eligible `012012` window whose cost has a
**strict local minimum** on its full same-word endpoint fiber. Consequently
one cannot prove L1 by asserting that every regular stationary same-word
fiber has a negative second variation. A different-word or nonlocal
replacement may still be cheaper. This is not a counterexample to Reinhardt,
nor a claim that this window occurs in a global minimizer.

The distinction matters because the proposed endpoint-fiber program in
[FIVE_TEMPLATE_HANDOFF.md](FIVE_TEMPLATE_HANDOFF.md) explicitly includes
stationary points and allows a different replacement word when same-word
variation fails. This note supplies a concrete exact obstruction at that
step, rather than a numerical optimizer failure.

## 1. Exact input

Use the triangular conventions and local endpoint map of
[BOUNDED_REDUCTION.md](BOUNDED_REDUCTION.md), §§4–5. Set

\[
 r=\frac{11}{10},\qquad t=\frac{4761}{3950},\qquad
 \sigma=\sqrt{\frac{1975}{1684}},\qquad
 p^{(0)}=\sigma(1,1,t),
\]

and choose the six factors

\[
 q=(r,r,r^2,r^2,r,r^2),\qquad i=(0,1,2,0,1,2).                 \tag{1}
\]

All factors are strictly greater than one. The normalization is exact:
\(\sigma^2(1+2t)=4\). Write \(P=p/\sigma\) for the unnormalized margins.
The seven switching states are the following exact rational vectors:

| Switching point | \(P_0\) | \(P_1\) | \(P_2\) |
| --- | --- | --- | --- |
| 0 | 1 | 1 | \(4761/3950\) |
| 1 | 1 | \(6/5\) | \(4366/4345\) |
| 2 | \(4/5\) | \(6/5\) | \(484/395\) |
| 3 | \(484/395\) | \(37236/47795\) | \(484/395\) |
| 4 | \(484/395\) | \(6/5\) | \(4/5\) |
| 5 | \(4366/4345\) | \(6/5\) | 1 |
| 6 | \(56321/39500\) | \(9/11\) | 1 |

These entries follow successively from

\[
 (A,B,C)\longmapsto(A,(A+B)q-A,(A+C)/q-A),              \tag{2}
\]

where the coordinates are placed in active, growing, decreasing cyclic
order. Every displayed margin is positive. Since the active margin stays
constant and the other two vary monotonically, all six entire arcs satisfy
the strict star inequalities.

## 2. The cost and sector hypotheses hold

Let \(L=\log(11/10)\). Summing the six exact vertex costs gives

\[
 J=\frac{147129319-407979220L}{234143360}
   <\frac{147129319}{234143360}<\frac23<\delta_{\rm oct}.       \tag{3}
\]

For the last inequality, one can use the stronger elementary bound
\(\delta_{\rm oct}>4/5\): after multiplying by the positive denominator,
this is \(44/5-(28/5)\sqrt2-\log2>0\), which follows from
\(\sqrt2<10/7\) and \(\log2<7/10\). The logarithm bound follows,
for example, by integrating the convergent series for
\(2\operatorname{artanh}(1/3)=\log2\) and bounding its geometric tail.
No decimal estimate of the octagon constant is needed.

Here is a finite rational check of the complete sector condition, including
interior times. Put

\[
 U(P)=\frac12\begin{pmatrix}-P_0&P_0+P_2\\-P_0-P_1&P_0\end{pmatrix},
 \quad v_0=(1,1),\quad v_1=(1,0),\quad v_2=(0,-1),\quad v_3=-v_0,
\]

and \([v,w]=-\det(v,w)\). At a partial factor \(z\in[1,q_k]\), the
frame increment is exactly

\[
 A_k(z)=I+\frac{\sigma^2P_{i_k}}4
 \{(z-z^{-1})U(P)-(z+z^{-1}-2)U(P)D_{i_k}\}.             \tag{4}
\]

Multiply by the preceding frame. For each \(j=0,1,2\), multiply each of
\([v_j,g(z)v_j]\), \([g(z)v_j,v_{j+1}]\) by \(z>0\).
With \(u=(z-1)/(q_k-1)\), each resulting polynomial has degree at most two.
Write it in Bernstein form

\[
 \beta_0(1-u)^2+2\beta_1u(1-u)+\beta_2u^2.
\]

The following table gives rational **lower bounds** for the three
coefficients, taking the minimum over the three contacts \(j\). All table
entries are integers divided by \(10000\); the expressions (1), (2), and
(4) specify every coefficient by rational arithmetic.

| Arc | First sector: \(10000(\beta_0,\beta_1,\beta_2)\) bounded below by | Second sector: corresponding lower bounds |
| --- | --- | --- |
| 1 | \((0,293,645)\) | \((10000,10323,10646)\) |
| 2 | \((586,969,1383)\) | \((9678,9937,10148)\) |
| 3 | \((1258,2142,3161)\) | \((9225,9659,9910)\) |
| 4 | \((2613,3594,4873)\) | \((8190,8404,8618)\) |
| 5 | \((4027,4628,5229)\) | \((7122,7229,7274)\) |
| 6 | \((4753,5887,6991)\) | \((6613,6808,6736)\) |

For illustration, the exact three contact-minima in the first row are
\((0,395/13472,869/13472)\) for the first sector and
\((1,278151/269440,143431/134720)\) for the second.
The other rows use precisely the same two-by-two multiplication and
quadratic coefficient conversion: if the polynomial is \(a+bu+cu^2\),
its Bernstein coefficients are \((a,a+b/2,a+b+c)\).
Thus every required determinant is positive at every positive interior
time; only the required first-sector zero at the initial endpoint occurs.
This is a whole-arc rational sign check, not sampling at switch points.

## 3. The full same-word endpoint fiber is regular

Hold the initial state \(p^{(0)}\) fixed and vary the six independent
factors in a neighborhood of (1). Let

\[
 F(q)=T_0(q_1)T_1(q_2)T_2(q_3)T_0(q_4)T_1(q_5)T_2(q_6),
\]

and let \(P^{(6)}(q)\) be the result of (2). A valid five-coordinate
endpoint chart is

\[
 E(q)=(F_{11},F_{12},F_{21},P^{(6)}_0,P^{(6)}_1).        \tag{5}
\]

At our tuple, \(F_{11}>0\). Since \(\det F=1\), its other three entries
fix \(F_{22}\). The invariant
\(P_0P_1+P_1P_2+P_2P_0=1+2t\), and positivity of \(P_0+P_1\),
show that fixing the last two coordinates of (5) fixes \(P^{(6)}_2\).
Thus (5) fixes the actual full tangent and state endpoints; by
\(g_{\rm end}=X_0 F X_{\rm end}^{-1}\), it fixes the frame endpoint too.

The following useful differentiation identities also provide compact
exact certificates for regularity and stationarity. Temporarily allow
\(P^{(0)}=(1,1,t)\) with variable positive \(t\), but keep the six base
factors in (1). Let \(M=DE\), differentiating in the independent factors,
and let \(M_{1:5}\) denote its first five columns. Direct differentiation
of (2) and the displayed triangular matrices gives

\[
 \det M_{1:5}=
 -\frac{362717989263(1750t+2689)(787648050t+11392799401)}
 {20796875000000000000000000}.                          \tag{6}
\]

It is strictly negative for positive \(t\). Moreover

\[
 w=\left(1,\frac{3049}{23100},\frac{115641}{100000},
 -\frac{115641}{100000},-\frac{3049}{23100},-\frac{11}{10}\right)
 \quad\hbox{satisfies }Mw=0.                           \tag{7}
\]

Equations (6)–(7) give rank exactly five and a nonzero tangent to the
one-dimensional exact endpoint fiber. They do not use the invalid
three-entry chart at \(F_{11}=0\): that entry is positive here.

## 4. Exact stationarity and positive constrained second variation

Let \(j\) be the cost computed with raw margins \(P\), so that the actual
cost is \(J=\sigma^2j\). Differentiate \(j\) in the six factors, keeping
the initial margins fixed, and let \(c=Dj\). Substitution into the same
recurrences yields the exact factorization

\[
 cw=\frac{(3950t-4761)}{\mathcal D}
 \bigl(170241480950Lt+167093446379L
       -20663242950t-22373451219\bigr),                 \tag{8}
\]

where \(\mathcal D=2541000000000000\). In particular \(cw=0\) at
\(t=4761/3950\); no estimate of a logarithm is needed for stationarity.
The endpoint rank in §3 then supplies unique multipliers \(\lambda\)
with \(c=\lambda M\).

For clarity, the constrained Hessian includes endpoint curvature. If
\(A=M_{1:5}\), then \(\lambda=c_{1:5}A^{-1}\), and its value on (7) is

\[
 Q=\sigma^2\left(w^TD^2j\,w-
       c_{1:5}A^{-1}
       \begin{pmatrix}w^TD^2E_1w\\\vdots\\w^TD^2E_5w\end{pmatrix}\right).
                                                               \tag{9}
\]

Differentiating the same rational state recurrence and exact cost formula
a second time, and inserting \(t=4761/3950\), gives

\[
 \boxed{Q=
 \frac{79359517360976760690-828902398596084416617L}
 {58144054680260010000}>\frac1{200}>0.}                  \tag{10}
\]

The sign has a short hand certificate. The alternating expansion of
\(\log(1+x)\), or integration of
\((1+s)^{-1}\le 1-s+s^2\) for \(0\le s\le1/10\), gives

\[
 0<L<\frac1{10}-\frac1{200}+\frac1{3000}
       =\frac{143}{1500}.
\]

Using this upper bound in (10), the resulting lower bound minus \(1/200\)
is the positive rational number

\[
 \frac{70152632123119383769}{87216082020390015000000}.
\]

The algebraic identities (6)–(10) are finite rational differentiations;
no optimized or approximate state enters them. They can be checked from
(2), (5), and the exact cost
\(\sum A[(A+B)(q-1)+(A+C)(1-q^{-1})-A\log q]/8\).
A supplementary exact-arithmetic script reproduces them and the sector
table; it is not a premise replacing these identities or the sign argument.

By the implicit function theorem, every nearby exact endpoint solution
lies on the smooth one-dimensional fiber. On this fiber the first cost
derivative vanishes and the second derivative on its nonzero tangent is
strictly positive. Therefore our tuple is a **strict local minimum of
cost among all sufficiently close same-word replacements with exactly
the same initial and final frame and state**. Strict star membership and
sector eligibility persist for those nearby factors.

## 5. Consequence for the finite research route

This example satisfies all the explicit local input restrictions in
BOUNDED_REDUCTION: six positive factors, an exact determinant-one initial
state, whole-arc strict star positivity, competitive cost, and complete
sector eligibility. It lies at regular endpoint rank. It therefore
invalidates the proposed stronger assertion that every stationary regular
L1 fiber has a negative constrained Hessian, even on the competitive
geometric domain.

It does **not** invalidate L1's broader existence claim. A cheaper
replacement could lie elsewhere on the same fiber or use another word of
at most six pieces. It also does not establish Pontryagin optimality with
respect to arbitrary controls, global optimality, or occurrence inside an
actual minimizing period. Any route using a universal same-word local
descent needs to be replaced or supplemented at this explicit example.

No Lean compilation, typechecking, Lake command, or CI was performed.
