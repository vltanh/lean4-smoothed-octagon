# The exact unequal-factor L1 window passes every needle test

Date: 2026-11-07. This is a hand certificate for the single eligible
\(\mathtt{012012}\) window in
[LOCAL_FORWARD_SIX.md](LOCAL_FORWARD_SIX.md). It strengthens that note's
same-word conclusion: the window satisfies the strict full-control
Hamiltonian conditions and is a **strict strong local minimum in the
normalized free-log-time formulation** specified in Section 6.

This is an obstruction to universal nearby descent, including insertion
of arbitrary nearby simplex controls. It is **not** a proof that no
distant endpoint-matching replacement is cheaper. It neither closes L1
nor shows that this window occurs in a global minimizer. L1, L2, L4, and
L5 remain open. The separate construction in
[LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md)
refutes the original L3 target even with arbitrary measurable replacements;
the sufficient reduction requires repair.

## 1. Fixed input and what is being varied

Use the exact data

\[
r=\frac{11}{10},\quad L=\log r,\quad
t=\frac{4761}{3950},\quad \sigma^2=\frac{1975}{1684},
\]
\[
P^{(0)}=(1,1,t),\qquad p^{(0)}=\sigma P^{(0)},\qquad
i=(0,1,2,0,1,2),\qquad q=(r,r,r^2,r^2,r,r^2).                 \tag{1}
\]

Throughout, arc indices are \(k=0,\ldots,5\); matrix-entry indices in
the endpoint chart below are one-based. The initial frame and state are
fixed. The final frame and state are also fixed, while elapsed time is
free. We make no closed-word assumption such as \(F=R\).

The seven strict-star switching states, full-arc sector inequalities, and
competitive cost are established in LOCAL_FORWARD_SIX. In particular,

\[
I=P_0P_1+P_1P_2+P_2P_0=1+2t=\frac4{\sigma^2},
\qquad
J=\frac{147129319-407979220L}{234143360}
<\frac23<\delta_{\rm oct}.                                  \tag{2}
\]

Here \(J\) is physical cost divided by \(\sqrt{12}\). The whole six-arc
trajectory has positive margins; the endpoint sign tests are equivalent
to positivity on each entire constant-control arc.

The tangent factors are

\[
T_0(q)=\begin{pmatrix}q&0\\0&q^{-1}\end{pmatrix},\quad
T_1(q)=\begin{pmatrix}q^{-1}&q-q^{-1}\\0&q\end{pmatrix},\quad
T_2(q)=\begin{pmatrix}q^{-1}&0\\q^{-1}-q&q\end{pmatrix}.
\]

For active, growing, and decreasing raw margins \((a,b,c)\), the update
and normalized arc cost are

\[
(a,b,c)\longmapsto
\left(a,(a+b)q-a,(a+c)q^{-1}-a\right),                        \tag{3}
\]
\[
J_i=\frac{a}{2I}
\left((a+b)(q-1)+(a+c)(1-q^{-1})-a\log q\right).              \tag{4}
\]

Use the endpoint chart

\[
E=(F_{11},F_{12},F_{21},P^{(6)}_0,P^{(6)}_1),
\qquad F=T_0(q_0)T_1(q_1)\cdots T_2(q_5).                   \tag{5}
\]

At (1), \(F_{11}>0\). The determinant of \(F\) and the invariant \(I\)
recover the omitted coordinates. With initial state fixed,
\(g_{\rm end}=X_0FX_{\rm end}^{-1}\), so fixing (5) fixes both actual
frame and state endpoints.

## 2. The unique stationary endpoint multiplier

Let \(M=DE\), differentiating in the six independent factors, and let
\(G=DJ\). The first five columns satisfy

\[
\det M_{0:4}
=-\frac{67030484100398003034549}
        {64896648437500000000000}\ne0.                      \tag{6}
\]

The stationary tangent and strictly positive constrained Hessian proved
in LOCAL_FORWARD_SIX imply \(G=\lambda M\), with the unique row covector
\(\lambda=G_{0:4}(M_{0:4})^{-1}\). For checking the calculations below, its
five entries are

\[
\begin{aligned}
\lambda_0&=-\frac{12478125(10880583036906L-4561898204113)}
 {36292975018558012847},\\
\lambda_1&=-\frac{3125(336770642156242162L-245852239863280901)}
 {611467718350641963283},\\
\lambda_2&=\frac{10312500(10880583036906L-4561898204113)}
 {36292975018558012847},\\
\lambda_3&=\frac{25(1408508704740720L-174843659719753)}
 {27385963183104416},\\
\lambda_4&=\frac{71164980509541600L-10502803950770983}
 {49792660332917120}.
\end{aligned}                                               \tag{7}
\]

These multipliers use the actual normalized cost \(J\) of (2), including
the fixed factor \(\sigma^2\), rather than a differently scaled raw cost.

At a partial factor \(z\in[1,q_k]\) in arc \(k\), split the old factor
into \(z\) and \(q_k/z\), and insert vertex \(j\) with factor
\(e^\varepsilon\). Define

\[
\mathcal D_{kj}(z)
=\left.\frac{d}{d\varepsilon}
 \left(J-\lambda E\right)\right|_{\varepsilon=0}.             \tag{8}
\]

The same derivative results from inserting factor \(1+\varepsilon\).
By (6), five old factors can be corrected smoothly to keep the full
endpoint \(E\) exactly fixed. Thus (8) is the cost derivative after that
correction. It has the usual direct interpretation: a negative value
would give a strictly cheaper finite-piece competitor. We will prove
that every nonactive value is positive except for the required adjacent
ties at switches.

At an arc endpoint, insert directly at the junction and vary the intact
old arcs, rather than retain a zero-duration split piece. At
\(\varepsilon=0\) this has the same derivative (8) and the same old-factor
Jacobian \(M\), so the correction uses positive old factors there too.

For the active vertex, \(\mathcal D_{k,i_k}\equiv0\). Indeed, insertion
of that vertex just changes the old arc's factor, and \(G=\lambda M\).

### 2.1 Finite differentiation recipe

For completeness, the identities below can be checked without an
optimizer or a symbolic-zero premise. Differentiate (3), writing a dot
for an arbitrary first variation:

\[
\begin{aligned}
\dot a_{\rm new}&=\dot a,\\
\dot b_{\rm new}&=(\dot a+\dot b)q+(a+b)\dot q-\dot a,\\
\dot c_{\rm new}&=(\dot a+\dot c)/q-(a+c)\dot q/q^2-\dot a.
\end{aligned}
\]

Update the tangent product by

\[
F_{\rm new}=FT_i(q),\qquad
\dot F_{\rm new}=\dot F\,T_i(q)+F\,T_i'(q)\dot q.              \tag{9}
\]

If \(B\) denotes the bracket in (4), then

\[
\begin{aligned}
\dot B={}&(\dot a+\dot b)(q-1)+(a+b)\dot q\\
&+(\dot a+\dot c)(1-q^{-1})+(a+c)\dot q/q^2\\
&-\dot a\log q-a\dot q/q,
\end{aligned}
\]
and the arc's cost derivative is \((\dot a B+a\dot B)/(2I)\).
Start with \(\dot P^{(0)}=0,\dot F=0\). For a needle, only its new
factor has \(\dot q=1\). On the split arc use
\(\log z\) and \(\log q_k-\log z\). Equations (3), (7), and (9)
then give every coefficient in the next section by a fixed sequence
of rational additions and two-by-two products.

## 3. All twelve full-arc needle functions

Every nonactive defect has the form

\[
\mathcal D_{kj}(z)=\frac{c_{kj}}{d_{kj}(z)}F_{kj}(z),\qquad
F_{kj}(z)=a_{kj}z\log z+b_{kj}(L)z^2+c^*_{kj}(L)z+d^*_{kj}(L), \tag{10}
\]

where the prefactor is strictly positive. The two occurrences of the
letter \(c\) in (10) have different roles: \(c_{kj}\) is the positive
prefactor numerator, while \(c^*_{kj}\) is the polynomial's linear
coefficient.

| \(k,j\) | \(c_{kj}\) | \(d_{kj}(z)\) |
|---|---:|---:|
| \(0,1\) | \(5\) | \(154480008848\) |
| \(0,2\) | \(1\) | \(5042942437600z^2\) |
| \(1,0\) | \(1\) | \(638347144z^2\) |
| \(1,2\) | \(1\) | \(3050980174748\) |
| \(2,0\) | \(1\) | \(762745043687\) |
| \(2,1\) | \(1\) | \(12607356094z^2\) |
| \(3,1\) | \(1\) | \(92292150286127\) |
| \(3,2\) | \(121\) | \(6303678047z^2\) |
| \(4,0\) | \(1\) | \(25214712188z^2\) |
| \(4,2\) | \(1\) | \(38620002212\) |
| \(5,0\) | \(1\) | \(12203920698992\) |
| \(5,1\) | \(1\) | \(1276694288z^2\) |

The primitive numerators are the following. Large integers here encode
only the single rational input (1), not an unresolved parameter search.

| \(k,j\) | \(a_{kj}\) | \(b_{kj}(L)\) | \(c^*_{kj}(L)\) | \(d^*_{kj}(L)\) |
|---|---:|---|---|---|
| \(0,1\) | \(-18117459470\) | \(12611108760-40122415960L\) | \(62252117026L-5637010786\) | \(-9058729735\) |
| \(0,2\) | \(3260768376925\) | \(-1478594316250\) | \(909938012265-13829191281815L\) | \(16320874555359L+348178853677\) |
| \(1,0\) | \(494112531\) | \(-269515926\) | \(1003060399L-45761793\) | \(315277719-1003060399L\) |
| \(1,2\) | \(-2366799023490\) | \(189943435000L+1028895579000\) | \(2157861244990L+39261561570\) | \(-1288151368317\) |
| \(2,0\) | \(-554990530600\) | \(2258091000000L+10170650000\) | \(265188778800-1622309048800L\) | \(-335769271013\) |
| \(2,1\) | \(10985143147\) | \(-5549905306\) | \(405427411-949717175L\) | \(949717175L+5144477895\) |
| \(3,1\) | \(-66460116039350\) | \(4748585875000L+25722389475000\) | \(127174443169950L+2452835836550\) | \(-40628081792573\) |
| \(3,2\) | \(45866986\) | \(-22933493\) | \(21916428-225809100L\) | \(225809100L+1017065\) |
| \(4,0\) | \(21516354759\) | \(-10645879077\) | \(356923287-1899434350L\) | \(1899434350L+10288955790\) |
| \(4,2\) | \(-27176189205\) | \(15763885950-50153019950L\) | \(82344511150L-2516898615\) | \(-16305713523\) |
| \(5,0\) | \(-7173690429235\) | \(32641749110718L+696357707354\) | \(2001863626983-23250530390758L\) | \(-3578198245325\) |
| \(5,1\) | \(823520885\) | \(-374327675\) | \(2006120798L-256227763\) | \(630555438-2006120798L\) |

## 4. A rational sign certificate on the entire arcs

### 4.1 A narrow elementary logarithm enclosure

We use only

\[
\ell_-:=\frac{9531}{100000}<L<
\frac{95311}{1000000}=:\ell_+.                              \tag{11}
\]

Indeed, integrating the geometric series gives

\[
L=2\operatorname{artanh}(1/21)
=2\sum_{n=0}^{\infty}\frac{1}{(2n+1)21^{2n+1}}.
\]

The first two terms and a geometric tail yield

\[
\frac{2648}{27783}<L<
\frac{2648}{27783}+\frac1{10187100}
=\frac{2912803}{30561300}.
\]

The cross-product surpluses for comparison with (11) are exactly

\[
2648\cdot100000-9531\cdot27783=227>0,
\]
\[
95311\cdot30561300-2912803\cdot1000000=25064300>0.
\]

For the tail bound, replace \(2n+1\) by \(5\) for \(n\ge2\) and sum the
remaining geometric series; the inequality is strict.

### 4.2 Endpoint arithmetic and derivative shape

Write \(f_{kj}=F_{kj}/|a_{kj}|\), and put \(b_k=q_k\). Then

\[
f''_{kj}(z)=\frac{\operatorname{sgn}(a_{kj})}{z}
             +\frac{2b_{kj}(L)}{|a_{kj}|},\qquad
f'''_{kj}(z)=-\frac{\operatorname{sgn}(a_{kj})}{z^2}.          \tag{12}
\]

The following table is a compact rational certificate. A pair \((m,n)\)
means a strict lower and upper bound for **\(10^6\) times** the indicated
quantity. A single \(0\) means an exact zero identity.

| \(k,j\) | \(10^6 f(1)\) | \(10^6 f(b_k)\) | \(10^6 f'(1)\) | \(10^6 f'(b_k)\) |
|---|---|---|---|---|
| \(0,1\) | \((1355,1357)\) | \(0\) | \((-13642,-13640)\) | \((-11953,-11950)\) |
| \(0,2\) | \((5214,5216)\) | \((2315,2317)\) | \((-32065,-32060)\) | \((-27444,-27440)\) |
| \(1,0\) | \(0\) | \((382,384)\) | \((9958,9961)\) | \((-3823,-3819)\) |
| \(1,2\) | \((1594,1596)\) | \(0\) | \((-11777,-11775)\) | \((-18614,-18612)\) |
| \(2,0\) | \((336,338)\) | \(0\) | \((11449,11456)\) | \((-8603,-8597)\) |
| \(2,1\) | \(0\) | \((2198,2201)\) | \((18228,18229)\) | \((-3344,-3341)\) |
| \(3,1\) | \((1816,1819)\) | \(0\) | \((6976,6979)\) | \((-18229,-18228)\) |
| \(3,2\) | \(0\) | \((406,409)\) | \((8597,8603)\) | \((-10781,-10777)\) |
| \(4,0\) | \(0\) | \((1754,1756)\) | \((18612,18614)\) | \((14966,14968)\) |
| \(4,2\) | \((347,349)\) | \(0\) | \((4516,4518)\) | \((-9961,-9958)\) |
| \(5,0\) | \((2104,2107)\) | \((11507,11508)\) | \((31650,31657)\) | \((63945,63952)\) |
| \(5,1\) | \(0\) | \((3114,3118)\) | \((11950,11953)\) | \((11660,11666)\) |

The few second-derivative bounds needed in addition are:

| \(k,j\) | Endpoint | Bound for \(10^6 f''\) |
|---|---|---|
| \(0,2\) | \(b_k\) | \((2191,2192)\) |
| \(1,0\) | \(1\) | \((-90910,-90909)\) |
| \(1,2\) | \(b_k\) | \((-24353,-24352)\) |
| \(2,0\) | \(b_k\) | \((-14219,-14210)\) |
| \(2,1\) | \(1\) | \((-10439,-10438)\) |
| \(3,1\) | \(b_k\) | \((-38757,-38756)\) |
| \(3,2\) | \(1\) | \(0\) |
| \(4,2\) | \(b_k\) | \((-100755,-100750)\) |
| \(5,0\) | \(1\) | \((61501,61511)\) |

These are rational inequalities, not rounded evaluations of a logarithm.
Here is a uniform way to check each entry. Substitute
\(z=1,r,r^2\) and \(\log z=0,L,2L\) in the displayed coefficient table.
Every resulting expression is affine in \(L\), say \(u+vL\), and hence
lies between

\[
\min(u+v\ell_-,u+v\ell_+)
\quad\hbox{and}\quad
\max(u+v\ell_-,u+v\ell_+).                                  \tag{13}
\]

Multiplication by the positive integer denominators proves the tabulated
bounds. For two explicit examples,

\[
f''_{02}(r)=\frac{210}{95821},\quad
10^6f''_{02}(r)-2191=\frac{56189}{95821}>0,\quad
2192-10^6f''_{02}(r)=\frac{39632}{95821}>0,
\]

and

\[
-f'_{01}(1)=
\frac{2(8996357447L-733873632)}{18117459470}
>
\frac1{1000}+\frac{11451046653857}{905872973500000}.
\]

The latter follows by using \(\ell_-\). Thus the rational endpoint table
is directly checkable from small-degree expressions, without trusting
a graph, a grid, or a numerical sign.

Now use (12):

- For \((0,1)\), \(f'\) is strictly convex and negative at both endpoints.
  It is negative throughout, so \(f\) decreases to its zero at \(b_0\).
- For \((0,2)\), \(f''\) is decreasing and positive at \(b_0\).
  Hence \(f'\) is increasing but still negative at \(b_0\). The positive
  terminal value gives positivity everywhere.
- For \((1,0),(2,1)\), \(f''\) is decreasing and already negative at \(1\).
  Each \(f\) is strictly concave, with nonnegative endpoint values.
- For \((1,2),(2,0),(3,1),(4,2)\), \(f''\) is increasing but negative
  at the right endpoint. Again each \(f\) is strictly concave.
- For \((3,2)\), \(f''=1/z-1<0\) for \(z>1\); its endpoint values
  give the same conclusion.
- For \((4,0),(5,1)\), \(f'\) is strictly concave and positive at both
  endpoints, so \(f\) increases from its zero at \(1\).
- For \((5,0)\), \(f''\) is increasing and positive at \(1\), while
  \(f'(1)>0\) and \(f(1)>0\).

Strict concavity with the stated endpoints gives strict positivity
inside each of the corresponding intervals. This proves all twelve
whole-arc inequalities, including every interior time:

\[
\mathcal D_{kj}(z)>0\qquad
(j\ne i_k,\ 1<z<q_k).                                     \tag{14}
\]

## 5. External endpoints, simple switches, and crossings

At the initial endpoint, the two nonactive defects are
\(\mathcal D_{01}(1)\) and \(\mathcal D_{02}(1)\); both are strictly
positive. At the final endpoint they are
\(\mathcal D_{50}(r^2)\) and \(\mathcal D_{51}(r^2)\), also strictly
positive. Thus the active vertex is uniquely optimal at **both external
endpoints**, as well as throughout the open arcs.

At each internal switch, exactly the adjacent two vertices tie. The
third-vertex defect is strictly positive by the same endpoint table.
The zero pairs and their strict crossing directions are

| Switch | Outgoing zero with negative derivative | Incoming zero with positive derivative |
|---|---|---|
| \(0\to1\) | \(F_{01}(r)=0,\ F'_{01}(r)<0\) | \(F_{10}(1)=0,\ F'_{10}(1)>0\) |
| \(1\to2\) | \(F_{12}(r)=0,\ F'_{12}(r)<0\) | \(F_{21}(1)=0,\ F'_{21}(1)>0\) |
| \(2\to0\) | \(F_{20}(r^2)=0,\ F'_{20}(r^2)<0\) | \(F_{32}(1)=0,\ F'_{32}(1)>0\) |
| \(0\to1\) | \(F_{31}(r^2)=0,\ F'_{31}(r^2)<0\) | \(F_{40}(1)=0,\ F'_{40}(1)>0\) |
| \(1\to2\) | \(F_{42}(r)=0,\ F'_{42}(r)<0\) | \(F_{51}(1)=0,\ F'_{51}(1)>0\) |

After normalization by \(|a_{kj}|\), every derivative in this table has
absolute value greater than \(1/1000\). At a zero, differentiation of the
positive prefactor in (10) makes no additional contribution. Changing from
partial factor \(z\) to log time multiplies the derivative by \(z>0\).
Consequently these are strict transverse Hamiltonian crossings.

These conclusions concern the full simplex of controls. Section 6
identifies a smooth clock in which the control fields and running costs
are affine combinations of their three vertex values. Therefore positivity
at every inactive vertex gives strict Hamiltonian maximization at the
active vertex, with precisely the adjacent edge of maximizers at a switch.
There is no untested interior-simplex direction.

## 6. Strong local optimality with free elapsed time

We apply Theorem 2.6 of Agrachev, Stefani, and Zezza,
[*Strong Optimality for a Bang-Bang Trajectory*](https://people.sissa.it/~agrachev/agrachev_files/bang-bang.pdf),
SIAM Journal on Control and Optimization **41** (2002), 991–1014.
In its normal case, the theorem assumes a regular bang-bang extremal,
simple switches, strict bang-bang Legendre crossings, and positive
switching second variation. The conclusion is strict strong local
optimality for the fixed-interval Mayer problem. We spell out the
reduction of the present free-time problem to that setting.

### 6.1 The actual control dynamics in a smooth log clock

In the triangular basis let

\[
D_0=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad
D_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
D_2=\begin{pmatrix}1&0\\2&-1\end{pmatrix},
\]
\[
\widetilde X=\frac12
\begin{pmatrix}-P_0&P_0+P_2\\-P_0-P_1&P_0\end{pmatrix},
\qquad \widetilde V=g\widetilde X .
\]

The five-dimensional state manifold consists of \(\widetilde V\) with
fixed determinant \(1/\sigma^2\), and the trace-zero strict-star sheet
of \(\widetilde X\) with that same determinant. The frame is recovered
smoothly as \(g=\widetilde V\widetilde X^{-1}\).

For log time \(s\), use the smooth vertex fields and normalized costs

\[
f_i(\widetilde V,\widetilde X)
=\left(-\widetilde VD_i,\frac12[D_i,\widetilde X]\right),
\qquad
\ell_i(\widetilde X)=\frac{\sigma^2}{8}P_i(P_0+P_1+P_2).
                                                               \tag{15}
\]

The physical clock for an arbitrary simplex control \(u\) is

\[
\frac{dt_{\rm phys}}{ds}
=\frac{\sigma}{2}\sum_i u_iP_i>0.                            \tag{16}
\]

Thus general controls use \(\sum_i u_if_i\) and
\(\sum_i u_i\ell_i\). This is the same actual control problem in a
positive clock, not a new admissibility assumption. On vertex \(i\),
\(ds/dt_{\rm phys}=2/p_i\), so its duration in \(s\) is \(\log q_i\).
The commutator equation and
\(D_i\widetilde X+\widetilde XD_i=P_iI\) give (15);
differentiating (4) with respect to \(\log q_i\) gives its running cost.
The three fields are distinct because \(\widetilde V\) is invertible.

### 6.2 A fixed interval with free total log duration

Adjoin a constant state \(\rho>0\) and a cost accumulator \(z_{\rm c}\).
On the fixed interval \([0,1]\), take the three autonomous fields

\[
(\rho f_i,\ \rho\ell_i,\ 0)
\quad\hbox{on}\quad
(\widetilde V,\widetilde X,z_{\rm c},\rho).                   \tag{17}
\]

The initial submanifold fixes the original frame/state and
\(z_{\rm c}=0\), leaving \(\rho\) free. The terminal submanifold fixes the
target frame/state, leaving \(z_{\rm c}\) and \(\rho\) free. Minimize
terminal \(z_{\rm c}\). These are smooth endpoint submanifolds.

For (1),

\[
\rho=9L,\qquad
(\tau_1,\ldots,\tau_5)
=\left(\frac19,\frac29,\frac49,\frac69,\frac79\right).
                                                               \tag{18}
\]

The five normalized switching times and the free initial \(\rho\) are
smooth coordinates for the six positive log durations:

\[
q_k=\exp\!\bigl(\rho(\tau_{k+1}-\tau_k)\bigr),\qquad
\tau_0=0,\quad\tau_6=1.
\]

The inverse is \(\rho=\sum_k\log q_k\) and
\(\tau_j=(\sum_{k<j}\log q_k)/\rho\). Hence this is a local smooth
bijection. Rank (6) leaves exactly one dimension in the linearized
endpoint-constrained switching problem.

### 6.3 Normality and the complete second-variation test

Use normal cost multiplier one and terminal cost extension

\[
\beta=z_{\rm c}-\lambda\bigl(E-E_{\rm target}\bigr).
\]

It agrees with the objective on the terminal submanifold. Pull back
\(-d\beta\) by the reference flow to obtain the adjoint. Its cost
covector is \(-1\). Stationarity \(G=\lambda M\) in all six independent
log durations implies that the active unscaled Hamiltonian
\(h_i=\langle p,f_i\rangle-\ell_i\) is zero on each arc: the
duration variation is its negative, and it is constant along that
autonomous arc. For the augmented field, \(H_i=\rho h_i=0\).

The terminal \(\rho\)-covector is zero, and its adjoint equation is
\(\dot p_\rho=-h_i=0\). It is therefore also zero initially, as required
by the free initial \(\rho\). All other initial state coordinates are
fixed. Thus the endpoint transversality conditions hold.

The inactive unscaled Hamiltonian equals
\(-\mathcal D_{kj}\). Sections 4–5 verify unique active maximization,
including both external endpoints; exactly one edge of maximizers at
every switch; and a strictly positive derivative of the
next-minus-current Hamiltonian through each switch. The two one-sided
crossing derivatives agree because their difference is the Poisson
bracket of the Hamiltonian difference with itself. Multiplication by
\(\rho>0\) preserves strictness. These verify Assumptions 2.1–2.3 of
the cited theorem.

Finally, the constrained Hessian on a nonzero tangent of the
one-dimensional fiber is the exact quantity from LOCAL_FORWARD_SIX,

\[
Q=
\frac{79359517360976760690-828902398596084416617L}
 {58144054680260010000}>\frac1{200}>0.                        \tag{19}
\]

That calculation includes endpoint curvature. The local coordinate
change in (18) preserves positivity of the constrained second variation
at a stationary point; a harmless convention of multiplying the
quadratic form by \(1/2\) also preserves positivity. Since (6) exhausts
the linearized constraints, (19) is positive on every nonzero admissible
finite switching variation of (17). There is no additional untested
duration direction.

The sufficient theorem therefore applies. The reference is a strict
strong local minimum in the \(C^0\) topology of the augmented, normalized
free-log-time state
\((\widetilde V,\widetilde X,z_{\rm c},\rho)\).
This includes arbitrary nearby measurable simplex controls, and freely
varying total duration, rather than only nearby six-factor paths.

## 7. Scope and reproducibility

The result supplies a neighborhood of this one trajectory. It supplies
neither an explicit global radius nor a comparison against all remote
endpoint-matching trajectories. A distant cheaper path, including one
with six pieces and a different word, is entirely compatible with this
certificate. In particular, this note does not refute the full nonlocal
L1 replacement statement and does not prove any uniform arc bound.

The hand proof consists of the exact recurrences, the twelve displayed
functions, the rational enclosure (11), the derivative-shape argument,
and the checked hypotheses of the cited sufficient theorem. The original
eligibility, rank, and constrained Hessian identities are the named
inputs from LOCAL_FORWARD_SIX.

A supplementary fixed-input reproducer is
[local_l1_needle_certificate.py](../explorations/local_l1_needle_certificate.py).
From the repository root, run

```text
python explorations/local_l1_needle_certificate.py
```

It checks the twelve full-arc identities and the displayed rational
bounds with Python 3.12.14 and SymPy 1.14.0. It uses no optimizer, random
sample, or time grid. Its finite symbolic checks do not replace the hand
argument and do not search the full eight-dimensional eligibility domain.
The reproducer completed successfully. An independent hand review checked
the full-arc signs, exact switch zeros, external endpoint gaps, strict
crossings, and the free-time application of the primary sufficient theorem,
and found no material issue.
No Lean, Lake, typecheck, or CI command has been run for this result.

