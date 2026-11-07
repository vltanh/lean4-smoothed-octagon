# An eligible L3 window is a strict strong local minimum

Date: 2026-11-07. Hand certificate with an independently reviewed
application of the published sufficient-optimality theorem.

## Result and exact limitation

**Subsequent status:** the distinct small-window construction in
[LOCAL_REVERSE_SIX_OBSTRUCTION.md](LOCAL_REVERSE_SIX_OBSTRUCTION.md)
refutes the original universal L3 target with at most six replacement
pieces; [LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md)
extends that distinct family's result to all measurable replacements.
The theorem below remains a local result for its own exact input;
its limitations are not a claim that the original universal target is open.

There is an explicit eligible window of type **L3 = 021210** which is a
strict strong local minimum for its fixed initial and final frame and state,
with free elapsed time, in the normalized log-time formulation described
below. Its cost is strictly below the octagon cost. Every nonactive vertex
has a strictly unfavorable needle variation inside each of its six arcs;
at each switch exactly the two adjacent vertices tie, transversely.

This rules out a universal **nearby** improvement argument for L3, including
an argument using only first-order needles and the second variation of the
same-word endpoint fiber. It does **not** rule out a distant cheaper
replacement of at most six pieces. Consequently it does not refute L3 as
stated in [BOUNDED_REDUCTION.md](BOUNDED_REDUCTION.md), establish a uniform
bound, or advance the boundedness checkpoint to completion.

The proof consists of finite hand identities, elementary logarithm bounds,
and a stated application of a published sufficient-optimality theorem.
There is no numerical optimization premise and no kernel-validation claim.

## 1. The exact window

Use the triangular coordinates and generators of BOUNDED_REDUCTION. Put

\[
q=\frac54,\qquad L=\log\frac54,\qquad
\kappa^2=\frac{448}{803}.
\]

All six factors are \(q\), in the order \(0,2,1,2,1,0\). The initial
physical margins are

\[
\kappa\left(1,2,\frac{193}{112}\right),
\qquad g(0)=I.
\tag{1}
\]

Throughout this note a *raw* margin means the physical margin divided by
the fixed positive constant \(\kappa\). No variation of the initial state
is allowed. The raw quadratic invariant is

\[
p_0p_1+p_1p_2+p_2p_0=\frac{803}{112};
\]

multiplication by \(\kappa^2\) makes it exactly \(4\), as required for a
determinant-one state. The seven raw endpoint triples are

| Stage | Raw margins \((p_0,p_1,p_2)\) |
|---|---|
| Initial | \((1,2,193/112)\) |
| After control 0 | \((1,11/4,33/28)\) |
| After control 2 | \((173/112,55/28,33/28)\) |
| After control 1 | \((59/70,55/28,55/28)\) |
| After control 2 | \((173/112,33/28,55/28)\) |
| After control 1 | \((1,33/28,11/4)\) |
| Final | \((1,193/112,2)\) |

These follow from the exact affine margin recurrence. They are all strictly
positive. On each arc the active margin is constant, one other margin
increases, and the third decreases; hence the whole closed arc is strict
star, not just its endpoints. Every duration is positive.

The tangent endpoint and actual frame endpoint are respectively

\[
F=
\begin{pmatrix}7/16&18/25\\-18/25&688/625\end{pmatrix},
\qquad
g_{\rm end}=
\begin{pmatrix}
74568/140525&68837/100375\\
-68837/100375&500969/501875
\end{pmatrix}.
\tag{2}
\]

The final state is determined by the last row of the table. Neither
endpoint in (2) is replaced by the closed-word endpoint \(R\).

### 1.1 Cost eligibility

The exact normalized physical cost is

\[
\delta=\frac{C}{\sqrt{12}}
=\frac{4535-4898L}{5621}.
\tag{3}
\]

The elementary strict bounds used throughout this note are

\[
\frac29<L<\frac9{40}.
\tag{4}
\]

For every \(x>1\), integrating or differentiating gives
\(2(x-1)/(x+1)<\log x<(x-x^{-1})/2\); applying this at \(5/4\)
proves (4). Equation (3) therefore gives

\[
\delta<\frac{31019}{50589}<\frac23.
\]

Also \(\sqrt2<10/7\) and \(\log2<3/4\) imply

\[
\delta_{\rm oct}
=\frac{8-4\sqrt2-\log2}{2\sqrt2-1}
>\frac{43}{52}>\frac23.
\]

Thus the competitive-window cost condition holds strictly.

### 1.2 Full sector eligibility

For a frame \(g=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)\),
the six nonduplicate sector forms in BOUNDED_REDUCTION are

\[
a+b-c-d,\quad c+d,\quad -c,\quad a,\quad b,\quad d-b.
\tag{5}
\]

For each arc let \(r\in[1,5/4]\) be its partial factor. With the raw state
\(\widetilde X\) at the start of that arc and raw active margin \(a_i\),
the exact increment is

\[
I+\frac{\kappa^2a_i}{4}
\left[(r-r^{-1})\widetilde X
-(r+r^{-1}-2)\widetilde X D_i\right].
\tag{6}
\]

Multiply it on the left by the preceding frame. Each expression (5),
multiplied by the positive number \(r\), is a quadratic in
\(z=4(r-1)\in[0,1]\). Appendix A gives its three Bernstein coefficients
in the basis \((1-z)^2,2z(1-z),z^2\), after division by a displayed
positive common denominator. All coefficients are nonnegative; every
middle and final coefficient is strictly positive, and after the first arc
every initial coefficient is also strictly positive. The only zero
initial values are the expected three forms at \(g(0)=I\).

It follows directly that all six sector inequalities hold throughout the
window and are strict at every positive time, including its final time.
This verifies the full geometric eligibility condition, not merely an
endpoint or sampled version of it.

## 2. Exact endpoint rank and second variation

Let \(\mathcal I\) denote the raw cost: the physical normalized cost is
\(\kappa^2\mathcal I\), a fixed positive multiple. For nearby factors
\(q_0,\ldots,q_5\), keep the initial raw state in (1) fixed and use the
endpoint coordinates

\[
\mathcal E=(F_{00},F_{01},F_{10},p_{0,\rm end},p_{1,\rm end}).
\tag{7}
\]

These are a genuine local coordinate chart for the full frame and state
endpoint: \(F_{00}=7/16\ne0\) determines the omitted tangent entry using
\(\det F=1\); the positive raw state chart determines its omitted margin
from the fixed quadratic invariant. Fixed \(F\) and final state are
equivalent to fixed actual frame and state because
\(g_{\rm end}=\widetilde X_0F\widetilde X_{\rm end}^{-1}\).

Write \(J=D\mathcal E\) at the six factors \(5/4\). Scaling its rows by
\(20,125,125,875,3500\), respectively, gives the integer matrix

\[
\begin{pmatrix}
7&-7&-25&-25&-7&7\\
72&-72&200&0&128&-72\\
72&-128&0&-200&72&-72\\
-1484&2185&-1305&2405&-1525&0\\
9441&-6065&-4055&-8595&-1525&7625
\end{pmatrix}.
\tag{8}
\]

The minor of the unscaled matrix obtained by deleting its second column is
\(343552/546875>0\). Thus the rank is exactly five, and

\[
\ker J=\mathbb R v,\qquad v=(0,-1,-1,1,1,0).
\tag{9}
\]

Here are the exact normal multipliers for the raw cost, in the order (7):

\[
\lambda=\left(
\frac{685080L-95041}{54880},
\frac{5(257840L-3053)}{175616},
-\frac{5(257840L-3053)}{175616},
-\frac{3(167840L-18853)}{1366400},
-\frac{9(76120L-18789)}{341600}
\right).
\tag{10}
\]

Differentiating the stated recurrence and arc cost gives
\(D\mathcal I=J^\mathsf T\lambda\). For a short independently checkable
second-order identity, along the straight factor variation \(q+\varepsilon v\),

\[
\mathcal E''=
\left(\frac{192}{25},-\frac{3072}{625},\frac{3072}{625},
-\frac{2816}{875},\frac{8096}{875}\right),
\qquad
\mathcal I''=-\frac{11(3760L+4359)}{8750}.
\]

Substitution of (10) gives the constrained second variation

\[
\mathcal I''-\lambda\cdot\mathcal E''
=\frac{121(51-224L)}{2450}>0.
\tag{11}
\]

The sign follows already from \(L<9/40\), since \(51-224L>3/5\).
For the physical normalized cost, (11) is multiplied by \(448/803\)
and becomes \(352(51-224L)/12775>0\).

All displayed derivatives can be checked using only the product rule and
\((q^{-1})'=-q^{-2}\), \((q^{-1})''=2q^{-3}\),
\((\log q)'=q^{-1}\), \((\log q)''=-q^{-2}\).
In particular (11) is an identity for the actual fixed-initial-state
endpoint fiber; it is not an unconstrained cost Hessian or an initial-shape
variation.

## 3. Full-arc Hamiltonian inequalities

A switch-only needle check would be insufficient. We verify the inequalities
at every point of every arc.

At partial factor \(r\in[1,5/4]\) in arc \(a\), insert vertex \(j\)
for new factor \(e^\varepsilon\). Define its raw compensated derivative by

\[
\mathcal D_{a,j}(r)
=\left.\frac{d}{d\varepsilon}
\left(\mathcal I-\lambda\cdot\mathcal E\right)\right|_{\varepsilon=0}.
\tag{12}
\]

The original arc splits into factors \(r\) and \(q/r\). Formula (12) is
therefore obtained from the same explicit products and arc costs, using
\(\log(q/r)=L-\log r\). Inserting the active vertex gives zero: it is
equivalent to changing that arc's log factor, and stationarity in Section 2
makes the corresponding compensated derivative vanish.

Put \(m=\log r\). For the first three arcs the six other-vertex derivatives
are as follows. Every prefactor in the second column is positive.

| Arc and inserted vertex | Compensated derivative |
|---|---|
| \((0,1)\) | \(P_{01}(r)/392000\) |
| \((0,2)\) | \(P_{02}(r)/(200704r^2)\) |
| \((1,0)\) | \(11P_{10}(r)/62720\) |
| \((1,1)\) | \(121P_{11}(r)/(12544r^2)\) |
| \((2,0)\) | \(11P_{20}(r)/(200704r^2)\) |
| \((2,2)\) | \(605P_{22}(r)/3136\) |

Here

\[
\begin{aligned}
P_{01}&=(711040L-20548)r^2+(55685-352800L)r-98000-294000rm,\\
P_{02}&=-50176r^2+(894720L-247172)r+387365-1289200L+136640rm,\\
P_{10}&=(7043-23440L)r^2+(23440L-5063)r-1980-3660rm,\\
P_{11}&=-36r^2+(145-920L)r+1000L-125+120rm,\\
P_{20}&=-17600r^2+(15760L+1940)r+24287-53840L+31440rm,\\
P_{22}&=(32L-4)r^2+(9-32L)r-5-8rm.
\end{aligned}
\tag{13}
\]

The remaining six functions satisfy the exact reflection identities

\[
\mathcal D_{5-a,\sigma(j)}(r)=\mathcal D_{a,j}(q/r),
\quad \sigma(0)=0,\quad\sigma(1)=2,\quad\sigma(2)=1.
\tag{14}
\]

These identities follow either from the reflected state table or by direct
substitution in the same products; they do not identify arbitrary local
words by reversal.

### 3.1 Signs on the entire interval

All following estimates hold for \(1\le r\le5/4\).

**The function \(P_{01}\).** Using
\(\log r\le(r-r^{-1})/2\),

\[
P_{01}(r)\ge
(711040L-167548)r^2+(55685-352800L)r+49000.
\]

This lower quadratic is strictly concave by (4). Its endpoint values are
\(358240L-62863>150713/9>0\) and
\(670000L-286375/2>102625/18>0\). It is therefore strictly positive
throughout, so \(P_{01}>0\).

**The function \(P_{02}\).** It satisfies \(P_{02}(q)=0\),

\[
P_{02}''=-100352+136640/r\ge8960>0,
\qquad P_{02}'(q)=1031360L-235972<-3916<0.
\]

Thus its derivative is negative on the entire interval, and
\(P_{02}(r)>0\) for \(r<q\).

**The function \(P_{10}\).** It has \(P_{10}(1)=0\). Since
\(1-2r<0\), use \(L<9/40\) and \(\log r\le r-1\) in its derivative:

\[
\begin{aligned}
P_{10}'(r)
&=14086r-8723+23440L(1-2r)-3660\log r\\
&>211-122r\ge117/2>0.
\end{aligned}
\]

Hence \(P_{10}(r)>0\) for \(r>1\).

**The function \(P_{11}\).** It satisfies \(P_{11}(q)=0\),

\[
P_{11}''=-72+120/r\ge24>0,
\qquad P_{11}'(q)=175-800L<-25/9<0.
\]

It is strictly decreasing and positive before its final endpoint.

**The function \(P_{20}\).** It is strictly concave because
\(P_{20}''=-35200+31440/r\le-3760\). Its endpoint values are

\[
P_{20}(1)=8627-38080L>59>0,
\qquad P_{20}(q)=5160L-788>1076/3>0.
\]

Thus it is strictly positive throughout.

**The function \(P_{22}\).** Both endpoint values are zero, and

\[
P_{22}''=64L-8-8/r\le64L-72/5<0.
\]

It is strictly concave, hence strictly positive in the interior. Its
endpoint derivatives satisfy

\[
P_{22}'(1)=32L-7>1/9>0,
\qquad P_{22}'(q)=40L-9<0.
\]

Together with (14), these proofs establish all twelve full-arc inequalities.
The active vertex is uniquely optimal in every open arc. At every switch
the two adjacent vertices tie and the third has a strict gap. The displayed
nonzero endpoint derivatives, and their reflected versions, give strict
crossing at every switch. Positive clock factors preserve these signs.

## 4. From the finite certificate to strong local optimality

The sufficient theorem used here is Theorem 2.6 of Agrachev, Stefani, and
Zezza, [*Strong Optimality for a Bang-Bang Trajectory*](https://people.sissa.it/~agrachev/agrachev_files/bang-bang.pdf),
SIAM Journal on Control and Optimization 41 (2002), 991–1014. For a
control-affine fixed-time Mayer problem with simplex controls, it gives
strict strong local optimality from a regular normal bang-bang extremal,
simple transverse switches, and positive second variation on the
finite-dimensional switching problem. We now check the translation of this
free-time problem into that setting explicitly.

### 4.1 A smooth control-affine log clock

Let \(\widetilde X\) be the raw state and
\(\widetilde V=g\widetilde X\). The five-dimensional state manifold is
the product of the fixed-determinant tangent-frame manifold and the
fixed-determinant, trace-zero strict-star state sheet. In log time \(s\),
the vertex fields and raw running costs are

\[
f_i(\widetilde V,\widetilde X)
=\left(-\widetilde V D_i,\frac12[D_i,\widetilde X]\right),
\qquad
\ell_i(\widetilde X)=\frac18p_i(p_0+p_1+p_2).
\tag{15}
\]

They are smooth, distinct fields. General simplex controls use their convex
combinations. The actual physical clock is recovered by

\[
\frac{dt}{ds}=\frac\kappa2\sum_i u_i p_i>0.
\tag{16}
\]

The commutator equation gives the second component of (15); the identity
\(D_i\widetilde X+\widetilde XD_i=p_iI\) gives its first component.
The derivative of the exact arc cost gives \(\ell_i\). Thus (15) represents
the actual control problem, with the same frame/state endpoints and a fixed
positive cost normalization. It does not assume a new admissibility model.

### 4.2 Free total duration and the theorem's fixed interval

Let \(\rho>0\) be a constant state representing total log duration and
let \(z\) accumulate raw cost. On the fixed interval \([0,1]\), use fields

\[
(\rho f_i,\rho\ell_i,0)
\]

on \((\widetilde V,\widetilde X,z,\rho)\). The initial submanifold fixes
the original frame/state and \(z=0\), leaving \(\rho>0\) free. The terminal
submanifold fixes the target frame/state, leaving \(z,\rho\) free. The
Mayer objective is terminal \(z\). These are smooth submanifolds.

At the reference point, \(\rho=6L\) and the five switching times are
\(1/6,\ldots,5/6\). The five switching times together with the free initial
\(\rho\) give exactly the six positive log durations. The map from these
variables to the six factors is a local smooth bijection. Therefore the
rank-five endpoint calculation and positive one-dimensional constrained
Hessian in Section 2 are precisely the finite-dimensional second-variation
test required by the theorem, expressed in different coordinates.

### 4.3 The normal extremal and each regularity condition

The multiplier (10), with cost multiplier one, determines a normal adjoint:
pull back the terminal endpoint covector through the reference flow and
include cost covector \(-1\). Equivalently use the terminal cost extension
\(z-\lambda\cdot(\mathcal E-\mathcal E_{\rm target})\), which agrees with
\(z\) on the terminal submanifold.

Stationarity in all six durations makes the active Hamiltonian zero on
each entire constant-control arc. The total-duration component satisfies
the free-\(\rho\) transversality conditions: its terminal covector is zero,
and its variation is the integral of the zero active Hamiltonian. The
initial frame/state and cost are fixed, so there are no other free initial
directions to check.

For this adjoint, the negative of the nonactive Hamiltonian is exactly the
compensated needle derivative (12). Section 3 proves unique maximization
at the active vertex inside each arc, exactly two maximizers at each
switch, and strict crossing there. The latter is the strict bang-bang
Legendre condition: the derivative of the next-minus-current Hamiltonian
at the switch is positive. The one-sided computations agree because the
Poisson bracket of a Hamiltonian difference with itself is zero.

Finally (11) is positive on every nonzero admissible finite variation.
All hypotheses of the stated sufficient theorem are therefore satisfied.
The reference is a strict strong local minimum in the \(C^0\) topology
of this normalized free-log-time formulation, which includes the freely
varying duration coordinate. This conclusion concerns arbitrary nearby
simplex-controlled trajectories, not only same-word perturbations.

## 5. What this does not prove

Strong local optimality supplies a neighborhood, not a global comparison
with all endpoint-matching paths. It gives no explicit radius capable of
excluding every distant cheaper six-piece path, and small cost by itself
does not identify such a radius. A finite search over replacement words
cannot fill that gap.

Thus this local theorem alone does not decide universal L3. Its later
refutation for at most six pieces uses the distinct construction linked
at the top. What is proved here is a concrete obstruction to asserting that every
eligible L3 tuple has a nearby descent direction, a negative constrained
Hessian, or a favorable infinitesimal needle.

## Appendix A. Exact Bernstein sector certificate

Rows have the order (5); columns are the coefficients of
\((1-z)^2,2z(1-z),z^2\), for \(r\) times the corresponding sector form.
The integer matrices below are divided by the positive denominators

\[
(6424,\ 449680,\ 1124200,\ 2248400,\ 1124200,\ 5621000)
\]

for arcs \(0,\ldots,5\), respectively. These are obtained by substituting
the state table into (6), multiplying the preceding frame, and collecting
the three coefficients. They are a finite algebraic certificate on the
whole intervals; no sample-point positivity is used.

\[
B^{(0)}=\begin{pmatrix}
0&417&946\\6424&7003&7414\\0&336&840\\
6424&7115&7750\\0&305&610\\6424&7034&7644
\end{pmatrix},\qquad
B^{(1)}=\begin{pmatrix}
52976&95436&137896\\415184&439824&464464\\47040&87570&131796\\
434000&476700&509335\\34160&58560&93025\\428064&468834&503235
\end{pmatrix}.
\]

\[
B^{(2)}=\begin{pmatrix}
275792&429726&643390\\928928&954184&934010\\263592&425901&588210\\
1018670&1069760&1120850\\186050&314150&456550\\1006470&1065935&1065670
\end{pmatrix},\qquad
B^{(3)}=\begin{pmatrix}
1029424&1456752&1884080\\1494416&1454068&1413720\\941136&1265754&1580285\\
1793360&1895540&1900975\\730480&1015280&1396825\\1705072&1704542&1597180
\end{pmatrix}.
\]

\[
B^{(4)}=\begin{pmatrix}
753632&919512&1121230\\565488&581658&570570\\632114&758079&884044\\
760390&800040&839690\\558730&701130&852110\\638872&638607&602504
\end{pmatrix},\qquad
B^{(5)}=\begin{pmatrix}
4484920&5425635&6352014\\2282280&2278465&2194976\\3536176&4137546&4818590\\
3358760&3590585&3728400\\3408440&4113515&4818590\\2410016&2302496&2194976
\end{pmatrix}.
\]

## Reproduction and validation boundary

The finite identities can be reproduced by
`explorations/local_l3_exact_certificate.py`. Its input is only the single
tuple (1); it does not search a parameter domain or assert an exhaustive
optimization result. The sign arguments and the use of the sufficient
theorem are the hand proof above. The reproducer completed successfully
with Python 3.12.14 and SymPy 1.14.0. An independent hand review checked
all six sign arguments and the precise free-time augmentation against
Assumptions 2.1–2.3 and Theorem 2.6 of the primary paper; a further review
checked the normalization, multiplier, second-variation space, and scope.
Neither review found a material issue. No Lean, Lake, typecheck, or CI
command has been run for this result.

