# A minimum active margin excludes an entirely reverse period

Date: 2026-11-07. Hand proof with a supplementary exact identity checker
and an [independent internal audit](GLOBAL_REVERSE_PERIOD_EXCLUSION_AUDIT.md).
No Lean, Lake, typechecking, or CI.

## Theorem and scope

Let a strict-star trajectory carry a normal free-time Pontryagin lift.
Suppose it contains four positive vertex arcs with successive labels
`0,2,1,0`. Denote their constant active margins by `a_0,a_1,a_2,a_3`.
Then

\[
\boxed{\quad a_2\le\min(a_0,a_1,a_3)\quad\text{is impossible}.\quad}
\tag{1}
\]

The four arcs need not constitute a closed trajectory. Their adjoining
switches may be nontransverse or triple ties. No endpoint-rank assumption,
Casimir-sector assumption, or cost budget is used.

Consequently, **no finite positive strict-star normal PMP period with the
actual twisted state, frame, and cotangent endpoints can have every
switch in the reverse cyclic direction**. The active margins in such a
period form a finite periodic sequence, whose minimum would give (1).
[GLOBAL_NORMALITY](GLOBAL_NORMALITY.md) excludes abnormal lifts of these
finite closed trajectories. Thus the entire pure reverse case R in
[FINITE_CASE_COMPUTER_ROADMAP](FINITE_CASE_COMPUTER_ROADMAP.md) is excluded,
including negative elliptic, hyperbolic, and parabolic primary costates.

This is a necessary-PMP contradiction. The proof does not infer an exact
cheaper trajectory from a vector in the endpoint differential kernel.
It establishes neither a replacement theorem for arbitrary reverse local
windows nor any of the other four global case exclusions.

## 1. The margins at two successive reverse switches

Use the triangular coordinates and positive determinant-one margins of
[VERTEX_WORD_REDUCTION](VERTEX_WORD_REDUCTION.md) and
[GLOBAL_NORMALITY](GLOBAL_NORMALITY.md). They satisfy

\[
p_0p_1+p_1p_2+p_2p_0=4.
\]

On vertex `i`, its active margin is constant. If the active, growing,
and decreasing margins initially are `(a,b_0,c_0)`, the factor `q>1`
updates them to

\[
\bigl(a,(a+b_0)q-a,(a+c_0)/q-a\bigr).
\tag{2}
\]

Write `b>1,c>1` for the factors of the two interior arcs, with labels
2 and 1. At their shared switch write the margins in label order as

\[
(p_0,p_1,p_2)=(B,A,Z),\qquad A,B,Z>0,
\qquad AB+AZ+BZ=4.
\tag{3}
\]

At the preceding `0 -> 2` switch, the margins are `(P,Q,Z)`, where

\[
P=\frac{B+Z}{b}-Z,\qquad Q=bA+(b-1)Z.
\tag{4}
\]

At the following `1 -> 0` switch, its label-0 margin is

\[
E=\frac{B-(c-1)A}{c}.
\tag{5}
\]

Thus the four active margins are exactly

\[
(a_0,a_1,a_2,a_3)=(P,Z,A,E).
\tag{6}
\]

The hypothesized minimum in (1) therefore gives

\[
\boxed{
Z\ge A,\qquad B\ge bA+(b-1)Z,\qquad B\ge(2c-1)A.
}
\tag{7}
\]

These are non-strict inequalities; equal minima are retained.

## 2. Two positive needles with zero endpoint differential

Set

\[
D_0=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad
D_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
D_2=\begin{pmatrix}1&0\\2&-1\end{pmatrix},
\qquad T_i(q)=e^{-(\log q)D_i}.
\tag{8}
\]

Rebase the frame at the `0 -> 2` switch to the identity, and let its
state be

\[
Y=\frac12\begin{pmatrix}-P&P+Z\\-P-Q&P\end{pmatrix}.
\tag{9}
\]

For a formal sequence of factors with this fixed initial state, put
`F=product T_i(q)` and `G=product T_i(sqrt(q))`, in chronological order.
The actual endpoint map is

\[
X_e=G^{-1}YG,\qquad g_e=YF X_e^{-1}.
\tag{10}
\]

Consider the six labels and their base factors

\[
\begin{array}{c|rrrrrr}
\text{label}&0&1&2&0&1&0\\
\text{factor}&1&1&b&1&c&1.
\end{array}
\tag{11}
\]

The second and fourth columns are missing-control insertions at the
first two switches. The first and last columns are formal vertex-0
endpoint flows. Section 4 justifies them using the actual positive
outer arcs and their zero Hamiltonians; no negative-duration admissible
trajectory is assumed.

Put `D=A(c-1)+Z(b-1)>0`, and assign the log-factor derivatives

\[
\begin{array}{c|l}
d_0&-Ab^3(c-1)\\
w_1&B(c-1)\\
d_1&-(b^2-1)(c-1)(Ab+B)\\
w_2&bD\\
d_2&-b(c-1)\bigl[bB+(b-1)(c+1)Z\bigr]\\
d_3&-Zbc^2(b-1).
\end{array}
\tag{12}
\]

Both needle coefficients `w_1,w_2` are strictly positive; all four
original-control coefficients are strictly negative.

**Exact endpoint identity.** The derivative specified by (12) satisfies

\[
\boxed{
\delta F F^{-1}=0,\qquad
\delta G G^{-1}=-2b(b-1)(c-1)Y.
}
\tag{13}
\]

Here is a direct matrix verification procedure, with all its ingredients
displayed. A factor's right-trivialized log derivative is
`-Ad_(F_prefix) D_i` for `F` and `-Ad_(G_prefix) D_i/2` for `G`.
The nonidentity prefixes in (11) are respectively `T_2(b)` and
`T_2(b)T_1(c)`. For the half-factor conjugations one may replace
`T_i(sqrt(q))` by its scalar multiple `K_i(q)=sqrt(q)T_i(sqrt(q))`.
The four needed matrices are

\[
T_2(b)=\begin{pmatrix}b^{-1}&0\\b^{-1}-b&b\end{pmatrix},\quad
T_1(c)=\begin{pmatrix}c^{-1}&c-c^{-1}\\0&c\end{pmatrix},
\]
\[
K_2(b)=\begin{pmatrix}1&0\\1-b&b\end{pmatrix},\quad
K_1(c)=\begin{pmatrix}1&c-1\\0&c\end{pmatrix}.
\tag{14}
\]

For example, the first component in (13) is the sum

\[
\begin{aligned}
&-d_0D_0-w_1D_1-d_1D_2\\
&\quad-w_2\operatorname{Ad}_{T_2(b)}D_0
-d_2\operatorname{Ad}_{T_2(b)}D_1
-d_3\operatorname{Ad}_{T_2(b)T_1(c)}D_0.
\end{aligned}
\]

Substitution of (12) and (14) gives the zero matrix. Replacing `T` by
`K` and multiplying the sum by `1/2` gives the second component of
(13), using (4) and (9). These identities are polynomial/rational
identities in `A,B,Z,b,c`; they need no endpoint minor to be nonzero.

Since `[Y,delta G G^{-1}]=0`, differentiating (10) now gives

\[
\boxed{\delta X_e=0,\qquad\delta g_e=0.}
\tag{15}
\]

The scalar direction in the second component of (13) is the state
stabilizer, not an omitted endpoint constraint.

## 3. Its exact cost differential is strictly negative at the minimum

Use normalized cost `J=C/sqrt(12)`. In the notation of (2), the cost of
one vertex arc is

\[
J_i=\frac a8\left[(a+b_0)(q-1)+(a+c_0)(1-q^{-1})-a\log q\right].
\tag{16}
\]

Differentiate the sum of (16) for (11), with the initial margins (4)
fixed and the log-factor derivatives (12). The exact result is

\[
\boxed{\delta J=\frac Z4\,N,}
\tag{17}
\]

where, for `t>1`, define

\[
\eta(t)=t-1-\log t,\qquad
\zeta(t)=t\log t-t+1,
\]

and

\[
\begin{aligned}
N={}&b(b-1)A\,[Ac\eta(c)-B\zeta(c)]\\
&+(c-1)\,[bA(B+bZ)\eta(b)-B(bA+Z)\zeta(b)].
\end{aligned}
\tag{18}
\]

For a direct check of the differentiation, collecting constant,
`log b`, and `log c` terms in `4 delta J/Z` gives respectively

\[
\begin{array}{c|l}
1 &(b-1)(c-1)(bcA^2+3bAB+b^2AZ+BZ)\\
\log b&-b(c-1)((b+1)AB+bAZ+BZ)\\
\log c&-bc(b-1)A(A+B).
\end{array}
\tag{19}
\]

Expanding (18) gives the same three coefficients. The margin
derivatives at the terminal cut are all zero, consistently with (15).

We next prove `N<0` under (7). We will use the elementary strict inequalities

\[
0<\eta(t),\qquad
\frac{\zeta(t)}{\eta(t)}>\frac{2t+1}{t+2}>1\qquad(t>1).
\tag{20}
\]

The first follows from `eta(1)=0` and `eta'(t)=1-1/t>0`.
For the second, direct differentiation gives

\[
\frac{d}{dt}\left(\log t-\frac{3(t^2-1)}{t^2+4t+1}\right)
=\frac{(t-1)^4}{t(t^2+4t+1)^2}>0.
\]

The expression in parentheses vanishes at one. Multiplying its strict
positivity by `t^2+4t+1` gives

\[
(t+2)\zeta(t)-(2t+1)\eta(t)
=(t^2+4t+1)\log t-3(t^2-1)>0,
\]

which proves (20).

By (7), `B>=(2c-1)A>cA`. Consequently the first square bracket in
(18) is strictly negative by (20).

For the second bracket, set `z=Z/A>=1` and `beta=B/A`. Dividing that
bracket by `A^2` gives

\[
T(\beta,z)=b(\beta+bz)\eta(b)-\beta(b+z)\zeta(b).
\]

Its derivative in `beta` is
`b(eta(b)-zeta(b))-z zeta(b)<0`. Using (7), it therefore suffices
to put `beta=b+(b-1)z`. The resulting expression is

\[
S(z)=b[b+(2b-1)z]\eta(b)
-[b^2(1+z)+(b-1)z^2]\zeta(b).
\tag{21}
\]

The coefficient of `zeta(b)` being subtracted is positive. By (20),

\[
\begin{aligned}
S(z)
&<\frac{\eta(b)}{b+2}\left\{
b[b+(2b-1)z](b+2)
-[b^2(1+z)+(b-1)z^2](2b+1)\right\}\\
&=-\frac{(b-1)\eta(b)}{b+2}
\left[b^2+2bz(z-1)+z^2\right]<0.
\end{aligned}
\tag{22}
\]

The final sign uses only `b>1` and `z>=1`. Both square brackets
in (18) are therefore strictly negative, and hence

\[
\boxed{N<0,\qquad\delta J<0.}
\tag{23}
\]

## 4. The genuine PMP makes the same differential nonnegative

Normalize the physical maximizing cost multiplier to `lambda=-1`.
Write `xi` for the actual terminal cotangent vector at the
`1 -> 0` switch, divided by `sqrt(12)` to match cost `J`.
Transport that same cotangent vector backwards along the two actual
interior arcs. This is the given normal lift restricted to that interval.

For an infinitesimal inserted log factor `epsilon` of vertex `i` at
a strict-star state, its physical duration is
`p_i epsilon/2+O(epsilon^2)`, with `p_i>0`. The adjoint
first-variation identity therefore gives

\[
\partial_{\log q}J-\xi\,\partial_{\log q}(g_e,X_e)
=-\frac{p_i}{2\sqrt{12}}\,H_i.
\tag{24}
\]

Here `H_i` is the physical Hamiltonian at the corresponding cut;
for a variation of an active original factor it is its zero active
Hamiltonian. Changes of later physical durations caused by holding
their factors fixed add only multiples of their zero Hamiltonians.
Equivalently, the positive state-dependent vertex clock preserves
the adjoint pullback on the zero-Hamiltonian locus. This is the
cost-augmented form of the clock and endpoint identity in
GLOBAL_NORMALITY, Section 1.

The formal first and last vertex-0 factors in (11) have base value
one. Nevertheless their expressions (24) vanish: vertex 0 is active
on the actual positive arc immediately before the first cut and
immediately after the last cut. Continuity of all three vertex
Hamiltonians gives `H_0=0` at both cuts. Thus stripping those two
outer arcs loses neither a switching identity nor a cotangent condition.
Their formal negative derivatives in (12) are used only in this
zero-Hamiltonian identity. There is no assertion that (11), by itself,
is an admissible positive-duration family for nonzero `epsilon`.

The original interior factors also give zero in (24). At the two
missing-control insertions, the full Hamiltonian maximum gives
`H_i<=0`, including at a triple tie. Their expressions in (24) are
therefore nonnegative. Since `w_1,w_2>0`, taking the linear
combination (12) gives

\[
\delta J-\xi\,\delta(g_e,X_e)\ge0.
\tag{25}
\]

Equation (15) makes its endpoint term zero, contradicting (23).
This proves the local theorem (1). No endpoint-rank assertion,
implicit-function theorem, sufficient-optimality theorem, or
construction of a finite replacement is used.

## 5. Apply the minimum to the actual twisted period

Take a finite positive vertex representation of an entirely reverse
closed PMP period. Its genuine twisted extension has arc labels

\[
i_{j+1}=i_j-1\pmod3,\qquad i_{j+N}=i_j+1\pmod3.
\]

The state twist applies the same cyclic permutation to the margins.
Hence the active margin `a_j=p_(i_j)` on arc `j` satisfies

\[
a_{j+N}=a_j>0.
\tag{26}
\]

Choose an index `m` where this finite periodic sequence attains its
minimum. The four arcs `m-2,m-1,m,m+1`, cyclically relabeled, have
word `0,2,1,0`; their third active margin is no larger than any of
the other three. They contradict (1).

The four arcs may cross the terminal seam. The actual twisted state
and cotangent endpoint conditions continue the same PMP lift there,
as proved in [GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md). The local
contradiction uses necessary identities on that continued lift; it
does not splice a competitor extending beyond one period.

Every global minimizer has a finite representation under the retained
geometric, compact-state and PMP inputs, and every such minimizing
lift is normal by GLOBAL_NORMALITY. Thus none belongs to the pure
reverse case R. This argument treats all possible primary-costate
determinants together and needs no octagon budget. Pure forward and
the three mixed cases remain separate obligations.

## Validation boundary

[pure_reverse_minimum_certificate.py](../explorations/pure_reverse_minimum_certificate.py)
reproduces the endpoint identities, terminal margin derivatives,
cost coefficients, minimum-coordinate conversion, and elementary
derivative identities with exact SymPy arithmetic. All 20 checks pass
with Python 3.12.14 and SymPy 1.14.0. Its finite checks supplement the
displayed hand calculation; they are not a numerical search, an exhaustive
trajectory catalogue, or Lean kernel validation. Independent internal
reviews reconstructed the endpoint and cost algebra and checked the
positive clocks, outer-arc stripping, strict signs, and twisted minimum
placement. These reviews are not external peer review or kernel validation.
