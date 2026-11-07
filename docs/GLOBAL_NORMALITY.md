# Closed finite vertex extremals are normal

Date: 2026-11-07 (UTC). Hand proof with a supplementary exact algebra check.
No Lean, Lake, typechecking, or CI was run. This note has been self-reviewed;
it has not received independent mathematical review or kernel validation.

## Theorem and scope

Let a strict-star trajectory have a finite positive vertex representation
and the actual twisted complete-period state and frame endpoints. Suppose
it admits a nontrivial free-time Pontryagin lift with the actual twisted
state-costate endpoint condition. Then its cost multiplier is strictly
negative. In particular,

\[
\boxed{\text{every Pontryagin lift of every global minimizer is normal.}}
\]

The corollary uses the finite representation already established in
[SINGULAR_COST_BUDGET](SINGULAR_COST_BUDGET.md) and
[MEASURABLE_EDGE_PMP_BOUND](MEASURABLE_EDGE_PMP_BOUND.md). Those results
retain abnormal lifts, so this use is not circular. The normality theorem
itself needs neither the octagon cost budget nor a numerical switch bound.

This removes the abnormal alternative in the remaining global comparison.
It does not prove the sharp octagon inequality, uniqueness of a normal
multiplier, rank five on every reverse endpoint map, or affine uniqueness
of a minimizing disk. Arbitrary measurable nonclosed abnormal edge lifts
are not excluded. The latter exist in the source formulation; see
Hales--Vajjha, *Packings of Smoothed Polygons*, Remark 8.1.6.

## 1. Paired endpoint coordinates and abnormal needle inequalities

Use the triangular coordinates and exact vertex factors of
[LOCAL_L2_RANK_DROP](LOCAL_L2_RANK_DROP.md), Section 2:

\[
D_0=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad
D_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
D_2=\begin{pmatrix}1&0\\2&-1\end{pmatrix},
\]
\[
T_i(q)=e^{-(\log q)D_i}
=\frac{q+q^{-1}}2I+\frac{q^{-1}-q}{2}D_i.
\tag{1}
\]

For a chronological positive word, put

\[
F=\prod_jT_{i_j}(q_j),\qquad
G=\prod_jT_{i_j}(\sqrt{q_j}).
\]

With initial frame I and initial state X fixed, the actual endpoints are

\[
X_e=G^{-1}XG,\qquad g_e=XFX_e^{-1}.
\tag{2}
\]

For the prefixes before arc j, set

\[
t_j=\operatorname{Ad}_{F_j}D_{i_j},\qquad
l_j=\operatorname{Ad}_{G_j}D_{i_j}.
\]

Differentiation with respect to log q_j gives the paired right-trivialized
column (-t_j,-l_j/2). The projection (2) has exactly the tangent kernel

\[
\{(0,rX):r\in\mathbb R\}.
\tag{3}
\]

Indeed, the state derivative is G^{-1}[X,delta G G^{-1}]G, and the
trace-zero centralizer of the elliptic matrix X is the line R X. Once the
state derivative is zero, the frame derivative vanishes precisely when
the F derivative vanishes. Thus (2) is a submersion onto the actual
five-dimensional endpoint manifold.

Assume, towards a contradiction, that the multiplier is abnormal,
\(\lambda=0\). The actual terminal cotangent vector is nonzero, so its
pullback through (2) is a nonzero pair of linear functionals (alpha,beta).
The adjoint first-variation identity and the zero active Hamiltonians give

\[
-\alpha(t_j)-\tfrac12\beta(l_j)=0
\quad\text{for every original arc.}
\tag{4}
\]

An inserted vertex at an internal switch gives the same paired expression.
Its value is nonpositive by Hamiltonian maximization. To check the clock,
an inserted log factor epsilon has physical duration
p_i epsilon/2+O(epsilon^2), where its active margin p_i is positive.
The original factors can be kept fixed: their physical durations then
change smoothly, but their first-variation contributions are multiples of
zero active Hamiltonians. The insertion pairing is therefore p_i/2 times
the inserted physical Hamiltonian. Its sign and its vanishing are exactly
the required PMP sign and tie tests.

These statements also follow by rescaling a Hamiltonian vector field by
its positive vertex clock on its zero level. No optimality of a replacement
trajectory is asserted here. Only necessary identities of the given lift
are being used.

For a four-arc word beginning in label 0, conjugate the two paired blocks
by the inverses of their first factors. D_0 commutes with those factors.
Thus the first factor may be set to 1 in all the column calculations.
The state in (3) must be transformed at the same time: it becomes the
actual state Y just after the first arc. Write its positive margins as
(p_0,p_1,p_2), so

\[
Y=\frac12\begin{pmatrix}-p_0&p_0+p_2\\-p_0-p_1&p_0\end{pmatrix},
\quad p_i>0,\quad p_0p_1+p_1p_2+p_2p_0=4.
\tag{5}
\]

All matrix-coordinate vectors below use (M_00,M_01,M_10). Write b>1 and
c>1 for the second and third factors. The first and fourth positive
factors are arbitrary and do not enter the reduced calculation.

If the first three labels are distinct, their upper columns are independent.
Let L send these three upper columns to their corresponding lower columns.
Set n=-beta/2. Equation (4) gives alpha=nL, and every column or needle
pairs as

\[
n(l-Lt),\qquad n(Y)=0,\qquad n\ne0.
\tag{6}
\]

The last assertion follows because n=0 would give beta=alpha=0. The fourth
original arc imposes n(U)=0, where U=l_4-Lt_4. A missing-control needle at
either of the first two switches imposes n(r_j)<=0.

## 2. Exact four-arc algebra

All entries in this section follow by multiplying the matrices in (1).
For convenient hand verification, scalar factors may be removed inside
conjugations, and one can use

\[
\sqrt q\,T_i(\sqrt q)=\frac{q+1}{2}I+\frac{1-q}{2}D_i.
\tag{7}
\]

For P=((r,s),(t,u)), a useful additional identity is

\[
\operatorname{Ad}_P D_0
=\frac1{\det P}
\begin{pmatrix}-(ru+st)&2rs\\-2tu&ru+st\end{pmatrix}.
\tag{8}
\]

### 2.1 Forward first triple 012

The upper three-column determinant is 4b^2, and

\[
L_f(x,y,z)=\left(x-\frac{b-1}{b}z,
                 y+\frac{b-1}{b}z,\frac zb\right).
\]

The missing needles at 0 to 1 and 1 to 2, respectively, have residuals

\[
r^f_1=\frac{2(b-1)}b(1,-1,1),\qquad
r^f_2=(0,-2(b-1)/b^2,0).
\tag{9}
\]

For the fourth label 0, the fourth residual is

\[
U_f=\left(
-2c(b-1)(c-1),\quad
\frac{2c(b-1)}{b^2}[b(b-1)(c-1)-c],\quad
-2bc(c-1)\right).
\tag{10}
\]

For the fourth label 1 instead, it is

\[
U_{0121}=\frac{b^2(c-1)}{c^2(b-1)}r^f_1.
\tag{11}
\]

### 2.2 Reverse first triple 021

The upper three-column determinant is -4/b^2, and

\[
L_r(x,y,z)=(x+(1-b)y,by,z+(1-b)y).
\]

The missing needles at 0 to 2 and 2 to 1 have residuals

\[
r^r_1=2(b-1)(-1,1,-1),\qquad
r^r_2=(0,0,-2b(b-1)).
\tag{12}
\]

For the fourth label 0, the fourth residual is

\[
U_r=-\frac2{bc^2}\left(
(b-1)(c-1),\quad c-1,\quad
(b-1)[(c-1)+b(b-c+1)]\right).
\tag{13}
\]

For a direct check of (13), the upper and lower prefixes before that
fourth arc, up to scalar multiples, are

\[
\begin{pmatrix}1&c^2-1\\1-b^2&b^2+c^2-1\end{pmatrix},\qquad
\begin{pmatrix}1&c-1\\1-b&b+c-1\end{pmatrix}.
\]

Insert them in (8) and subtract L_r of the upper conjugate from the lower
one. For the fourth label 2 instead, the same recipe gives

\[
U_{0212}=\frac{c(c-1)}{b(b-1)}r^r_1.
\tag{14}
\]

Equations (11) and (14) are rational identities valid also for b,c>0
with b,c not equal to 1. This extended algebraic domain will be used only
for reading zero identities backwards, not for asserting admissibility of
negative-time competitors.

## 3. An abnormal lift cannot contain 0120 or 0210

Put n_*=Y_coord cross U, using the ordinary cross product of the three
coordinate vectors. It annihilates Y and U. The following explicit pairings
both show that n_* is nonzero and give opposite strict signs.

For 0120, set

\[
S_f=(c-1)[b^2(p_1+p_2)-p_1]+(b-1)p_1>0.
\]

Expansion of (5), (9), and (10) gives

\[
n_*(r^f_1)=-\frac{2c(b-1)}{b^3}S_f<0,
\]
\[
n_*(r^f_2)=\frac{2c(b-1)(c-1)}{b^2}
                    [p_0-(b-1)p_1]>0.
\tag{15}
\]

For the second sign, the second arc has label 1, and strict star at its
end requires (p_0-(b-1)p_1)/b>0. The first sign uses only p_i>0 and b,c>1.

For 0210, set

\[
S_r=(c-1)[p_1-(b-1)p_2]+b(b-1)p_2>0.
\]

Here strict star after the second arc, of label 2, requires
(p_1-(b-1)p_2)/b>0. Expanding (5), (12), and (13) gives

\[
n_*(r^r_1)=\frac{2(b-1)}{c^2}S_r>0,
\]
\[
n_*(r^r_2)=-\frac{2(b-1)(c-1)}{c^2}
                      [bp_0+(b-1)p_2]<0.
\tag{16}
\]

In each case Y and U are independent. Every n in (6) that annihilates U
is therefore a nonzero scalar multiple of n_*. Neither choice of sign for
that scalar makes both displayed pairings nonpositive. This contradicts
the two necessary needle inequalities. Consequently,

\[
\boxed{0120\text{ and }0210\text{ cannot occur on an abnormal lift}.}
\tag{17}
\]

Cyclic relabeling preserves this conclusion. In switch-sign language,
no three consecutive signs can all be + or all be -.

There is also a short scalar check of the reverse sign contradiction.
Set A=-n_x+n_y-n_z, B=-n_z, C=n_y. The two needle inequalities say A<=0,
B<=0. Equation n(U_r)=0 gives

\[
C=\frac{b-1}{b}A+
  \frac{(b-1)(b-c+1)}{c-1}B.
\]

The state equation 2n(Y)=Ap_0+Bp_1+Cp_2=0 becomes

\[
A\left[p_0+\frac{b-1}{b}p_2\right]+
B\left[p_1-(b-1)p_2+
        \frac{b(b-1)}{c-1}p_2\right]=0.
\]

Both brackets are strictly positive. Thus A=B=C=0, hence n=0, a
contradiction. This verifies (16)'s implication without a sign choice
for the cross product.

## 4. Two adjacent equal signs next to the opposite sign force a triple tie

In 0121 or 0212, equation (11) or (14) and n(U)=0 force n(r_1)=0.
The two neighboring active Hamiltonians already vanish at that first
switch; the missing vertex Hamiltonian now vanishes too. Thus all three
vertices tie there. In signs:

\[
++-\text{ or }--+\quad\Longrightarrow\quad
\text{the first switch is a triple tie.}
\tag{18}
\]

We also need the backwards version, but do not reverse the maximum
principle. The identities proving (18) use only the vanishing of active
Hamiltonians, the cotangent constraint, and invertible vertex flows.
Read a given four-arc solution backwards with factors q_j^{-1} in reversed
order. Its adjoint transports backwards as well and still annihilates
all the active duration columns. Equations (11) and (14) remain valid
because their internal factors are positive and different from 1. They
force vanishing of the corresponding missing pairing. Vanishing is
unaffected by reversing a clock or multiplying it by a nonzero factor.
No backwards Hamiltonian inequality is asserted or needed.

For explicit label checks, 0102 reverses to 2010, which cyclically relabels
to 0121; 0201 reverses to 1020, which cyclically relabels to 0212.
Consequently

\[
-++\text{ or }+--\quad\Longrightarrow\quad
\text{the last switch is a triple tie.}
\tag{19}
\]

Triple ties are permitted in (18)-(19); they are not discarded as generic
exceptions. The next lemma controls exactly the configuration needed.

## 5. No positive vertex arc joins two triple ties in an abnormal lift

Rebase a single positive arc and cyclically relabel it to control 0. Let
its factor be q>1 and its initial state be Y from (5). At a triple tie at
its initial time, the three initial needle columns have l=t=D_i.
The three D_i span the trace-zero matrices. Hence the abnormal endpoint
functional has the form n(l-t), with n(Y)=0 and n nonzero, by the same
argument as (6), now with L the identity.

At its terminal time, the residuals for the two other vertices are

\[
\operatorname{Ad}_{T_0(\sqrt q)}D_1-
\operatorname{Ad}_{T_0(q)}D_1=(0,2q(q-1),0),
\]
\[
\operatorname{Ad}_{T_0(\sqrt q)}D_2-
\operatorname{Ad}_{T_0(q)}D_2=(0,0,2(q-1)/q^2).
\tag{20}
\]

A terminal triple tie makes both pairings zero. Their nonzero coefficients
force n_y=n_z=0. Equation (5) then gives n(Y)=-p_0 n_x/2=0, so n_x=0.
This contradicts nontriviality. Thus such a positive arc does not exist.

## 6. The twisted period gives the global contradiction

Take a finite positive vertex representation of the supposed abnormal
closed lift. The genuine twisted extension in
[GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md), Section 3, continues the
same state and cotangent trajectory across every seam. After merging equal
neighbors, choose the period cut at a genuine switch. The bi-infinite
arc labels satisfy

\[
i_{j+N}=i_j+1\pmod3,
\qquad i_{j+1}\ne i_j.
\tag{21}
\]

There is at least one switch: a globally constant vertex label cannot
satisfy the twist. Set s_j=+ when the label increases by one and s_j=-
when it decreases by one, modulo three. The signs are N-periodic.

By (17), no three consecutive signs are equal. Suppose two consecutive
signs s_j=s_{j+1}=sigma were equal. Both neighboring signs must then be
-sigma. The right-hand pattern sigma,sigma,-sigma makes switch j a
triple tie by (18). The left-hand pattern -sigma,sigma,sigma makes switch
j+1 a triple tie by (19). Those adjacent switches bound a positive vertex
arc, contradicting Section 5.

Therefore the signs alternate everywhere. It follows that i_{j+2}=i_j:
the entire extended trajectory uses exactly two labels. But (21) makes its
set of labels invariant under addition of 1 modulo three, which no
two-element subset of {0,1,2} satisfies. This is the final contradiction.

The four-arc tests may cross one or several period seams. This is legitimate
because they use only necessary PMP identities on the genuine extended
lift. They do not splice a multi-period cheaper competitor or assume that
several periods together are minimizing. Thus shorter fundamental periods
are included, including the four-piece octagon.

The cost multiplier satisfies lambda<=0 in the maximizing convention;
excluding lambda=0 proves lambda<0. Positive homogeneous rescaling therefore
permits lambda=-1 on every global minimizing lift.

## 7. Validation and remaining task

The hand proof consists of the exact endpoint/covector interface, the finite
matrix identities (9)-(16), the two triple-tie implications, and the run
argument. The supplementary script
[abnormal_normality_certificate.py](../explorations/abnormal_normality_certificate.py)
recomputes 22 rational identities from the three matrices (1). It passed
with Python 3.13.5 and SymPy 1.14.0. The script uses no samples, numerical
optimization, trajectory integration, or growing word enumeration. It does
not independently check the PMP interpretation, the positivity deductions,
the backwards-flow argument, or the combinatorial theorem.

The physical PMP and endpoint conventions are the ones derived in
GLOBAL_PERIODIC_PMP, following Hales--Vajjha Sections 6.2 and 6.6:
https://arxiv.org/html/2405.04331v1#Ch6.S2
The matrix flow and endpoint identities are retained repository inputs.
All additional arguments are displayed above; no new external optimality
theorem is imported.

This is a new hand-proof result in the branch, not a claim of novelty
relative to all literature. Self-review and exact algebraic reproduction
are not independent review, external peer review, or kernel validation.

The sharp global comparison and affine equality remain open. Normality
removes an entire multiplier regime, not all normal competitors. In
particular the full asymmetric normal reverse domain is not excluded, and
normality must not be silently replaced by uniqueness or full endpoint rank.
