# Active-margin minimum principles exclude every long reverse run

Date: 2026-11-07 UTC. Hand proof with an
[independent internal audit](MIXED_GLOBAL_MINIMUM_STRUCTURE_AUDIT.md).
No Lean, Lake, typechecking, or CI.

## Results and scope

1. Reflection combined with reversal of time is an exact symmetry of
   the actual Reinhardt state, cost, and Pontryagin equations. It preserves
   the physical cost multiplier and all Hamiltonian inequalities. This is
   stronger than formally reading a control word backwards.
2. The reverse-four theorem in
   [GLOBAL_REVERSE_PERIOD_EXCLUSION](GLOBAL_REVERSE_PERIOD_EXCLUSION.md)
   consequently forbids a four-arc minimum in **either interior position**
   of a normal strict-star `0210` window.
3. On any three positive normal PMP arcs `i,j,i`, the active margins
   satisfy strict log-concavity, `a_1^2>a_0a_2`. In particular the
   middle margin cannot be a minimum of the three. Its proof
   restricts the **same actual normal covector** to the two-control edge;
   it does not choose a new multiplier for an auxiliary edge problem.
4. In a finite normal strict-star mixed period, **every maximal run of
   reverse switches has exactly two switches**. Runs of length one and
   every length at least three are impossible. In particular the entire
   mixed case M3, containing the sign pattern `---++`, is excluded.
5. Each surviving two-switch reverse run has a strict middle
   active-margin minimum in its five-arc `01020` window. At a global
   active-margin minimum the four neighboring switch signs are therefore
   `++++` or `+--+`.

These are full-domain necessary conditions, with arbitrary unequal
positive factors and without a transverse-switch assumption, endpoint-rank
assumption, Casimir-sector restriction, or cost budget. Global normality
and the established finite representation apply them to every minimizing
period. They close **M3**, in addition to the independently established
pure-reverse exclusion R. The pure-forward case F and mixed cases M1/M2
remain open. A local `01020` minimum is compatible with normal PMP;
Section 8 states that limitation explicitly.

## 1. A reflection that restores the positive control system

Use the original physical matrices

\[
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad
R=e^{\pi J/3},\quad S=\begin{pmatrix}1&0\\0&-1\end{pmatrix},
\qquad S^2=I.
\]

Let `rho` fix label 0 and exchange labels 1 and 2, equivalently
`rho(i)=-i mod 3`. The three actual vertex matrices satisfy

\[
SJS=-J,\qquad SZ_iS=-Z_{\rho(i)}.
\tag{1}
\]

For any trajectory on `[0,T]`, first normalize its initial frame to
`I` if necessary, and define

\[
\widetilde g(t)=Sg(T)^{-1}g(T-t)S,\qquad
\widetilde X(t)=-SX(T-t)S,\qquad
\widetilde u_i(t)=u_{\rho(i)}(T-t).
\tag{2}
\]

For `X=Phi(x,y)`, one has `-SXS=Phi(-x,y)`, so strict star is
preserved. If `P=Z_u/tr(Z_u X)`, equations (1)--(2) give

\[
\widetilde P(t)=-SP(T-t)S.
\tag{3}
\]

The trace denominator is unchanged, and `u -> u_tilde` is a permutation
of the same positive simplex. Direct differentiation now gives

\[
\widetilde g'=\widetilde g\widetilde X,
\qquad
\widetilde X'=[\widetilde P,\widetilde X].
\tag{4}
\]

Both signs in the state commutator change together. Also
`tr(J X_tilde)=tr(J X(T-t))`, so the positive physical cost density
and its total integral are preserved.

The reversal in (2) by itself would give the wrong vector-field sign.
Equations (1)--(4) show why the additional reflection produces an
ordinary trajectory of the original admissible control system.

## 2. The actual cotangent transformation and the maximum principle

Transport the same cost multiplier `lambda<=0`, and define

\[
\widetilde\Lambda_1(t)=-S\Lambda_1(T-t)S,
\qquad
\widetilde\Lambda_R(t)=-S\Lambda_R(T-t)S.
\tag{5}
\]

Equivalently an ambient state-covector representative transforms as
`Lambda_2_tilde=S Lambda_2(T-t) S`. Its commutator with `X_tilde`
is exactly the second formula in (5), so this is the correct transformed
cotangent class, not an added normal component. The reduced constraint
`tr(Lambda_R X)=0` is preserved.

In the physical maximizing convention,

\[
H_i=\operatorname{tr}\bigl((\Lambda_1-\tfrac32\lambda J)X\bigr)
     -\operatorname{tr}(\Lambda_RP_i).
\]

Equations (1), (3), and (5) give

\[
\widetilde H_{\rho(i)}(t)=H_i(T-t).
\tag{6}
\]

Thus zero active Hamiltonians, all simplex maximum inequalities,
nontriviality, and normality are preserved. In particular the physical
normalization `lambda=-1` does not change sign.

The adjoint equations are preserved as well. For the primary costate,

\[
\widetilde\Lambda_1'
=S[\Lambda_1,X]S
=[\widetilde\Lambda_1,\widetilde X].
\]

Substitution in the reduced state-covector equation

\[
\Lambda_R'=[P,\Lambda_R]
-\operatorname{tr}(\Lambda_RP)[P,X]
+[-\Lambda_1+\tfrac32\lambda J,X]
\tag{7}
\]

gives the same formula with tildes. Each commutator has two reflected
minus signs, and `tr(Lambda_R P)` is unchanged. This checks the
Hamiltonian flow as well as its pointwise maximum inequalities.

Another way to describe the sign in (5) is to take the cotangent lift
of the state diffeomorphism in (2) and then negate the cotangent vector
when reversing time. Negating the cost multiplier as well would be
incorrect; the running cost remains positive.

## 3. Complete twisted endpoints and active margins

If the original trajectory has the actual closed endpoints, then
`g(T)=R` and `S R^{-1}S=R` give

\[
\widetilde g(0)=I,\qquad\widetilde g(T)=R.
\]

Using `X(T)=R^{-1}X(0)R` in (2) yields

\[
\widetilde X(T)=R^{-1}\widetilde X(0)R.
\tag{8}
\]

The identical calculation with each matrix in (5) gives

\[
\widetilde\Lambda_R(T)=R^{-1}\widetilde\Lambda_R(0)R,
\quad
\widetilde\Lambda_1(T)=R^{-1}\widetilde\Lambda_1(0)R.
\tag{9}
\]

Therefore free-initial-state transversality is retained, rather than
replaced by unrelated fixed state endpoints. The transformed control
problem has the same cost and the same complete-period admissibility
conditions. Its transformation is invertible, so a minimizing trajectory
is also sent to a minimizing trajectory.

The physical margins obey

\[
p_0(-SXS)=p_0(X),\qquad
p_1(-SXS)=p_2(X),\qquad p_2(-SXS)=p_1(X).
\tag{10}
\]

Hence the constant active margins are merely reversed in order. No
scale factor or sign is introduced. If `epsilon_i` is the cyclic
switch sign after arc `i`, reversing the chronology changes its sign,
and `rho(i)=-i` changes it back. The sign sequence is therefore
**read in reverse order without negating its signs**. A purely reverse
sequence remains purely reverse.

## 4. Both interior positions in a reverse-four window

The known reverse-four theorem forbids

\[
a_2\le\min(a_0,a_1,a_3)
\]

for four positive normal strict-star PMP arcs with word `0210`.
Apply (2)--(7) to that local window, where its terminal frame need not
be `R`. The reversed labels are `0120`, and applying `rho` restores
`0210`. Its active margins are `(a_3,a_2,a_1,a_0)`.

The same theorem therefore also forbids

\[
a_1\le\min(a_0,a_2,a_3).
\tag{11}
\]

This argument uses an actual transformed PMP lift on the local window.
It does not assume that a time-reversed control is admissible, or borrow
Hamiltonian inequalities from the wrong time orientation. Equal margins,
triple ties, and nontransverse switches remain covered by the original
necessary-PMP theorem.

## 5. A middle minimum is impossible on three alternating arcs

**Three-arc strict log-concavity lemma.** Suppose three positive
strict-star arcs of a normal free-time PMP trajectory have labels
`i,j,i`, with `i!=j`. Their constant active margins satisfy

\[
\boxed{a_1^2>a_0a_2.}
\tag{12}
\]

In particular the middle active margin cannot be no greater than both
outer active margins.

Here the arcs may be portions of longer arcs. Only their positive lengths,
the two joining ties, and the same actual normal PMP lift are used.

By a cyclic rotation the two labels can be taken to be 1 and 2. Work in
the original physical coordinates

\[
q=1/\sqrt3,\qquad
X=\Phi(x,y)=\frac1y
\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix},
\quad -q<x<q,\quad y>0,\quad x^2+y^2>q^2.
\]

On either vertex 1 or vertex 2, `dx/dt=y>0`. Introduce the positive
clock `d tau=y dt`, set `w=y^-2`, and use the shear frame

\[
\mathcal F=gK(x),\qquad
K(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}.
\]

The physical equations, derived in
[LOCAL_REVERSE_SIX_OBSTRUCTION, Section 2](LOCAL_REVERSE_SIX_OBSTRUCTION.md#2-exact-third-control-needle-signs-on-the-core),
give on these two vertices

\[
x_\tau=1,\qquad
w_\tau=b_i(x)w,\qquad
\mathcal F_\tau=\mathcal F wE_{21},
\quad b_1=\frac2{q-x},\quad b_2=-\frac2{q+x}.
\tag{13}
\]

The scaled physical cost `mathcal A=(2/3)C` has density
`mathcal L=1+(1+x^2)w` in this clock. Transform the **given** physical
normal maximizing covector by the shear state diffeomorphism and the
positive clock, and multiply its cotangent coordinates by `-2/3`.
It is then the minimizing covector with normal running-cost coefficient
one for `mathcal A`. The zero active Hamiltonian is preserved by the
clock change; its adjoint equations acquire no extra term on that
zero-Hamiltonian locus. Thus this construction does not replace the
full-system PMP lift by a separately obtained edge lift.

Let `p_x,p_w` be its scalar covector coordinates and `M` its group
covector. Write `m=<M,E_21>`. Along either field in (13), the group
adjoint equation gives

\[
m'=0,
\]

since the group velocity is a multiple of `E_21` and
`[E_21,E_21]=0`. The covector is continuous at a switch, so **one
constant** `m`, and hence one constant `mu=-1-m`, applies throughout
all three arcs. With primes now denoting the increasing `x` clock,
the two minimizing Hamiltonians are

\[
\mathcal H_i=1+(1+x^2)w+p_x+b_i(x)wp_w+mw,
\]

and their exact adjoint and comparison equations are

\[
p_w'=\mu-x^2-b_i(x)p_w,\qquad
\mathcal H_2-\mathcal H_1=-(b_1-b_2)wp_w,
\quad (b_1-b_2)w>0.
\tag{14}
\]

In particular, minimizing vertex 1 requires `p_w<=0`, and minimizing
vertex 2 requires `p_w>=0`. At each joining tie `p_w=0`. Equation (14)
has the same limiting right side `mu-x^2` from both incident arcs at
a tie, so `p_w` is differentiable there even when the switch is
nontransverse.

The physical margins have the ratio

\[
\frac{p_1(X)}{p_2(X)}=\frac{q-x}{q+x}.
\tag{15}
\]

For the word `1,2,1`, write `s<t` for its two switch abscissas and
`A>0` for the middle constant margin `p_2`. At the two switches the
outer active margins are respectively

\[
A\frac{q-s}{q+s},\qquad A\frac{q-t}{q+t}.
\]

The sign changes required by (14) give

\[
p_w'(s)=\mu-s^2\ge0,
\qquad p_w'(t)=\mu-t^2\le0.
\]

Thus `s^2<=mu<=t^2`, and hence `s+t>=0` since `s<t`. Equality would
force `t=-s` and `mu=s^2`. Choose a positive integrating factor `rho`
for the middle equation in (14), so `rho'=b_2 rho`. Then

\[
(\rho p_w)'=\rho(\mu-x^2)>0\qquad(s<x<t).
\]

This contradicts `p_w(s)=p_w(t)=0`. Consequently `s+t>0`, and

\[
\frac{a_0a_2}{A^2}
=\frac{(q-s)(q-t)}{(q+s)(q+t)}<1,
\]

because the denominator minus the numerator is `2q(s+t)>0`.

For the word `2,1,2`, the ratios in (15) are inverted. The required
sign changes give

\[
p_w'(s)=\mu-s^2\le0,
\qquad p_w'(t)=\mu-t^2\ge0,
\]

Thus `t^2<=mu<=s^2`, so `s+t<=0`. The same integrating-factor
argument, now with `rho'=b_1 rho`, excludes equality. Hence `s+t<0`
and

\[
\frac{a_0a_2}{A^2}
=\frac{(q+s)(q+t)}{(q-s)(q-t)}<1.
\]

This proves (12) in both orientations. The weak derivative inequalities
retain zero derivatives, cubic contacts, and triple ties. No strict
crossing hypothesis is used. The strict product inequality is stronger
than the middle-minimum prohibition needed below.

## 6. Every bounded reverse run has exactly two switches

Write `epsilon_i=+` when the switch after arc `i` advances its label
by one modulo three and `epsilon_i=-` when it decreases that label by
one. Let `a_i>0` be the constant active margin on arc `i`, and let
`q_i>1` be its vertex factor. A direct feasibility rule from the
margin update gives

\[
\begin{array}{c|c|c}
(\epsilon_{i-1},\epsilon_i)&q_i&\text{strict consequence}\\ \hline
(-,+)&(a_i+a_{i+1})/(a_i+a_{i-1})&a_{i+1}>a_{i-1}\\
(+,-)&(a_i+a_{i-1})/(a_i+a_{i+1})&a_{i+1}<a_{i-1}.
\end{array}
\tag{16}
\]

In the first row the repeated neighboring control is the growing
margin on arc `i`; in the second row it is the decreasing margin.
All denominators are positive.

Consider a maximal reverse run of length `L>=1` bounded by forward
switches. Index its switches as

\[
\epsilon_{-1}=+,\qquad
\epsilon_0=\cdots=\epsilon_{L-1}=-,\qquad
\epsilon_L=+.
\tag{17}
\]

Its arcs are indexed `0,...,L`, with surrounding arcs `-1,L+1`.
Take a minimum of the finite list `a_0,...,a_L`.

It cannot occur at arc 0. If it did, `a_0<=a_1`; the second row of
(16) at arc 0 gives `a_1<a_-1`. Thus
`a_0<=min(a_-1,a_1)`. The three arcs `-1,0,1` have labels `i,j,i`,
contradicting Section 5. The minimum likewise cannot occur at arc `L`:
the first row of (16) at that arc gives `a_(L+1)>a_(L-1)`, and a
run minimum there would give
`a_L<=min(a_(L-1),a_(L+1))`, the same contradiction.

If `L=1`, every entry is one of these two impossible endpoints. So a
single reverse switch bounded by forward switches is impossible; this
also excludes the local sign pattern `+-+` directly from normal PMP.

Suppose `L>=3`. Every interior arc of `0,...,L` is an interior arc of
some four consecutive arcs wholly within that list. Indeed arc 1 is
second in `0,1,2,3`, and each arc `j` with `2<=j<=L-1` is third in
`j-2,j-1,j,j+1`. All three switches of each chosen four-arc window
are reverse. If that interior arc were a minimum of the whole run,
it would be no greater than all three other margins in the chosen
window, contradicting one of the two reverse-four principles in
Section 4. This also excludes the possibility of equal run minima.

The only possible length is therefore

\[
\boxed{L=2.}
\tag{18}
\]

In this case the minimum must occur at the sole interior arc 1, and
the endpoint arguments show that it is strict:

\[
a_1<a_0,\quad a_1<a_2.
\]

The entry and exit consequences in (16) add
`a_1<a_-1` and `a_1<a_3`. Consequently every such run has the
five-arc sign and margin pattern

\[
\boxed{+--+,\quad\text{labels }01020\text{ up to rotation},\quad
a_1<\min(a_{-1},a_0,a_2,a_3).}
\tag{19}
\]

The middle arc in this five-arc display is arc 1. The notation in (19)
does not assert a forbidden local minimum: it describes the necessary
form of every surviving reverse run.

## 7. Apply the run theorem to actual twisted periods: M3 is excluded

Take a finite positive normal strict-star period with its actual state,
frame, and costate twists, after merging equal adjacent controls across
the seam. Its active margins and switch signs form finite periodic
sequences: the seam permutes all three labels and all three margins
together, so it changes neither an active value nor a switch direction.
The same PMP lift continues across that seam by
[GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md).

An entirely reverse period is already impossible by
[GLOBAL_REVERSE_PERIOD_EXCLUSION](GLOBAL_REVERSE_PERIOD_EXCLUSION.md).
In a mixed period each maximal reverse run is finite and bounded by
forward switches. Section 6 therefore applies to every such run,
including one crossing the chosen seam, and proves that all of them
have length exactly two.

In particular no such period contains `---`. The mixed template M3
in [FINITE_CASE_COMPUTER_ROADMAP](FINITE_CASE_COMPUTER_ROADMAP.md) has
signs `---++` and labels `021012`. Its reverse part would lie in a
maximal run of length at least three, which is impossible. This is a
uniform exclusion of **the whole M3 domain**, with arbitrary unequal
positive factors and every costate sector. It uses the same full lift
throughout and needs no uniform lower bound on an individual factor.
Normality of every minimizing finite lift, proved in
[GLOBAL_NORMALITY](GLOBAL_NORMALITY.md), removes the abnormal
alternative for the global minimizing application.

The argument uses local necessary-PMP identities on a continued
trajectory. It never splices a comparison path longer than one period,
so a run or four-arc window spanning the seam, or more than one chosen
short period, causes no replacement or geometric-eligibility issue.
Finite representation and global normality enter only at the stated
complete-minimizer interface.

For completeness, choose an arc indexed 0 that minimizes the entire
periodic active-margin sequence. Write the four neighboring signs as
`(epsilon_-2,epsilon_-1,epsilon_0,epsilon_1)`. Formula (16) at arc
`-1` excludes the left pair `(-,+)`, and at arc 1 excludes the right
pair `(+,-)`. Section 5 at arc 0 excludes either central opposite
pair. Section 4 excludes `---` in either consecutive triple. The
only remaining patterns are

| Four signs | Five labels, starting at 0 | Minimum location |
|---|---|---|
| ++++ | 01201 | third arc |
| +--+ | 01020 | third arc, strict among these five |

The table is a fixed consequence of the displayed inequalities, not
an enumeration of complete words. The run theorem is stronger for the
mixed application: it applies to a minimum within each reverse run,
even if the global minimum lies inside a forward run.

## 8. Remaining cases and the precise local limitation

The surviving mixed periods have reverse runs of length exactly two,
separated by nonempty forward runs. A separating forward run of length
one gives the M1 pattern `--+--`; a forward run of length at least two
gives M2's `+--++` near a neighboring double reverse run. Neither M1
nor M2 is excluded by the minimum principles here. The all-forward
case F also remains a separate obligation.

The strict middle minimum in (19) alone gives no further local PMP
contradiction. The already certified local normal witness in
[MIXED_GLOBAL_SHORT_PAD_OBSTRUCTION](MIXED_GLOBAL_SHORT_PAD_OBSTRUCTION.md)
contains a positive `01020` subwindow, up to cyclic relabeling, whose
middle active margin is strictly below all four others. Its last arc
has a proved positive germ; complete continuation, geometric sector
eligibility, and complete-period closure were not asserted for that
witness. Thus it does not obstruct the global conjecture or a theorem
using those extra conditions, but it does rule out excluding (19)
solely from the local normal PMP inequalities and active-margin order.

A valid next argument must use additional complete-period continuation,
geometry, cost, or a necessary higher-order minimizing condition. If it
uses a constrained variation, it must retain both actual endpoint
constraints and the endpoint-curvature term; an unconstrained action
derivative or a differential-kernel vector alone is insufficient.

## Validation boundary

The reflection identities, common-covector edge equations, and finite
minimum argument above are hand calculations. The reverse-four input has
its own [independent internal audit](GLOBAL_REVERSE_PERIOD_EXCLUSION_AUDIT.md)
and supplementary 20-identity exact checker. The three-arc argument
does not use the separate auxiliary edge multiplier of
MEASURABLE_EDGE_PMP_BOUND. No numerical sample, word-length catalogue,
endpoint-rank claim, or sufficient-optimality theorem enters this proof.
Independent internal review remains distinct from external peer review
and Lean kernel validation.
