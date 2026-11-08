# Exact elimination of every mixed turn block

Date: 2026-11-07 UTC. Hand congruences for the actual scalar dual
Hessian. No Lean, Lake, typechecking, or CI.

## Result and scope

Use the actual finite normal geometric period after the reverse-run
classification. Let \(m\) be its number of double reverse runs,
\(N\) its number of arcs, \(P=N-2m\), and
\(n=(N-m-1)/3\). The sign changes occur at exactly \(2m\) turn
arcs. In the scalar dual Hessian of
[MIXED_GLOBAL_SCALAR_DUAL](MIXED_GLOBAL_SCALAR_DUAL.md), the principal
block on their physical and auxiliary margin variables is invertible
with inertia

\[
\boxed{(n_+,n_0,n_-)=(2m,0,2m).}
\tag{1}
\]

The proof covers isolated turns, adjacent turn pairs, and zero bridge
diagonals. It uses no assumption that all forward runs have length one.
Eliminating this block leaves an explicit \((2P+1)\)-dimensional
symmetric form \(\mathcal S\), on the remaining physical/auxiliary
variables and the Casimir variable. For the full-rank domain \(N\ge6\),

\[
\boxed{\operatorname{ind}_-(Q_{\rm closed})
=\operatorname{ind}_-(\mathcal S)-k-3,\qquad k=n-m.}
\tag{2}
\]

In particular the baseline bound \(\operatorname{ind}_-Q_{\rm closed}
\ge-k-3\) agrees with the already proved phase-density bound. It is
not an additional excluded family. The purpose here is the exact
remaining matrix: equations (9) and (15) below retain its local
couplings and its Casimir variable. Its needed extra negative index
remains unproved.

## 1. Common normalization and edge expansion

Write \(a_i>0\) for the physical active margins, \(b_i\in\mathbb R\)
for the auxiliary variables, and \(\gamma=\sqrt{\det U}>0\).
Set

\[
s_i=a_i+a_{i+1},\quad t_i=b_i+b_{i+1}>0,\quad K_i=a_i^2+4,
\quad\delta_i=(\epsilon_{i-1}+\epsilon_i)/2,
\]
\[
d_i=\frac{\gamma t_i}{2s_i^2},\qquad
\beta_i=\epsilon_i(2d_i-j_i)>0,
\quad j_i=\frac{a_i^2+a_i a_{i+1}+a_{i+1}^2}{4s_i^2}.
\]

Use variations \(v_i=\delta a_i\), \(w_i=\delta b_i\), and
\(\zeta=\delta\gamma/\gamma\). At the actual critical point,
use \(\nabla J=\gamma B(a)b\) in the physical diagonal. Direct
completion of the fixed-\(\gamma\) scalar Hessian then gives the edge contributions

\[
\mathcal E_i=
\frac{\gamma\epsilon_i}{2t_i}
\left[w_i+w_{i+1}-\frac{2t_i}{s_i}(v_i+v_{i+1})\right]^2
+\beta_i a_i a_{i+1}
\left(\frac{v_i}{a_i}-\frac{v_{i+1}}{a_{i+1}}\right)^2,
\tag{3}
\]

and the onsite contributions

\[
\mathcal N_i=\delta_i\left[
-\frac{\gamma b_i}{b_i^2+4}w_i^2
+\frac{4\gamma a_i}{K_i}v_iw_i
-\frac{4\gamma b_i a_i^2+8}{K_i^2}v_i^2\right].
\tag{4}
\]

The remaining Casimir terms are exactly
\(-2\zeta\sum_i J_{a_i}v_i\); there is initially no
\(\zeta^2\) term. These expressions are the full scalar dual
Hessian, not the constrained cost Hessian with its endpoint curvature
discarded. At a turn \(\delta_i=0\), and the two incident switch
norms are the same positive number \(\nu\).

After every reverse run has length two, connected components of turn
indices contain either one or two indices. A pair occurs precisely
at a forward run of length one. Different components have no mutual
principal-block coupling, since the scalar Hessian only joins adjacent
indices.

## 2. An isolated turn and its exact remaining edge

Let \((a,b,d)\) be its physical neighbouring margins, with the turn
at \(b\). Put \(s=a+b\), \(t=b+d\), and let its outgoing switch
sign be \(\epsilon\); the incoming sign is \(-\epsilon\).
Positive duration gives \(\epsilon(t-s)>0\). Let \(\nu\) be the
common incident norm and \(\beta_L,\beta_R>0\) the two switching
coefficients. The physical diagonal is

\[
A=\frac{\beta_La+\beta_Rd}{b}>0.
\]

The auxiliary diagonal and physical/auxiliary entry are

\[
D_{\rm aux}=\frac{\gamma^2\epsilon}{4\nu}
\left(\frac1{t^2}-\frac1{s^2}\right)<0,
\qquad B=-\gamma\epsilon\left(\frac1t-\frac1s\right).
\tag{5}
\]

Thus the principal matrix \(\left(\begin{smallmatrix}A&B\\B&D_{\rm aux}
\end{smallmatrix}\right)\) has one positive and one negative
eigenvalue. This follows from the strictly negative determinant,
without dividing by the mixed entry.

Here is a convenient formula retaining both neighbouring nodes and
\(\zeta\). Define

\[
q_a=w_a-\frac{4\nu s}{\gamma}v_a,
\qquad q_d=w_d-\frac{4\nu t}{\gamma}v_d,
\quad q=q_a-q_d,
\]
\[
h=\frac{4\nu(t-s)}\gamma,
\qquad \kappa=\frac{\gamma^2}{4\nu\epsilon(t^2-s^2)}>0,
\]
\[
R=\beta_L\frac ba v_a^2+\beta_R\frac bd v_d^2,
\qquad
\ell_\zeta=\beta_Lv_a+\beta_Rv_d
 +2\nu\epsilon(d-a)\zeta.
\tag{6}
\]

First shift the eliminated auxiliary variable by
\(x=w_b-(4\nu s/\gamma)v_b\). Its two signed squares in (3)
are

\[
-\frac{\gamma^2\epsilon}{4\nu s^2}(x+q_a)^2
+\frac{\gamma^2\epsilon}{4\nu t^2}(x-hv_b+q_d)^2.
\tag{7}
\]

Their summed \(x^2\) coefficient is negative. Eliminating \(x\)
leaves \(\kappa(hv_b+q)^2\). The remaining physical coefficient
is \(A+\kappa h^2>0\), and its linear term is
\(-2\ell_\zeta v_b\). The Casimir coefficient here uses the
actual turn stationarity identity
\(J_b=2\nu\epsilon(d-a)\). Eliminating \(v_b\) gives the exact
replacement

\[
\boxed{\mathcal S_{\rm single}
=R+\kappa q^2-
\frac{(\ell_\zeta-\kappa hq)^2}{A+\kappa h^2}.}
\tag{8}
\]

At fixed Casimir this can equivalently be written

\[
\mathcal S_{\rm single}\big|_{\zeta=0}
=R-\frac{\ell_0^2}{A}
+\frac{\kappa A}{A+\kappa h^2}
\left(q+\frac hA\ell_0\right)^2\ge0.
\tag{9}
\]

The first two terms are the positive series-conductance energy from
eliminating a vertex of the physical weighted Laplacian. Thus (9)
is an identity and a useful sign; it does not assert a sign after
the global Casimir coupling is added.

## 3. An adjacent pair: all bridge signs

Write its physical margins as \((a,b,c,d)\), with turns at \(b,c\)
and reverse centres at \(a,d\). Strict centre minima and turn
feasibility give \(a,d<\min(b,c)\). Set

\[
s=a+b,\quad t=b+c,\quad u=c+d,\qquad
D=s^2+u^2-t^2,
\quad l=\begin{pmatrix}c-a\\b-d\end{pmatrix}>0.
\tag{10}
\]

All three bridge switch norms equal \(\nu>3/32\). Its physical
turn matrix is

\[
A=\begin{pmatrix}
(\beta_La+\beta_Mc)/b&-\beta_M\\
-\beta_M&(\beta_Mb+\beta_Rd)/c
\end{pmatrix}>0.
\tag{11}
\]

When both endpoint variations vanish, shift
\(x_b=w_b-(4\nu s/\gamma)v_b\) and
\(x_c=w_c-(4\nu u/\gamma)v_c\). The whole turn block becomes

\[
v^TAv-\frac{\gamma^2x_b^2}{4\nu s^2}
-\frac{\gamma^2x_c^2}{4\nu u^2}
+\frac{\gamma^2}{4\nu t^2}
\left[x_b+x_c-\frac{4\nu}\gamma l^Tv\right]^2.
\tag{12}
\]

The auxiliary block has two negative diagonal entries and determinant
\(-\gamma^4D/(16\nu^2s^2t^2u^2)\). For \(D\ne0\), its
elimination leaves exactly \(A-(4\nu/D)ll^T\).

If \(D<0\), the auxiliary block is negative definite and the
physical Schur complement is positive definite. The turn block has
inertia \((2,0,2)\).

If \(D>0\), its auxiliary block has one eigenvalue of each sign.
Put \(v_*=(b,c)^T\), \(Q=l^Tv_*>0\), and
\(\Omega=v_*^TAv_*\). The incident reverse inequalities and
\(\nu>3/32\) give

\[
\Omega=\beta_Lab+\beta_Rcd
<\frac{(b-a)^2+(c-d)^2}{64}.
\]

Direct use of \(a,d<\min(b,c)\) gives

\[
D<4\min(b,c)^2,\qquad
Q\ge\min(b,c)[(b-a)+(c-d)].
\]

Therefore \(D\Omega<Q^2/16<4\nu Q^2\). The rank-one
subtraction \(A-(4\nu/D)ll^T\) is positive on \(l^\perp\)
and negative at \(v_*\), so has one eigenvalue of each sign.
Again the full turn block has inertia \((2,0,2)\). No angle-sum
assumption or sign of \(D\) was imported from the all-short case.

For completeness, the determinant of the full block (12) is

\[
\frac{\gamma^4}{16\nu^2s^2t^2u^2}
\left[4\nu\,l^T\operatorname{adj}(A)l-D\det A\right].
\tag{13}
\]

At \(D=0\) this is strictly positive because \(A>0\) and
\(l\ne0\). The matrix stays nonsingular, and continuity from
either side therefore gives the same inertia. Equivalently its one
auxiliary kernel direction has a nonzero coupling to \(l^Tv\),
which supplies one positive and one negative constraint pair.

## 4. Exact adjacent-pair replacement with the Casimir retained

Let \(L=l^TA^{-1}l>0\) and define

\[
R=\beta_L\frac ba v_a^2+\beta_R\frac cd v_d^2,
\qquad \ell_\zeta=
\begin{pmatrix}\beta_Lv_a\\\beta_Rv_d\end{pmatrix}
+2\nu\zeta l,
\]
\[
z=s v_a+u v_d-\frac{\gamma}{4\nu}(w_a+w_d).
\tag{14}
\]

The exact remaining form after eliminating all four turn variables is

\[
\boxed{\mathcal S_{\rm pair}
=R-\ell_\zeta^TA^{-1}\ell_\zeta
+\frac{4\nu}{4\nu L-D}
\left(z-l^TA^{-1}\ell_\zeta\right)^2.}
\tag{15}
\]

The denominator is strictly positive for every bridge. For \(D\le0\)
this is immediate; for \(D>0\), Cauchy--Schwarz in the positive
form \(A\) and the preceding test vector give
\(4\nu L\ge4\nu Q^2/\Omega>D\).
Thus (15) is smooth also at \(D=0\); no singular auxiliary inverse
is used there. At \(\zeta=0\), its first two terms are again the
positive series-conductance energy, and the final square is positive.

One may derive (15) first for \(D\ne0\): auxiliary elimination
gives
\(R+v^TAv-2\ell_\zeta^Tv-(4\nu/D)(l^Tv-z)^2\).
The rank-one inverse formula then gives (15). Both sides extend
continuously to \(D=0\), since the full block is nonsingular by
(13). The actual turn gradients are
\(J_b=2\nu(c-a)\), \(J_c=2\nu(b-d)\), which explain the
\(2\nu\zeta l\) term without changing the multiplier.

## 5. Assembly and the remaining sign problem

To assemble \(\mathcal S\), retain the onsite forms (4) at all
nonturn indices. Retain (3) on each edge directly joining two
nonturns; every such edge is forward. Replace each one-turn component
by (8) and each two-turn component by (15). Finally retain
\(-2\zeta\sum_{\text{nonturn }i}J_{a_i}v_i\).
This is a complete explicit prescription for the remaining matrix,
including its one global Casimir coordinate.

Each isolated turn contributes one positive and one negative pivot;
each pair contributes two of each. The components are disjoint in
the turn principal block, proving (1). Sylvester's law therefore gives
\(\operatorname{ind}_-\operatorname{Hess}\Psi=2m+
\operatorname{ind}_-\mathcal S\). Substituting the already proved
three-constraint index transfer gives (2).

At fixed Casimir all replacement edge forms are nonnegative. The
remaining onsite terms and their simultaneous interaction with these
edges and the global Casimir coordinate require a further sign
argument. Negativity of an onsite term at a global minimum is not
negativity of the resulting full principal block. The present exact
elimination makes that unresolved problem concrete and preserves the
actual endpoint-rank and curvature accounting.

## Supplementary exact checker

Run

```
python3 explorations/mixed_global_turn_elimination_certificate.py
```

All 23 exact identities pass with Python 3.12.14 and SymPy 1.14.0.
The checker derives the completed physical diagonal from the signed
cyclic action with its stationarity residual still present, checks the
physical, mixed and auxiliary entries, both signs of the single-turn
elimination, the paired-turn determinant and its full smooth remaining
form, and the three-constraint index arithmetic. The inequalities,
inertia, zero-bridge continuity and actual full-period interface are
the hand arguments above. No numerical sampling or additional cost-case
closure is supplied by the script.
