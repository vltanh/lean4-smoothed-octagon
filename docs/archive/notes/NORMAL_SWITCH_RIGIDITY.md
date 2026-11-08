# Unique normal outgoing vertex germs and transverse closed-period switches

Date: 2026-11-07 UTC. Hand proof with an
[independent internal audit](GLOBAL_NORMAL_PERIOD_STRUCTURE_AUDIT.md).
No Lean, Lake, typechecking, or CI.

## Results and scope

At any fixed strict-star normal zero-Hamiltonian phase, **at most one
vertex has a positive outgoing PMP germ**. A germ means an actual
positive-duration constant-vertex solution of the state and adjoint
equations, with all simplex Hamiltonian inequalities, starting from
that same phase and normal covector. This includes phases with two or
three tied vertex Hamiltonians.

Existence is a separate question. Some phases, including the full normal
circle singular phase, have no positive vertex germ. Along an actual
finite positive vertex trajectory, the representation supplies an
outgoing germ, so it is unique. The exact tests in
[NORMAL_TIE_BRANCHING](NORMAL_TIE_BRANCHING.md) still apply; the present
argument proves that no two of their candidates can pass simultaneously.
It gives no common positive duration for nearby phases.

Furthermore, every actual switch in a finite positive strict-star normal
period with the complete twisted endpoints is **transverse for its
incoming/outgoing pair**. This follows from the reverse-run theorem in
[MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md).
It is not a transversality assertion for arbitrary local normal windows:
genuine cubic reverse switches remain possible there. A transverse
switch can still be a triple tie. We do not infer strictness of every
inactive initial gap from pairwise transversality.

These are structural consequences, not further cost-case exclusions.
The remaining comparisons F/M1/M2 and their boundary/equality arguments
are unchanged.

## 1. The same-covector equation for any pair of vertices

Suppose two candidate vertices at a fixed phase were both to have
positive outgoing PMP germs. Both are initially maximizers, and both
initial active Hamiltonians are zero. Rotate their pair to labels 1 and
2. Use the original physical coordinates

\[
q=1/\sqrt3,\qquad X=\Phi(x,y),\qquad -q<x<q,\quad y>0,
\qquad w=y^{-2}.
\]

On either vertex `dx/dt=y>0`. Use the common positive clock
`d tau=y dt` and shear frame `mathcal F=g[[1,x],[0,1]]`.
Normalize the cost to the minimizing convention
`mathcal A=(2/3)C`, with covector `p_min=-(2/3)p_max`.
The same-covector interface is proved in Section 5 of
MIXED_GLOBAL_MINIMUM_STRUCTURE: along either vertex,

\[
x_\tau=1,\qquad w_\tau=b_i(x)w,\qquad
\mathcal F_\tau=\mathcal FwE_{21},
\quad b_1=\frac2{q-x},\quad b_2=-\frac2{q+x}.
\]

The group-covector evaluation `m=<M,E_21>` is constant on both
candidate flows. Since the initial actual covector is the same,
**its initial value, and hence `mu=-1-m`, are the same for both**.
With primes in the increasing `x` clock,

\[
p_w'=\mu-x^2-b_i(x)p_w,
\qquad
\mathcal H_2-\mathcal H_1=-(b_1-b_2)wp_w,
\quad (b_1-b_2)w>0.
\tag{1}
\]

Thus an outgoing vertex-1 germ requires `p_w<=0` on its right
interval; an outgoing vertex-2 germ requires `p_w>=0` there.
The common initial tie gives `p_w(a)=0`, where `a=x(0)`.

## 2. The two hypothetical flows have the same first nonzero right sign

Equation (1) is analytic while `-q<x<q`. At the common initial tie,

\[
p_w'(a)=\mu-a^2.
\tag{2}
\]

If this is nonzero, its sign is the first right-hand sign on **both**
candidate flows. If it vanishes, differentiating (1) gives

\[
p_w''(a)=-2a.
\tag{3}
\]

Again the value is independent of the candidate vertex. If that also
vanishes, `a=mu=0`; one more derivative gives on both flows

\[
p_w'''(0)=-2<0.
\tag{4}
\]

The terms involving `b_i` and its derivatives multiply already
vanishing lower derivatives at each step. Thus the first nonzero
coefficient appears by order three and has the **same sign** on the
two right-hand intervals. In particular the switching function is
not identically zero on either hypothetical positive vertex germ.

The opposite necessary signs following (1) cannot both hold. Therefore
the two candidate germs cannot both be PMP germs. The argument applies
to every pair of tied candidates, so at most one of all three vertices
passes the complete outgoing-germ test.

The third vertex can disqualify the remaining candidate; nothing in
this pairwise argument supplies existence. At a phase lying on a finite
positive vertex trajectory, existence comes from its actual next arc.
At an arbitrary normal phase, retaining zero passing candidates is
essential.

## 3. A nontransverse actual switch can only be a cubic reverse switch

Now take an actual two-sided switch and rotate its incident labels to
the same edge. Both vertex fields share the strictly increasing
coordinate `x`, so the incident arcs lie on opposite sides of `a`.
The switching function `p_w` is continuous; its first derivative at
the tie agrees from both sides by (1). If that derivative vanishes,
its second derivative also agrees by (3). If both vanish, its third
derivative agrees by (4).

For a forward switch `1 -> 2`, the required signs are
`p_w<=0` on the left and `p_w>=0` on the right. Therefore
`p_w'(a)>=0`. Suppose it were zero. If `a!=0`, (3) supplies a
nonzero quadratic leading term, with the same sign on both sides,
which cannot give the required change of sign. If `a=0`, then
`mu=0` and (4) gives a negative cubic leading term: it is positive
to the left and negative to the right, the reverse of the required
forward orientation. Both possibilities are impossible. Hence

\[
\boxed{p_w'(a)>0\quad\text{at every actual forward switch}.}
\tag{5}
\]

For a reverse switch `2 -> 1`, the required signs are instead
`p_w>=0` on the left and `p_w<=0` on the right. Thus
`p_w'(a)<=0`. The only way equality can occur is

\[
a=\mu=p_w(a)=0,\qquad p_w'''(a)=-2,
\tag{6}
\]

the genuine cubic reverse alternative. This conclusion does not claim
that every phase satisfying (6) also meets the third-control PMP test;
it is the necessary form of any nontransverse actual reverse switch.

The two physical active margins have ratio

\[
\frac{p_1(X)}{p_2(X)}=\frac{q-x}{q+x}.
\]

At (6), they are equal. The actual physical-time Hamiltonian gap is
a positive smooth multiple of `p_w`, and the clock satisfies
`dx/dt=y>0`. Thus a strict derivative in (5), or its negative reverse
analogue, is exactly transversality of the physical pairwise switch.

## 4. The complete-period minimum principle removes the cubic alternative

Take a finite positive normal period with the actual twisted endpoints.
Entirely reverse periods are impossible. If it is mixed, every maximal
reverse run has exactly two switches, by
MIXED_GLOBAL_MINIMUM_STRUCTURE. The active margin of its middle arc
is strictly smaller than those of both adjacent arcs. At either reverse
switch the two incident active margins are therefore **unequal**.

The only nontransverse reverse alternative in (6) requires those two
margins to be equal. It cannot occur in such a period. Every reverse
switch consequently has `p_w'(a)<0` in its rotated edge chart, and
every forward switch has (5). A pure-forward period is covered by (5)
alone. This proves transversality of every switch of the finite normal
closed period.

The minimum principle and its actual cotangent extension apply across
the twisted seam, so the same conclusion holds at the chosen initial
and terminal cut. Zero-duration pieces are deleted before choosing the
positive representation. No uniform separation from zero duration,
uniform switching-derivative lower bound, or strict third-control gap
has been inferred.

## Validation boundary

Equations (2)--(4) are successive exact derivatives of the same full
normal adjoint equation (1). The proof keeps the candidate-dependent
functions `b_i` until the vanishing lower derivatives remove them.
The common multiplier, positive clock and physical signs are therefore
part of the calculation, not assumptions of a generic switching rule.
The global transversality statement additionally uses the independently
audited minimum/run theorem. No numerical sample, uniform dwell-time
claim, or additional closure of a comparison case is involved.
