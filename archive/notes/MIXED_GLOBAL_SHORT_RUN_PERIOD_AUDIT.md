# Independent audit of the short-forward-run period equations

Date: 2026-11-07 UTC. Independent internal hand review of
[MIXED_GLOBAL_SHORT_RUN_PERIOD](MIXED_GLOBAL_SHORT_RUN_PERIOD.md).
No Lean, Lake, typechecking, or CI was run.

## Verdict and scope

The common recurrence, normal Euler cost identity, and complete
two-centre exclusion are valid. The two-centre branch has

\[
C>2\sqrt6-\sqrt3>\pi>A_{\rm oct},
\]

for arbitrary unequal positive factors satisfying its actual closed
normal PMP hypotheses. No endpoint-rank, simple-switch, or equal-factor
assumption is introduced.

This is a fixed base branch of one uniform cyclic problem. It does
not close the whole M1 comparison: the same equations for every
`m>=5`, `m=2 mod 3`, still require a uniform cost or index argument.
The antiperiodic boundary sign alone gives no lifted winding or
constrained index. No such conclusion is included in this audit.

The sufficient assignment of mixed periods is sound. The proved
reverse-run theorem leaves exactly two reverse switches in every
negative run. Any forward run of length at least two supplies M2;
otherwise the entire sign sequence is `(--+)^m`, which is the
whole-period domain treated here. This assignment does not forbid
local M1 windows inside a period assigned to M2.

## 1. Labels, state closure, and the full central sign

Each centre `a_j` is followed by two turn arcs `b_j,c_j`. Their
outgoing signs are `-,+,-`, a cyclic shift of the stated repeated
pattern. Thus the cumulative label advance over the period is `-m`.
The actual label twist is advance by one modulo three, giving
`m=2 mod 3` and `N=3m`.

The three factor formulas are precisely the `--`, `-+`, and `+-`
specializations of the common active-margin formula. They reconstruct
the actual state trajectory, including its twisted seam. Strict
positivity of the centre factor and the two neighboring strict margin
comparisons give

\[
K_j>(c_{j-1}+a_j)(a_j+b_j)>4a_j^2,
\qquad a_j^2<4/3.
\]

The prefix matrices retain the full tangent product. Because
`sum epsilon=-m=3k+1`, one has `k=-(m+1)/3`, and the actual frame
endpoint gives the central monodromy

\[
P_N=(-1)^k I=(-1)^{(m+1)/3}I.
\]

Hence the displayed sign `sigma` is correct. It is derived from the
full matrix endpoint, not only from a trace condition or the label
congruence. The actual primary covector and the free-state cotangent
twist are those of the common normal boundary identity in
[MIXED_GLOBAL_COSTATE_ELLIPTIC](MIXED_GLOBAL_COSTATE_ELLIPTIC.md).

## 2. The collapsed recurrence and its two-node convention

At the two turn arcs the actual switch-vector identities give
`z_j,-z_j,z_j`. In the prefix frame at centre `a_j`, the incoming
vector is `-e_1/h` and the outgoing one is `h e_2/K`, with the
notation of the proof. This immediately gives determinant `-1/K`.

For an independent multiplication, write

\[
A_-(q)=\begin{pmatrix}0&q\\-q^{-1}&q^{-1}\end{pmatrix},
\qquad
A_+(q)=\begin{pmatrix}q&-q\\q^{-1}&0\end{pmatrix}.
\]

Applying the three factors successively to `e_2` gives

\[
A_-(v/w)e_2=(v/w,w/v)^T,
\]

\[
A_+(v/u)A_-(v/w)e_2
=\bigl((v^2-w^2)/(uw),u/w\bigr)^T,
\]

and finally

\[
wA_-(K/(hu))A_+(v/u)A_-(v/w)e_2
=\frac Khe_1+\frac hK(u^2+w^2-v^2)e_2.
\]

This proves exactly
`-K_j z_(j-1)+D_j z_j-K_(j+1) z_(j+1)=0`, including the signs
and the prefix transport. The same central monodromy supplies its
twisted boundary condition.

For `m=2` the two off-diagonal incidences reach the same other node
with opposite boundary signs. Combining them gives
`D_0 z_0+(K_0-K_1)z_1=0`, rather than a matrix with two independent
off-diagonal entries. Since `det(z_0,z_1)` is nonzero, this forces
`D_0=0` and `K_0=K_1`; the other row gives `D_1=0`. This special
two-node treatment is necessary and has been handled correctly.

The gauge `z_j -> (-1)^j z_j` makes the off-diagonal coefficients
positive. Its boundary sign is
`(-1)^((m+1)/3+m)=-1` for `m=2 mod 3`. This verifies the parity
claim, while preserving the stated distinction from a winding theorem.

## 3. The normal Euler cost identity

Direct differentiation of the symmetric edge action gives

\[
(a\partial_a+b\partial_b)G(a,b)-2G(a,b)
=16\left(\frac1{a^2+4}+\frac1{b^2+4}\right).
\]

After summing with the actual signs, the two incident contributions
cancel at every turn and add negatively at every centre. Therefore

\[
EJ=2J-4\sum_j K_j^{-1}.
\]

The independent frame-column calculation is also exact. Multiplying
each common column by its active margin and summing, an edge contributes
`epsilon_i(Z_i+Z_(i+1))`, because its two margins sum to `s_i`.
The remaining diagonal term then gives

\[
\sum_i a_iV_i
=4\sum_i\frac{\epsilon_{i-1}+\epsilon_i}{K_i}Z_i.
\]

At a centre, `tr(UZ_i)=2K_j e_j`; at a turn the coefficient vanishes.
The boundary identity from the same normalized actual covector thus
gives `EJ=-16 sum e_j`. Combining these two formulas proves

\[
J=2\sum_j K_j^{-1}-8\sum_j e_j,
\qquad J=C/\sqrt{12}.
\]

Common scaling is used only to differentiate an identity on the
state-closed family. It is not asserted to preserve the frame endpoint.
The frame multiplier accounts for exactly that endpoint derivative.
The initial-state and terminal-state terms have already cancelled by
the actual free-initial-state transversality; no unrelated local
endpoint multiplier is substituted.

## 4. Strict two-centre cost exclusion

For `m=2`, the equal positive centre margins follow from `K_0=K_1`.
The two zero diagonal relations become

\[
(b_j-a)(c_j-a)=2a^2\quad(j=0,1).
\]

Antiperiodicity gives `z_-1=-z_1`; symmetry of the same matrix `S`
therefore gives `e_0+e_1=0`. The normal Euler formula reduces to
`J=4/K`. This uses no definiteness estimate on `S` beyond the
already established actual normal interface.

After dividing all four turn margins by `a`, the two bridge relations
give `xz=x+z+1` and `yt=y+t+1`, with all four variables greater
than one. The arithmetic-geometric mean inequality on
`(x-1)(z-1)=2` yields `xz>=3+2sqrt(2)`, and similarly for `yt`.
The two strictly positive centre durations consequently imply

\[
\tau:=K/a^2>
\sqrt{(1+t)(1+x)(1+z)(1+y)}
=2\sqrt{xz\,yt}\ge6+4\sqrt2.
\]

Since `4/K=1-1/tau` increases with `tau`, this gives the strict
cost bound in the verdict. The rational check of the last comparison
is correct: after squaring positive quantities it becomes
`545^2>3*308^2`, with difference `12433>0`, followed by the standard
positive-integral proof of `pi<22/7`.

The strict inequality comes from positive centre durations. Equality
of the turn-pair arithmetic-geometric means does not create an
uncovered positive-duration boundary case. Zero-duration limits are
not claimed to satisfy this strict branch hypothesis.

## Validation and remaining obligation

The supplementary command

```
python3 explorations/mixed_global_short_run_certificate.py
```

passes all eight exact identities with Python 3.12.14 and SymPy 1.14.0.
The independent calculation above also checks the full endpoint sign,
normal multiplier interpretation, two-node recurrence, and inequalities
that are not established merely by those symbolic checks.

The remaining `m>=5` family is one uniform problem. In particular,
negative centre cross pairings were proved earlier only under a
contradicted nonelliptic hypothesis; that sign cannot be reused after
negative physical ellipticity has been established. Neither the Euler
identity nor the antiperiodic kernel by itself supplies the required
aggregate pairing inequality or index. This audit endorses no growing
period catalogue and no additional comparison-case closure.
