# Exact vertex flows and exclusions by cyclic rebasing

## Results

The fixed-edge exclusion in [SWITCHING_WORDS.md](SWITCHING_WORDS.md) has two
further consequences for an admissible finite vertex-control trajectory:

1. Every reduced switching word has at least four positive-duration arcs.
2. If it has exactly four arcs, then, up to cyclic relabeling of the three
   controls, its word is **`0,1,2,0`**.

These are feasibility exclusions, with no assumption of optimality,
Pontryagin conditions, equal durations, reflection symmetry, or membership
in the regular `(6k+2)` family. The argument is a cyclic time translation
of the actual trajectory followed by the fixed-edge exclusion. It also
gives an ordering test that excludes arbitrarily long words.

The remaining four-arc family still has unrestricted positive durations
and initial state at this stage of the argument. Its full asymmetric cost
comparison is now proved separately in
[FOUR_LINK_HAND_PROOF.md](FOUR_LINK_HAND_PROOF.md). This note also derives
exact recurrences, cost, and continuous feasibility constraints for
arbitrary vertex words, for use in longer-word comparison and in any
properly scoped exploration.

No Lean file was added, and no Lean compilation or CI was run.

## 1. Cyclic rebasing preserves admissibility

Start with an actual integral-form admissible trajectory on `[0,T]`:

\[
g(0)=I,\qquad g(T)=R,\qquad X(T)=R^{-1}X(0)R.
\tag{1}
\]

Extend it to the next time cell by

\[
G(t+T)=g(t)R,\qquad
Y(t+T)=R^{-1}X(t)R,\qquad
Z_{v(t+T)}=R^{-1}Z_{u(t)}R
\quad(0\le t\le T).
\tag{2}
\]

On the original cell take `G=g`, `Y=X`, and `v=u`. The endpoint conditions
(1) match the values of `G,Y` at the join. The resulting curves are
absolutely continuous on `[0,2T]`. Conjugation preserves the state
equations and the strict star domain, and it permutes the control simplex;
the equations therefore hold almost everywhere on both cells and hence
on their union. The control value at the single join can be chosen
arbitrarily in the simplex.

With the source's indexing,

\[
R^{-1}Z_{e_i}R=Z_{e_{i+1}},
\tag{3}
\]

where indices are modulo three. Thus the wrapped part of a word has every
letter **increased by one**. This direction is opposite to the conjugation
used to relabel a word in the fixed-edge proof.

For any `s∈[0,T]`, rebase the time interval and the left frame:

\[
\widehat g(t)=G(s)^{-1}G(s+t),\qquad
\widehat X(t)=Y(s+t),\qquad
\widehat u(t)=v(s+t),\quad 0\le t\le T.
\tag{4}
\]

Left multiplication by the constant matrix `G(s)⁻¹` preserves `g′=gX`.
The state and control equations are unchanged by the time translation.
Equations (2) give

\[
\widehat g(0)=I,\qquad
\widehat g(T)=R,\qquad
\widehat X(T)=R^{-1}\widehat X(0)R.
\]

Thus this is again an admissible trajectory, with the same terminal time.
Its cost is also the same: `J` commutes with `R`, so `tr(JY)` has period
`T`, and its integral over any interval of length `T` is unchanged.
Cost invariance is useful for comparisons, although the exclusions below
do not need it.

## 2. An ordering condition for every finite word

Represent the original control by a word

\[
i_0,i_1,\ldots,i_{N-1}\in\mathbb Z/3\mathbb Z
\]

with positive durations. Delete zero-duration entries and merge consecutive
equal letters. Rebasing at the end of the first `r` arcs gives

\[
i_r,\ldots,i_{N-1},\quad i_0+1,\ldots,i_{r-1}+1.
\tag{5}
\]

There can be adjacent equal letters in this displayed word; they may be
merged. Its set of letters, which is all the fixed-edge argument uses,
does not change on merging.

The fixed-edge exclusion says that every word (5) must contain all three
letters. Write `first(j)` and `last(j)` for the first and last arc indices
carrying `j`. Each letter occurs, so these indices are defined. Then

\[
\boxed{\operatorname{last}(j)>
\operatorname{first}(j-1)\qquad(j\bmod3).}
\tag{6}
\]

To prove this, suppose instead that `last(j)<first(j−1)`, and cut after
the last occurrence of `j`, before the first occurrence of `j−1`. The
suffix contains no `j`, and the prefix contains no `j−1`; after its
letters are increased by one, it also contains no `j`. The rebased word
is confined to the edge missing `j`, a contradiction. Equality of the two
indices is impossible because they carry distinct letters. This proves
the strict inequality (6).

Conversely, for a given finite word that uses all three letters, (6) says
exactly that no arc-boundary rebase can omit a letter. Indeed, omitting
`j` after the cut `r` would mean `last(j)<r≤first(j−1)`. For cuts inside
an arc, both adjacent portions have positive length, so their letter set
contains the sets at the adjacent limiting cuts. Therefore the same
condition covers every time rebase, not just the listed arc boundaries.
This converse concerns the letter-coverage test only; it does not assert
admissibility of a word passing the test.

There is an integral version that does not assume a finite word. For
`A_j(s)=∫₀ˢu_j(t)dt` and `M_j=A_j(T)`, every actual admissible control
satisfies

\[
\boxed{M_j-A_j(s)+A_{j-1}(s)>0
\quad(0\le s\le T,\ j\bmod3).}
\tag{7}
\]

The left side is the integral of coordinate `j` on the rebased window.
It is strictly positive by the measurable-control fixed-edge exclusion.
For finite words these integrals are linear between switching times, so
their positivity is equivalently tested at the cuts. No uniform positive
lower bound is asserted in (7).

## 3. All words with at most three arcs are excluded

Words with fewer than three distinct letters are already excluded. A
three-arc word that uses all three letters can be cyclically relabeled
to start with `0`. Its first arc is its only `0`. Rebase just after that
arc. The remaining two letters are `1,2` in some order, and the wrapped
first letter becomes `1`. The new word omits `0`, a contradiction.

Equivalently, in a three-letter permutation the first and last occurrence
of each letter coincide, and (6) would impose a strict cycle of three
inequalities. Thus every admissible reduced finite word has `N≥4`.

## 4. Only the forward cyclic pattern survives at four arcs

Use cyclic relabeling to make the first letter `0`. A reduced four-arc
word with all three letters is one of the six listed below. The table
gives an explicit rebase that excludes every pattern except `0120`.
The cut index `r` is the number of original arcs moved to the end and
relabelled by `+1`.

| Original word | Cut `r` | Rebased word | Missing letter |
| --- | ---: | --- | ---: |
| `0102` | 3 | `2121` | 0 |
| `0121` | 1 | `1211` | 0 |
| `0201` | 2 | `0110` | 2 |
| `0210` | 2 | `1010` | 2 |
| `0212` | 1 | `2121` | 0 |
| `0120` | — | All cuts contain all three letters | — |

The other two reduced four-letter words starting with `0`, namely `0101`
and `0202`, omit a vertex from the outset. This exhausts the possibilities.
All arc durations remain arbitrary throughout the argument.

The surviving word is exactly the cyclic order used by the octagon after
relabeling; this fact does **not** identify its initial state, switch times,
or geometric body with those of the octagon.

## 5. Coordinates for exact arbitrary-word calculations

The following change of coordinates removes square roots from the three
vertex matrices while preserving determinant one. Put

\[
D=\operatorname{diag}(3^{1/4},3^{-1/4}),\quad
\mathsf X=DXD^{-1},\quad \mathsf g=DgD^{-1},\quad
\mathsf Z_i=\sqrt3\,DZ_{e_i}D^{-1}.
\]

Then

\[
\mathsf Z_0=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
\mathsf Z_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
\mathsf Z_2=\begin{pmatrix}-1&-2\\0&1\end{pmatrix},
\qquad
\mathsf R=\begin{pmatrix}1/2&-3/2\\1/2&1/2\end{pmatrix}.
\tag{8}
\]

Scaling `Z` by `√3` cancels between numerator and denominator of `P`.
Thus no time scaling is introduced. Define

\[
p_i=-\operatorname{tr}(\mathsf Z_i\mathsf X),\qquad
S=p_0+p_1+p_2.
\]

The matrix identities

\[
\mathsf Z_i^2=I,\qquad
\operatorname{tr}(\mathsf Z_i\mathsf Z_j)=-2\ (i\ne j),\qquad
[\mathsf Z_i,\mathsf Z_{i+1}]=2(\mathsf Z_i+\mathsf Z_{i+1})
\tag{9}
\]

follow by multiplying the matrices in (8). They give

\[
\mathsf X=\frac14\sum_i(S-p_i)\mathsf Z_i,
\quad
\operatorname{tr}(\mathsf X^2)
=-\frac12(p_0p_1+p_1p_2+p_2p_0).
\]

The strict star states are therefore exactly

\[
\boxed{p_i>0,\qquad p_0p_1+p_1p_2+p_2p_0=4.}
\tag{10}
\]

For completeness, if `\mathsf X=Φ(ξ,η)`, with `ξ=√3x`, `η=√3y`, then

\[
p_0=(\xi^2+\eta^2-1)/\eta,\quad
p_1=2(1-\xi)/\eta,\quad
p_2=2(1+\xi)/\eta.
\]

These are positive exactly on the scaled strict star domain. Conversely
positive `p_i` in (10) reconstruct `η=4/(p₁+p₂)>0` and
`ξ=(p₂−p₁)/(p₁+p₂)` through the displayed matrix formula.

The cost and terminal state condition take the particularly simple forms

\[
L= -\frac32\operatorname{tr}(JX)
=\frac{\sqrt3}{2}S,
\qquad
(p_0(T),p_1(T),p_2(T))=(p_2(0),p_0(0),p_1(0)).
\tag{11}
\]

To check the cost normalization, `Σ_i\mathsf Z_i=√3DJD⁻¹`.
To check the endpoint permutation, use
`\mathsf R\mathsf Z_i\mathsf R⁻¹=\mathsf Z_{i−1}` inside the trace.

## 6. One vertex arc: complete feasibility and exact cost

On an arc with control `i`, (9) and the state equation give

\[
p_i'=0,\quad
p_{i+1}'=\frac{2(p_i+p_{i+1})}{p_i},\quad
p_{i-1}'=-\frac{2(p_i+p_{i-1})}{p_i}.
\tag{12}
\]

Let its initial margins be `p_i=a`, `p_{i+1}=b`, `p_{i−1}=c`, with
`a,b,c>0` and `ab+bc+ca=4`. For duration `τ>0` set `w=exp(2τ/a)`. The
exact endpoint map is

\[
\boxed{a\longmapsto a,\qquad
b\longmapsto(a+b)w-a,\qquad
c\longmapsto(a+c)/w-a.}
\tag{13}
\]

The increasing coordinate stays positive, and the decreasing one is
positive throughout the closed arc exactly when its final value is
positive. Thus the **entire continuous arc** lies in the strict star domain
if and only if

\[
\boxed{1<w<1+c/a.}
\tag{14}
\]

This replaces a sampled feasibility test by an exact inequality. It gives
an upper bound `τ<(a/2)log(1+c/a)` for this particular initial state, not a
uniform lower bound on durations.

Integrating (11) using `dt=(a/2)dw/w` gives the exact arc cost

\[
\boxed{\mathcal C_i(a,b,c,w)
=\frac{\sqrt3\,a}{4}
\left((a+b)(w-1)+(a+c)(1-w^{-1})-a\log w\right).}
\tag{15}
\]

The chronological group product is equally explicit. At the beginning of
an arc write `\mathsf X=\mathsf X(p)` and `P=-\mathsf Z_i/a`. The
constant-control formula is

\[
F_i=\exp(\tau(\mathsf X+P))\exp(-\tau P).
\]

Here `P²=(\mathsf X+P)²=I/a²`, since `\mathsf X²=-I` and
`\mathsf X\mathsf Z_i+\mathsf Z_i\mathsf X=-aI`. Writing each exponential
as its `cosh/sinh` expression and multiplying gives

\[
\boxed{F_i(p,w)=I+\frac a4
\left((w-w^{-1})\mathsf X(p)
 +(w+w^{-1}-2)\mathsf X(p)\mathsf Z_i\right).}
\tag{16}
\]

The update is `\mathsf g_{k+1}=\mathsf g_kF_{i_k}(p^{(k)},w_k)`, with the
state updated by (13). This order matters: the factors multiply on the
right in chronological order.

For a fixed word, an exact feasibility and cost comparison therefore needs
the initial conditions (10), the per-arc inequalities (14), the state twist
(11), the full matrix product `F₀⋯F_{N−1}=\mathsf R`, and the sum of (15).
Neither state closure alone nor the trace of the group product replaces
the full matrix endpoint. These equations impose no unproved symmetric
subfamily restriction. They also do not bound `N`.

## 7. Exploratory algebra retained, and remaining comparison

Before the shorter rebasing proof was found, an exact symbolic calculation
eliminated the state endpoint for the two three-arc orders and inspected
the remaining group defect. Its reproducible script is
[`explorations/vertex_word_algebra.py`](../explorations/vertex_word_algebra.py).
It uses Python 3.12.14 and SymPy 1.14.0, exact rational arithmetic, and the
recurrences (13), (16). Its docstring specifies the domain and limitations.

The script reports zero residuals for the two state-twist substitutions
and three explicit group identities. Those outputs are exploratory
algebra, **not the hand proof** of the exclusion. Sections 1–4 provide
the independent proof and do not invoke the script, elimination software,
numerical tolerances, or a search over candidates. The retained calculation
prevents a repeated attempt at the longer three-arc algebra and provides
an exact word-evaluation routine for further exploration.

The concrete new restriction is: every finite admissible word obeys (6),
has at least four arcs, and at four arcs has forward order `0120` up to
cyclic relabeling. The separate four-link hand proof now compares that
entire unequal-duration family with the octagon. The comparison of all
allowed longer words remains open. None of these exclusions supplies a uniform bound on word length
or a classification of all minimizers as finite vertex words.

## Sources

- The pinned source defines the actual integral trajectories, strict star
  states, controls, endpoint constraints, and cost in
  [`SmoothedPolygons/Defs.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean).
- The conjugation convention is `R_conj_controlMatrix_vertex` in
  [`Ch4/StarDomain.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch4/StarDomain.lean).
- The constant-control solutions used to derive (16) are
  `constControl_solution` and `lemma7_1_3` in
  [`Ch7/ConstantControl.lean`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch7/ConstantControl.lean),
  corresponding to [Hales–Vajjha, §§7.1–7.4](https://arxiv.org/html/2405.04331v1#Ch7.S1).
- [SWITCHING_WORDS.md](SWITCHING_WORDS.md) supplies the measurable-control
  fixed-edge exclusion on which Sections 1–4 rely.
