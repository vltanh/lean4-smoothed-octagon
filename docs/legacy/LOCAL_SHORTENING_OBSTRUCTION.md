# A three-arc backtrack cannot simply be deleted locally

## Exact obstruction

Consider a state-trajectory segment with the positive vertex word `010`:
three positive-duration arcs using vertices `0,1,0`, with the state in the
strict star domain throughout. Fix both its initial pair `(g₀,X₀)` and its
terminal pair `(g₁,X₁)`.

**There is no replacement by at most two positive-duration vertex-control
arcs with those same two endpoint pairs.** The replacement may have a
different total duration and may use any of the three vertices. The
obstruction concerns existence, so allowing a larger cost would not help.

This disproves the proposed universal local rule that deletes a `010`
backtrack while preserving its endpoints. It does not obstruct a
replacement that changes neighboring arcs, moves the endpoints of the
window, or uses nonvertex controls. It is not a result about Hales's
larger link-reduction conjectures.

The proof is elementary matrix algebra. An explicit strict star segment
below shows that the hypothesis is nonvacuous. No numerical computation,
Lean implementation, or kernel validation is involved.

## 1. The two kinds of endpoint information

Use the rational coordinates of
[`WORD_HOLONOMY.md`](WORD_HOLONOMY.md), then conjugate once more by
`L=[[1,1],[1,−1]]`. In this basis the tangent transition matrices are

\[
T_0(q)=\begin{pmatrix}q&0\\0&q^{-1}\end{pmatrix},\qquad
T_1(q)=\begin{pmatrix}q^{-1}&q-q^{-1}\\0&q\end{pmatrix},
\]

\[
T_2(q)=\begin{pmatrix}q^{-1}&0\\q^{-1}-q&q\end{pmatrix}.
\tag{1}
\]

For a positive-duration vertex arc, `q=exp(2t/c)>1`, where its active
margin `c` is positive and constant. The state conjugator is

\[
H_i(q)=T_i(q^{-1/2}).
\tag{2}
\]

These formulas follow from the actual equations

\[
g'=gX,\quad X'=[D_i,X]/c,\quad c=\operatorname{tr}(D_iX),
\quad (gX)'=-2(gX)D_i/c.
\]

They are the same conventions as the pinned
[`reference definitions`](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean)
and [Hales–Vajjha, §7.1](https://arxiv.org/html/2405.04331v1#Ch7.S1).
All matrices in this note use row and column indices `1,2`.

For any finite arc word, the tangent product `F` acts on the right of
`V=gX`, while the state product `H` acts by conjugation:

\[
V_1=V_0F,\qquad X_1=HX_0H^{-1}.
\tag{3}
\]

In particular, two segments with the same endpoint pairs have the same
`F`, since `V₀` is invertible. Their state conjugators need not generally
be equal: they can differ by a matrix commuting with `X₀`. The argument
below proves equality in the triangular situation at hand. Ignoring this
second kind of endpoint information would give a false shortening rule.

## 2. The exact `010` data

Let its three factors be `p,q,r>1`, in chronological order. Direct
multiplication of (1) gives

\[
F=T_0(p)T_1(q)T_0(r)
=\begin{pmatrix}A&B\\0&A^{-1}\end{pmatrix},
\]

\[
A=\frac{pr}{q}>0,\qquad
B=\frac{p(q-q^{-1})}{r}>0.
\tag{4}
\]

The order of the state factors is reversed:

\[
H=H_0(r)H_1(q)H_0(p)
=\begin{pmatrix}A^{-1/2}&-C A^{1/2}\\0&A^{1/2}\end{pmatrix},
\qquad C=\frac{q-1}{r}>0.
\tag{5}
\]

The same formulas hold for `p,r≥1`, `q>1`; a factor equal to one denotes
a zero-duration outer arc. This includes the potential shorter words
`01`, `10`, and `1`.

### Why matching just the tangent product looks misleadingly promising

The matrix `F` in (4) can always be reproduced by two positive factors
of the word `01`. Set

\[
\widetilde q=\sqrt{1+\frac{q^2-1}{r^2}},\qquad
\widetilde p=\frac{pr}{q}\widetilde q.
\]

Then `q̃>1`,

\[
\widetilde p^2
=\frac{p^2(r^2+q^2-1)}{q^2}>p^2>1,
\]

and `T₀(p̃)T₁(q̃)=F`. However, its state conjugator has coefficient
`q̃−1` in place of `C` in (5). Since

\[
\left(1+\frac{q-1}{r}\right)^2
-\left(1+\frac{q^2-1}{r^2}\right)
=\frac{2(q-1)(r-1)}{r^2}>0,
\]

one has `q̃−1<C`. Thus these two pieces match the tangent endpoint but
fail to match the state endpoint. The remainder of the proof excludes
every other two-piece option as well.

## 3. Complete coverage of the shorter words

Adjacent equal labels can be merged without changing either endpoint.
An empty replacement has `F=I`; a replacement using only vertex `0`
has zero upper-right entry. Both contradict `B>0` in (4).

Every replacement of at most two positive arcs that uses vertex `2`
has a strictly negative lower-left entry in its tangent product:

- `T₂(q)` has lower-left entry `q⁻¹−q<0`.
- Multiplication by `T₀` on either side multiplies that entry by a
  positive diagonal entry.
- In `T₁(a)T₂(b)`, the lower-left entry is
  `a(b⁻¹−b)<0`.
- In `T₂(a)T₁(b)`, it is `(a⁻¹−a)/b<0`.
- Two consecutive `2` arcs merge into one, since
  `T₂(a)T₂(b)=T₂(ab)`.

None can equal (4), whose lower-left entry is zero.

The only remaining shorter words are therefore `01`, `10`, and `1`.
They use only vertices `0,1`, so their state conjugators are upper
triangular with positive diagonal entries. They can be represented in
the notation (4)–(5) by factors `p̃,r̃≥1`, `q̃>1`, with at least one
of `p̃,r̃` equal to one. The single `1` case has both equal to one.

## 4. The state endpoint removes the apparent freedom

Suppose such a shorter segment has the same terminal state. Let its
state conjugator be `H̃`. From (3),

\[
\widetilde H X_0\widetilde H^{-1}=H X_0H^{-1},
\]

so `K=H̃⁻¹H` commutes with `X₀`. Both `H̃` and `H` are upper
triangular with positive diagonal entries and determinant one. The same
is true of `K`.

A real traceless determinant-one matrix satisfies `X₀²=−I`, and every
commuting real matrix has the form

\[
K=\alpha I+\beta X_0.
\tag{6}
\]

For a direct proof, `v,X₀v` are independent for any nonzero real `v`;
otherwise `X₀` would have a real eigenvalue. A commuting matrix is
determined on this basis by its value on `v`, giving (6).

The lower-left entry of `X₀` cannot vanish in any real basis: for a
traceless upper triangular matrix the determinant would be the negative
of a square, contrary to `det X₀=1`. Since the lower-left entry of `K`
is zero, equation (6) forces `β=0`. Its determinant then gives
`α=±1`, and its positive diagonal entries give `α=1`. Consequently

\[
\boxed{\widetilde H=H.}
\tag{7}
\]

The positivity argument is needed here to exclude the central matrix
`−I`; it has not been silently identified with `I`.

## 5. The two endpoint matrices recover all three factors

Define `M=B/A`. For the data (4)–(5),

\[
M=\frac{q^2-1}{r^2},\qquad
C^2=\frac{(q-1)^2}{r^2},\qquad
M-C^2=\frac{2(q-1)}{r^2}>0.
\]

Hence the three factors are uniquely reconstructed by

\[
\boxed{
r=\frac{2C}{M-C^2},\qquad
q=\frac{M+C^2}{M-C^2},\qquad
p=\frac{A(M+C^2)}{2C}.
}
\tag{8}
\]

These formulas also apply to the degenerate representation of the
shorter words in Section 3. The same endpoint pairs force the same
`F` and, by (7), the same `H`, hence the same `A,B,C`. Equation (8)
therefore forces all three factors to agree with the original
`p,q,r>1`. This contradicts the required `p̃=1` or `r̃=1` for a
shorter word. The obstruction is proved.

In fact, the argument also proves uniqueness among `010` segments with
fixed initial state and both endpoint pairs: there are no distinct
positive factors of that same word yielding those endpoints. Physical
durations are then fixed by their positive active margins.

## 6. An explicit feasible segment

Start at the circle state `X₀=J` in the original coordinates, with any
initial frame of determinant one. Its three star margins in the scaled
coordinates are all `k=2/√3`. Take the factors

\[
p=q=r=6/5
\]

on the word `010`. The exact prefix margins, divided by `k`, are

| Stage | Margins divided by `k` |
| --- | --- |
| Initial | `(1,1,1)` |
| After the first `0` arc | `(1,7/5,2/3)` |
| After the `1` arc | `(3/5,7/5,27/25)` |
| After the last `0` arc | `(3/5,9/5,4/5)` |

These follow directly from the vertex recurrence

\[
p_i=a,\qquad p_{i+1}=(a+b)w-a,\qquad
p_{i-1}=(a+c)/w-a.
\]

All listed margins are positive. On each arc one margin is constant,
one increases, and the other decreases. Thus the entire closed segment
is in the strict star domain, not just its sampled endpoints. Its
positive durations are exactly

\[
(t_1,t_2,t_3)
=\frac{\log(6/5)}{\sqrt3}(1,7/5,3/5).
\]

Solving `g′=gX` gives an actual integral-form state-trajectory segment.
No global closing condition `g(T)=R` is imposed on this local example.
The theorem applies to any occurrence of such a positive `010` window
inside a longer trajectory, with that window's endpoints held fixed.

## 7. What a viable shortening argument must change

A local three-to-two deletion preserving both endpoint states and frames
is impossible in the stated vertex class. Matching only the tangent
product does not preserve the state, as the explicit two-factor attempt
in Section 2 demonstrates.

The proof leaves open replacements that also change neighboring arcs,
use a larger window, alter the initial shape of the complete trajectory,
or use nonvertex controls. It supplies no lower bound on the number of
arcs of a global minimizer and no uniform bound on longer words. It is
recorded to prevent a false elementary shortening step from being used
in the unrestricted Reinhardt comparison.
