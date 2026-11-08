# Constructing the determinant-one clock

`SmoothedOctagon/DeterminantClock.lean` constructs the matrix frame and time change
needed to pass from a balanced contact curve toward the Reinhardt control problem.
Its main theorem starts from `IsBalancedPair K σ tf`. The frame, the positive clock,
and the normalized matrix state are all constructed from that data.

**Validation: not run.** These are source-level Lean proofs with the hand derivation
below. Lean compilation, Lake commands, kernel validation, and CI have not been run.
The module introduces no axiom, `sorry`, or `admit`.

## The global contact frame

Let `s_j*` be the standard sixth-root contact configuration and put

\[
g(t)=\left[\;\sigma_0(t)\quad
 \frac{2\sigma_1(t)-\sigma_0(t)}{\sqrt3}\;\right].
\]

Because `s₀* = (1,0)` and `s₁* = (1/2, √3/2)`, this matrix satisfies

\[
g(t)s_0^*=\sigma_0(t),\qquad g(t)s_1^*=\sigma_1(t).
\]

These two equations determine the matrix uniquely. The multi-point relation
`s_{j+1} = s_j + s_{j+2}` propagates them to all six indices:

\[
\sigma_j(t)=g(t)s_j^*.
\]

Both standard and moving adjacent contacts have determinant `√3/2`. Applying the
usual determinant transformation law to the two contact equations yields
`det g(t) = 1`. Every matrix entry is a fixed linear combination of contact
coordinates, so it is `C¹`. Every common period of the six contacts is a period of
`g`. In circle representation, uniqueness of the frame gives `g(0) = I`.

The source makes this frame global on `ℝ`; it does not choose unrelated frames on
different parameter intervals.

## The positive speed derived from the star condition

Define the raw logarithmic derivative by

\[
X(t)=g(t)^{-1}g'(t).
\]

The frame is invertible, and therefore `g' = gX`. Differentiating `det g = 1`
gives `tr X = 0`. The upstream balanced star inequalities, through
`corollary3_1_6`, give

\[
\rho_0(X(t))>0,\quad\rho_1(X(t))>0,\quad\rho_2(X(t))>0,
\quad\det X(t)>0.
\]

The raw state is continuous: `g'` is continuous and the inverse of the regular
matrix frame is continuous. It is periodic because both the frame and its
entrywise derivative have the common full period `6 tf`.

Consequently the determinant speed

\[
w(t)=\sqrt{\det X(t)}
\]

is continuous, strictly positive, and periodic. This speed is the one required for
determinant normalization. It need not equal the Euclidean speed used earlier to
construct the balanced boundary parametrization.

## The constructed inverse clock

Define

\[
S(t)=\int_0^t w(u)\,du,
\qquad P=\int_0^{6t_f}w(u)\,du>0.
\]

The general theorem `exists_inverse_integral_reparam` from `ArcLength.lean`
constructs an increasing order isomorphism `a = S⁻¹` with

\[
a(0)=0,\qquad a\in C^1,\qquad
 a'(s)=\frac1{w(a(s))}>0,\qquad
 a(s+P)=a(s)+6t_f.
\]

Thus the curve in the new time parameter is

\[
G(s)=g(a(s)),\qquad
Y(s)=a'(s)X(a(s)).
\]

The chain rule gives the actual matrix differential equation

\[
G'(s)=G(s)Y(s).
\]

Since these matrices are two-dimensional,

\[
\det Y(s)=a'(s)^2\det X(a(s))
 =\frac{\det X(a(s))}{w(a(s))^2}=1.
\]

The trace remains zero, and each `ρ_i` is linear under scalar multiplication.
The scalar `a'(s)` is positive, so all three star inequalities remain strict.
The source therefore proves `IsStarState (Y s)` for every real `s`.

Upstream `proposition3_1_9` concludes that this normalized state is globally
Lipschitz entry by entry. Its hypotheses include an existing positive change of
parameter and the determinant-one equation. The present module supplies both
of those hypotheses by the explicit construction above.

## Compatibility with the cyclic contact successor

The module also proves an identity that will be used to determine the control
terminal time. Suppose a `C¹` map `φ` has positive derivative and advances every
contact by one:

\[
\sigma_j(\phi(t))=\sigma_{j+1}(t).
\]

The frame uniqueness theorem and `R s_j* = s_{j+1}*` give

\[
g(\phi(t))=g(t)R.
\]

Differentiate this equation and take determinants. Since `det R = 1` and
`det g = 1`, the result is

\[
\phi'(t)^2\det X(\phi(t))=\det X(t).
\]

All relevant speeds are positive, so the source concludes

\[
\boxed{w(\phi(t))\phi'(t)=w(t).}
\]

This is `determinantSpeed_contact_shift`. Its contact-successor assumptions are
explicit; constructing such a successor for the actual worst disk is the separate
contact-lift step. The identity explains why the determinant clock is compatible
with cyclic contact geometry and avoids choosing an unrelated second clock.

Suppose also that the successor has the actual sixfold lift relation

\[
\phi^{\circ6}(t)=t+6t_f.
\]

The theorem `determinantClock_conjugates_successor` proves the corresponding
constant translation in determinant time. Set

\[
F(s)=a^{-1}(\phi(a(s))).
\]

The inverse-function derivative formula gives `(a⁻¹)'(t) = w(t)`. Combining the
three chain-rule factors with the speed identity above yields

\[
F'(s)=w(\phi(a(s)))\,\phi'(a(s))\,\frac1{w(a(s))}=1.
\]

The function `F(s) − s` therefore has zero derivative everywhere on `ℝ` and is
constant. Write `F(s) = s + c`; equivalently,

\[
\phi(a(s))=a(s+c).
\]

Iterating this identity six times gives `φ⁶(a(s)) = a(s + 6c)`. The sixfold lift
relation and the already constructed full-period identity give

\[
a(s+6c)=a(s)+6t_f=a(s+P).
\]

Injectivity of the order isomorphism `a` implies `6c = P`. Consequently the source
proves the exact time normalization

\[
\boxed{\phi(a(s))=a(s+P/6).}
\]

This proof uses the constructed clock derivative and its full-period drift; it
does not assume that the new parameter already has a constant contact shift.

## Main theorem and remaining interfaces

`balanced_exists_determinant_clock` produces a positive full period `P` and an
order isomorphism `a : ℝ ≃o ℝ`. Its conclusions include:

- `a 0 = 0` and `ContDiff ℝ 1 a`.
- The exact inverse-speed `HasDerivAt` formula and positivity of `deriv a`.
- The full-period identity `a(t + P) = a(t) + 6 tf`.
- `IsStarState (normalizedContactState σ a t)` for every `t`.
- Global `LipschitzOnEntrywise` of that state.
- The global entrywise differential equation `G' = GY`.

The definitions are

```lean
contactLogDerivative σ t =
  (contactFrame σ t)⁻¹ * derivEntrywise (contactFrame σ) t

determinantSpeed σ t = √((contactLogDerivative σ t).det)

normalizedContactState σ a t =
  deriv a t • contactLogDerivative σ (a t)
```

The additional `determinantClock_conjugates_successor` theorem proves the precise
`P / 6` contact translation once the positive successor and its sixfold relation
are supplied. `CyclicClock.lean` applies it to the successor constructed by
`ContactLift.lean` and derives matrix terminal conditions. Measurable control
construction and its integral state equations belong to their own bridge. Comparing against every admissible control trajectory
also requires the converse passage from those trajectories to the geometric
competitor class; this time-normalization theorem supplies no such comparison.

## Source references

The upstream polygon dependency is pinned at
`8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f`.

- [Boundary.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch2/Boundary.lean):
  `bdy_mp_succ`, `bdy_seq_eq`, and `bdy_isMultiPoint_sixthRoot`.
- [StateDynamics.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch3/StateDynamics.lean):
  `corollary3_1_6` and `proposition3_1_9`.
- [AreaFormula.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch3/AreaFormula.lean):
  `oct_det2_mulVec`, `oct_trace_eq_zero`, and `oct_R_mulVec_sixthRoot`.
- [MatrixEntrywise.lean](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/Basic/Analysis/Calculus/MatrixEntrywise.lean):
  entrywise differentiation, inverse differentiation, the chain rule, and derivative
  uniqueness for the matrix curves.

The scalar inverse-integral construction and its pinned Mathlib dependencies are
recorded in [ARC_LENGTH.md](ARC_LENGTH.md).
