# Refactor the hand proof to avoid very large integer coefficients

Date: 2026-11-08 UTC. **Optimization project, not a reopened proof
gap.** The existing hand argument and all of its certificates remain
intact until independently checked analytic replacements exist. This
document identifies the high-cost sign arguments and gives exact,
finite replacement targets. **No coefficient-heavy proof is yet
removed by this document.**

## Why a purely cosmetic edit is insufficient

The current sources prove several difficult signs by explicitly
expanding high-degree rational numerators. Moving the arrays to an
appendix, truncating their digits, or replacing them with an
unexplained "computer algebra says positive" would make the displayed
text shorter but would not establish the desired proof without
computer-assisted premises. Large exact constants may also be a sign
that the comparison was performed on an unnecessarily enlarged box.

For example, the central S1 proof derives its incoming-norm derivative
sign on \(8/5\le x\le2,\ 1\le\alpha\le7/6\), despite the **actual
central-cap condition**
\[
\alpha^2\le\frac{x(x+2)}6.
\]
That condition forces \(x\ge\sqrt7-1>23/14\), and the existing proof
already supplies the tighter *correlated* ceiling
\[
1\le\alpha\le
a_U(x):=\frac{1013x+676}{2340}.
\tag{1}
\]
A replacement should exploit this correlation before clearing
denominators. The artificially enlarged rectangle contains hard
points unnecessary for the actual theorem.

## High-cost sources, in priority order

Numbers below count **occurrences of integer literals with 12 or more
digits** in the files at the initial refactor snapshot. They are an
index of the presentation burden, not a substitute for profiling.

| Source | 12+-digit occurrences | Longest integer | Main obstacle |
|---|---:|---:|---|
| [S1 central lower-ratio sign](MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN.md) | 161 | 85 digits | Five derivative/shape lower polynomials and three terminal numerators |
| [S2 central upper-ratio sign](MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_SIGN.md) | 120 | 73 digits | Four derivative lower polynomials and two terminal signs |
| [S2 outer upper-ratio sign](MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_SIGN.md) | 95 | 33 digits | Four derivative lower polynomials, two large-alpha Bernstein tests |
| [S1 outer lower-ratio sign](MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN.md) | 0 | — | 17 coefficient-majorant vectors standing for hundreds of coefficient comparisons |
| [Extended Casimir derivatives](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md) | 11 | 34 digits | Six product-majorant expansions |

These signs do not occur in the terminal five-piece comparison or the
final affine transport. Eliminate the **ratio sign certificates first**;
rewriting the global theorem would not address the bottleneck.

## First completed small-coefficient improvement

The independent [sharper competitive Casimir lemma](HAND_SHARPER_COMPETITIVE_CASIMIR.md)
proves on the *original* competitive noncircular period
\[
\Gamma_{\rm actual}<\frac{9191}{50000},
\]
using only the original spectral inequality, elementary rational bounds
for \(\pi\) and the octagon cost, and integers of at most nine digits
in its main comparison. This improves the older competitive ceiling
by \(1/25000\), without changing an auxiliary scalar shape. The
terminal S1 corrected-Casimir target can therefore be relaxed by
exactly this amount when deriving a new sign proof. **It does not
remove the old coefficient proof.**

## Finite replacement gates

- [ ] **R1 — S1 central:** Retain (1) and the exact equal-secant
  ordering. Replace the enlarged-rectangle incoming/beta derivative
  tables by short derivative or integral bounds on the coupled cone.
  Use the new competitive ceiling and replace the three degree-23-or-
  lower endpoint numerator tables by a few one-variable monotonicity,
  concavity or tangent estimates with explicitly checked rational
  endpoint values.
- [ ] **R2 — S1 outer:** Replace the 17 coefficient vectors and
  hundreds of implied checks by a short order/convexity reduction.
  Keep the three already proved shape ranges if necessary, but seek
  direct analytic bounds for the two duration tests at the actual
  incoming norm. Do not transport a cap to artificial endpoints.
- [ ] **R3 — S2 central:** Retain the integrated cubic duration loss
  (a linear duration bound is not uniformly strong enough). Seek
  simple beta and ratio-direction derivative estimates before
  clearing a numerator; replace both large terminal expansions with
  rational inequalities on the original coupled domain.
- [ ] **R4 — S2 outer:** Keep the exhaustive split at
  \(\alpha=3/2\) only if needed. Replace the large-alpha Bernstein
  coefficient table by derivative/concavity bounds whose constants
  have small rational numerators.
- [ ] **R5 — S4 and physical cost:** Only after R1--R4, simplify
  the surviving six derivative majorants and physical-cost sign
  products. Their factored presentation is already considerably
  more compact; prioritize signs on which the accepted proof depends.

Each replacement gate requires **(i)** a full analytic identity or
inequality with every domain recorded, **(ii)** a sign argument that
does not invoke an executable coefficient scan, **(iii)** checks at
every equality and zero-displacement face, **(iv)** an independent
actual-period and arithmetic review, and **(v)** a commit that
replaces the specific old proof dependency. A numerical experiment
may select a plausible inequality but never closes a gate.

## Stop rule

Do not delete or demote a necessary coefficient expansion merely to
make the Markdown shorter or the arithmetic run faster. A replacement
can have factored expressions, rational endpoint calculations, a few
short polynomial signs or a small justified table, but must stand on
its stated mathematical derivation. If its sign fails, record the
actual counterexample or exact failing scalar inequality and revise
the comparison rather than relaxing the theorem's quantifier.

**Accepted hand theorem:** [HAND_COST_EQUALITY_THEOREM](HAND_COST_EQUALITY_THEOREM.md).
**Active completion ledger:** [HAND_PROOF_STATUS](HAND_PROOF_STATUS.md).
