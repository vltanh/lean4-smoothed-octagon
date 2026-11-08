# Terminal period coverage by a hand switch count

Date: 2026-11-07. Hand proof. No enumeration, executable identity test,
interval certificate, Lean, Lake, typechecking or CI is a premise.

## Theorem

Let an actual globally minimizing Reinhardt trajectory have a finite
positive strict-star vertex representation. Delete zero-duration pieces
and merge adjacent equal controls, including at the actual twisted seam.
Suppose the resulting period has at most five pieces. Then, after a cut
at a genuine switch and a cyclic relabeling, its control word is either

- `0120`, with four pieces; or
- `01020`, with five pieces.

The four-piece cost comparison in
[SMALL_PERIOD_COST_EQUALITY_AUDIT, Section 2](SMALL_PERIOD_COST_EQUALITY_AUDIT.md)
is sharp only at the four octagon factors. The five-piece comparison in
Section 3 of the same note is strict. Consequently every such global
minimizer is the octagon trajectory after the indicated normalization.

This theorem does **not** establish the hypothesis that every minimizer
has at most five pieces. The missing mixed-period hand exclusions must
supply that hypothesis separately. It replaces only the finite-word
coverage in Section 1 of the terminal audit; no numerical or exhaustive
word-generation calculation is needed for that coverage.

## 1. The actual twist gives a congruence

The [finite normality theorem](GLOBAL_NORMALITY.md) applies to every
finite positive minimizing representation, with no lower restriction
on the number of pieces. Use its normal lift on the genuine twisted
extension, as specified in [GLOBAL_PERIODIC_PMP](GLOBAL_PERIODIC_PMP.md).
Write the extended control labels as `i_j` and the number of pieces in
one period as `N`. Then

\[
i_{j+N}=i_j+1\pmod3,\qquad i_{j+1}\ne i_j.
\tag{1}
\]

Each switch therefore has a unique sign
\(\epsilon_j\in\{+1,-1\}\), according as
\(i_{j+1}-i_j\equiv+1\) or \(-1\pmod3\). The signs are
\(N\)-periodic. Summing their label increments across one actual
period, including its seam, gives

\[
\boxed{\sum_{j=0}^{N-1}\epsilon_j\equiv1\pmod3.}
\tag{2}
\]

The last term of (2) compares the final label with the **twisted**
initial label. Omitting that term or replacing the twist by an ordinary
periodic word would give the wrong congruence.

A trajectory using one fixed control edge throughout its period is
impossible, independently of the maximum principle. The explicit shear
frame in [the terminal audit, Section 1](SMALL_PERIOD_COST_EQUALITY_AUDIT.md)
would force the initial half-plane coordinate to be
\(-1/\sqrt3\), outside the strict star. In particular, a one-piece
period is impossible. The same observation handles the unswitched
case before a cut at a genuine switch is selected.

## 2. Two uniform hand inputs

Only the following already proved normal-PMP consequences are used.

1. [GLOBAL_REVERSE_PERIOD_EXCLUSION](GLOBAL_REVERSE_PERIOD_EXCLUSION.md)
   rules out every entirely reverse finite positive period. Its proof
   takes a global minimum of the cyclic active-margin sequence and
   applies the four-arc reverse contradiction. It has no hypothesis
   `N>=6`.
2. [MIXED_GLOBAL_MINIMUM_STRUCTURE, Section 6](MIXED_GLOBAL_MINIMUM_STRUCTURE.md)
   proves that every maximal reverse run in a mixed finite positive
   period has exactly two switches. It likewise has no hypothesis
   `N>=6`.

The local PMP windows used by these results may cross the seam. They
use the genuine extension of the same normal lift and do not assert
that a multi-period splicing variation is globally minimizing. Their
application to the short fundamental periods here is therefore valid.

## 3. All-forward periods

If every switch is forward, (2) gives \(N\equiv1\pmod3\). The only
positive possibilities with \(N\le5\) are \(N=1\) and \(N=4\).
The fixed-edge obstruction removes \(N=1\). When \(N=4\), set the
first label to zero by a cyclic relabeling. The labels advance by one,
so the actual word is

\[
0120.
\tag{3}
\]

Its final label zero is followed by the twisted initial label one,
as required by its forward seam switch.

## 4. Mixed periods

Let \(m\ge1\) be the number of maximal reverse runs, and let
\(F\ge1\) be the total number of forward switches. Each reverse run
has length two by Section 2; each is followed by a nonempty forward
run. Thus

\[
N=2m+F,\qquad F\ge m,\qquad N\ge3m.
\tag{4}
\]

Since \(N\le5\), equation (4) forces \(m=1\). The reverse block
therefore has exactly two switches and the sole forward block has
\(F=N-2\) switches, where \(1\le F\le3\). The twist congruence
(2) now reads

\[
F-2\equiv1\pmod3.
\]

Hence \(F=3\) and \(N=5\). Choose the cut so that the five signs
are \((+,-,-,+,+)\), and cyclically relabel the first arc by zero.
Their successive labels are

\[
0,1,0,2,0,1.
\]

The first five entries form the word

\[
01020,
\tag{5}
\]

and the last entry is exactly the twisted initial label at the next
period. This proves the claimed mixed representative without listing
all words or testing all rebases.

The entirely reverse case has already been excluded by Section 2, so
(3) and (5) exhaust the terminal possibilities.

## 5. The retained analytic comparisons

For (3), tangent closure first forces alternating factors and then the
state endpoint forces the initial state; symmetry is a conclusion.
The derivative/integral inequality in the terminal audit gives a unique
minimum at four factors \(\sqrt2\). For (5), its strict envelope and
positive middle-duration inequality give cost strictly greater than
the octagon. Their displayed identities and calculus arguments are
the mathematical premises; their companion scripts are supplementary.

Thus, conditional only on reaching \(N\le5\), no additional terminal
word search or computational sign theorem is needed. The actual
four-piece equality data determine the original state and frame by
constant-control flow uniqueness. The affine boundary transport in
[GLOBAL_COST_EQUALITY_ASSEMBLY, Section 6](GLOBAL_COST_EQUALITY_ASSEMBLY.md)
then applies to the retained realization of each original equality
disk.
