# Lighter polynomial proofs: replacement ledger

This work starts from `main` at
`128a58e456f52fb16768820d564a620fa6313448`. The archived notes are the
source statements; the replacement standard is the user's request of
8 November 2026.

A replacement is accepted here only after its mathematical sign, domain,
caller, and expanded-identity sizes have been checked. A numerical probe
or a large alternative coefficient expansion does not close a row.
The previous archived hand-proof acceptance does not establish that the
requested signs meet this stricter standard. In particular, the S1
generated coefficient tables remain an open hand-proof dependency.

## Already formalized signs, in requested priority order

| Priority | Requested sign | Replacement status |
|---|---|---|
| N1 | `MIXED_NONSHORT_LARGE_GAP_LOW_T_SIGN` (1), `k=1` | Open; first priority. |
| N2 | `MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION` (10), `k=1` | Full sign open. Its [base-quadratic subclaim](NONSHORT_LOW_RATIO.md) is replaced by three 21-monomial degree-eight square identities, with margin greater than 4. |
| N3 | `MIXED_NONSHORT_LARGE_GAP_UPPER_SHAPE_SIGN`, `k=1+j` | Open. |
| N4a | `MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_EXCLUSION` (13), `k=29t²/4` | Open. |
| N4b | The same caller's upper face, `k=1+j` | **Hand dependency removed**, conditional on the retained N4a sign; [shape monotonicity proof](NONSHORT_HIGH_RATIO_SHAPE.md). Lean integration remains open. |

N4b is a caller-preserving weakening, not a claim on an enlarged face
outside the actual feasible shape interval. The exact caller is
`fh_LGB_core` in `SmoothedOctagon/Exclusion/Mixed/FwdHand/LargeGap.lean`.
Its existing lower-endpoint proof `hA` is retained; the new monotonicity
argument replaces `hB` and `fh_comb_pos_of_ends`.

## H-S signs, in requested priority order

| Priority | Gate and note | Replacement status |
|---|---|---|
| S1.1 | `MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN` (16)--(21), Section 5 | Open; first H-S priority. |
| S1.2 | `MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN` (20)--(25), Appendices A--C | Open. |
| S1.3 | `MIXED_SMALLER_SHORT_OUTER_SCALE_LARGE_RATIO_SIGN` (7) | Open. |
| S1.4 | `MIXED_SMALLER_SHORT_CENTRAL_TAU_TWO_SIGN` (3) and `MIXED_SMALLER_SHORT_CENTRAL_DURATION_FACES` (5) | Open. |
| S2.1 | `MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_SIGN` (5) | Open. |
| S2.2 | `MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_SIGN` (11)--(18) | Open. |
| S3.1 | `MIXED_SMALLER_SHORT_DISPLACEMENT_OUTER_FACE` (7)--(21) | Open. |
| S3.2 | `MIXED_SMALLER_SHORT_DISPLACEMENT_CENTRAL_FACE`, Section 2 (4)--(10) | Open. |
| S4 | `MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES` (4)--(30) | Open. |
| S6 | `MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION` (20)--(31) | Open. |

These are the finite requested obligations. The three corrections below
are recorded separately and are not counted as polynomial replacements.

## Repaired H-S interfaces

The [errata and explicit proofs](HS_ERRATA.md) repair all three reported
issues in their original notes:

- Root shear: prove `W>0` and `V>0` before asserting `F>0` and `G>0`
  or multiplying by their denominators. The actual shape yields
  `m≥335/19`, `beta*x-alpha≥54/19`, and `Q≥70/19`.
- Cost exclusion: supply the actual outer cap `rho_A<1/7` from the
  reverse-centre scope theorem at the original competitive period.
  The later scalar continuation uses its critical-angle argument.
- Tau-two scale monotonicity: explicitly require
  `u≥3/4+(x-1)²/[28(x+1)²]`; the actual incoming secant supplies this
  hypothesis and the named caller keeps it unchanged during comparison.

The new expanded correction identities have at most six monomials and
degree at most four. The high-ratio endpoint derivative checks have
11, 15, 12 and 5 monomials, in two variables and degree at most six.
All necessary polynomials and the size counts are printed in the notes.
Independent mathematical and exact-algebra reviews accepted the
high-ratio caller reduction and the low-ratio base quadratic; the three
corrections were separately reviewed against their actual domains and
source callers. The base quadratic is a subordinate replacement and
does not close N2's remaining monotonicity and remainder obligations.

## Validation boundary

Exact rational symbolic calculations check transcription and monomial
counts. The displayed identities and inequalities supply the hand
arguments. No Lean compilation, Lake, typechecking, or CI has been run;
existing Lean proofs, certificate files, and dependency pins are unchanged.
No lower memory or timing measurement is claimed.

The remaining priorities stay open until a complete replacement meets
the requested dimension and size bounds. Smaller coefficients alone,
a sampling result, or a formula defining an unprinted polynomial will
not be used as evidence of closure.
