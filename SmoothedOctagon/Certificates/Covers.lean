module

public import SmoothedOctagon.Certificates.SmallerShort
public import SmoothedOctagon.Certificates.Nonshort

/-!
# The interval covers, as named hypotheses

The computer-assisted interval covers that the proof still uses, collected into the hypothesis
`IntervalCovers` of the main theorem. Each field is the proposition its C++ run certifies (see
`SmoothedOctagon.Certificates.SmallerShort` and `.Nonshort`). They stay hypotheses until their hand
replacements are complete (`docs/HAND_PROOF_STATUS.md`): gate H-S for the smaller-short cover, and
the forward-successor part of gate H-N for the two forward endpoint covers.

All three are used by case M2 (`MIXED_SMALLER_SHORT_PERIOD_EXCLUSION`,
`MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION`). The two case-F covers, the nonshort reverse-successor
cover and the low-`a` cover are no longer used: those steps follow ChatGPT Pro's hand theorems
(`HAND_FORWARD_PERIOD_EXCLUSION`, `MIXED_NONSHORT_REVERSE_HAND_EXCLUSION`,
`MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION`).
-/

@[expose] public section

namespace SmoothedOctagon.Certificates

/-- The case-M2 covers still in use, hypotheses pending the hand proofs of gate H-S and of the
forward-successor part of gate H-N. -/
structure MixedCovers : Prop where
  /-- The smaller-short cover (`MIXED_SMALLER_SHORT_PERIOD_EXCLUSION`, gate H-S). -/
  smallerShort : CertSmallerShort
  /-- Cert-FWD0 (`MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION`, lower endpoint, gate H-N). -/
  nonshortForwardLower : CertNonshortForwardLower
  /-- Cert-FWD1 (`MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION`, upper endpoint, gate H-N). -/
  nonshortForwardUpper : CertNonshortForwardUpper

/-- The interval covers still in use: the hypothesis of the main theorem. -/
structure IntervalCovers : Prop where
  /-- The case-M2 covers (gates H-S and H-N). -/
  mixed : MixedCovers

end SmoothedOctagon.Certificates
