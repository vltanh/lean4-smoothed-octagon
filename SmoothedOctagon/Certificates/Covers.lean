module

public import SmoothedOctagon.Certificates.SmallerShort

/-!
# The interval cover, as a named hypothesis

The one computer-assisted interval cover that the proof still uses, the smaller-short cover of
case M2 (`MIXED_SMALLER_SHORT_PERIOD_EXCLUSION`, gate H-S of `docs/HAND_PROOF_STATUS.md`), as the
hypothesis `IntervalCovers` of the main theorem; its proposition is the one the C++ run certifies
(`SmoothedOctagon.Certificates.SmallerShort`). It is being replaced by a kernel-checked certificate
(`SmoothedOctagon.Interval`).

The other six covers of the original notes are no longer used: case F and the nonshort part of
case M2 follow ChatGPT Pro's hand theorems (`HAND_FORWARD_PERIOD_EXCLUSION`,
`MIXED_NONSHORT_REVERSE_HAND_EXCLUSION`, `MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION`,
`MIXED_NONSHORT_FORWARD_HAND_EXCLUSION`). `Certificates/Nonshort.lean` keeps the scalar
definitions that the M2 chart lemmas and the interval library use.
-/

@[expose] public section

namespace SmoothedOctagon.Certificates

/-- The case-M2 cover still in use, a hypothesis pending the hand proof of gate H-S. -/
structure MixedCovers : Prop where
  /-- The smaller-short cover (`MIXED_SMALLER_SHORT_PERIOD_EXCLUSION`, gate H-S). -/
  smallerShort : CertSmallerShort

/-- The interval covers still in use: the hypothesis of the main theorem. -/
structure IntervalCovers : Prop where
  /-- The case-M2 covers (gates H-S and H-N). -/
  mixed : MixedCovers

end SmoothedOctagon.Certificates
