module

public import SmoothedOctagon.Certificates.SmallerShort

/-!
# The interval cover

The one interval cover that the proof still uses, the smaller-short cover of case M2
(`MIXED_SMALLER_SHORT_PERIOD_EXCLUSION`), packaged as `IntervalCovers`; its proposition is the one
the C++ run of the notes certifies (`SmoothedOctagon.Certificates.SmallerShort`). Lean proves it
with a kernel-checked certificate, `SmoothedOctagon.Interval.certSmallerShort`, and
`ReinhardtSolution.lean` supplies it to the main theorems. The notes have since proved this case
by hand (gate H-S of `archive/notes/HAND_PROOF_STATUS.md`); its formalization will replace the
certificate.

The other six covers of the original notes are no longer used: case F and the nonshort part of
case M2 follow ChatGPT Pro's hand theorems (`HAND_FORWARD_PERIOD_EXCLUSION`,
`MIXED_NONSHORT_REVERSE_HAND_EXCLUSION`, `MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION`,
`MIXED_NONSHORT_FORWARD_HAND_EXCLUSION`). `Certificates/Nonshort.lean` keeps the scalar
definitions that the M2 chart lemmas and the interval library use.
-/

@[expose] public section

namespace SmoothedOctagon.Certificates

/-- The case-M2 cover still in use (gate H-S). -/
structure MixedCovers : Prop where
  /-- The smaller-short cover (`MIXED_SMALLER_SHORT_PERIOD_EXCLUSION`, gate H-S). -/
  smallerShort : CertSmallerShort

/-- The interval covers still in use, proved by `Interval.certSmallerShort`. -/
structure IntervalCovers : Prop where
  /-- The case-M2 cover (gate H-S). -/
  mixed : MixedCovers

end SmoothedOctagon.Certificates
