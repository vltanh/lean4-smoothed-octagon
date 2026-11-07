module

public import SmoothedOctagon.Certificates.Forward
public import SmoothedOctagon.Certificates.SmallerShort
public import SmoothedOctagon.Certificates.Nonshort

/-!
# The interval covers, as named hypotheses

The seven computer-assisted interval covers of the hand/computer-assisted proof, collected into
the hypothesis `IntervalCovers` of the main theorem. Each field is the proposition its C++ run
certifies (see `SmoothedOctagon.Certificates.Forward`, `.SmallerShort`, `.Nonshort`). They stay
hypotheses until their hand replacements are complete (`docs/HAND_PROOF_STATUS.md` on the PR
branch): gate H-F for `ForwardCovers`, gates H-S and H-N for `MixedCovers`.

* Case F (`GLOBAL_FORWARD_PERIOD_EXCLUSION`): the neighbour cover (CERT-N, 1 root) and the
  complementary Casimir cover (CERT-C, 3 roots).
* Case M2 (`MIXED_SMALLER_SHORT_PERIOD_EXCLUSION`, `MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION`): the
  smaller-short cover (1 root) and the four smaller-nonshort boundary covers (reverse, low-`a`,
  forward lower and upper endpoint; 2 roots each).
-/

@[expose] public section

namespace SmoothedOctagon.Certificates

/-- The five case-M2 covers, hypotheses pending the hand proofs of gates H-S and H-N. -/
structure MixedCovers : Prop where
  /-- The smaller-short cover (`MIXED_SMALLER_SHORT_PERIOD_EXCLUSION`, gate H-S). -/
  smallerShort : CertSmallerShort
  /-- Cert-REV (`MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION`, gate H-N). -/
  nonshortReverse : CertNonshortReverse
  /-- Cert-LOWA (`MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION`, gate H-N). -/
  nonshortLowA : CertNonshortLowA
  /-- Cert-FWD0 (`MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION`, lower endpoint, gate H-N). -/
  nonshortForwardLower : CertNonshortForwardLower
  /-- Cert-FWD1 (`MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION`, upper endpoint, gate H-N). -/
  nonshortForwardUpper : CertNonshortForwardUpper

/-- All seven interval covers: the hypothesis of the main theorem. -/
structure IntervalCovers : Prop where
  /-- The case-F covers (gate H-F). -/
  forward : ForwardCovers
  /-- The case-M2 covers (gates H-S and H-N). -/
  mixed : MixedCovers

end SmoothedOctagon.Certificates
