module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S0
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S1
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S2
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S3
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S4
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S5
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S6

/-!
# Hand proof of the smaller-short case: the assembly (gate S7)

`MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION` §§1-5 and `HAND_ONLY_COMPLETION_PLAN` S7; inventory
HS-S567 Part IV (S7.1-S7.4). The gates S0-S6 apply to the original actual data in order:
S0 `x < 12/5`; S1 `x > 2`; S2 `x < 13/6`; S3 `δ < 1/19`; S4 `α ≤ 1 + 3δ`, `Γ > 1829/10000`; the
strong order gives `α ≥ 1 + 13δ/5`, so the window lies in the common small-shape domain
(`HAND_PERIOD_EXCLUSION` (5)); S5 gives a negative physical shear with `-hR > 5A/2`; S6 then makes
the window cost plus completion exceed `A_oct`, contradicting the window-defect inequality
(`M2Short.defect`).

## Main API

* `m2_short_exclusion_hand`: no smaller-short window exists. It replaces the six-variable interval
  cover of the notes' first proof, which this library used to check by a kernel certificate.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The smaller-short window is excluded by hand** (`MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION`;
gates S0-S7 of `HAND_ONLY_COMPLETION_PLAN`). -/
theorem m2_short_exclusion_hand (D : M2Short) : False := by
  obtain ⟨h0, -, -⟩ := D.hs_S0
  have h1 := D.hs_S1
  have h2 := D.hs_S2 h0
  have h3 := D.hs_S3 h1.le h2.le
  have hδ : 0 ≤ D.B / D.C - 1 := D.ss_box_delta.1
  obtain ⟨hU, hΓ⟩ := D.hs_S4 h1.le h2.le h3.le
  have hL := D.hs_strong_box h1.le
  obtain ⟨-, -, hh, hhR⟩ := D.hs_S5 h1.le h2.le hδ h3.le hL hU
  have h6 := D.hs_S6 h1.le h2.le hδ h3.le hL hU hΓ hh hhR
  exact absurd D.ss_defect.2.2.2.2 (not_le.2 h6)

end SmoothedOctagon
