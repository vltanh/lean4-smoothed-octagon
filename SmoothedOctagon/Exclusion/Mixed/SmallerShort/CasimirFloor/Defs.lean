module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Interface
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.CasimirScale
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.NormEndpoint
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.CapData

/-!
# Smaller-short window, Casimir floor: definitions

The scalar functions of the Casimir floor, kept apart from `SmallerShort/CasimirFloor` so that
the modules of `SmallerShort/CasimirFloor/` can state their signs with them.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `Φ = Γ_*(q_c) - R*_2(q_c)/7`. -/
noncomputable def casPhi (x be al u : ℝ) : ℝ :=
  ssGs x al u (ssQc x al) - ssRs x be al u (ssQc x al) 2 / 7

/-- `Ψ = Φ - (T - 2)(w_*(q_c) - 3/4)/7`, `T = r_A/q_c`. -/
noncomputable def casPsi (x be al u : ℝ) : ℝ :=
  casPhi x be al u - (ssRA al be / ssQc x al - 2) * (ssWs x be al u (ssQc x al) - 3 / 4) / 7

end SmoothedOctagon
