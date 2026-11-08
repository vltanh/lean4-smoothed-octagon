module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Interface
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs14.Basic
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs14.Slope
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Hs14.Data

/-!
# Gate S4: definitions

The scalar functions of gate S4, kept apart from `S4.lean` so that the certificate modules
`Heavy/S4*.lean` can state their signs with them and `S4.lean` can import those certificates.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `Φ = Γ_*(q_c) - R*_2(q_c)/7` (`SMALL_SHAPE_CASIMIR_FLOOR` (10)). -/
noncomputable def hs4Phi (x be al u : ℝ) : ℝ :=
  hsGs x al u (hsQc x al) - hsRs x be al u (hsQc x al) 2 / 7

/-- `Ψ = Φ - (T - 2)(w_*(q_c) - 3/4)/7`, `T = r_A/q_c` (`SMALL_SHAPE_CASIMIR_FLOOR` (11)). -/
noncomputable def hs4Psi (x be al u : ℝ) : ℝ :=
  hs4Phi x be al u - (hsRA al be / hsQc x al - 2) * (hsWs x be al u (hsQc x al) - 3 / 4) / 7

end SmoothedOctagon
