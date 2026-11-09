module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope

/-!
# The two endpoint values of the exact duration tangent
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

noncomputable def ssS5J (x be al : ℝ) : ℝ :=
  ssE0 x (19/25)+(19/25-1)/ssRA al be+ssRA al be+1-ssRA al be*ssA1 x be al (19/25)+
    (15/16*ssQc x al)*(ssRA al be*ssA2 x be al (19/25)+1/ssRA al be-1-ssA3 x be al (19/25))

noncomputable def ssS5T (x be al : ℝ) : ℝ :=
  ssE0 x (19/25)+(19/25-1)/ssRA al be+ssRA al be+
    (15/16*ssQc x al)*(4/ssRA al be-2*ssA1 x be al (19/25)-1-ssA3 x be al (19/25))+
    2*(15/16*ssQc x al)^2*(ssA2 x be al (19/25)-1/(ssRA al be)^2)

end SmoothedOctagon
