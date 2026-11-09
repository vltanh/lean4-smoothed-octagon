module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Duration
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Geometry
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Shear.Shape

/-!
# The negative S5 residual at the natural constant norm ceiling
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The original residual is negative at every allowed scale and duration. -/
theorem shr_residual_neg {x be al p q : ℝ}
    (hx : 2 ≤ x) (hx1 : x ≤ 13/6) (hal : 1 ≤ al) (hal1 : al ≤ 7/6)
    (hb : x ≤ be) (hb1 : be ≤ 20*x/19)
    (hq : 0 ≤ q) (hqb : q ≤ (15/16)*ssQc x al) (hp : 0 < p)
    (hpq : 2*q ≤ p) (hpr : p ≤ ssRA al be) : ssPhi x be al (19/25) p 0 q < 0 := by
  obtain ⟨hr,hqc,hA2,hslope,hJ0⟩ := shr_rect_coefficients hx hx1 hal hal1 hb hb1
  have hqc0 : 0 ≤ ssQc x al := by unfold ssQc; positivity
  have hqbhalf : (15/16)*ssQc x al ≤ ssRA al be/2 := by nlinarith only [hqc0,hqc]
  have hJ := ssS5J_neg hx hx1 hal hal1 hb hb1
  have hT := ssS5T_neg hx hx1 hb hb1 hal hal1
  have hres := shr_residual_of_endpoints
    (X := ssE0 x (19/25)+(19/25-1)/ssRA al be+ssRA al be)
    hq hqb hqbhalf hp hpq hpr hA2 hslope hJ0 hJ hT
  simpa only [ssPhi,ssCp,ssLp,zero_mul,add_zero,sub_zero,zero_div] using hres

end SmoothedOctagon
