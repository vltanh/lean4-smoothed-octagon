module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Defs
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.AngleCancellation

/-!
# S6 exact central score

The identity `JK = 2c - 3b/2` converts the additional-angle estimate into
a shear loss. Norm monotonicity and the supplied shear envelopes give a lower score.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- Norm monotonicity of the exact score. -/
theorem s6_exact_norm_mono {R T u v ZU ZL : ℝ}
    (hR : 0 ≤ R) (hT : 0 ≤ T) (hZU : 0 ≤ ZU) (huv : u ≤ v) :
    costBExact R T u ZU ZL ≤ costBExact R T v ZU ZL := by
  have hid : costBExact R T v ZU ZL-costBExact R T u ZU ZL =
      (v-u)*(2*R/(3+R^2)+2*T/(3+T^2)+
        ZU/2*(1/(3+R^2)+1/(3+T^2))) := by
    unfold costBExact
    ring
  have hpos : 0 ≤ (v-u)*(2*R/(3+R^2)+2*T/(3+T^2)+
        ZU/2*(1/(3+R^2)+1/(3+T^2))) := by
    have : 0 ≤ v-u := sub_nonneg.mpr huv
    positivity
  linarith only [hid,hpos]

/-- The two supplied envelopes give a lower score. -/
theorem s6_exact_envelopes {R T u Z ZU ZL : ℝ}
    (hb : 0 ≤ (1-4*u/(3+R^2))+(1-4*u/(3+T^2)))
    (hZL : 0 < ZL) (hZLZ : ZL ≤ Z) (hZZU : Z ≤ ZU) :
    costBExact R T u ZU ZL ≤ costBExact R T u Z Z := by
  have hZ : 0 < Z := hZL.trans_le hZLZ
  have hid : costBExact R T u Z Z-costBExact R T u ZU ZL =
      ((1-4*u/(3+R^2))+(1-4*u/(3+T^2)))*(ZU-Z)/8+
      (161/54)*((R^2-T^2)/(3+T^2))^2*(Z-ZL)/(8*Z*ZL) := by
    unfold costBExact
    field_simp
    ring
  have hfirst : 0 ≤ ((1-4*u/(3+R^2))+(1-4*u/(3+T^2)))*(ZU-Z)/8 := by
    exact div_nonneg (mul_nonneg hb (sub_nonneg.mpr hZZU)) (by norm_num)
  have hlast : 0 ≤ (161/54)*((R^2-T^2)/(3+T^2))^2*(Z-ZL)/(8*Z*ZL) := by
    have : 0 ≤ Z-ZL := sub_nonneg.mpr hZLZ
    positivity
  linarith only [hid,hfirst,hlast]

/-- The exact angle cancellation and the original JK identity give the shear loss. -/
theorem s6_exact_shear_loss {J K b H nu omega : ℝ}
    (hH : 0 < H) (hK : 4 < K) (hb : 0 ≤ b)
    (hJK : J*K = 161/27-3*b/2)
    (homega : omega < 2*H/K+nu^2/(8*H)) :
    -(3/8)*b*H-(161/54)*nu^2/(8*H) < J*H-(161/54)*omega := by
  have hK0 : 0 < K := by linarith only [hK]
  have hcancel : J*H-(161/54)*(2*H/K+nu^2/(8*H)) =
      -(3/2)*b*H/K-(161/54)*nu^2/(8*H) := by
    field_simp
    nlinarith only [hJK]
  have hdiv : b*H/K ≤ b*H/4 :=
    div_le_div_of_nonneg_left (mul_nonneg hb hH.le) (by norm_num) hK.le
  have hstrict := mul_lt_mul_of_pos_left homega (by norm_num : (0:ℝ)<161/54)
  ring_nf at hcancel hdiv hstrict ⊢
  linarith only [hcancel,hdiv,hstrict]

/-- The original anisotropy is the ratio of the two switch ceilings. -/
private lemma s6_An_eq {x be al : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    (1+ssAn x be al)*((3+ssTs al be^2)/4) = (3+ssRr x^2)/4 := by
  unfold ssAn ssRr ssTs
  have : 0 < al^2+al*be+be^2 := by positivity
  field_simp
  ring

/-- The exact raw score follows from the original central cost and angle definitions. -/
theorem s6_exact_raw_score {x be al u : ℝ}
    (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be)
    (hu : 0 < u) (hJk : costJ0 x u < 40/27)
    (hAn : 0 ≤ ssAn x be al)
    (hu1 : u ≤ (3+ssRr x^2)/4) (hu2 : u ≤ (3+ssTs al be^2)/4)
    (hH : 0 < costZ x be al/sqrt 3) (hH1 : costZ x be al/sqrt 3 < 1/5)
    (hvar : 6*(ssAn x be al)^2 < (costZ x be al/sqrt 3)^2) :
    (161/54)*π/3+sqrt 3*costBExact (ssRr x) (ssTs al be) u
      (costZ x be al) (costZ x be al) < costFc x be al u := by
  have hU1 : m2U (1/(1+x)) = (3+ssRr x^2)/4 := by
    unfold m2U ssRr
    field_simp
    ring
  have hAnEq := s6_An_eq hx hal hbe
  have hs : 0 < sqrt (3:ℝ) := by positivity
  have hs2 : (sqrt (3:ℝ))^2 = 3 := sq_sqrt (by norm_num)
  have hJ : 0 < costJ0 x u := by rw [costJ0,hU1]; positivity
  have hK : ssAn x be al+4 < costK x be al u := by
    have hdiv : 2 < 2*(40/27)/costJ0 x u := by
      rw [lt_div_iff₀ hJ]
      linarith only [hJk]
    unfold costK
    linarith only [hdiv]
  have hK4 : 4 < costK x be al u := by linarith only [hK,hAn]
  have homega := s6_additional_angle_lt hAn hK hH hH1 hvar
  change costomega x be al u < _ at homega
  let b := (1-4*u/(3+ssRr x^2))+(1-4*u/(3+ssTs al be^2))
  have hb : 0 ≤ b := by
    have h1 : 4*u/(3+ssRr x^2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith only [hu1]
    have h2 : 4*u/(3+ssTs al be^2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith only [hu2]
    dsimp [b]
    linarith only [h1,h2]
  have hnu : ssAn x be al = (ssRr x^2-ssTs al be^2)/(3+ssTs al be^2) := by
    rw [eq_div_iff (by positivity)]
    nlinarith only [hAnEq]
  have hJK : costJ0 x u*costK x be al u = 161/27-3*b/2 := by
    unfold costK costJ0 b
    rw [hU1,hnu]
    field_simp
    ring
  have hloss := s6_exact_shear_loss hH hK4 hb hJK homega
  have hinv : (1:ℝ)/sqrt 3 = sqrt 3/3 := by
    rw [div_eq_div_iff hs.ne' (by norm_num)]
    nlinarith only [hs2]
  have hHform : costZ x be al/sqrt 3 = sqrt 3*costZ x be al/3 := by
    calc
      costZ x be al/sqrt 3 = costZ x be al*(1/sqrt 3) := by ring
      _ = sqrt 3*costZ x be al/3 := by rw [hinv]; ring
  have hsplit : costCc x be al u-costJ0 x u*(costZ x be al/sqrt 3) =
      sqrt 3*(ssRr x+ssTs al be-
        ((1-4*u/(3+ssRr x^2))*ssRr x+(1-4*u/(3+ssTs al be^2))*ssTs al be)/2) := by
    rw [hHform]
    unfold costCc costZ costJ0
    rw [hU1,hnu]
    field_simp
    ring
  have hZ : 0 < costZ x be al := by
    have : 0 < (costZ x be al/sqrt 3)*sqrt 3 := mul_pos hH hs
    simpa only [div_mul_cancel₀ _ hs.ne'] using this
  have hCexpr : costCc x be al u =
      sqrt 3*(ssRr x+ssTs al be-
        ((1-4*u/(3+ssRr x^2))*ssRr x+(1-4*u/(3+ssTs al be^2))*ssTs al be)/2)+
      costJ0 x u*(costZ x be al/sqrt 3) := by linarith only [hsplit]
  have hnuconv : (161/54)*(ssAn x be al)^2/(8*(costZ x be al/sqrt 3)) =
      sqrt 3*(161/54)*(ssAn x be al)^2/(8*costZ x be al) := by
    field_simp
  have hid :
      (161/54)*π/3+sqrt 3*costBExact (ssRr x) (ssTs al be) u
        (costZ x be al) (costZ x be al) - costFc x be al u =
      -(3/8)*b*(costZ x be al/sqrt 3)-
        (161/54)*(ssAn x be al)^2/(8*(costZ x be al/sqrt 3))-
        (costJ0 x u*(costZ x be al/sqrt 3)-(161/54)*costomega x be al u) := by
    unfold costBExact costLExact costFc
    rw [costpsi,← hnu,hCexpr,hnuconv,hHform]
    dsimp [b]
    field_simp
    ring
  linarith only [hid,hloss]

end SmoothedOctagon
