module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope

/-!
# Coefficient bounds on the enlarged S5 shape rectangle
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

private lemma shr_rect_basics {x be al : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hal : 1 ≤ al) (hal1 : al ≤ 7/6) (hb : x ≤ be) (hb1 : be ≤ 20*x/19) :
    3/10 < ssRA al be ∧ ssRA al be < 3/8 ∧ ssQc x al < ssRA al be/2 ∧
      -1/2 < ssE0 x (19/25) ∧ ssE0 x (19/25) ≤ -1/3 ∧
      0 < ssDg x be al/al^2 ∧ ssDg x be al/al^2 ≤ 9/4 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hal0 : 0 < al := by linarith only [hal]
  have hb0 : 0 < be := hx0.trans_le hb
  have hS : 0 < 1+x := by positivity
  have hN : 0 < x*(x+2)+al^2 := by positivity
  have hsum : 0 < al+be := by positivity
  have hbe1 : be ≤ 130/57 := by linarith only [hb1,hx1]
  have hrlo : 3/10 < ssRA al be := by
    unfold ssRA
    rw [lt_div_iff₀ hsum]
    linarith only [hal,hbe1]
  have hrhi : ssRA al be < 3/8 := by
    unfold ssRA
    rw [div_lt_iff₀ hsum]
    linarith only [hal1,hb,hx]
  have hal2 : al^2 ≤ (7/6)^2 := by nlinarith only [hal,hal1]
  have hp := mul_le_mul hal1 hbe1 hb0.le (by norm_num : (0:ℝ) ≤ 7/6)
  have hV : 8 ≤ x*(x+2) := by nlinarith only [hx]
  have hshape : al^2+2*al*be < x*(x+2) := by nlinarith only [hal2,hp,hV]
  have hqc : ssQc x al < ssRA al be/2 := by
    have heq : ssRA al be/2 = al/(2*(al+be)) := by unfold ssRA; field_simp
    rw [heq,ssQc,div_lt_div_iff₀ hN (by positivity)]
    have hm := mul_pos hal0 (show 0 < x*(x+2)-al^2-2*al*be by linarith only [hshape])
    nlinarith only [hm]
  have hi1 : 1/(1+x) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) (by linarith only [hx])
  have hi2 : 6/19 ≤ 1/(1+x) := by
    have hm := one_div_le_one_div_of_le hS (show 1+x ≤ 19/6 by linarith only [hx1])
    norm_num at hm
    simpa only [one_div] using hm
  have helo : -1/2 < ssE0 x (19/25) := by unfold ssE0; linarith only [hx1,hi2]
  have hehi : ssE0 x (19/25) ≤ -1/3 := by unfold ssE0; linarith only [hx,hi1]
  have hgap : 0 ≤ x-al := by linarith only [hx,hal1]
  have hDlo : 2*(1+2*x-(20/19)*x^2) ≤ ssDg x be al := by
    have hm1 := mul_nonneg hb0.le (show 0 ≤ al-1 by linarith only [hal])
    have hm2 := mul_le_mul_of_nonneg_right hb1 (show 0 ≤ x-1 by linarith only [hx])
    unfold ssDg
    have hm3 := mul_nonneg (show 0 ≤ al-1 by linarith only [hal])
      (show 0 ≤ al+1 by positivity)
    nlinarith only [hm1,hm2,hm3,hx]
  have hx2 : x^2 < 19/4 := by nlinarith only [hx,hx1]
  have hD0 : 0 < ssDg x be al := by nlinarith only [hDlo,hx2,hx]
  have hDhi : ssDg x be al ≤ al^2+4*al-3 := by
    have hm1 := mul_le_mul_of_nonneg_right hb hgap
    have hm2 := mul_nonneg (show 0 ≤ x-2 by linarith only [hx])
      (show 0 ≤ x+1-al by linarith only [hx,hal1])
    unfold ssDg
    nlinarith only [hm1,hm2]
  have hg9 : ssDg x be al/al^2 ≤ 9/4 := by
    rw [div_le_iff₀ (by positivity)]
    have hm := mul_nonneg (show 0 ≤ 6-5*al by linarith only [hal1])
      (show 0 ≤ 2-al by linarith only [hal1])
    nlinarith only [hDhi,hm]
  exact ⟨hrlo,hrhi,hqc,helo,hehi,div_pos hD0 (by positivity),hg9⟩

/-- The endpoint signs and scale motion use only the enlarged closed rectangle. -/
theorem shr_rect_coefficients {x be al : ℝ} (hx : 2 ≤ x) (hx1 : x ≤ 13/6)
    (hal : 1 ≤ al) (hal1 : al ≤ 7/6) (hb : x ≤ be) (hb1 : be ≤ 20*x/19) :
    0 < ssRA al be ∧ ssQc x al < ssRA al be/2 ∧ 0 < ssA2 x be al (19/25) ∧
      2*ssA1 x be al (19/25)+1+ssA3 x be al (19/25) < 2/ssRA al be ∧
      ssE0 x (19/25)+(19/25-1)/ssRA al be+ssRA al be+1-
        ssRA al be*ssA1 x be al (19/25) < 0 := by
  obtain ⟨hrlo,hrhi,hqc,helo,hehi,hg0,hg9⟩ := shr_rect_basics hx hx1 hal hal1 hb hb1
  have hr0 : 0 < ssRA al be := by linarith only [hrlo]
  have hx0 : 0 < x := by linarith only [hx]
  have hal0 : 0 < al := by linarith only [hal]
  have hal2 : 1 ≤ al^2 := by nlinarith only [hal]
  have hal2hi : al^2 ≤ (7/6)^2 := by nlinarith only [hal,hal1]
  let a := 1/al^2
  let e := ssE0 x (19/25)
  let g := ssDg x be al/al^2
  have ha0 : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := by dsimp [a]; rw [div_le_one (by positivity)]; exact hal2
  have ha25 : 25/36 < a := by dsimp [a]; rw [lt_div_iff₀ (by positivity)]; nlinarith only [hal2hi]
  have hepos : 0 ≤ 19/25+e := by dsimp [e]; linarith only [helo]
  have hesum : 19/25+e ≤ 4/9 := by dsimp [e]; linarith only [hehi]
  have hmix := mul_le_mul hg9 hesum hepos (by norm_num : (0:ℝ) ≤ 9/4)
  have heps := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1-a by linarith only [ha1])
    (show e ≤ 0 by dsimp [e]; linarith only [hehi])
  have hid : 2*ssA1 x be al (19/25)+1+ssA3 x be al (19/25) =
      5-3*a+2*g*(19/25+e)+(1-a)*e := by dsimp [a,e,g]; unfold ssA1 ssA3; ring
  have hsum : 2*ssA1 x be al (19/25)+1+ssA3 x be al (19/25) < 59/12 := by
    rw [hid]
    nlinarith only [hmix,heps,ha25]
  have hir : 16/3 < 2/ssRA al be := by rw [lt_div_iff₀ hr0]; linarith only [hrhi]
  have hslope : 2*ssA1 x be al (19/25)+1+ssA3 x be al (19/25) < 2/ssRA al be := by
    linarith only [hsum,hir]
  have hgem := mul_le_mul hg9 (show -e ≤ 1/2 by dsimp [e]; linarith only [helo])
    (show 0 ≤ -e by dsimp [e]; linarith only [hehi]) (by norm_num : (0:ℝ) ≤ 9/4)
  have hna := mul_le_mul_of_nonneg_right (show 1 ≤ 1+x-2 by linarith only [hx]) ha0.le
  have hA1id : ssA1 x be al (19/25) = 2+(1+x-2)*a+g*e := by dsimp [a,g,e]; unfold ssA1; ring
  have hA1 : 3/2 < ssA1 x be al (19/25) := by
    rw [hA1id]
    nlinarith only [hgem,hna,ha25]
  have hterm : (19/25-1)/ssRA al be ≤ -16/27 := by
    rw [div_le_iff₀ hr0]
    linarith only [hrhi]
  have hprod := mul_le_mul hrlo.le hA1.le (by norm_num : (0:ℝ) ≤ 3/2) hr0.le
  have hJ0 : ssE0 x (19/25)+(19/25-1)/ssRA al be+ssRA al be+1-
      ssRA al be*ssA1 x be al (19/25) < 0 := by
    nlinarith only [hehi,hterm,hrhi,hprod]
  exact ⟨hr0,hqc,ss_A2_pos hx (by linarith only [hx1]) hal (by norm_num) (by norm_num),hslope,hJ0⟩

end SmoothedOctagon
