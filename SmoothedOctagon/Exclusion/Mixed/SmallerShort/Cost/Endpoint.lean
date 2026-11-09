module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.Displacement
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity

/-!
# S6 final score: the unconditional closed-box comparison
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set MeasureTheory

/-- Exact shape-coordinate concavity at the variance floor, including d=0. -/
theorem s6_final_score_shape_min {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    min (s6FinalScore R d 3) (s6FinalScore R d (13/5)) ≤ s6FinalScore R d e := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hRlt : R < 1 := by linarith only [hR1]
  have hV := (s6_final_v_bounds hR hR1 hd).1
  have hu : 3/4 ≤ s6VarianceFloor R d := by unfold s6FinalV at hV; linarith only [hV]
  obtain ⟨hZU,hZL⟩ := cost_shear_envelopes_pos hR hR1 hd hd1
  have hc := (costBExact_strictConcaveOn hR hR1 hu hZU.le hZL).concaveOn
  have hleft := costT_correlated_bounds hR hR1 hd hd1 (by norm_num : (13/5:ℝ) ≤ 3) (le_refl 3)
  have hright := costT_correlated_bounds hR hR1 hd hd1 (le_refl (13/5)) (by norm_num : (13/5:ℝ) ≤ 3)
  have hlo := costT_antitone_shape hR0 hRlt hd (by linarith only [he] : 1 ≤ e) he1
  have hhi := costT_antitone_shape hR0 hRlt hd (by norm_num : (1:ℝ) ≤ 13/5) he
  exact hc.min_le_of_mem_Icc hleft hright ⟨hlo,hhi⟩

/-- Endpoint assembly from proved maximal-displacement concavity. -/
theorem s6_final_score_endpoint_of_R_concavity {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : e=13/5 ∨ e=3)
    (hc : ConcaveOn ℝ (Icc (1/3:ℝ) (7/19)) (fun R => s6FinalScore R (1/19) e)) :
    9/4000 < s6FinalScore R d e := by
  have he0 : 13/5 ≤ e := by rcases he with rfl | rfl <;> norm_num
  have he1 : e ≤ 3 := by rcases he with rfl | rfl <;> norm_num
  have hcorner0 := s6_final_four_corners (R:=1/3) (Or.inl rfl) he
  have hcorner1 := s6_final_four_corners (R:=7/19) (Or.inr rfl) he
  have hmin := hc.min_le_of_mem_Icc
    (show (1/3:ℝ)∈Icc (1/3) (7/19) by norm_num)
    (show (7/19:ℝ)∈Icc (1/3) (7/19) by norm_num) ⟨hR,hR1⟩
  have hscore : 9/4000 < s6FinalScore R (1/19) e := (lt_min hcorner0 hcorner1).trans_le hmin
  exact hscore.trans_le (s6_final_score_antitone_displacement hR hR1 hd hd1 (le_refl (1/19)) he0 he1)

/-- The two endpoint concavities are discharged by the final theorem below. -/
theorem s6_final_score_of_two_R_concavities {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3)
    (hc3 : ConcaveOn ℝ (Icc (1/3:ℝ) (7/19)) (fun R => s6FinalScore R (1/19) 3))
    (hc13 : ConcaveOn ℝ (Icc (1/3:ℝ) (7/19)) (fun R => s6FinalScore R (1/19) (13/5))) :
    9/4000 < s6FinalScore R d e := by
  have h3 := s6_final_score_endpoint_of_R_concavity hR hR1 hd hd1 (Or.inr rfl) hc3
  have h13 := s6_final_score_endpoint_of_R_concavity hR hR1 hd hd1 (Or.inl rfl) hc13
  exact (lt_min h3 h13).trans_le (s6_final_score_shape_min hR hR1 hd hd1 he he1)

/-- Face of gate S6: the exact score at the genuine variance floor exceeds
  the paper's threshold on its whole closed shape/displacement box. -/
theorem s6_final_score_gt {R d e : ℝ}
    (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) (hd : 0 ≤ d) (hd1 : d ≤ 1/19)
    (he : 13/5 ≤ e) (he1 : e ≤ 3) : 9/4000 < s6FinalScore R d e := by
  exact s6_final_score_of_two_R_concavities hR hR1 hd hd1 he he1
    (s6_final_score_concave_R (by norm_num) (le_refl 3))
    (s6_final_score_concave_R (le_refl (13/5)) (by norm_num))

end SmoothedOctagon
