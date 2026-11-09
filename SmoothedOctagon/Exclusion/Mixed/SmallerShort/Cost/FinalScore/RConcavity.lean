module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity.Pair
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity.Shear
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.FinalScore.RConcavity.Anisotropy

/-!
# S6 final score: concavity at maximal displacement

Combine the three curvature budgets, then apply the second-derivative
criterion on the closed ratio interval.
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set

noncomputable def s6FinalRScore1 (e R : ℝ) : ℝ :=
  s6FinalRPair1 e R-s6FinalRShear1 e R-s6FinalRAniso1 e R
noncomputable def s6FinalRScore2 (e R : ℝ) : ℝ :=
  s6FinalRPair2 e R-s6FinalRShear2 e R-s6FinalRAniso2 e R

private theorem s6_final_rscore_derivatives {e R : ℝ}
    (he : 13/5 ≤ e) (he1 : e ≤ 3) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    HasDerivAt (fun R => s6FinalScore R (1/19) e) (s6FinalRScore1 e R) R ∧
    HasDerivAt (s6FinalRScore1 e) (s6FinalRScore2 e R) R := by
  have hp := s6_final_rpair_derivatives he he1 hR hR1
  have hs := s6_final_rshear_derivatives he he1 hR hR1
  have ha := s6_final_raniso_derivatives he he1 hR hR1
  constructor
  · convert (hp.1.sub hs.1).sub ha.1 using 1
    · ext x
      simp only [Pi.sub_apply]
      exact s6_final_score_decomposition x (1/19) e
    · rfl
  · convert (hp.2.sub hs.2).sub ha.2 using 1 <;> rfl

/-- The paper's maximal-displacement score curvature, with the genuine norm floor. -/
theorem s6_final_score_R_curvature {e R : ℝ}
    (he : 13/5 ≤ e) (he1 : e ≤ 3) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19) :
    s6FinalRScore2 e R < -(1/1764:ℝ) := by
  have hp := s6_final_rpair_second_upper he he1 hR hR1
  have hs := s6_final_rshear_second_lower he he1 hR hR1
  have ha := s6_final_raniso_second_lower he he1 hR hR1
  unfold s6FinalRScore2
  linarith only [hp,hs,ha]

/-- Concavity in R at delta=1/19. -/
theorem s6_final_score_concave_R {e : ℝ} (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    ConcaveOn ℝ (Icc (1/3) (7/19)) (fun R => s6FinalScore R (1/19) e) := by
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (f' := s6FinalRScore1 e) (f'' := s6FinalRScore2 e) ?_ ?_ ?_ ?_
  · intro R hR
    exact (s6_final_rscore_derivatives he he1 hR.1 hR.2).1.continuousAt.continuousWithinAt
  · intro R hR
    have hRc : R ∈ Icc (1/3:ℝ) (7/19) := interior_subset hR
    exact (s6_final_rscore_derivatives he he1 hRc.1 hRc.2).1.hasDerivWithinAt
  · intro R hR
    have hRc : R ∈ Icc (1/3:ℝ) (7/19) := interior_subset hR
    exact (s6_final_rscore_derivatives he he1 hRc.1 hRc.2).2.hasDerivWithinAt
  · intro R hR
    have hRc : R ∈ Icc (1/3:ℝ) (7/19) := interior_subset hR
    have hc := s6_final_score_R_curvature he he1 hRc.1 hRc.2
    linarith only [hc]

end SmoothedOctagon
