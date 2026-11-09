module

public import SmoothedOctagon.Exclusion.ShortRuns.Gap.Log
public import SmoothedOctagon.Exclusion.ShortRuns.Gap.SymmetricRoot

/-!
# The symmetric minimum in the M1 angle gap

A positive-product Padé remainder makes the Gram quotient increase with
radius. Lowering to the stationarity root and then to the symmetric shape
proves the full-parameter minimum. At `c = 3/5`, an exact quadratic comparison
gives the natural competitive cap `5/27`.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real Filter
open scoped Topology

/-- The elementary logarithmic Padé bound in the radial argument. -/
theorem agSym_log_pade {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    log z ≤ 2*(z-1)/(z+1) := by
  let g : ℝ → ℝ := fun x => log x-2*(x-1)/(x+1)
  have hd : ∀ x ∈ Ioi (0:ℝ), HasDerivAt g ((x-1)^2/(x*(x+1)^2)) x := by
    intro x hx
    change 0 < x at hx
    have hxp : x+1 ≠ 0 := by linarith only [hx]
    have h := (hasDerivAt_log hx.ne').sub
      ((((hasDerivAt_id x).sub_const 1).const_mul 2).div
        ((hasDerivAt_id x).add_const 1) hxp)
    convert h using 1
    · rfl
    · simp only [id_eq]
      field_simp [hx.ne',hxp]; ring
  have hm : MonotoneOn g (Ioi (0:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : x ∈ Ioi (0:ℝ) := interior_subset hx
      rw [(hd x hx').deriv]
      exact div_nonneg (sq_nonneg _) (mul_nonneg hx'.le (sq_nonneg _))
  have h := hm hz0 (by norm_num) hz1
  dsimp [g] at h
  rw [log_one] at h
  linarith only [h]

noncomputable def agSymGram (S rho E : ℝ) : ℝ :=
  (4*agSymQ S-E^2)/(16*(1-rho)^2)
noncomputable def agSymRadial (S rho : ℝ) : ℝ := agSymGram S rho (agSymF S rho)
noncomputable def agSymPade (S z : ℝ) : ℝ :=
  (1-S)*(1-z/4)+2*(z-1)/(z+1)

theorem agSymF_rho_hasDerivAt {S rho : ℝ} (hS : S < 1) (hr : 0 < rho) :
    HasDerivAt (agSymF S) (1/rho-1) rho := by
  have hs : 1-S ≠ 0 := by linarith only [hS]
  have harg : 4*rho/(1-S) ≠ 0 := div_ne_zero (by positivity) hs
  have hlog := (((hasDerivAt_id rho).const_mul 4).div_const (1-S)).log harg
  have h := ((hasDerivAt_const rho (1-S)).sub (hasDerivAt_id rho)).add hlog
  convert h using 1
  · rfl
  · simp only [id_eq]
    field_simp [hr.ne',hs]; ring

/-- The original fixed-shape radial derivative. -/
theorem agSymRadial_hasDerivAt {S rho : ℝ} (hS : S < 1)
    (hr : 0 < rho) (hr1 : rho < 1) :
    HasDerivAt (agSymRadial S)
      ((4*agSymQ S-(agSymF S rho)^2-
        agSymF S rho*(1-rho)^2/rho)/(8*(1-rho)^3)) rho := by
  have hd : 1-rho ≠ 0 := by linarith only [hr1]
  have hdpos : 0 < 1-rho := by linarith only [hr1]
  have hF := agSymF_rho_hasDerivAt hS hr
  have h := ((hF.pow 2).const_sub (4*agSymQ S)).div
    ((((hasDerivAt_id rho).const_sub 1).pow 2).const_mul 16) (by simpa using mul_ne_zero (by norm_num : (16:ℝ) ≠ 0) (pow_ne_zero 2 hd))
  convert h using 1
  · rfl
  · simp only [Pi.pow_apply,id_eq]
    field_simp [hr.ne',hd]; ring

/-- Positive-product radial Padé identity. -/
theorem agSymPade_radial_identity {S z : ℝ} (hS : S < 1) (hz : 0 < z) :
    4*agSymQ S-(agSymPade S z)^2-
      agSymPade S z*(1-(1-S)*z/4)^2/((1-S)*z/4) =
    (1-z)*(1-z+S*(1+z))*
      ((1-S)^2*z^2+(S^2+14*S+1)*z+16)/(4*z*(1-S)*(1+z)^2) := by
  have hs : 1-S ≠ 0 := by linarith only [hS]
  have hzp : z+1 ≠ 0 := by linarith only [hz]
  unfold agSymQ agSymPade
  field_simp
  ring

/-- The radial derivative is nonnegative on the paper's nonnegative-level region. -/
theorem agSymRadial_derivative_nonneg {S rho : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hr : rho ∈ Ioc (0:ℝ) ((1-S)/4)) (hF0 : 0 ≤ agSymF S rho) :
    0 ≤ (4*agSymQ S-(agSymF S rho)^2-
      agSymF S rho*(1-rho)^2/rho)/(8*(1-rho)^3) := by
  let z := 4*rho/(1-S)
  have hs : 0 < 1-S := by linarith only [hS1]
  have hr0 : 0 < rho := hr.1
  have hr1 : rho < 1 := by linarith only [hS0,hr.2]
  have hz0 : 0 < z := div_pos (by linarith only [hr.1]) hs
  have hz1 : z ≤ 1 := by dsimp [z]; rw [div_le_one hs]; linarith only [hr.2]
  have hrz : (1-S)*z/4 = rho := by dsimp [z]; field_simp
  have hFH : agSymF S rho ≤ agSymPade S z := by
    have hl := agSym_log_pade hz0 hz1
    unfold agSymF agSymPade
    change 1-S-rho+log z ≤ (1-S)*(1-z/4)+2*(z-1)/(z+1)
    have heq : (1-S)*(1-z/4) = 1-S-rho := by rw [← hrz]; ring
    rw [heq]
    linarith only [hl]
  have hH0 : 0 ≤ agSymPade S z := hF0.trans hFH
  have hnumH : 0 ≤ 4*agSymQ S-(agSymPade S z)^2-
      agSymPade S z*(1-rho)^2/rho := by
    rw [← hrz,agSymPade_radial_identity hS1 hz0]
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg (by linarith only [hz1])
        (add_nonneg (by linarith only [hz1]) (mul_nonneg hS0 (by positivity)))) (by positivity)
    · positivity
  have hsq := sq_le_sq₀ hF0 hH0 |>.2 hFH
  have hlin := mul_le_mul_of_nonneg_right hFH (by positivity : 0 ≤ (1-rho)^2/rho)
  rw [← mul_div_assoc,← mul_div_assoc] at hlin
  have hn : 0 ≤ 4*agSymQ S-(agSymF S rho)^2-
      agSymF S rho*(1-rho)^2/rho := by nlinarith only [hnumH,hsq,hlin]
  exact div_nonneg hn (by positivity)

/-- On the nonnegative level region, lowering rho to its root lowers the
original radial quotient. The entire closed interval is included. -/
theorem agSymRadial_root_le {c S rho : ℝ} (hc : 0 ≤ c) (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hr : rho ∈ Ioc (0:ℝ) ((1-S)/4))
    (hlevel : c*sqrt (agSymQ S) ≤ agSymF S rho) :
    agSymRadial S (agSymRoot c S) ≤ agSymRadial S rho := by
  obtain ⟨hroot,hrootF⟩ := agSymRoot_below_actual hS0 hS1 hr hlevel
  have hr1 : rho < 1 := by linarith only [hS0,hr.2]
  have hr0 : 0 < rho := hr.1
  have hroot1 : agSymRoot c S < 1 := hroot.2.trans_lt hr1
  have hinterval : ∀ t ∈ Icc (agSymRoot c S) rho,
      t ∈ Ioc (0:ℝ) ((1-S)/4) ∧ 0 ≤ agSymF S t := by
    intro t ht
    have ht0 : 0 < t := hroot.1.trans_le ht.1
    have ht1 : t < 1 := ht.2.trans_lt hr1
    have hFt := (agSymF_strictMonoOn_rho hS1).monotoneOn
      ⟨hroot.1,hroot1⟩ ⟨ht0,ht1⟩ ht.1
    rw [hrootF] at hFt
    exact ⟨⟨ht0,ht.2.trans hr.2⟩,(mul_nonneg hc (sqrt_nonneg _)).trans hFt⟩
  have hd : ∀ t ∈ Icc (agSymRoot c S) rho, HasDerivAt (agSymRadial S)
      ((4*agSymQ S-(agSymF S t)^2-agSymF S t*(1-t)^2/t)/(8*(1-t)^3)) t := by
    intro t ht
    exact agSymRadial_hasDerivAt hS1 (hinterval t ht).1.1 (ht.2.trans_lt hr1)
  have hm : MonotoneOn (agSymRadial S) (Icc (agSymRoot c S) rho) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' := interior_subset ht
      rw [(hd t ht').deriv]
      exact agSymRadial_derivative_nonneg hS0 hS1 (hinterval t ht').1 (hinterval t ht').2
  exact hm ⟨le_rfl,hroot.2⟩ ⟨hroot.2,le_rfl⟩ hroot.2

/-- On the root, the original Gram expression is the constrained ratio. -/
theorem agSymRadial_root_eq {c S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hfeas : c*sqrt (agSymQ S) ≤ 3*(1-S)/4) :
    agSymRadial S (agSymRoot c S) = (4-c^2)/16*agSymRootRatio c S := by
  have hroot := agSymRoot_spec hS0 hS1 hfeas
  have hsq : (sqrt (agSymQ S))^2 = agSymQ S := sq_sqrt (agSymQ_pos S).le
  unfold agSymRadial agSymGram agSymRootRatio
  rw [hroot.2,mul_pow,hsq]
  have hd : 1-agSymRoot c S ≠ 0 := by linarith only [hroot.1.2,hS0]
  field_simp [hd]

/-- The full-parameter symmetric minimum, with the exact paper domain. -/
theorem agSymmetric_gram_min {c S rho E : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hS0 : 0 ≤ S) (hS1 : S < 1) (hr : rho ∈ Ioc (0:ℝ) ((1-S)/4))
    (hElo : c*sqrt (agSymQ S) ≤ E) (hEup : E ≤ agSymF S rho) :
    9*(4-c^2)/(256*(1-agSymRoot c 0)^2) ≤ agSymGram S rho E := by
  have hfeas := agSymRoot_feasible_of_level hS0 hS1 hr (hElo.trans hEup)
  have hcurve := agSymRoot_ratio_zero_le hc0.le hS0 hS1 hfeas
  have hcoef : 0 ≤ (4-c^2)/16 := by nlinarith only [hc0,hc1]
  have hcurve' := mul_le_mul_of_nonneg_left hcurve hcoef
  have hbase : (4-c^2)/16*agSymRootRatio c 0 =
      9*(4-c^2)/(256*(1-agSymRoot c 0)^2) := by
    unfold agSymRootRatio agSymQ
    norm_num
    have hd : 1-agSymRoot c 0 ≠ 0 := by
      have hr0 := (agSymRoot_zero_spec hc1).2.1
      linarith only [hr0]
    field_simp [hd]
    ring
  rw [hbase,← agSymRadial_root_eq hS0 hS1 hfeas] at hcurve'
  have hrad := agSymRadial_root_le hc0.le hS0 hS1 hr (hElo.trans hEup)
  have hE0 : 0 ≤ E := (mul_nonneg hc0.le (sqrt_nonneg _)).trans hElo
  have hF0 : 0 ≤ agSymF S rho := hE0.trans hEup
  have hsq := (sq_le_sq₀ hE0 hF0).2 hEup
  have hraise : agSymRadial S rho ≤ agSymGram S rho E := by
    unfold agSymRadial agSymGram
    exact div_le_div_of_nonneg_right (by linarith only [hsq]) (by positivity)
  exact hcurve'.trans (hrad.trans hraise)

/-- At the paper's natural level c=3/5, the Padé bound is a quadratic
in x0=4rho0. -/
theorem agSymRoot_three_fifths_quadratic :
    5*(4*agSymRoot (3/5) 0)^2-46*(4*agSymRoot (3/5) 0)+29 ≤ 0 := by
  obtain ⟨hr0,hr1,hF⟩ := agSymRoot_zero_spec (c := (3/5:ℝ)) (by norm_num)
  have hx0 : 0 < 4*agSymRoot (3/5) 0 := by linarith only [hr0]
  have hx1 : 4*agSymRoot (3/5) 0 ≤ 1 := by linarith only [hr1]
  have hl := agSym_log_pade hx0 hx1
  have hb : 9/20-1+(4*agSymRoot (3/5) 0)/4 ≤
      2*(4*agSymRoot (3/5) 0-1)/(4*agSymRoot (3/5) 0+1) := by
    norm_num at hF
    linarith only [hF,hl]
  have hh := (le_div_iff₀ (by linarith only [hx0] : 0 < 4*agSymRoot (3/5) 0+1)).mp hb
  nlinarith only [hh]

theorem agSymRoot_three_fifths_lower :
    (23-8*sqrt 6)/5 ≤ 4*agSymRoot (3/5) 0 := by
  have hq := agSymRoot_three_fifths_quadratic
  have hr := agSymRoot_zero_spec (c := (3/5:ℝ)) (by norm_num)
  have hs : (sqrt (6:ℝ))^2 = 6 := sq_sqrt (by norm_num)
  have hs0 : 0 < sqrt (6:ℝ) := sqrt_pos.mpr (by norm_num)
  by_contra hn
  have hx : 4*agSymRoot (3/5) 0 < (23-8*sqrt 6)/5 := lt_of_not_ge hn
  have h1 : 0 < 23-5*(4*agSymRoot (3/5) 0)-8*sqrt 6 := by linarith only [hx]
  have h2 : 0 < 23-5*(4*agSymRoot (3/5) 0)+8*sqrt 6 := by linarith only [h1,hs0]
  have hp := mul_pos h1 h2
  nlinarith only [hq,hs,hp]

/-- The symmetric endpoint estimate, retaining the paper's exact radical. -/
theorem agSymRoot_three_fifths_gram_lower :
    273/(16*(131-16*sqrt 6)) ≤
      9*(4-(3/5:ℝ)^2)/(256*(1-agSymRoot (3/5) 0)^2) := by
  obtain ⟨hr0,hr1,hF⟩ := agSymRoot_zero_spec (c := (3/5:ℝ)) (by norm_num)
  have hrlo := agSymRoot_three_fifths_lower
  have hs : (sqrt (6:ℝ))^2 = 6 := sq_sqrt (by norm_num)
  have hs0 : 0 ≤ sqrt (6:ℝ) := sqrt_nonneg _
  have hs5 : sqrt (6:ℝ) < 5/2 := by nlinarith only [hs,hs0]
  have hd : 0 < 131-16*sqrt 6 := by linarith only [hs5]
  have hdroot : 0 < 1-agSymRoot (3/5) 0 := by linarith only [hr1]
  have hup : 1-agSymRoot (3/5) 0 ≤ (8*sqrt 6-3)/20 := by linarith only [hrlo]
  have hupos : 0 ≤ (8*sqrt 6-3)/20 := hdroot.le.trans hup
  have hsq := (sq_le_sq₀ hdroot.le hupos).2 hup
  have hden : (1-agSymRoot (3/5) 0)^2 ≤ 3*(131-16*sqrt 6)/400 := by
    nlinarith only [hsq,hs]
  apply (div_le_div_iff₀ (by positivity : 0 < 16*(131-16*sqrt (6:ℝ)))
    (by positivity : 0 < 256*(1-agSymRoot (3/5) 0)^2)).2
  nlinarith only [hden]

/-- The final strict comparison uses only sqrt6>39/16 and the exact gap11. -/
theorem agSymRoot_three_fifths_exceeds :
    (5/27:ℝ) < 9*(4-(3/5:ℝ)^2)/(256*(1-agSymRoot (3/5) 0)^2) := by
  have hs : (sqrt (6:ℝ))^2 = 6 := sq_sqrt (by norm_num)
  have hs0 : 0 ≤ sqrt (6:ℝ) := sqrt_nonneg _
  have hslo : (39/16:ℝ) < sqrt 6 := by nlinarith only [hs,hs0]
  have hshi : sqrt (6:ℝ) < 5/2 := by nlinarith only [hs,hs0]
  have hd : 0 < 131-16*sqrt 6 := by linarith only [hshi]
  have hmid : (273/1472:ℝ) < 273/(16*(131-16*sqrt 6)) := by
    apply (div_lt_div_iff₀ (by norm_num : (0:ℝ) < 1472) (by positivity)).2
    nlinarith only [hslo]
  have hgap : (5/27:ℝ) < 273/1472 := by norm_num
  exact hgap.trans (hmid.trans_le agSymRoot_three_fifths_gram_lower)

/-- The original core inequality on the paper's full natural competitive cap. -/
theorem ag_core {S z E : ℝ} (hS0 : 0 ≤ S) (hz0 : 0 < z) (hz1 : z ≤ 1)
    (hE : E ≤ (1-S)*(1-z/4)+log z) (hE0 : 0 < E)
    (hE2 : 9/25*(3*(3+S^2)/16) ≤ E^2) :
    16*(5/27)*(1-(1-S)*z/4)^2 < 4*(3*(3+S^2)/16)-E^2 := by
  have hlog : log z ≤ 0 := log_nonpos hz0.le hz1
  have hzquarter : 0 ≤ 1-z/4 := by linarith only [hz1]
  have hS1 : S < 1 := by
    by_contra hn
    have hp : (1-S)*(1-z/4) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith only [hn]) hzquarter
    linarith only [hE,hE0,hlog,hp]
  let rho := (1-S)*z/4
  have hs : 0 < 1-S := by linarith only [hS1]
  have hr0 : 0 < rho := by dsimp [rho]; positivity
  have hrU : rho ≤ (1-S)/4 := by dsimp [rho]; nlinarith only [hz1,hs]
  have hr1 : rho < 1 := by linarith only [hrU,hS0]
  have hF : agSymF S rho = (1-S)*(1-z/4)+log z := by
    unfold agSymF
    have hzid : 4*rho/(1-S) = z := by dsimp [rho]; field_simp
    rw [hzid]
    dsimp [rho]
    ring
  have hQsq : (sqrt (agSymQ S))^2 = agSymQ S := sq_sqrt (agSymQ_pos S).le
  have hroot : 0 ≤ sqrt (agSymQ S) := sqrt_nonneg _
  have hElo : (3/5)*sqrt (agSymQ S) ≤ E := by
    change 9/25*agSymQ S ≤ E^2 at hE2
    nlinarith only [hE2,hQsq,hroot,hE0]
  have hmin := agSymmetric_gram_min (c := (3/5:ℝ)) (by norm_num) (by norm_num)
    hS0 hS1 ⟨hr0,hrU⟩ hElo (hF.symm ▸ hE)
  have hstrict := agSymRoot_three_fifths_exceeds.trans_le hmin
  unfold agSymGram at hstrict
  have hd : 0 < 16*(1-rho)^2 := by positivity
  have hclear := (lt_div_iff₀ hd).mp hstrict
  dsimp [rho,agSymQ] at hclear
  nlinarith only [hclear]

end SmoothedOctagon
