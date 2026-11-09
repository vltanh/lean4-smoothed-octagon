module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The constrained symmetric root of the M1 angle comparison

The stationarity level is solved by the inverse of `log ρ - ρ` on `(0,1)`.
Its defining equation and derivative give the minimum of the constrained
shape ratio at the symmetric centre, including the feasible boundary.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real Filter
open scoped Topology

/-- The paper's fixed product coordinate. -/
noncomputable def agSymQ (S : ℝ) : ℝ := 3*(3+S^2)/16
/-- The paper's original stationarity upper bound. -/
noncomputable def agSymF (S rho : ℝ) : ℝ := 1-S-rho+log (4*rho/(1-S))
/-- Separating the rho variable makes the implicit root a one-dimensional inverse. -/
noncomputable def agRootBase (rho : ℝ) : ℝ := log rho-rho
noncomputable def agRootOffset (S : ℝ) : ℝ := 1-S+log 4-log (1-S)
noncomputable def agRootTarget (c S : ℝ) : ℝ := c*sqrt (agSymQ S)-agRootOffset S
noncomputable def agRootInverse : ℝ → ℝ := Function.invFunOn agRootBase (Ioo 0 1)
noncomputable def agSymRoot (c S : ℝ) : ℝ := agRootInverse (agRootTarget c S)

theorem agSymQ_pos (S : ℝ) : 0 < agSymQ S := by unfold agSymQ; positivity

theorem agSymF_split {S rho : ℝ} (hS : S < 1) (hrho : 0 < rho) :
    agSymF S rho = agRootBase rho+agRootOffset S := by
  unfold agSymF agRootBase agRootOffset
  rw [log_div (by positivity : (4*rho:ℝ) ≠ 0) (by linarith : (1-S:ℝ) ≠ 0),
    log_mul (by norm_num : (4:ℝ) ≠ 0) hrho.ne']
  ring

theorem agRootBase_hasStrictDerivAt {rho : ℝ} (hrho : 0 < rho) :
    HasStrictDerivAt agRootBase (1/rho-1) rho := by
  have h := (hasStrictDerivAt_log hrho.ne').sub (hasStrictDerivAt_id rho)
  convert h using 1
  · rfl
  · simp only [one_div]

theorem agRootBase_strictMonoOn : StrictMonoOn agRootBase (Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro rho hrho
    exact (agRootBase_hasStrictDerivAt hrho.1).hasDerivAt.continuousAt.continuousWithinAt
  · intro rho hrho
    rw [interior_Ioo] at hrho
    rw [(agRootBase_hasStrictDerivAt hrho.1).hasDerivAt.deriv]
    rw [sub_pos,lt_div_iff₀ hrho.1]
    linarith only [hrho.2]

theorem agRootInverse_left {rho : ℝ} (hrho : rho ∈ Ioo (0:ℝ) 1) :
    agRootInverse (agRootBase rho) = rho := by
  exact agRootBase_strictMonoOn.injOn.leftInvOn_invFunOn hrho

/-- A root anywhere in the positive monotonicity interval is the chosen root. -/
theorem agSymRoot_eq_of_root {c S rho : ℝ} (hS : S < 1)
    (hrho : rho ∈ Ioo (0:ℝ) 1) (hF : agSymF S rho = c*sqrt (agSymQ S)) :
    agSymRoot c S = rho := by
  have hbase : agRootBase rho = agRootTarget c S := by
    rw [agSymF_split hS hrho.1] at hF
    unfold agRootTarget
    linarith only [hF]
  unfold agSymRoot
  rw [← hbase]
  exact agRootInverse_left hrho

theorem agSymF_at_upper {S : ℝ} (hS : S < 1) :
    agSymF S ((1-S)/4) = 3*(1-S)/4 := by
  have hs : 1-S ≠ 0 := by linarith only [hS]
  unfold agSymF
  rw [show 4*((1-S)/4)/(1-S) = 1 by field_simp]
  rw [log_one]
  ring

/-- IVT existence on an explicit positive compact interval. This retains
equality at the upper feasible endpoint. -/
theorem agSymRoot_exists {c S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hfeas : c*sqrt (agSymQ S) ≤ 3*(1-S)/4) :
    ∃ rho ∈ Ioc (0:ℝ) ((1-S)/4), agSymF S rho = c*sqrt (agSymQ S) := by
  let U := (1-S)/4
  let Y := agRootTarget c S
  let l := exp (Y-1)
  have hU0 : 0 < U := by dsimp [U]; linarith only [hS1]
  have hU1 : U < 1 := by dsimp [U]; linarith only [hS0]
  have hl0 : 0 < l := exp_pos _
  have hY : Y ≤ agRootBase U := by
    have hupper := agSymF_at_upper hS1
    rw [agSymF_split hS1 hU0] at hupper
    dsimp [Y,agRootTarget]
    change c*sqrt (agSymQ S)-agRootOffset S ≤ agRootBase U
    change agRootBase U+agRootOffset S = 3*(1-S)/4 at hupper
    linarith only [hfeas,hupper]
  have hlU : l < U := by
    have htarget : Y-1 < log U := by
      unfold agRootBase at hY
      linarith only [hY,hU0]
    have h := exp_lt_exp.mpr htarget
    rw [exp_log hU0] at h
    exact h
  have hleft : agRootBase l < Y := by
    have hlog : log l = Y-1 := log_exp _
    unfold agRootBase
    rw [hlog]
    linarith only [hl0]
  have hcont : ContinuousOn agRootBase (Icc l U) := by
    intro rho hrho
    exact (agRootBase_hasStrictDerivAt (hl0.trans_le hrho.1)).hasDerivAt.continuousAt.continuousWithinAt
  obtain ⟨rho,hrho,hvalue⟩ := intermediate_value_Icc hlU.le hcont ⟨hleft.le,hY⟩
  refine ⟨rho,⟨hl0.trans_le hrho.1,hrho.2⟩,?_⟩
  rw [agSymF_split hS1 (hl0.trans_le hrho.1),hvalue]
  dsimp [Y,agRootTarget]
  ring

/-- The chosen root has the original equation and the full feasible range. -/
theorem agSymRoot_spec {c S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hfeas : c*sqrt (agSymQ S) ≤ 3*(1-S)/4) :
    agSymRoot c S ∈ Ioc (0:ℝ) ((1-S)/4) ∧
      agSymF S (agSymRoot c S) = c*sqrt (agSymQ S) := by
  obtain ⟨rho,hrho,hF⟩ := agSymRoot_exists hS0 hS1 hfeas
  have hrho1 : rho < 1 := by linarith only [hrho.2,hS0]
  have heq := agSymRoot_eq_of_root hS1 ⟨hrho.1,hrho1⟩ hF
  rw [heq]
  exact ⟨hrho,hF⟩

/-- Uniqueness in the same closed feasible interval, including its upper endpoint. -/
theorem agSymRoot_existsUnique {c S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hfeas : c*sqrt (agSymQ S) ≤ 3*(1-S)/4) :
    ∃! rho, rho ∈ Ioc (0:ℝ) ((1-S)/4) ∧ agSymF S rho = c*sqrt (agSymQ S) := by
  obtain ⟨hrho,hF⟩ := agSymRoot_spec hS0 hS1 hfeas
  refine ⟨agSymRoot c S,⟨hrho,hF⟩,?_⟩
  intro rho hroot
  have hrho1 : rho < 1 := by linarith only [hroot.1.2,hS0]
  exact (agSymRoot_eq_of_root hS1 ⟨hroot.1.1,hrho1⟩ hroot.2).symm

/-- The inverse has an actual derivative wherever its root is in(0,1).
The local inverse theorem applies even at a feasible upper boundary. -/
theorem agRootInverse_hasStrictDerivAt {rho : ℝ} (hrho : rho ∈ Ioo (0:ℝ) 1) :
    HasStrictDerivAt agRootInverse (1/rho-1)⁻¹ (agRootBase rho) := by
  have hd := agRootBase_hasStrictDerivAt hrho.1
  have hd0 : 0 < 1/rho-1 := by
    rw [sub_pos,lt_div_iff₀ hrho.1]
    linarith only [hrho.2]
  have hleft : ∀ᶠ t in 𝓝 rho, agRootInverse (agRootBase t) = t := by
    filter_upwards [isOpen_Ioo.mem_nhds hrho] with t ht
    exact agRootInverse_left ht
  exact hd.to_local_left_inverse hd0.ne' hleft

theorem agSymQ_hasDerivAt (S : ℝ) : HasDerivAt agSymQ (3*S/8) S := by
  have h := (((hasDerivAt_pow 2 S).const_add 3).const_mul 3).div_const 16
  refine h.congr_deriv ?_
  norm_num
  ring

theorem agRootOffset_hasDerivAt {S : ℝ} (hS : S < 1) :
    HasDerivAt agRootOffset (S/(1-S)) S := by
  have hs : 1-S ≠ 0 := by linarith only [hS]
  have h := (((hasDerivAt_id' S).const_sub 1).add_const (log 4)).sub
    (((hasDerivAt_id' S).const_sub 1).log hs)
  refine h.congr_deriv ?_
  field_simp
  ring

theorem agRootTarget_hasDerivAt {c S : ℝ} (hS : S < 1) :
    HasDerivAt (agRootTarget c)
      (c*3*S/(16*sqrt (agSymQ S))-S/(1-S)) S := by
  have h := (((agSymQ_hasDerivAt S).sqrt (agSymQ_pos S).ne').const_mul c).sub
    (agRootOffset_hasDerivAt hS)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- The full-parameter paper root is differentiable in S, including a point
where it meets rho=(1-S)/4. No feasibility-neighborhood hypothesis is added. -/
theorem agSymRoot_hasDerivAt {c S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hfeas : c*sqrt (agSymQ S) ≤ 3*(1-S)/4) :
    HasDerivAt (agSymRoot c)
      (agSymRoot c S/(1-agSymRoot c S)*
        (c*3*S/(16*sqrt (agSymQ S))-S/(1-S))) S := by
  obtain ⟨hrho,hF⟩ := agSymRoot_spec hS0 hS1 hfeas
  have hrho1 : agSymRoot c S < 1 := by linarith only [hrho.2,hS0]
  have hi := agRootInverse_hasStrictDerivAt ⟨hrho.1,hrho1⟩
  have heq : agRootBase (agSymRoot c S) = agRootTarget c S := by
    rw [agSymF_split hS1 hrho.1] at hF
    unfold agRootTarget
    linarith only [hF]
  rw [heq] at hi
  have h := hi.hasDerivAt.comp S (agRootTarget_hasDerivAt (c := c) hS1)
  have hinv : (1/agSymRoot c S-1)⁻¹ = agSymRoot c S/(1-agSymRoot c S) := by
    have hid : 1/agSymRoot c S-1 = (1-agSymRoot c S)/agSymRoot c S := by
      field_simp [hrho.1.ne']
    rw [hid,inv_div]
  rw [hinv] at h
  exact h

/-- Feasibility at the actual shape supplies every preceding shape on the
same closed interval. -/
theorem agRoot_feasible_preceding {c S T : ℝ} (hc : 0 ≤ c) (hS : 0 ≤ S) (hST : S ≤ T)
    (hfeas : c*sqrt (agSymQ T) ≤ 3*(1-T)/4) :
    c*sqrt (agSymQ S) ≤ 3*(1-S)/4 := by
  have hQ : agSymQ S ≤ agSymQ T := by
    unfold agSymQ
    nlinarith only [hS,hST]
  have hroot := sqrt_le_sqrt hQ
  have hm := mul_le_mul_of_nonneg_left hroot hc
  linarith only [hm,hfeas,hST]

theorem agSymQ_zero_sqrt : sqrt (agSymQ 0) = 3/4 := by
  rw [show agSymQ 0 = (3/4:ℝ)^2 by norm_num [agSymQ],sqrt_sq (by norm_num : (0:ℝ) ≤ 3/4)]

/-- The symmetric endpoint has the strict interval stated in the paper. -/
theorem agSymRoot_zero_spec {c : ℝ} (hc : c < 1) :
    0 < agSymRoot c 0 ∧ agSymRoot c 0 < 1/4 ∧
      1-agSymRoot c 0+log (4*agSymRoot c 0) = 3*c/4 := by
  have hfeas : c*sqrt (agSymQ 0) ≤ 3*(1-(0:ℝ))/4 := by
    rw [agSymQ_zero_sqrt]
    linarith only [hc]
  obtain ⟨hrho,hF⟩ := agSymRoot_spec (by norm_num : (0:ℝ) ≤ 0) (by norm_num) hfeas
  have hF0 : 1-agSymRoot c 0+log (4*agSymRoot c 0) = 3*c/4 := by
    rw [agSymQ_zero_sqrt] at hF
    simp only [agSymF,sub_zero,div_one] at hF
    linarith only [hF]
  have hrho1 : agSymRoot c 0 < 1/4 := by
    by_contra hnot
    have hup : agSymRoot c 0 ≤ 1/4 := by simpa only [sub_zero] using hrho.2
    have heq : agSymRoot c 0 = 1/4 := le_antisymm hup (not_lt.mp hnot)
    rw [heq] at hF0
    norm_num at hF0
    linarith only [hc,hF0]
  exact ⟨hrho.1,hrho1,hF0⟩

/-- The same derivative written using the original level equation F=c sqrtQ. -/
theorem agSymRoot_level_hasDerivAt {c S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hfeas : c*sqrt (agSymQ S) ≤ 3*(1-S)/4) :
    HasDerivAt (agSymRoot c)
      (agSymRoot c S/(1-agSymRoot c S)*
        (agSymF S (agSymRoot c S)*S/(3+S^2)-S/(1-S))) S := by
  have h := agSymRoot_hasDerivAt hS0 hS1 hfeas
  have hF := (agSymRoot_spec hS0 hS1 hfeas).2
  have hQrt : 0 < sqrt (agSymQ S) := sqrt_pos.mpr (agSymQ_pos S)
  have hQsq : (sqrt (agSymQ S))^2 = 3*(3+S^2)/16 := by
    exact sq_sqrt (agSymQ_pos S).le
  have heq : c*3*S/(16*sqrt (agSymQ S)) = agSymF S (agSymRoot c S)*S/(3+S^2) := by
    rw [hF]
    have hd : 3+S^2 ≠ 0 := by positivity
    field_simp
    linear_combination -(16*c*S)*hQsq
  rw [heq] at h
  exact h

noncomputable def agSymRootRatio (c S : ℝ) : ℝ := agSymQ S/(1-agSymRoot c S)^2
noncomputable def agSymRootZ (c S : ℝ) : ℝ := 4*agSymRoot c S/(1-S)

theorem agSymRoot_ratio_pos {c S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hfeas : c*sqrt (agSymQ S) ≤ 3*(1-S)/4) : 0 < agSymRootRatio c S := by
  have hrho := (agSymRoot_spec hS0 hS1 hfeas).1
  have hrho1 : agSymRoot c S < 1 := by linarith only [hS0,hrho.2]
  unfold agSymRootRatio
  exact div_pos (agSymQ_pos S) (sq_pos_of_pos (by linarith only [hrho1]))

theorem agSymRoot_z_mem {c S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hfeas : c*sqrt (agSymQ S) ≤ 3*(1-S)/4) : agSymRootZ c S ∈ Ioc (0:ℝ) 1 := by
  have hrho := (agSymRoot_spec hS0 hS1 hfeas).1
  have hd : 0 < 1-S := by linarith only [hS1]
  constructor
  · unfold agSymRootZ; exact div_pos (by linarith only [hrho.1]) hd
  · unfold agSymRootZ
    rw [div_le_one hd]
    linarith only [hrho.2]

/-- Exact simplification of the implicit-gradient bracket. -/
theorem agSymRoot_bracket {c S : ℝ} (hS : S < 1) :
    (1-agSymRoot c S)^2+agSymRoot c S*agSymF S (agSymRoot c S)-
      agSymRoot c S*(3+S^2)/(1-S) =
    1-agSymRootZ c S+agSymRoot c S*log (agSymRootZ c S) := by
  have hs : 1-S ≠ 0 := by linarith only [hS]
  unfold agSymF agSymRootZ
  field_simp
  ring

/-- The exact logarithmic derivative used by the paper's root-curve
comparison. All functions are the original chosen implicit root. -/
theorem agSymRoot_logRatio_hasDerivAt {c S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hfeas : c*sqrt (agSymQ S) ≤ 3*(1-S)/4) :
    HasDerivAt (fun S => log (agSymRootRatio c S))
      (2*S/((3+S^2)*(1-agSymRoot c S)^2)*
        (1-agSymRootZ c S+agSymRoot c S*log (agSymRootZ c S))) S := by
  have hrho := (agSymRoot_spec hS0 hS1 hfeas).1
  have hlt : agSymRoot c S < 1 := by linarith only [hrho.2,hS0]
  have hd : 1-agSymRoot c S ≠ 0 := by linarith only [hlt]
  have hs : 1-S ≠ 0 := by linarith only [hS1]
  have hq : 3+S^2 ≠ 0 := by positivity
  have hr := agSymRoot_level_hasDerivAt hS0 hS1 hfeas
  have hden := (hr.const_sub 1).pow 2
  have hratio := (agSymQ_hasDerivAt S).div hden (pow_ne_zero 2 hd)
  have h := hratio.log (agSymRoot_ratio_pos hS0 hS1 hfeas).ne'
  convert h using 1
  · rfl
  · rw [← agSymRoot_bracket hS1]
    simp only [Pi.pow_apply,Pi.div_apply]
    dsimp only [agSymQ]
    field_simp
    ring

/-- The paper's logarithm lower bound leaves a positive-product bracket. -/
theorem agSymRoot_bracket_nonneg {c S : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hfeas : c*sqrt (agSymQ S) ≤ 3*(1-S)/4) :
    0 ≤ 1-agSymRootZ c S+agSymRoot c S*log (agSymRootZ c S) := by
  have hrho := (agSymRoot_spec hS0 hS1 hfeas).1
  have hz := agSymRoot_z_mem hS0 hS1 hfeas
  have hlog := one_sub_inv_le_log_of_pos hz.1
  have hm := mul_le_mul_of_nonneg_left hlog hrho.1.le
  have heq : 1-agSymRootZ c S+agSymRoot c S*(1-(agSymRootZ c S)⁻¹) =
      (1-agSymRootZ c S)*(3+S)/4 := by
    unfold agSymRootZ
    field_simp [hrho.1.ne']
    ring
  have hp : 0 ≤ (1-agSymRootZ c S)*(3+S)/4 := by
    exact div_nonneg (mul_nonneg (by linarith only [hz.2]) (by linarith only [hS0])) (by norm_num)
  linarith only [hm,heq,hp]

/-- The paper's constrained product ratio has its minimum at the symmetric
shape. The entire closed shape interval is included, even when it collapses. -/
theorem agSymRoot_ratio_zero_le {c S : ℝ} (hc : 0 ≤ c) (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hfeas : c*sqrt (agSymQ S) ≤ 3*(1-S)/4) :
    agSymRootRatio c 0 ≤ agSymRootRatio c S := by
  let f : ℝ → ℝ := fun t => log (agSymRootRatio c t)
  let fp : ℝ → ℝ := fun t =>
    2*t/((3+t^2)*(1-agSymRoot c t)^2)*
      (1-agSymRootZ c t+agSymRoot c t*log (agSymRootZ c t))
  have hfeasible : ∀ t ∈ Icc (0:ℝ) S,
      c*sqrt (agSymQ t) ≤ 3*(1-t)/4 := by
    intro t ht
    exact agRoot_feasible_preceding hc ht.1 ht.2 hfeas
  have hd : ∀ t ∈ Icc (0:ℝ) S, HasDerivAt f (fp t) t := by
    intro t ht
    exact agSymRoot_logRatio_hasDerivAt ht.1 (ht.2.trans_lt hS1) (hfeasible t ht)
  have hn : ∀ t ∈ Icc (0:ℝ) S, 0 ≤ fp t := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hb := agSymRoot_bracket_nonneg ht.1 (ht.2.trans_lt hS1) (hfeasible t ht)
    exact mul_nonneg (by positivity) hb
  have hm : MonotoneOn f (Icc (0:ℝ) S) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 S)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : t ∈ Icc (0:ℝ) S := interior_subset ht
      rw [(hd t ht').deriv]
      exact hn t ht'
  have hlog := hm ⟨le_rfl,hS0⟩ ⟨hS0,le_rfl⟩ hS0
  have hfeas0 := hfeasible 0 ⟨le_rfl,hS0⟩
  exact (log_le_log_iff (agSymRoot_ratio_pos (by norm_num) (by norm_num) hfeas0)
    (agSymRoot_ratio_pos hS0 hS1 hfeas)).mp hlog

theorem agSymF_strictMonoOn_rho {S : ℝ} (hS1 : S < 1) :
    StrictMonoOn (agSymF S) (Ioo (0:ℝ) 1) := by
  intro rho hrho eta heta hlt
  rw [agSymF_split hS1 hrho.1,agSymF_split hS1 heta.1]
  have h := agRootBase_strictMonoOn hrho heta hlt
  linarith only [h]

/-- The original actual-point level hypothesis implies feasibility of the
whole root curve; it is not an extra assumption of the eventual Gram bound. -/
theorem agSymRoot_feasible_of_level {c S rho : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hrho : rho ∈ Ioc (0:ℝ) ((1-S)/4))
    (hlevel : c*sqrt (agSymQ S) ≤ agSymF S rho) :
    c*sqrt (agSymQ S) ≤ 3*(1-S)/4 := by
  have hU0 : 0 < (1-S)/4 := by linarith only [hS1]
  have hU1 : (1-S)/4 < 1 := by linarith only [hS0]
  have hrho1 : rho < 1 := hrho.2.trans_lt hU1
  have hF := (agSymF_strictMonoOn_rho hS1).monotoneOn
    ⟨hrho.1,hrho1⟩ ⟨hU0,hU1⟩ hrho.2
  rw [agSymF_at_upper hS1] at hF
  exact hlevel.trans hF

/-- Lowering the actual radius to the root is justified on the full paper
domain, retaining equality when the actual point is already on the level. -/
theorem agSymRoot_below_actual {c S rho : ℝ} (hS0 : 0 ≤ S) (hS1 : S < 1)
    (hrho : rho ∈ Ioc (0:ℝ) ((1-S)/4))
    (hlevel : c*sqrt (agSymQ S) ≤ agSymF S rho) :
    agSymRoot c S ∈ Ioc (0:ℝ) rho ∧
      agSymF S (agSymRoot c S) = c*sqrt (agSymQ S) := by
  have hfeas := agSymRoot_feasible_of_level hS0 hS1 hrho hlevel
  obtain ⟨hroot,hF⟩ := agSymRoot_spec hS0 hS1 hfeas
  have hroot1 : agSymRoot c S < 1 := by linarith only [hS0,hroot.2]
  have hrho1 : rho < 1 := by linarith only [hS0,hrho.2]
  have hle : agSymRoot c S ≤ rho := by
    apply ((agSymF_strictMonoOn_rho hS1).le_iff_le ⟨hroot.1,hroot1⟩ ⟨hrho.1,hrho1⟩).mp
    rw [hF]
    exact hlevel
  exact ⟨⟨hroot.1,hle⟩,hF⟩

end SmoothedOctagon
