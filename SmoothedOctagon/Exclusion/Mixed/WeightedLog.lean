module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# A weighted reciprocal bound for the mixed logarithm estimates

The density `3s²` has mean-square `3/5`. Its reciprocal tangent has a positive
square remainder, giving the logarithm bound for both mixed secant ceilings.
-/

@[expose] public section

namespace SmoothedOctagon
open Set Real

/-- Weighted reciprocal mean: the density `3s²` has mean-square `3/5`.
The reciprocal's tangent has a positive square remainder. -/
theorem mix_weighted_reciprocal_log {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1) :
    2*tau*(1+tau^2/(3*(1-3*tau^2/5))) < log (1+tau)-log (1-tau) := by
  let D := 1-3*tau^2/5
  let f : ℝ → ℝ := fun s => s^2/(1-tau^2*s^2)
  let p : ℝ → ℝ := fun s => s^2/D+tau^2/D^2*s^2*(s^2-3/5)
  have ht2 : tau^2 < 1 := by simpa using (sq_lt_sq₀ ht0.le (by norm_num : (0:ℝ) ≤ 1)).2 ht1
  have hD : 0 < D := by dsimp [D]; nlinarith only [ht2]
  have hden : ∀ s ∈ Icc (0:ℝ) 1, 0 < 1-tau^2*s^2 := by
    intro s hs
    have hss : s^2 ≤ 1 := by simpa using (sq_le_sq₀ hs.1 (by norm_num : (0:ℝ) ≤ 1)).2 hs.2
    have hm := mul_le_mul_of_nonneg_left hss (sq_nonneg tau)
    nlinarith only [hm,ht2]
  have hf : ContinuousOn f (Icc (0:ℝ) 1) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro s hs; exact (hden s hs).ne'
  have hp : Continuous p := by dsimp [p]; fun_prop
  have hid : ∀ s ∈ Icc (0:ℝ) 1,
      f s-p s=tau^4*s^2*(s^2-3/5)^2/((1-tau^2*s^2)*D^2) := by
    intro s hs
    have hd' : 1-s^2*tau^2 ≠ 0 := by nlinarith only [hden s hs]
    dsimp [f,p]
    field_simp [hD.ne',(hden s hs).ne',hd']
    dsimp [D]
    ring
  have hcmp := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0:ℝ) < 1) hp.continuousOn hf (fun s hs => by
      have hh := hid s ⟨hs.1.le,hs.2⟩
      have hpos : 0 ≤ tau^4*s^2*(s^2-3/5)^2/((1-tau^2*s^2)*D^2) := by
        apply div_nonneg (by positivity)
        exact mul_nonneg (hden s ⟨hs.1.le,hs.2⟩).le (sq_nonneg _)
      linarith only [hh,hpos]) (by
      refine ⟨1,⟨by norm_num,le_rfl⟩,?_⟩
      have hh := hid 1 ⟨by norm_num,le_rfl⟩
      have hpos : 0 < tau^4*(1:ℝ)^2*((1:ℝ)^2-3/5)^2/((1-tau^2*(1:ℝ)^2)*D^2) := by
        have hd1 := hden 1 ⟨by norm_num,le_rfl⟩
        positivity
      linarith only [hh,hpos])
  have hpi : (∫ s in (0:ℝ)..1, p s)=1/(3*D) := by
    let P : ℝ → ℝ := fun s => s^3/(3*D)+tau^2/D^2*(s^5/5-s^3/5)
    have hd : ∀ s : ℝ, HasDerivAt P (p s) s := by
      intro s
      have h := ((hasDerivAt_pow 3 s).div_const (3*D)).add
        ((((hasDerivAt_pow 5 s).div_const 5).sub
          ((hasDerivAt_pow 3 s).div_const 5)).const_mul (tau^2/D^2))
      refine h.congr_deriv ?_
      dsimp [p]
      norm_num
      field_simp
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hd s) (hp.intervalIntegrable 0 1)
    simpa [P] using hi
  have hfi : (∫ s in (0:ℝ)..1, f s)=
      (log (1+tau)-log (1-tau))/(2*tau^3)-1/tau^2 := by
    let P : ℝ → ℝ := fun s =>
      (log (1+tau*s)-log (1-tau*s))/(2*tau^3)-s/tau^2
    have hd : ∀ s ∈ uIcc (0:ℝ) 1, HasDerivAt P (f s) s := by
      intro s hs
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
      have hmul : tau*s ≤ tau := mul_le_of_le_one_right ht0.le hs.2
      have hs0 : 0 ≤ s := hs.1
      have hp1 : 0 < 1+tau*s := by positivity
      have hm1 : 0 < 1-tau*s := by linarith only [hmul,ht1]
      have hd1 : 1-tau^2*s^2 ≠ 0 := (hden s hs).ne'
      have h := (((((hasDerivAt_id' s).const_mul tau).const_add 1).log hp1.ne').sub
        ((((hasDerivAt_id' s).const_mul tau).const_sub 1).log hm1.ne')).div_const (2*tau^3)
      have hh := h.sub ((hasDerivAt_id' s).div_const (tau^2))
      refine hh.congr_deriv ?_
      dsimp [f]
      field_simp [ht0.ne',hp1.ne',hm1.ne',hd1]
      ring
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      (hf.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1))
    simpa [P] using hi
  rw [hpi,hfi] at hcmp
  have hs : 1/(3*D)+1/tau^2 <
      (log (1+tau)-log (1-tau))/(2*tau^3) := by linarith only [hcmp]
  have hclear := (lt_div_iff₀ (by positivity : (0:ℝ) < 2*tau^3)).mp hs
  have heq : 2*tau*(1+tau^2/(3*D))=(1/(3*D)+1/tau^2)*(2*tau^3) := by
    field_simp
    ring
  change 2*tau*(1+tau^2/(3*D)) < log (1+tau)-log (1-tau)
  rw [heq]
  exact hclear

/-- The weighted-Jensen logarithm bound in its symmetric coordinate. -/
noncomputable def mixLogWeighted (x : ℝ) : ℝ :=
  let tau := x/(x+2)
  2*tau*(1+tau^2/(3*(1-3*tau^2/5)))

theorem mix_log_weighted_lt {x : ℝ} (hx : 0 < x) :
    mixLogWeighted x < log (1+x) := by
  have hxp : 0 < x+2 := by positivity
  have ht0 : 0 < x/(x+2) := div_pos hx hxp
  have ht1 : x/(x+2) < 1 := by rw [div_lt_one hxp]; linarith only
  have h := mix_weighted_reciprocal_log ht0 ht1
  have hp : 0 < 1+x/(x+2) := by positivity
  have hm : 0 < 1-x/(x+2) := by linarith only [ht1]
  rw [← log_div hp.ne' hm.ne'] at h
  have heq : (1+x/(x+2))/(1-x/(x+2))=1+x := by field_simp; ring
  rw [heq] at h
  exact h

/-- Exact rational form used when subtracting the secant ceilings. -/
theorem mixLogWeighted_eq {x : ℝ} (hx : 0 < x) :
    mixLogWeighted x = x*(15*(x+2)^2-4*x^2)/(3*(x+2)*(x^2+10*x+10)) := by
  let X := x+2
  let Q := x^2+10*x+10
  have hX : 0 < X := by dsimp [X]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hD : 1-3*(x/X)^2/5=2*Q/(5*X^2) := by
    field_simp [hX.ne']
    dsimp [X,Q]
    ring
  change 2*(x/X)*(1+(x/X)^2/(3*(1-3*(x/X)^2/5))) =
    x*(15*X^2-4*x^2)/(3*X*Q)
  rw [hD]
  field_simp [hX.ne',hQ.ne']
  dsimp [X,Q]
  ring

end SmoothedOctagon
