module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW4a
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW4b

/-!
# Gate S4, hand proof W4: `Φ` decreases in `x` on the boundary `d = 1/19`

At fixed `e`, `a = 1 + e/19`, write `Φ = Γ(x, U) - [r₀(x, a, v) + (U - v)ρ]/7`
(`hl46W4_R0_affine`). Its derivative is
`[Γ_x + Γ_u U'] - [f + (U' - 9/1000)ρ + (U - v)C/(361aK³)]/7`
with `Γ_x + Γ_u U' < -7/1000` (`hl46W4_Gamma_slope`), `f > -9/200` (from `N > 0`),
`U' > 9/1000`, `U > v`, `ρ > 0`, `C > 0` (`S4HandW4b`). Hence `Φ_x < -1/1750 < 0`.

## Main API

* `hl46_W4`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- **W4**: at `d = 1/19`, `Φ` decreases in `x`. -/
theorem hl46_W4 {e x₁ x₂ : ℝ} (he : 13 / 5 ≤ e) (he' : e ≤ 3) (h1 : 2 ≤ x₁) (h12 : x₁ ≤ x₂)
    (h2 : x₂ ≤ 13 / 6) : hl46PhiC x₂ (1 / 19) e ≤ hl46PhiC x₁ (1 / 19) e := by
  set a := 1 + e * (1 / 19) with ha_def
  have ha : 108 / 95 ≤ a := by rw [ha_def]; linarith
  have ha' : a ≤ 22 / 19 := by rw [ha_def]; linarith
  have ha0 : 0 < a := by linarith
  -- `Φ = Γ(x, U) - (r₀(x, a, v) + (U - v)ρ)/7` on the boundary
  have hfun : ∀ x, hl46PhiC x (1 / 19) e = hh46S4G x (hsUbar x (x * (1 + 1 / 19))) -
      (hl46W4R0 x a (hl46W4v x) +
        (hsUbar x (x * (1 + 1 / 19)) - hl46W4v x) * hl46W4rho x a) / 7 := by
    intro x
    rw [← hl46W4_R0_affine]
    rfl
  have hd : ∀ x ∈ Icc (2 : ℝ) (13 / 6), HasDerivAt (fun x => hl46PhiC x (1 / 19) e)
      ((hl46W4Gx x (hsUbar x (x * (1 + 1 / 19))) +
          hl46W4Gu x (hsUbar x (x * (1 + 1 / 19))) * hl46W4U1 x) -
        (hl46W4f x a + ((hl46W4U1 x - 9 / 1000) * hl46W4rho x a +
          (hsUbar x (x * (1 + 1 / 19)) - hl46W4v x) *
            (hl46W4C (a - 1) (x - 2) / (361 * a * hl46W4K x a ^ 3)))) / 7) x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hU := hl46W4_U_deriv hx.1
    have := (hl46W4_G_deriv hx0 hU).fun_sub (((hl46W4_ell_deriv hx0 ha0).fun_add
      ((hU.fun_sub (hl46W4_v_deriv x)).fun_mul (hl46W4_rho_deriv hx0 ha0))).div_const 7)
    refine (this.congr_deriv (by ring)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => hfun y)
  refine hl46_anti_of hd (fun x hx => ?_) h1 h12 h2
  obtain ⟨hx, hx'⟩ := hx
  have hx0 : 0 < x := by linarith
  obtain ⟨hUv, hU19, hUs⟩ := hl46W4_U_bounds hx hx'
  obtain ⟨hp, hp'⟩ := hl46W4_U1_bounds hx hx'
  have hv : hl46W4v x = 757 / 1000 + 9 / 1000 * (x - 2) := rfl
  -- the Casimir slope
  have hG := hl46W4_Gamma_slope (u := hsUbar x (x * (1 + 1 / 19))) (p := hl46W4U1 x) hx hx'
    (by linarith) hU19.le (fun h => (hUs h).le) (by linarith) hp'.le
  -- `f > -9/200`
  have hf : -9 / 200 < hl46W4f x a := by
    have e := hl46W4_f_eq hx0 ha0
    have hN := hl46W4_N_pos hx hx' ha ha'
    have hCs : 0 < hl46W4Cs x a := by unfold hl46W4Cs; positivity
    have hK := hl46W4_K_pos x a hx0
    have : 0 < hl46W4N x a / (45125 * a * hl46W4Cs x a ^ 2 * hl46W4K x a ^ 3) := by positivity
    linarith
  -- the two positive coefficients
  have hr := hl46W4_rho_pos hx (by linarith) ha'
  have hC : 0 < hl46W4C (a - 1) (x - 2) / (361 * a * hl46W4K x a ^ 3) := by
    have := hl46W4_C_pos (c := a - 1) (h := x - 2) (by linarith) (by linarith) (by linarith)
    have hK := hl46W4_K_pos x a hx0
    positivity
  have t1 : 0 ≤ (hl46W4U1 x - 9 / 1000) * hl46W4rho x a :=
    mul_nonneg (by linarith) hr.le
  have t2 : 0 ≤ (hsUbar x (x * (1 + 1 / 19)) - hl46W4v x) *
      (hl46W4C (a - 1) (x - 2) / (361 * a * hl46W4K x a ^ 3)) :=
    mul_nonneg (by rw [hv]; linarith) hC.le
  linarith

end SmoothedOctagon
