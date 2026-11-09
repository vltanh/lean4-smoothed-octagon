module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.ShapeCurve
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PsiRatio.Numerator

/-!
# Smaller-short window, Casimir floor: at `e = 13/5`, `Ψ` decreases in `x`

At fixed `d ∈ [0, 1/19]`, on the shape curve `a = 1 + 13d/5`, `b = x(1 + d)`, `u = U(x) = ū(x, b)`,
write (`cas_w3_psi_eq`)

`Ψ = Γ(x, U) - (F(x) + (U - v)ρ)/7`,

where `F = r₁(x, v)` is the cost along the lower norm `v` and `ρ = (r₁)_u`. Its derivative is

`Γ_x + Γ_u U' - (f + (U' - 9/1000)ρ + (U - v)ρ_x)/7`

with `Γ_x ≤ -17/2000`, `0 ≤ Γ_u ≤ 41/200` (`PsiRatio/CasimirPart`), `9/1000 ≤ U' ≤ 1/100`, `U ≥ v`
(`PsiRatio/IncomingNorm`), `ρ > 0`, `ρ_x ≥ 0` (`PsiRatio/NormCoefficient`) and `f > -1/25` (`PsiRatio/LowerNorm`,
`PsiRatio/Numerator`), so it is at most `-17/2000 + 41/20000 + 1/175 < 0`.

## Main API

* `cas_W3`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- **W3**: at `e = 13/5`, `Ψ` decreases in `x`. -/
theorem cas_W3 {d x₁ x₂ : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) (h1 : 2 ≤ x₁) (h12 : x₁ ≤ x₂)
    (h2 : x₂ ≤ 13 / 6) : casPsiC x₂ d (13 / 5) ≤ casPsiC x₁ d (13 / 5) := by
  have hanti := jet_anti_of (a := 2) (b := 13 / 6)
    (f := fun x => casClosedG x (ssUbar x (x * (1 + d))) -
      (casW3F x d + (ssUbar x (x * (1 + d)) - casW3v x d) * casW3rho x d) / 7)
    (f₁ := fun x => casW3Gx x (ssUbar x (x * (1 + d))) +
        casW3Gu x (ssUbar x (x * (1 + d))) * casW3UX x d -
      (casW3n x d / ((1 + 13 / 5 * d) * casW3B x d ^ 2 * casW3K x d ^ 2) - 1 / 25 +
        ((casW3UX x d - 9 / 1000) * casW3rho x d + (ssUbar x (x * (1 + d)) - casW3v x d) *
          (casW3q x d / ((1 + 13 / 5 * d) * casW3B x d ^ 2 * casW3K x d ^ 2)))) / 7)
    (fun x hx => by
      have hU := cas_w3_U_deriv hx.1 hd
      exact (cas_w3_G_deriv hU (by linarith [hx.1])).fun_sub
        (((cas_w3_F_deriv hx.1 hx.2 hd hd').fun_add ((hU.fun_sub (cas_w3_v_deriv x d)).fun_mul
          (cas_w3_rho_deriv hx.1 hx.2 hd hd'))).div_const 7))
    (fun x hx => by
      obtain ⟨hx0, hx1⟩ := hx
      obtain ⟨hUX0, hUX1⟩ := cas_w3_UX_bounds hx0 hx1 hd hd'
      have hUl := cas_w3_U_ge hx0 hx1 hd hd'
      have hUu := cas_w3_U_le hx0 hx1 hd hd'
      have hUv := cas_w3_U_ge_v hx0 hx1 hd hd'
      have hGx := cas_w3_Gx_le (u := ssUbar x (x * (1 + d))) hx0 hUu
      obtain ⟨hGu0, hGu1⟩ := cas_w3_Gu_bounds hx0 hx1 hUl hUu
      obtain ⟨ha, haB, hK, -, -⟩ := cas_w3_curve hx0 hx1 hd hd'
      have hn : 0 < casW3n x d / ((1 + 13 / 5 * d) * casW3B x d ^ 2 * casW3K x d ^ 2) :=
        div_pos (cas_w3_n_pos hx0 hx1 hd hd')
          (mul_pos (mul_pos (by linarith) (pow_pos (by linarith) 2)) (pow_pos hK 2))
      have hrho := cas_w3_rho_pos hx0 hx1 hd hd'
      have hq := cas_w3_rho_deriv_nonneg hx0 hx1 hd hd'
      have t1 : casW3Gu x (ssUbar x (x * (1 + d))) * casW3UX x d ≤ 41 / 200 * (1 / 100) :=
        mul_le_mul hGu1 hUX1 (by linarith) (by norm_num)
      have t2 : 0 ≤ (casW3UX x d - 9 / 1000) * casW3rho x d :=
        mul_nonneg (by linarith) hrho.le
      have t3 : 0 ≤ (ssUbar x (x * (1 + d)) - casW3v x d) *
          (casW3q x d / ((1 + 13 / 5 * d) * casW3B x d ^ 2 * casW3K x d ^ 2)) :=
        mul_nonneg (by linarith) hq
      linarith)
    h1 h12 h2
  have e₁ := cas_w3_psi_eq h1 (h12.trans h2) hd hd' (ssUbar x₁ (x₁ * (1 + d)))
  have e₂ := cas_w3_psi_eq (h1.trans h12) h2 hd hd' (ssUbar x₂ (x₂ * (1 + d)))
  unfold casPsiC
  rw [e₁, e₂]
  exact hanti

end SmoothedOctagon
