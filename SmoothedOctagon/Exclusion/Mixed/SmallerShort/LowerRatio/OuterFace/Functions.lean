module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.FaceFunctions

/-!
# Smaller-short window, lower ratio, outer face: the face functions

On the outer face `q = 1/7` (`ρ = 1/K`, `K = 6α² + 1`) the upper envelope has the transport form
`λ = K/(7α²)`, `d = D/(7α²)`, `v = U(S/K)`, `E = S(u - 1) + 1/S + (2S - 1)/K`,
`Γ_* = K²(4uv - E²)/(576α⁴)`, `T = 7r_A = 7α/(α + β)`, `y = 2/T = 2(α + β)/(7α)`.

## Main API

* atoms `lroK`, `lroL`, `lrod`, `lrov`, `lroE`, `lroy`, `lroT`; envelope values `lrow`, `lroEL`,
  `lroG`; tests `lroR2`, `lroF0`, `lroF1`;
* `lro_face_red`: `Γ_*(1/7) - (7/96)R*_τ(1/7) - g ≥ min(F₀, F₁)` for `2 ≤ τ ≤ 7r_A`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `K = 6α² + 1`. -/
noncomputable def lroK (a : ℝ) : ℝ := 6 * a ^ 2 + 1

/-- `λ = K/(7α²)`. -/
noncomputable def lroL (a : ℝ) : ℝ := lroK a / (7 * a ^ 2)

/-- `d = D/(7α²)`. -/
noncomputable def lrod (x a b : ℝ) : ℝ := ssDg x b a / (7 * a ^ 2)

/-- `v = U(S/K)`. -/
noncomputable def lrov (x a : ℝ) : ℝ := 1 - (1 + x) / lroK a + ((1 + x) / lroK a) ^ 2

/-- `E = S(u - 1) + 1/S + (2S - 1)/K`. -/
noncomputable def lroE (x a u : ℝ) : ℝ := (1 + x) * (u - 1) + 1 / (1 + x) + (2 * (1 + x) - 1) / lroK a

/-- `w = λ²v + d²u - dλE`. -/
noncomputable def lrow (x a b u : ℝ) : ℝ :=
  lroL a ^ 2 * lrov x a + lrod x a b ^ 2 * u - lrod x a b * lroL a * lroE x a u

/-- `E_L = 2du - λE`. -/
noncomputable def lroEL (x a b u : ℝ) : ℝ := 2 * lrod x a b * u - lroL a * lroE x a u

/-- `Γ_* = K²(4uv - E²)/(576α⁴)`. -/
noncomputable def lroG (x a u : ℝ) : ℝ :=
  (4 * u * lrov x a - lroE x a u ^ 2) * lroK a ^ 2 / (576 * a ^ 4)

/-- `y = 2/T = 2(α + β)/(7α)`. -/
noncomputable def lroy (a b : ℝ) : ℝ := 2 * (a + b) / (7 * a)

/-- `T = 7r_A = 7α/(α + β)`. -/
noncomputable def lroT (a b : ℝ) : ℝ := 7 * a / (a + b)

/-- `R̄₂ = 2w - 1/2 + (u - 1)/r_A + r_A - 1/7 - E_L + ℓ(2/T)`. -/
noncomputable def lroR2 (x a b u : ℝ) : ℝ :=
  2 * lrow x a b u - 1 / 2 + (u - 1) * (a + b) / a + a / (a + b) - 1 / 7 - lroEL x a b u +
    lrell (lroy a b)

/-- The outer test `F₀`. -/
noncomputable def lroF0 (x a b u : ℝ) : ℝ := lroG x a u - 7 / 96 * lroR2 x a b u - 9193 / 50000

/-- The outer test `F₁ = F₀ - (7/96)(T - 2)(w - 3/4)`. -/
noncomputable def lroF1 (x a b u : ℝ) : ℝ :=
  lroF0 x a b u - 7 / 96 * (lroT a b - 2) * (lrow x a b u - 3 / 4)

theorem lro_env {x a b u : ℝ} (hx : 0 < x) (ha : 1 ≤ a) :
    ssGs x a u (1 / 7) = lroG x a u ∧ ssWs x b a u (1 / 7) = lrow x a b u ∧
      ssELs x b a u (1 / 7) = lroEL x a b u := by
  have ha0 : 0 < a := by linarith
  have hrho : ssRhoOf a (1 / 7) = 1 / lroK a := by
    have h1 : a ^ 2 - (a ^ 2 - 1) * (1 / 7) = (6 * a ^ 2 + 1) / 7 := by ring
    unfold ssRhoOf lroK; rw [h1]; field_simp
  have hK : 0 < lroK a := by unfold lroK; positivity
  have hS : 0 < 1 + x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold ssGs lroG lrov lroE ssE0 m2U
    rw [hrho]
    have h1 : 1 - 1 / lroK a = 6 * a ^ 2 / lroK a := by unfold lroK; field_simp; ring
    rw [h1]
    field_simp
    ring
  · simp only [ssWs, ssA1, ssA2, ssE0, lrow, lrov, lroE, lroL, lrod, lroK]
    field_simp
    ring
  · simp only [ssELs, ssA3, ssE0, lroEL, lroE, lroL, lrod, lroK]
    field_simp
    ring

/-- **The outer duration reduction**: for `x > 0`, `α ≥ 1`,
`β > 0` and `2 ≤ τ ≤ 7r_A`: `Γ_*(1/7) - (7/96)R*_τ(1/7) - 9193/50000 ≥ min(F₀, F₁)`. -/
theorem lro_face_red {x a b u τ : ℝ} (hx : 0 < x) (ha : 1 ≤ a) (hb : 0 < b) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * ssRA a b) :
    min (lroF0 x a b u) (lroF1 x a b u) ≤
      ssGs x a u (1 / 7) - 7 / 96 * ssRs x b a u (1 / 7) τ - 9193 / 50000 := by
  obtain ⟨hG, hW, hE⟩ := lro_env (b := b) (u := u) hx ha
  have ha0 : 0 < a := by linarith
  have hrA : ssRA a b = a / (a + b) := rfl
  have hred := lr_tau_red (G := lroG x a u) (w := lrow x a b u)
    (κ := (u - 1) / ssRA a b + ssRA a b + 1 - 1 / 7 - lroEL x a b u) (T := 7 * ssRA a b) hτ hτT
  have hlog : log (τ * (1 / 7) / ssRA a b) = log (τ / (7 * ssRA a b)) := by
    congr 1; field_simp
  have hR : ssRs x b a u (1 / 7) τ = (lrow x a b u - 1) * τ + 1 / τ +
      ((u - 1) / ssRA a b + ssRA a b + 1 - 1 / 7 - lroEL x a b u) + log (τ / (7 * ssRA a b)) := by
    unfold ssRs ssF
    rw [hW, hE, hlog]; ring
  rw [hR, hG]
  refine le_trans (le_of_eq ?_) hred
  have h2T : 2 / (7 * ssRA a b) = lroy a b := by
    rw [hrA]; unfold lroy; field_simp
  unfold lroF1 lroF0 lroR2 lroT
  rw [h2T, hrA]
  have hab : a + b ≠ 0 := by positivity
  congr 1 <;> field_simp <;> ring

end SmoothedOctagon
