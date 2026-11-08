module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1Base

/-!
# Gate S1, outer face: the face functions

On the outer face `q = 1/7` (`ρ = 1/K`, `K = 6α² + 1`) the upper envelope has the transport form
`λ = K/(7α²)`, `d = D/(7α²)`, `v = U(S/K)`, `E = S(u - 1) + 1/S + (2S - 1)/K`,
`Γ_* = K²(4uv - E²)/(576α⁴)`, `T = 7r_A = 7α/(α + β)`, `y = 2/T = 2(α + β)/(7α)`
(`LOW_RATIO_OUTER_HAND_SIGN` §3; inventory HS-S01 D-R5(b)).

## Main API

* atoms `hh1oK`, `hh1oL`, `hh1od`, `hh1ov`, `hh1oE`, `hh1oy`, `hh1oT`; envelope values `hh1ow`, `hh1oEL`,
  `hh1oG`; tests `hh1oR2`, `hh1oF0`, `hh1oF1`;
* `hh1o_face_red`: `Γ_*(1/7) - (7/96)R*_τ(1/7) - g ≥ min(F₀, F₁)` for `2 ≤ τ ≤ 7r_A`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `K = 6α² + 1`. -/
noncomputable def hh1oK (a : ℝ) : ℝ := 6 * a ^ 2 + 1

/-- `λ = K/(7α²)`. -/
noncomputable def hh1oL (a : ℝ) : ℝ := hh1oK a / (7 * a ^ 2)

/-- `d = D/(7α²)`. -/
noncomputable def hh1od (x a b : ℝ) : ℝ := hsDg x b a / (7 * a ^ 2)

/-- `v = U(S/K)`. -/
noncomputable def hh1ov (x a : ℝ) : ℝ := 1 - (1 + x) / hh1oK a + ((1 + x) / hh1oK a) ^ 2

/-- `E = S(u - 1) + 1/S + (2S - 1)/K`. -/
noncomputable def hh1oE (x a u : ℝ) : ℝ := (1 + x) * (u - 1) + 1 / (1 + x) + (2 * (1 + x) - 1) / hh1oK a

/-- `w = λ²v + d²u - dλE`. -/
noncomputable def hh1ow (x a b u : ℝ) : ℝ :=
  hh1oL a ^ 2 * hh1ov x a + hh1od x a b ^ 2 * u - hh1od x a b * hh1oL a * hh1oE x a u

/-- `E_L = 2du - λE`. -/
noncomputable def hh1oEL (x a b u : ℝ) : ℝ := 2 * hh1od x a b * u - hh1oL a * hh1oE x a u

/-- `Γ_* = K²(4uv - E²)/(576α⁴)`. -/
noncomputable def hh1oG (x a u : ℝ) : ℝ :=
  (4 * u * hh1ov x a - hh1oE x a u ^ 2) * hh1oK a ^ 2 / (576 * a ^ 4)

/-- `y = 2/T = 2(α + β)/(7α)`. -/
noncomputable def hh1oy (a b : ℝ) : ℝ := 2 * (a + b) / (7 * a)

/-- `T = 7r_A = 7α/(α + β)`. -/
noncomputable def hh1oT (a b : ℝ) : ℝ := 7 * a / (a + b)

/-- `R̄₂ = 2w - 1/2 + (u - 1)/r_A + r_A - 1/7 - E_L + ℓ(2/T)`. -/
noncomputable def hh1oR2 (x a b u : ℝ) : ℝ :=
  2 * hh1ow x a b u - 1 / 2 + (u - 1) * (a + b) / a + a / (a + b) - 1 / 7 - hh1oEL x a b u +
    hh1ell (hh1oy a b)

/-- The outer test `F₀`. -/
noncomputable def hh1oF0 (x a b u : ℝ) : ℝ := hh1oG x a u - 7 / 96 * hh1oR2 x a b u - 9193 / 50000

/-- The outer test `F₁ = F₀ - (7/96)(T - 2)(w - 3/4)`. -/
noncomputable def hh1oF1 (x a b u : ℝ) : ℝ :=
  hh1oF0 x a b u - 7 / 96 * (hh1oT a b - 2) * (hh1ow x a b u - 3 / 4)

theorem hh1o_env {x a b u : ℝ} (hx : 0 < x) (ha : 1 ≤ a) :
    hsGs x a u (1 / 7) = hh1oG x a u ∧ hsWs x b a u (1 / 7) = hh1ow x a b u ∧
      hsELs x b a u (1 / 7) = hh1oEL x a b u := by
  have ha0 : 0 < a := by linarith
  have hrho : hsRhoOf a (1 / 7) = 1 / hh1oK a := by
    have h1 : a ^ 2 - (a ^ 2 - 1) * (1 / 7) = (6 * a ^ 2 + 1) / 7 := by ring
    unfold hsRhoOf hh1oK; rw [h1]; field_simp
  have hK : 0 < hh1oK a := by unfold hh1oK; positivity
  have hS : 0 < 1 + x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold hsGs hh1oG hh1ov hh1oE hsE0 m2U
    rw [hrho]
    have h1 : 1 - 1 / hh1oK a = 6 * a ^ 2 / hh1oK a := by unfold hh1oK; field_simp; ring
    rw [h1]
    field_simp
    ring
  · simp only [hsWs, hsA1, hsA2, hsE0, hh1ow, hh1ov, hh1oE, hh1oL, hh1od, hh1oK]
    field_simp
    ring
  · simp only [hsELs, hsA3, hsE0, hh1oEL, hh1oE, hh1oL, hh1od, hh1oK]
    field_simp
    ring

/-- **The outer duration reduction** (`LOW_RATIO_OUTER_HAND_SIGN` (5)-(8)): for `x > 0`, `α ≥ 1`,
`β > 0` and `2 ≤ τ ≤ 7r_A`: `Γ_*(1/7) - (7/96)R*_τ(1/7) - 9193/50000 ≥ min(F₀, F₁)`. -/
theorem hh1o_face_red {x a b u τ : ℝ} (hx : 0 < x) (ha : 1 ≤ a) (hb : 0 < b) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA a b) :
    min (hh1oF0 x a b u) (hh1oF1 x a b u) ≤
      hsGs x a u (1 / 7) - 7 / 96 * hsRs x b a u (1 / 7) τ - 9193 / 50000 := by
  obtain ⟨hG, hW, hE⟩ := hh1o_env (b := b) (u := u) hx ha
  have ha0 : 0 < a := by linarith
  have hrA : hsRA a b = a / (a + b) := rfl
  have hred := hh1_tau_red (G := hh1oG x a u) (w := hh1ow x a b u)
    (κ := (u - 1) / hsRA a b + hsRA a b + 1 - 1 / 7 - hh1oEL x a b u) (T := 7 * hsRA a b) hτ hτT
  have hlog : log (τ * (1 / 7) / hsRA a b) = log (τ / (7 * hsRA a b)) := by
    congr 1; field_simp
  have hR : hsRs x b a u (1 / 7) τ = (hh1ow x a b u - 1) * τ + 1 / τ +
      ((u - 1) / hsRA a b + hsRA a b + 1 - 1 / 7 - hh1oEL x a b u) + log (τ / (7 * hsRA a b)) := by
    unfold hsRs hsF
    rw [hW, hE, hlog]; ring
  rw [hR, hG]
  refine le_trans (le_of_eq ?_) hred
  have h2T : 2 / (7 * hsRA a b) = hh1oy a b := by
    rw [hrA]; unfold hh1oy; field_simp
  unfold hh1oF1 hh1oF0 hh1oR2 hh1oT
  rw [h2T, hrA]
  have hab : a + b ≠ 0 := by positivity
  congr 1 <;> field_simp <;> ring

end SmoothedOctagon
