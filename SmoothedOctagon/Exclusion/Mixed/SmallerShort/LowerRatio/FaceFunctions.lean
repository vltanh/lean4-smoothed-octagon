module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Basic

/-!
# Gate S1, terminal faces: the face functions and the duration reduction

Shared definitions for the two terminal face signs of gate S1 (`hs1_central_face`,
`hs1_outer_face`). On a face the upper envelope `Γ_*`,
`w_*`, `E_{L,*}` have closed transport forms (`λ`, `d = λρD`, `v = U(ρS)`, `E = E₀ + ρ(2S - 1)`):

* central face `q = q_c` (`ρ = 1/S²`): `λ = S²/K`, `d = D/K`, `K = x(x + 2) + α²`;
* outer face `q = 1/7` (`ρ = 1/(6α² + 1)`): `λ = K/(7α²)`, `d = D/(7α²)`, `K = 6α² + 1`.

The two duration tests (`hs_dur_max` with the cubic log ceiling `hh1ell`) are
`F₀ = Γ - c R̄₂ - g` and `F₁ = F₀ - c(T - 2)(w - 3/4)`, `R̄₂ = 2w - 1/2 + (u - 1)/r_A + r_A - q - E_L
+ ℓ(2/T)`, `T = r_A/q`, `c = 7/96`, `g = 9193/50000`.

## Main API

* `hh1ell`; the central face atoms `hh1cK`, `hh1cL` (`λ`), `hh1cd`, `hh1cv`, `hh1cE`, `hh1cq`, `hh1cy`,
  `hh1cT`, the envelope values `hh1cw`, `hh1cEL`, `hh1cG` and the tests `hh1cR2`, `hh1cF0`, `hh1cF1`.
* `hh1_tau_red`: the duration reduction for an abstract envelope.
* `hh1c_face_red`: `Γ_*(q_c) - (7/96)R*_τ(q_c) - g ≥ min(F₀, F₁)` for `2 ≤ τ ≤ T`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- The cubic log ceiling `ℓ(y) = 2z + (2/3)z³`, `z = (y - 1)/(y + 1)` (`log y ≤ ℓ(y)` on
`(0, 1]`, `hs_log_le_cubic_le_one`). -/
noncomputable def hh1ell (y : ℝ) : ℝ := 2 * ((y - 1) / (y + 1)) + 2 / 3 * ((y - 1) / (y + 1)) ^ 3

/-! ### The central face `q = q_c` -/

/-- `K = x(x + 2) + α²` on the central face (`q_c = α²/K`). -/
noncomputable def hh1cK (x a : ℝ) : ℝ := x * (x + 2) + a ^ 2

/-- The central envelope pairing `E = S(u - 1) + 1/S + (2S - 1)/S²`, `S = 1 + x`. -/
noncomputable def hh1cE (x u : ℝ) : ℝ :=
  (1 + x) * (u - 1) + 1 / (1 + x) + (2 * (1 + x) - 1) / (1 + x) ^ 2

/-- The central envelope norm `v = U(1/S) = 1 - 1/S + 1/S²`. -/
noncomputable def hh1cv (x : ℝ) : ℝ := 1 - 1 / (1 + x) + 1 / (1 + x) ^ 2

/-- `λ = S²/K` on the central face. -/
noncomputable def hh1cL (x a : ℝ) : ℝ := (1 + x) ^ 2 / hh1cK x a

/-- `d = λρD = D/K` on the central face. -/
noncomputable def hh1cd (x a b : ℝ) : ℝ := hsDg x b a / hh1cK x a

/-- The central transported norm `w = λ²v + d²u - dλE`. -/
noncomputable def hh1cw (x a b u : ℝ) : ℝ :=
  hh1cL x a ^ 2 * hh1cv x + hh1cd x a b ^ 2 * u - hh1cd x a b * hh1cL x a * hh1cE x u

/-- The central transported pairing `E_L = 2du - λE`. -/
noncomputable def hh1cEL (x a b u : ℝ) : ℝ := 2 * hh1cd x a b * u - hh1cL x a * hh1cE x u

/-- The central envelope Casimir `Γ_* = (4uv - E²)S⁴/(16X²)`, `X = x(x + 2)`. -/
noncomputable def hh1cG (x u : ℝ) : ℝ :=
  (4 * u * hh1cv x - hh1cE x u ^ 2) * (1 + x) ^ 4 / (16 * (x * (x + 2)) ^ 2)

/-- `q_c = α²/K`. -/
noncomputable def hh1cq (x a : ℝ) : ℝ := a ^ 2 / hh1cK x a

/-- The log argument `y = 2/T = 2q_c/r_A = 2α(α + β)/K`. -/
noncomputable def hh1cy (x a b : ℝ) : ℝ := 2 * a * (a + b) / hh1cK x a

/-- The duration endpoint `T = r_A/q_c = K/(α(α + β))`. -/
noncomputable def hh1cT (x a b : ℝ) : ℝ := hh1cK x a / (a * (a + b))

/-- The central residual `R̄₂ = 2w - 1/2 + (u - 1)/r_A + r_A - q_c - E_L + ℓ(2q_c/r_A)`. -/
noncomputable def hh1cR2 (x a b u : ℝ) : ℝ :=
  2 * hh1cw x a b u - 1 / 2 + (u - 1) * (a + b) / a + a / (a + b) - hh1cq x a -
    hh1cEL x a b u + hh1ell (hh1cy x a b)

/-- The central test `F₀ = Γ_* - (7/96)R̄₂ - 9193/50000`. -/
noncomputable def hh1cF0 (x a b u : ℝ) : ℝ :=
  hh1cG x u - 7 / 96 * hh1cR2 x a b u - 9193 / 50000

/-- The central test `F₁ = F₀ - (7/96)(T - 2)(w - 3/4)`, `T = r_A/q_c`. -/
noncomputable def hh1cF1 (x a b u : ℝ) : ℝ :=
  hh1cF0 x a b u - 7 / 96 * (hh1cT x a b - 2) * (hh1cw x a b u - 3 / 4)

/-! ### The duration reduction -/

/-- **The duration reduction**: for `2 ≤ τ ≤ T`,
`Γ - (7/96)((w - 1)τ + 1/τ + κ + log(τ/T)) - g ≥ min(F₀, F₁)` with
`F₀ = Γ - (7/96)(2w - 3/2 + κ + ℓ(2/T)) - g`, `F₁ = F₀ - (7/96)(T - 2)(w - 3/4)`. -/
theorem hh1_tau_red {G w κ T τ : ℝ} (h2 : 2 ≤ τ) (hτ : τ ≤ T) :
    min (G - 7 / 96 * (2 * w - 3 / 2 + κ + hh1ell (2 / T)) - 9193 / 50000)
        (G - 7 / 96 * (2 * w - 3 / 2 + κ + hh1ell (2 / T)) - 9193 / 50000 -
          7 / 96 * (T - 2) * (w - 3 / 4)) ≤
      G - 7 / 96 * ((w - 1) * τ + 1 / τ + κ + log (τ / T)) - 9193 / 50000 := by
  have hT : 2 ≤ T := h2.trans hτ
  have hd := hs_dur_max (w := w) h2 hτ
  have hl := hs_log_le_cubic_le_one (y := 2 / T) (by positivity)
    (by rw [div_le_one (by linarith)]; exact hT)
  unfold hh1ell
  rcases le_total (2 * w - 3 / 2 + log (2 / T)) (2 * w - 3 / 2 + log (2 / T) + (T - 2) * (w - 3 / 4))
    with h | h
  · rw [max_eq_right h] at hd
    refine (min_le_right _ _).trans ?_
    nlinarith
  · rw [max_eq_left h] at hd
    refine (min_le_left _ _).trans ?_
    nlinarith

/-- **The central face in transport form**: for `x > 0`, `α ≥ 1`,
`Γ_*(q_c) = hh1cG`, `w_*(q_c) = hh1cw`, `E_{L,*}(q_c) = hh1cEL`. -/
theorem hh1c_env {x a b u : ℝ} (hx : 0 < x) (ha : 1 ≤ a) :
    hsGs x a u (hsQc x a) = hh1cG x u ∧ hsWs x b a u (hsQc x a) = hh1cw x a b u ∧
      hsELs x b a u (hsQc x a) = hh1cEL x a b u := by
  have ha0 : 0 < a := by linarith
  have hX : 0 < x * (x + 2) := by positivity
  have hK : 0 < hh1cK x a := by unfold hh1cK; positivity
  have hS : 0 < 1 + x := by linarith
  have hrho : hsRhoOf a (hsQc x a) = 1 / (1 + x) ^ 2 := by
    unfold hsRhoOf hsQc
    have h1 : a ^ 2 - (a ^ 2 - 1) * (a ^ 2 / (x * (x + 2) + a ^ 2)) =
        a ^ 2 * (1 + x) ^ 2 / (x * (x + 2) + a ^ 2) := by
      field_simp; ring
    rw [h1]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · unfold hsGs hh1cG hh1cv hh1cE hsE0 m2U
    rw [hrho]
    have h1 : 1 - 1 / (1 + x) ^ 2 = x * (x + 2) / (1 + x) ^ 2 := by field_simp; ring
    rw [h1]
    field_simp
  · simp only [hsWs, hsA1, hsA2, hsE0, hsQc, hh1cw, hh1cv, hh1cE, hh1cL, hh1cd, hh1cK]
    field_simp
    ring
  · simp only [hsELs, hsA3, hsE0, hsQc, hh1cEL, hh1cE, hh1cL, hh1cd, hh1cK]
    field_simp
    ring

/-- **The central duration reduction**: for `x > 0`,
`α ≥ 1`, `β > 0`, `2 ≤ τ` and `τ q_c ≤ r_A`:
`Γ_*(q_c) - (7/96)R*_τ(q_c) - 9193/50000 ≥ min(F₀, F₁)`. -/
theorem hh1c_face_red {x a b u τ : ℝ} (hx : 0 < x) (ha : 1 ≤ a) (hb : 0 < b) (hτ : 2 ≤ τ)
    (hτT : τ * hsQc x a ≤ hsRA a b) :
    min (hh1cF0 x a b u) (hh1cF1 x a b u) ≤
      hsGs x a u (hsQc x a) - 7 / 96 * hsRs x b a u (hsQc x a) τ - 9193 / 50000 := by
  obtain ⟨hG, hW, hE⟩ := hh1c_env (b := b) (u := u) hx ha
  have ha0 : 0 < a := by linarith
  have hK : 0 < hh1cK x a := by unfold hh1cK; positivity
  have hq : 0 < hsQc x a := by unfold hsQc; positivity
  have hrA : hsRA a b = a / (a + b) := rfl
  set T := hsRA a b / hsQc x a with hTdef
  have hTe : T = hh1cK x a / (a * (a + b)) := by
    rw [hTdef, hrA]; unfold hsQc hh1cK; field_simp
  have hτT' : τ ≤ T := by rw [hTdef, le_div_iff₀ hq]; exact hτT
  have hred := hh1_tau_red (G := hh1cG x u) (w := hh1cw x a b u)
    (κ := (u - 1) / hsRA a b + hsRA a b + 1 - hsQc x a - hh1cEL x a b u) hτ hτT'
  have hlog : log (τ * hsQc x a / hsRA a b) = log (τ / T) := by
    rw [hTdef]; congr 1; field_simp
  have h2T : 2 / T = 2 * a * (a + b) / hh1cK x a := by rw [hTe]; field_simp
  have hR : hsRs x b a u (hsQc x a) τ = (hh1cw x a b u - 1) * τ + 1 / τ +
      ((u - 1) / hsRA a b + hsRA a b + 1 - hsQc x a - hh1cEL x a b u) + log (τ / T) := by
    unfold hsRs hsF
    rw [hW, hE, hlog]; ring
  rw [hR, hG]
  refine le_trans (le_of_eq ?_) hred
  unfold hh1cF1 hh1cF0 hh1cR2 hh1cy hh1cT hh1cq
  rw [h2T, hTe, hrA]
  unfold hsQc
  congr 1 <;> unfold hh1cK <;> field_simp <;> ring

end SmoothedOctagon
