module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic

/-!
# Smaller-short window, lower ratio, terminal faces: the face functions and the duration reduction

Shared definitions for the two terminal face signs of the lower-ratio bound (`lr_central_face`,
`lr_outer_face`). On a face the upper envelope `Γ_*`,
`w_*`, `E_{L,*}` have closed transport forms (`λ`, `d = λρD`, `v = U(ρS)`, `E = E₀ + ρ(2S - 1)`):

* central face `q = q_c` (`ρ = 1/S²`): `λ = S²/K`, `d = D/K`, `K = x(x + 2) + α²`;
* outer face `q = 1/7` (`ρ = 1/(6α² + 1)`): `λ = K/(7α²)`, `d = D/(7α²)`, `K = 6α² + 1`.

The two duration tests (`ss_dur_max` with the cubic log ceiling `lrell`) are
`F₀ = Γ - c R̄₂ - g` and `F₁ = F₀ - c(T - 2)(w - 3/4)`, `R̄₂ = 2w - 1/2 + (u - 1)/r_A + r_A - q - E_L
+ ℓ(2/T)`, `T = r_A/q`, `c = 7/96`, `g = 9193/50000`.

## Main API

* `lrell`; the central face atoms `lrcK`, `lrcL` (`λ`), `lrcd`, `lrcv`, `lrcE`, `lrcq`, `lrcy`,
  `lrcT`, the envelope values `lrcw`, `lrcEL`, `lrcG` and the tests `lrcR2`, `lrcF0`, `lrcF1`.
* `lr_tau_red`: the duration reduction for an abstract envelope.
* `lrc_face_red`: `Γ_*(q_c) - (7/96)R*_τ(q_c) - g ≥ min(F₀, F₁)` for `2 ≤ τ ≤ T`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- The cubic log ceiling `ℓ(y) = 2z + (2/3)z³`, `z = (y - 1)/(y + 1)` (`log y ≤ ℓ(y)` on
`(0, 1]`, `ss_log_le_cubic_le_one`). -/
noncomputable def lrell (y : ℝ) : ℝ := 2 * ((y - 1) / (y + 1)) + 2 / 3 * ((y - 1) / (y + 1)) ^ 3

/-! ### The central face `q = q_c` -/

/-- `K = x(x + 2) + α²` on the central face (`q_c = α²/K`). -/
noncomputable def lrcK (x a : ℝ) : ℝ := x * (x + 2) + a ^ 2

/-- The central envelope pairing `E = S(u - 1) + 1/S + (2S - 1)/S²`, `S = 1 + x`. -/
noncomputable def lrcE (x u : ℝ) : ℝ :=
  (1 + x) * (u - 1) + 1 / (1 + x) + (2 * (1 + x) - 1) / (1 + x) ^ 2

/-- The central envelope norm `v = U(1/S) = 1 - 1/S + 1/S²`. -/
noncomputable def lrcv (x : ℝ) : ℝ := 1 - 1 / (1 + x) + 1 / (1 + x) ^ 2

/-- `λ = S²/K` on the central face. -/
noncomputable def lrcL (x a : ℝ) : ℝ := (1 + x) ^ 2 / lrcK x a

/-- `d = λρD = D/K` on the central face. -/
noncomputable def lrcd (x a b : ℝ) : ℝ := ssDg x b a / lrcK x a

/-- The central transported norm `w = λ²v + d²u - dλE`. -/
noncomputable def lrcw (x a b u : ℝ) : ℝ :=
  lrcL x a ^ 2 * lrcv x + lrcd x a b ^ 2 * u - lrcd x a b * lrcL x a * lrcE x u

/-- The central transported pairing `E_L = 2du - λE`. -/
noncomputable def lrcEL (x a b u : ℝ) : ℝ := 2 * lrcd x a b * u - lrcL x a * lrcE x u

/-- The central envelope Casimir `Γ_* = (4uv - E²)S⁴/(16X²)`, `X = x(x + 2)`. -/
noncomputable def lrcG (x u : ℝ) : ℝ :=
  (4 * u * lrcv x - lrcE x u ^ 2) * (1 + x) ^ 4 / (16 * (x * (x + 2)) ^ 2)

/-- `q_c = α²/K`. -/
noncomputable def lrcq (x a : ℝ) : ℝ := a ^ 2 / lrcK x a

/-- The log argument `y = 2/T = 2q_c/r_A = 2α(α + β)/K`. -/
noncomputable def lrcy (x a b : ℝ) : ℝ := 2 * a * (a + b) / lrcK x a

/-- The duration endpoint `T = r_A/q_c = K/(α(α + β))`. -/
noncomputable def lrcT (x a b : ℝ) : ℝ := lrcK x a / (a * (a + b))

/-- The central residual `R̄₂ = 2w - 1/2 + (u - 1)/r_A + r_A - q_c - E_L + ℓ(2q_c/r_A)`. -/
noncomputable def lrcR2 (x a b u : ℝ) : ℝ :=
  2 * lrcw x a b u - 1 / 2 + (u - 1) * (a + b) / a + a / (a + b) - lrcq x a -
    lrcEL x a b u + lrell (lrcy x a b)

/-- The central test `F₀ = Γ_* - (7/96)R̄₂ - 9193/50000`. -/
noncomputable def lrcF0 (x a b u : ℝ) : ℝ :=
  lrcG x u - 7 / 96 * lrcR2 x a b u - 9193 / 50000

/-- The central test `F₁ = F₀ - (7/96)(T - 2)(w - 3/4)`, `T = r_A/q_c`. -/
noncomputable def lrcF1 (x a b u : ℝ) : ℝ :=
  lrcF0 x a b u - 7 / 96 * (lrcT x a b - 2) * (lrcw x a b u - 3 / 4)

/-! ### The duration reduction -/

/-- **The duration reduction**: for `2 ≤ τ ≤ T`,
`Γ - (7/96)((w - 1)τ + 1/τ + κ + log(τ/T)) - g ≥ min(F₀, F₁)` with
`F₀ = Γ - (7/96)(2w - 3/2 + κ + ℓ(2/T)) - g`, `F₁ = F₀ - (7/96)(T - 2)(w - 3/4)`. -/
theorem lr_tau_red {G w κ T τ : ℝ} (h2 : 2 ≤ τ) (hτ : τ ≤ T) :
    min (G - 7 / 96 * (2 * w - 3 / 2 + κ + lrell (2 / T)) - 9193 / 50000)
        (G - 7 / 96 * (2 * w - 3 / 2 + κ + lrell (2 / T)) - 9193 / 50000 -
          7 / 96 * (T - 2) * (w - 3 / 4)) ≤
      G - 7 / 96 * ((w - 1) * τ + 1 / τ + κ + log (τ / T)) - 9193 / 50000 := by
  have hT : 2 ≤ T := h2.trans hτ
  have hd := ss_dur_max (w := w) h2 hτ
  have hl := ss_log_le_cubic_le_one (y := 2 / T) (by positivity)
    (by rw [div_le_one (by linarith)]; exact hT)
  unfold lrell
  rcases le_total (2 * w - 3 / 2 + log (2 / T)) (2 * w - 3 / 2 + log (2 / T) + (T - 2) * (w - 3 / 4))
    with h | h
  · rw [max_eq_right h] at hd
    refine (min_le_right _ _).trans ?_
    nlinarith
  · rw [max_eq_left h] at hd
    refine (min_le_left _ _).trans ?_
    nlinarith

/-- **The central face in transport form**: for `x > 0`, `α ≥ 1`,
`Γ_*(q_c) = lrcG`, `w_*(q_c) = lrcw`, `E_{L,*}(q_c) = lrcEL`. -/
theorem lrc_env {x a b u : ℝ} (hx : 0 < x) (ha : 1 ≤ a) :
    ssGs x a u (ssQc x a) = lrcG x u ∧ ssWs x b a u (ssQc x a) = lrcw x a b u ∧
      ssELs x b a u (ssQc x a) = lrcEL x a b u := by
  have ha0 : 0 < a := by linarith
  have hX : 0 < x * (x + 2) := by positivity
  have hK : 0 < lrcK x a := by unfold lrcK; positivity
  have hS : 0 < 1 + x := by linarith
  have hrho : ssRhoOf a (ssQc x a) = 1 / (1 + x) ^ 2 := by
    unfold ssRhoOf ssQc
    have h1 : a ^ 2 - (a ^ 2 - 1) * (a ^ 2 / (x * (x + 2) + a ^ 2)) =
        a ^ 2 * (1 + x) ^ 2 / (x * (x + 2) + a ^ 2) := by
      field_simp; ring
    rw [h1]
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · unfold ssGs lrcG lrcv lrcE ssE0 m2U
    rw [hrho]
    have h1 : 1 - 1 / (1 + x) ^ 2 = x * (x + 2) / (1 + x) ^ 2 := by field_simp; ring
    rw [h1]
    field_simp
  · simp only [ssWs, ssA1, ssA2, ssE0, ssQc, lrcw, lrcv, lrcE, lrcL, lrcd, lrcK]
    field_simp
    ring
  · simp only [ssELs, ssA3, ssE0, ssQc, lrcEL, lrcE, lrcL, lrcd, lrcK]
    field_simp
    ring

/-- **The central duration reduction**: for `x > 0`,
`α ≥ 1`, `β > 0`, `2 ≤ τ` and `τ q_c ≤ r_A`:
`Γ_*(q_c) - (7/96)R*_τ(q_c) - 9193/50000 ≥ min(F₀, F₁)`. -/
theorem lrc_face_red {x a b u τ : ℝ} (hx : 0 < x) (ha : 1 ≤ a) (hb : 0 < b) (hτ : 2 ≤ τ)
    (hτT : τ * ssQc x a ≤ ssRA a b) :
    min (lrcF0 x a b u) (lrcF1 x a b u) ≤
      ssGs x a u (ssQc x a) - 7 / 96 * ssRs x b a u (ssQc x a) τ - 9193 / 50000 := by
  obtain ⟨hG, hW, hE⟩ := lrc_env (b := b) (u := u) hx ha
  have ha0 : 0 < a := by linarith
  have hK : 0 < lrcK x a := by unfold lrcK; positivity
  have hq : 0 < ssQc x a := by unfold ssQc; positivity
  have hrA : ssRA a b = a / (a + b) := rfl
  set T := ssRA a b / ssQc x a with hTdef
  have hTe : T = lrcK x a / (a * (a + b)) := by
    rw [hTdef, hrA]; unfold ssQc lrcK; field_simp
  have hτT' : τ ≤ T := by rw [hTdef, le_div_iff₀ hq]; exact hτT
  have hred := lr_tau_red (G := lrcG x u) (w := lrcw x a b u)
    (κ := (u - 1) / ssRA a b + ssRA a b + 1 - ssQc x a - lrcEL x a b u) hτ hτT'
  have hlog : log (τ * ssQc x a / ssRA a b) = log (τ / T) := by
    rw [hTdef]; congr 1; field_simp
  have h2T : 2 / T = 2 * a * (a + b) / lrcK x a := by rw [hTe]; field_simp
  have hR : ssRs x b a u (ssQc x a) τ = (lrcw x a b u - 1) * τ + 1 / τ +
      ((u - 1) / ssRA a b + ssRA a b + 1 - ssQc x a - lrcEL x a b u) + log (τ / T) := by
    unfold ssRs ssF
    rw [hW, hE, hlog]; ring
  rw [hR, hG]
  refine le_trans (le_of_eq ?_) hred
  unfold lrcF1 lrcF0 lrcR2 lrcy lrcT lrcq
  rw [h2T, hTe, hrA]
  unfold ssQc
  congr 1 <;> unfold lrcK <;> field_simp <;> ring

end SmoothedOctagon
