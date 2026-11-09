module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic

/-!
# Smaller-short window: the opposite-turn envelope and the scale form

The comparison machinery shared by the large-ratio to shear bounds: removing the opposite turn `(t, v)` from the outer
root residual, with or without a floor weight `m(w - 3/4)`, and the reparametrization of the
upper envelope by the outer scale `q`.

## Main API

* `ss_B_factor_pos`: the positive factor `B_τ(s) = 1 + τ(λs - d) > 0`.
* `ss_env_weighted`: for any floor weight `m` with `B_{τ+m} > 0` on `[t₀, t]`,
  `R_τ(t, v) + m(w(t, v) - 3/4) ≤ R_τ(t₀, U(t₀)) + m(w(t₀, U(t₀)) - 3/4)`.
* `ss_scale_coords`, `ss_env_scale`: at `ρ = ρ(q)` and `t₀ = ρS` the envelope values are
  `w_* = ssWs`, `E_{L,*} = ssELs`, `R*_τ = ssRs`, `Γ_* = ssGs`.
* `ss_q_le_qc_iff` (`q ≤ q_c ⟺ ρ ≤ r²`), `ss_qc_le_iff` (`q_c ≤ 1/7 ⟺ 6α² ≤ x(x + 2)`).
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- **The positive factor**: for `1 ≤ α ≤ x ≤ β`, `x > 1`, `ρ > 0`, `s ≥ t₀ = ρ(1 + x)` and
`0 ≤ τ ≤ T = r_A/q`, `B_τ(s) = 1 + τ(λs - d) > 0` (minimum at `τ = T`:
`Q + s/ρ - D ≥ x(β - 1) + β(x - α) > 0`). -/
theorem ss_B_factor_pos {x be al rho s τ : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hax : al ≤ x) (hxb : x ≤ be)
    (hρ : 0 < rho) (hs : rho * (1 + x) ≤ s) (hτ : 0 ≤ τ) (hτT : τ * ssQ al rho ≤ ssRA al be) :
    0 < 1 + τ * (ssLam al rho * s - ssLam al rho * rho * ssDg x be al) := by
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hK : 0 < 1 + rho * (al ^ 2 - 1) := by
    have := mul_nonneg hρ.le (by nlinarith : (0 : ℝ) ≤ al ^ 2 - 1); linarith
  have hL : 0 < ssLam al rho := by unfold ssLam; positivity
  have hQ : 0 < al * (al + be) := by positivity
  -- `k = τλρ` satisfies `kQ ≤ 1`
  have hk : τ * ssLam al rho * rho * (al * (al + be)) ≤ 1 := by
    unfold ssQ ssRA at hτT
    rw [le_div_iff₀ (by positivity)] at hτT
    have e : τ * (al ^ 2 * ssLam al rho * rho) * (al + be) =
        al * (τ * ssLam al rho * rho * (al * (al + be))) := by ring
    rw [e] at hτT
    exact le_of_mul_le_mul_left (by linarith) hal0
  have hk0 : 0 ≤ τ * ssLam al rho * rho := by positivity
  have hQSD : 0 < al * (al + be) + (1 + x) - ssDg x be al := by
    unfold ssDg
    linarith [mul_le_mul_of_nonneg_right hxb (by linarith : (0 : ℝ) ≤ 2 * x - al),
      mul_nonneg (by linarith : (0 : ℝ) ≤ x) (by linarith : (0 : ℝ) ≤ x - al),
      mul_pos (by linarith : (0 : ℝ) < x) (by linarith : (0 : ℝ) < x - 1)]
  have hB1 : 1 + τ * ssLam al rho * rho * ((1 + x) - ssDg x be al) ≤
      1 + τ * (ssLam al rho * s - ssLam al rho * rho * ssDg x be al) := by
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg hτ hL.le)
    linarith
  rcases le_or_gt (ssDg x be al) (1 + x) with hD | hD
  · have := mul_nonneg hk0 (sub_nonneg.2 hD)
    linarith
  · have h1 := mul_le_mul_of_nonneg_right hk (sub_nonneg.2 hD.le)
    have h2 : al * (al + be) * (1 + τ * ssLam al rho * rho * ((1 + x) - ssDg x be al)) ≥
        al * (al + be) + (1 + x) - ssDg x be al := by linarith
    have h3 : 0 < 1 + τ * ssLam al rho * rho * ((1 + x) - ssDg x be al) := by
      by_contra hc
      push Not at hc
      linarith [mul_nonpos_of_nonneg_of_nonpos hQ.le hc]
    linarith

/-- `G = R_τ + m(w - 3/4)` in the form `kλ²v + (1 - kd)λE + K`, `k = τ + m`, `d = λρD`. -/
private theorem ss_G_eq (x be al rho u τ m t v : ℝ) :
    ssR x be al rho u τ t v + m * (ssW x be al rho u t v - 3 / 4) =
      (τ + m) * ssLam al rho ^ 2 * v +
      (1 - (τ + m) * (ssLam al rho * rho * ssDg x be al)) * ssLam al rho * ssE x rho u t v +
      ((τ + m) * (ssLam al rho * rho * ssDg x be al) ^ 2 * u - τ + 1 / τ + (u - 1) / ssRA al be +
        ssRA al be + 1 - ssQ al rho - 2 * (ssLam al rho * rho * ssDg x be al) * u +
        log (τ * ssQ al rho / ssRA al be) - 3 / 4 * m) := by
  unfold ssR ssW ssEL; ring

/-- **The weighted opposite-turn envelope**: with `G = R_τ + m(w - 3/4)`,
`∂_v G = (λ/t)B_{τ+m}(t)` and `d/dt G(t, U(t)) = λ(2t - 1)B_{τ+m}(t)/t`; so if `B_{τ+m} > 0` on
`[t₀, t]`, `t₀ = ρ(1 + x) ≤ t ≤ 1/(1 + x)`, and `v ≤ U(t)`, then `G(t, v) ≤ G(t₀, U(t₀))`. -/
theorem ss_env_weighted {x be al rho u τ m t v : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hρ : 0 < rho)
    (ht0 : rho * (1 + x) ≤ t) (htr : t ≤ 1 / (1 + x)) (hv : v ≤ m2U t)
    (hB : ∀ s ∈ Icc (rho * (1 + x)) t,
      0 < 1 + (τ + m) * (ssLam al rho * s - ssLam al rho * rho * ssDg x be al)) :
    ssR x be al rho u τ t v + m * (ssW x be al rho u t v - 3 / 4) ≤
      ssR x be al rho u τ (rho * (1 + x)) (m2U (rho * (1 + x))) +
        m * (ssW x be al rho u (rho * (1 + x)) (m2U (rho * (1 + x))) - 3 / 4) := by
  have hS : 0 < 1 + x := by linarith
  have ht0p : 0 < rho * (1 + x) := by positivity
  have htp : 0 < t := lt_of_lt_of_le ht0p ht0
  have ht2 : t < 1 / 2 := by
    have : 1 / (1 + x) < 1 / 2 := by rw [div_lt_div_iff₀ hS (by norm_num)]; linarith
    linarith
  have hK : 0 < 1 + rho * (al ^ 2 - 1) := by
    have := mul_nonneg hρ.le (by nlinarith : (0 : ℝ) ≤ al ^ 2 - 1); linarith
  have hL : 0 < ssLam al rho := by unfold ssLam; positivity
  rw [ss_G_eq, ss_G_eq]
  generalize ssLam al rho = L at hL hB ⊢
  generalize L * rho * ssDg x be al = d at hB ⊢
  generalize τ + m = k at hB ⊢
  -- the `v`-step: `∂_v G = (λ/t)B(t) > 0`
  have step1 : k * L ^ 2 * v + (1 - k * d) * L * ssE x rho u t v ≤
      k * L ^ 2 * m2U t + (1 - k * d) * L * ssE x rho u t (m2U t) := by
    have e : (k * L ^ 2 * m2U t + (1 - k * d) * L * ssE x rho u t (m2U t)) -
        (k * L ^ 2 * v + (1 - k * d) * L * ssE x rho u t v) =
        L * (m2U t - v) * (1 + k * (L * t - d)) / t := by
      unfold ssE; field_simp; ring
    have hBt := hB t ⟨ht0, le_rfl⟩
    have : 0 ≤ L * (m2U t - v) * (1 + k * (L * t - d)) / t := by
      have : 0 ≤ m2U t - v := by linarith
      positivity
    linarith
  -- the `t`-step along `v = U(t)`: derivative `λ(2s - 1)B(s)/s ≤ 0`
  set c := (u - 1) * (1 + x) + 1 / (1 + x) - rho + log (rho * (1 + x)) with hc
  have hEU : ∀ s, 0 < s → ssE x rho u s (m2U s) = c + 2 * s - log s := by
    intro s hs
    unfold ssE m2U
    rw [Real.log_div (by positivity) hs.ne', hc]
    field_simp
    ring
  have hψ : ∀ s, 0 < s → HasDerivAt
      (fun s => -(k * L ^ 2 * (1 - s + s ^ 2) + (1 - k * d) * L * (c + 2 * s - log s)))
      (-(L * (2 * s - 1) * (1 + k * (L * s - d)) / s)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => 1 - s + s ^ 2) (-1 + 2 * s) s := by
      have := ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id' s)).add ((hasDerivAt_id' s).pow 2)
      refine this.congr_deriv ?_
      push_cast; ring
    have h2 : HasDerivAt (fun s : ℝ => c + 2 * s - log s) (2 - 1 / s) s := by
      have := (((hasDerivAt_id' s).const_mul (2 : ℝ)).const_add c).sub (Real.hasDerivAt_log hs.ne')
      refine this.congr_deriv ?_
      field_simp
    have := ((h1.const_mul (k * L ^ 2)).add (h2.const_mul ((1 - k * d) * L))).neg
    refine this.congr_deriv ?_
    field_simp
    ring
  have hmono := ss_le_of_deriv
    (f := fun s => -(k * L ^ 2 * (1 - s + s ^ 2) + (1 - k * d) * L * (c + 2 * s - log s)))
    (f' := fun s => -(L * (2 * s - 1) * (1 + k * (L * s - d)) / s)) ht0
    (fun s hs => hψ s (lt_of_lt_of_le ht0p hs.1)) (fun s hs => by
      have hs0 : 0 < s := lt_trans ht0p hs.1
      have hBs := hB s ⟨hs.1.le, hs.2.le⟩
      have h2s : 0 < 1 - 2 * s := by linarith [hs.2]
      have : 0 ≤ L * (1 - 2 * s) * (1 + k * (L * s - d)) / s := by positivity
      have e : -(L * (2 * s - 1) * (1 + k * (L * s - d)) / s) =
          L * (1 - 2 * s) * (1 + k * (L * s - d)) / s := by ring
      rw [e]; exact this)
  rw [hEU _ ht0p]
  rw [hEU t htp] at step1
  unfold m2U at step1 ⊢
  linarith

/-- **The scale coordinates**: for `α ≥ 1`, `0 < ρ`,
`q = α²λρ` gives back `ρ = q/(α² - (α² - 1)q)`, `λ = 1 - εq` and `d = λρD = qΔ`
(`ε = 1 - α⁻²`, `Δ = D/α²`). -/
theorem ss_scale_coords {x be al rho : ℝ} (hal : 1 ≤ al) (hρ : 0 < rho) :
    ssRhoOf al (ssQ al rho) = rho ∧ ssLam al rho = 1 - (1 - 1 / al ^ 2) * ssQ al rho ∧
      ssLam al rho * rho * ssDg x be al = ssQ al rho * (ssDg x be al / al ^ 2) := by
  have hal0 : 0 < al := by linarith
  have hK : 0 < 1 + rho * (al ^ 2 - 1) := by
    have := mul_nonneg hρ.le (by nlinarith : (0 : ℝ) ≤ al ^ 2 - 1); linarith
  have hL : 0 < ssLam al rho := by unfold ssLam; positivity
  have hLK : ssLam al rho * (1 + rho * (al ^ 2 - 1)) = 1 := by unfold ssLam; field_simp
  have hinv : 1 / al ^ 2 * al ^ 2 = 1 := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · unfold ssRhoOf ssQ
    have hden : al ^ 2 - (al ^ 2 - 1) * (al ^ 2 * ssLam al rho * rho) = al ^ 2 * ssLam al rho := by
      linear_combination (-(al ^ 2)) * hLK
    rw [hden, div_eq_iff (by positivity)]
    ring
  · unfold ssQ
    linear_combination hLK - ssLam al rho * rho * hinv
  · unfold ssQ
    linear_combination (-(ssLam al rho * rho * ssDg x be al)) * hinv

/-- **The upper envelope in the scale variable**: for `x > 0`, `α ≥ 1`,
`0 < q < 1`, with `ρ = ρ(q)` and `t₀ = ρ(1 + x)`: `w(t₀, U(t₀)) = 1 - qA₁ + q²A₂`,
`E_L(t₀, U(t₀)) = -E₀ + qA₃`, `R_τ(t₀, U(t₀)) = R*_τ(q)` and `Γ(t₀, U(t₀)) = Γ_*(q)`. -/
theorem ss_env_scale {x be al u q τ : ℝ} (hx : 0 < x) (hal : 1 ≤ al) (hq : 0 < q) (hq1 : q < 1) :
    ssW x be al (ssRhoOf al q) u (ssRhoOf al q * (1 + x)) (m2U (ssRhoOf al q * (1 + x))) =
        ssWs x be al u q ∧
      ssEL x be al (ssRhoOf al q) u (ssRhoOf al q * (1 + x)) (m2U (ssRhoOf al q * (1 + x))) =
        ssELs x be al u q ∧
      ssR x be al (ssRhoOf al q) u τ (ssRhoOf al q * (1 + x)) (m2U (ssRhoOf al q * (1 + x))) =
        ssRs x be al u q τ ∧
      ssGam (ssRhoOf al q) u (m2U (ssRhoOf al q * (1 + x)))
          (ssE x (ssRhoOf al q) u (ssRhoOf al q * (1 + x)) (m2U (ssRhoOf al q * (1 + x)))) =
        ssGs x al u q := by
  have hal0 : 0 < al := by linarith
  have ha2 : 0 < al ^ 2 := by positivity
  have hden : 0 < al ^ 2 - (al ^ 2 - 1) * q := by nlinarith
  have hρ : 0 < ssRhoOf al q := by unfold ssRhoOf; positivity
  have hinv : 1 / al ^ 2 * al ^ 2 = 1 := by field_simp
  -- `λ(ρ(q)) (1 + ρ(q)(α² - 1)) = 1` and `ρ(q)(α² - (α² - 1)q) = q`
  have hρq : ssRhoOf al q * (al ^ 2 - (al ^ 2 - 1) * q) = q := by
    unfold ssRhoOf; exact div_mul_cancel₀ _ hden.ne'
  have hK : 0 < 1 + ssRhoOf al q * (al ^ 2 - 1) := by
    have := mul_nonneg hρ.le (by nlinarith : (0 : ℝ) ≤ al ^ 2 - 1); linarith
  have hLK : ssLam al (ssRhoOf al q) * (1 + ssRhoOf al q * (al ^ 2 - 1)) = 1 := by
    unfold ssLam; field_simp
  -- `λρ = q/α²` and `λ = 1 - εq`
  have hLρ : ssLam al (ssRhoOf al q) * ssRhoOf al q = q * (1 / al ^ 2) := by
    -- `(1 + ρ(α² - 1)) α² = α²(α² - (α² - 1)q + (α² - 1)q)/(...)`: use `ρ D_q = q`
    have hKq : (1 + ssRhoOf al q * (al ^ 2 - 1)) * (al ^ 2 - (al ^ 2 - 1) * q) = al ^ 2 := by
      linear_combination (al ^ 2 - 1) * hρq
    have h1 : ssLam al (ssRhoOf al q) * al ^ 2 = al ^ 2 - (al ^ 2 - 1) * q := by
      linear_combination (al ^ 2 - (al ^ 2 - 1) * q) * hLK -
        ssLam al (ssRhoOf al q) * hKq
    linear_combination (1 / al ^ 2) * ssRhoOf al q * h1 + (1 / al ^ 2) * hρq -
      ssLam al (ssRhoOf al q) * ssRhoOf al q * hinv
  have hL : ssLam al (ssRhoOf al q) = 1 - (1 - 1 / al ^ 2) * q := by
    linear_combination hLK - (al ^ 2 - 1) * hLρ - q * hinv
  have hQ : ssQ al (ssRhoOf al q) = q := by
    unfold ssQ
    linear_combination al ^ 2 * hLρ + q * hinv
  have ht0 : 0 < ssRhoOf al q * (1 + x) := by positivity
  have hE : ssE x (ssRhoOf al q) u (ssRhoOf al q * (1 + x)) (m2U (ssRhoOf al q * (1 + x))) =
      ssE0 x u + ssRhoOf al q * (2 * (1 + x) - 1) := by
    unfold ssE ssE0 m2U
    rw [div_self ht0.ne', Real.log_one]
    field_simp
    ring
  have hW : ssW x be al (ssRhoOf al q) u (ssRhoOf al q * (1 + x)) (m2U (ssRhoOf al q * (1 + x))) =
      ssWs x be al u q := by
    unfold ssW ssWs ssA1 ssA2
    rw [hE]
    unfold m2U
    have e : ssLam al (ssRhoOf al q) ^ 2 *
          (1 - ssRhoOf al q * (1 + x) + (ssRhoOf al q * (1 + x)) ^ 2) +
        (ssLam al (ssRhoOf al q) * ssRhoOf al q * ssDg x be al) ^ 2 * u -
        ssLam al (ssRhoOf al q) * ssRhoOf al q * ssDg x be al * ssLam al (ssRhoOf al q) *
          (ssE0 x u + ssRhoOf al q * (2 * (1 + x) - 1)) =
        ssLam al (ssRhoOf al q) ^ 2 -
          ssLam al (ssRhoOf al q) * (ssLam al (ssRhoOf al q) * ssRhoOf al q) * (1 + x) +
          (ssLam al (ssRhoOf al q) * ssRhoOf al q) ^ 2 * (1 + x) ^ 2 +
          (ssLam al (ssRhoOf al q) * ssRhoOf al q) ^ 2 * ssDg x be al ^ 2 * u -
          (ssLam al (ssRhoOf al q) * ssRhoOf al q) * ssDg x be al * ssLam al (ssRhoOf al q) *
            ssE0 x u -
          (ssLam al (ssRhoOf al q) * ssRhoOf al q) ^ 2 * ssDg x be al * (2 * (1 + x) - 1) := by
      ring
    rw [e, hLρ, hL]
    ring
  have hEL : ssEL x be al (ssRhoOf al q) u (ssRhoOf al q * (1 + x)) (m2U (ssRhoOf al q * (1 + x))) =
      ssELs x be al u q := by
    unfold ssEL ssELs ssA3
    rw [hE]
    have e : 2 * (ssLam al (ssRhoOf al q) * ssRhoOf al q * ssDg x be al) * u -
        ssLam al (ssRhoOf al q) * (ssE0 x u + ssRhoOf al q * (2 * (1 + x) - 1)) =
        2 * (ssLam al (ssRhoOf al q) * ssRhoOf al q) * ssDg x be al * u -
          ssLam al (ssRhoOf al q) * ssE0 x u -
          (ssLam al (ssRhoOf al q) * ssRhoOf al q) * (2 * (1 + x) - 1) := by ring
    rw [e, hLρ, hL]
    ring
  refine ⟨hW, hEL, ?_, ?_⟩
  · unfold ssR ssRs ssF
    rw [hW, hEL, hQ]
    ring
  · unfold ssGs
    rw [hE]
    rfl

/-- **The floor-weighted positive factor**: for `x > 5/3`, `1 ≤ α ≤ x ≤ β`, `ρ > 0`, `s ≥ ρ(1 + x)`,
`T = r_A/q ≥ 2` and `0 ≤ z ≤ T + 1/2`: `B_z(s) = 1 + z(λs - d) > 0`
(`4Q - 5(D - S) = β(10x - 6α) - α² - 5x ≥ x(3x - 5) > 0`). -/
theorem ss_B_pos_weighted {x be al rho s z : ℝ} (hx : 5 / 3 < x) (hal : 1 ≤ al) (hax : al ≤ x)
    (hxb : x ≤ be) (hρ : 0 < rho) (hs : rho * (1 + x) ≤ s) (hz : 0 ≤ z)
    (hT : 2 * ssQ al rho ≤ ssRA al be) (hzT : z * ssQ al rho ≤ ssRA al be + ssQ al rho / 2) :
    0 < 1 + z * (ssLam al rho * s - ssLam al rho * rho * ssDg x be al) := by
  have hal0 : 0 < al := by linarith
  have hbe0 : 0 < be := by linarith
  have hK : 0 < 1 + rho * (al ^ 2 - 1) := by
    have := mul_nonneg hρ.le (by nlinarith : (0 : ℝ) ≤ al ^ 2 - 1); linarith
  have hL : 0 < ssLam al rho := by unfold ssLam; positivity
  have hQ : 0 < al * (al + be) := by positivity
  have hP0 : 0 ≤ ssLam al rho * rho * (al * (al + be)) := by positivity
  have hP : 2 * (ssLam al rho * rho * (al * (al + be))) ≤ 1 := by
    unfold ssQ ssRA at hT
    rw [le_div_iff₀ (by positivity)] at hT
    have e : 2 * (al ^ 2 * ssLam al rho * rho) * (al + be) =
        al * (2 * (ssLam al rho * rho * (al * (al + be)))) := by ring
    rw [e] at hT
    exact le_of_mul_le_mul_left (by linarith) hal0
  have hk : z * ssLam al rho * rho * (al * (al + be)) ≤ 5 / 4 := by
    unfold ssQ ssRA at hzT
    have e : al / (al + be) + al ^ 2 * ssLam al rho * rho / 2 =
        (al + al * (ssLam al rho * rho * (al * (al + be))) / 2) / (al + be) := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)] at hzT
    have e2 : z * (al ^ 2 * ssLam al rho * rho) * (al + be) =
        al * (z * ssLam al rho * rho * (al * (al + be))) := by ring
    rw [e2] at hzT
    have : z * ssLam al rho * rho * (al * (al + be)) ≤
        1 + ssLam al rho * rho * (al * (al + be)) / 2 :=
      le_of_mul_le_mul_left (by linarith) hal0
    linarith
  have hk0 : 0 ≤ z * ssLam al rho * rho := by positivity
  have hB1 : 1 + z * ssLam al rho * rho * ((1 + x) - ssDg x be al) ≤
      1 + z * (ssLam al rho * s - ssLam al rho * rho * ssDg x be al) := by
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg hz hL.le)
    linarith
  rcases le_or_gt (ssDg x be al) (1 + x) with hD | hD
  · have := mul_nonneg hk0 (sub_nonneg.2 hD)
    linarith
  · have h1 := mul_le_mul_of_nonneg_right hk (sub_nonneg.2 hD.le)
    have h45 : 0 < 4 * (al * (al + be)) - 5 * (ssDg x be al - (1 + x)) := by
      unfold ssDg
      have e : 4 * (al * (al + be)) -
          5 * (al ^ 2 + 2 * al * be + 1 + 2 * x - 2 * be * x - (1 + x)) =
          be * (10 * x - 6 * al) - al ^ 2 - 5 * x := by ring
      rw [e]
      -- `β(10x - 6α) - α² - 5x ≥ x(10x - 6α) - α² - 5x ≥ x(3x - 5)`
      linarith [mul_le_mul_of_nonneg_right hxb (by linarith : (0 : ℝ) ≤ 10 * x - 6 * al),
        mul_nonneg (by linarith : (0 : ℝ) ≤ x - al) (by linarith : (0 : ℝ) ≤ 7 * x + al),
        mul_pos (by linarith : (0 : ℝ) < x) (by linarith : (0 : ℝ) < 3 * x - 5)]
    have h2 : 4 * (al * (al + be)) * (1 + z * ssLam al rho * rho * ((1 + x) - ssDg x be al)) ≥
        4 * (al * (al + be)) - 5 * (ssDg x be al - (1 + x)) := by linarith
    have h3 : 0 < 1 + z * ssLam al rho * rho * ((1 + x) - ssDg x be al) := by
      by_contra hc
      push Not at hc
      linarith [mul_nonpos_of_nonneg_of_nonpos hQ.le hc]
    linarith

/-- **`D < Q` and `D < 3α²`**: for `x ≥ 2`, `1 ≤ α ≤ x`, `β ≥ b₀ = x(9x + 8α)/(9x + 8)`:
`D < α(α + β)` and `D < 3α²`. -/
theorem ss_D_lt_Q {x be al : ℝ} (hx : 2 ≤ x) (hal : 1 ≤ al) (hax : al ≤ x)
    (hb : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be) :
    ssDg x be al < al * (al + be) ∧ ssDg x be al < 3 * al ^ 2 := by
  have h98 : 0 < 9 * x + 8 := by linarith
  rw [div_le_iff₀ h98] at hb
  unfold ssDg
  constructor
  · have h1 := mul_le_mul_of_nonneg_right hb (by linarith : (0 : ℝ) ≤ 2 * x - al)
    have h2 : 0 < x * (9 * x + 8 * al) * (2 * x - al) - (1 + 2 * x) * (9 * x + 8) := by
      linarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hal) (sub_nonneg.2 hax))
          (by linarith : (0 : ℝ) ≤ x),
        mul_nonneg (sub_nonneg.2 hax) (by positivity : (0 : ℝ) ≤ x ^ 2 + 8 * x),
        mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2)
          (by positivity : (0 : ℝ) ≤ 17 * x ^ 2 + 16 * x + 7)]
    have h3 : 0 < (be * (2 * x - al) - 1 - 2 * x) * (9 * x + 8) := by linarith
    have h4 : 0 < be * (2 * x - al) - 1 - 2 * x := by
      by_contra hc; push Not at hc
      linarith [mul_nonpos_of_nonpos_of_nonneg hc h98.le]
    linarith
  · have h1 := mul_le_mul_of_nonneg_right hb (by linarith : (0 : ℝ) ≤ x - al)
    have h2 : 0 < (9 * x + 8) * (2 * al ^ 2 - 1 - 2 * x) +
        2 * (x * (9 * x + 8 * al)) * (x - al) := by
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x) (sq_nonneg (al - x / 2)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2)
          (by positivity : (0 : ℝ) ≤ 35 / 2 * x ^ 2 + 17 * x + 9),
        mul_nonneg (by linarith : (0 : ℝ) ≤ al - 1) (by linarith : (0 : ℝ) ≤ al + 1)]
    have h3 : 0 < (2 * al ^ 2 - 2 * al * be - 1 - 2 * x + 2 * be * x) * (9 * x + 8) := by linarith
    have h4 : 0 < 2 * al ^ 2 - 2 * al * be - 1 - 2 * x + 2 * be * x := by
      by_contra hc; push Not at hc
      linarith [mul_nonpos_of_nonpos_of_nonneg hc h98.le]
    linarith

/-- **`A₂ > 0`**: for `2 ≤ x ≤ 12/5`, `α ≥ 1`, `3/4 ≤ u ≤ 31/40` and every `β`, `A₂ > 0`.
Proof: `4uA₂ = (2uΔ + K)² + 4u𝒜 - K²` with the exact `K = εE₀ - (2S - 1)a`, `a = α⁻²`, and
`3𝒜 - K² = (1 - a)²(3 - E₀²) + (1 - a)a(3S + 2E₀(2S - 1)) + a²(3S² - (2S - 1)²) > 0` from
`-189/340 ≤ E₀ ≤ -41/120`. -/
theorem ss_A2_pos {x be al u : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 12 / 5) (hal : 1 ≤ al) (hu : 3 / 4 ≤ u)
    (hu' : u ≤ 31 / 40) : 0 < ssA2 x be al u := by
  have hal0 : 0 < al := by linarith
  have ha0 : 0 < 1 / al ^ 2 := by positivity
  have ha1 : 1 / al ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [mul_le_mul hal hal zero_le_one hal0.le]
  have hS : 0 < 1 + x := by linarith
  have hE0lo : -(189 / 340) ≤ ssE0 x u := by
    unfold ssE0
    have h1 : 5 / 17 ≤ 1 / (1 + x) := by rw [div_le_div_iff₀ (by norm_num) hS]; linarith
    linarith [mul_nonneg_of_nonpos_of_nonpos (by linarith : 1 + x - 17 / 5 ≤ 0)
      (by linarith : u - 1 ≤ 0)]
  have hE0hi : ssE0 x u ≤ -(41 / 120) := by
    unfold ssE0
    have h1 : 1 / (1 + x) ≤ 1 / 3 := by rw [div_le_div_iff₀ hS (by norm_num)]; linarith
    linarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : (0 : ℝ) ≤ 1 + x - 3)
      (by linarith : u - 1 ≤ 0)]
  have e : ssA2 x be al u = (1 - 1 / al ^ 2) ^ 2 + (1 - 1 / al ^ 2) * ((1 + x) * (1 / al ^ 2)) +
      ((1 + x) * (1 / al ^ 2)) ^ 2 + (ssDg x be al / al ^ 2) ^ 2 * u +
      (ssDg x be al / al ^ 2) *
        ((1 - 1 / al ^ 2) * ssE0 x u - (2 * (1 + x) - 1) * (1 / al ^ 2)) := by
    unfold ssA2; ring
  rw [e]
  generalize 1 / al ^ 2 = a at ha0 ha1 ⊢
  generalize ssDg x be al / al ^ 2 = Δ
  generalize ssE0 x u = E0 at hE0lo hE0hi ⊢
  set S := 1 + x with hSdef
  have hS3 : 3 ≤ S := by linarith
  have hS4 : S ≤ 17 / 5 := by linarith
  have hA : 0 ≤ (1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 := by
    have : 0 ≤ 1 - a := by linarith
    positivity
  have h3 : 0 < 3 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2) -
      ((1 - a) * E0 - (2 * S - 1) * a) ^ 2 := by
    have e3 : 3 * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2) -
        ((1 - a) * E0 - (2 * S - 1) * a) ^ 2 = (1 - a) ^ 2 * (3 - E0 ^ 2) +
        (1 - a) * a * (3 * S + 2 * E0 * (2 * S - 1)) + a ^ 2 * (3 * S ^ 2 - (2 * S - 1) ^ 2) := by
      ring
    rw [e3]
    have c1 : 0 < 3 - E0 ^ 2 := by
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 189 / 340 - E0)
        (by linarith : (0 : ℝ) ≤ E0 + 189 / 340)]
    have c2 : 0 < 3 * S + 2 * E0 * (2 * S - 1) := by
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ E0 + 189 / 340)
        (by linarith : (0 : ℝ) ≤ 2 * S - 1)]
    have c3 : 0 < 3 * S ^ 2 - (2 * S - 1) ^ 2 := by
      linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ S - 3) (by linarith : (0 : ℝ) ≤ 17 / 5 - S)]
    have k1 : 0 ≤ (1 - a) ^ 2 * (3 - E0 ^ 2) := mul_nonneg (sq_nonneg _) c1.le
    have k2 : 0 ≤ (1 - a) * a * (3 * S + 2 * E0 * (2 * S - 1)) :=
      mul_nonneg (mul_nonneg (by linarith) ha0.le) c2.le
    have k3 : 0 < a ^ 2 * (3 * S ^ 2 - (2 * S - 1) ^ 2) := mul_pos (pow_pos ha0 2) c3
    linarith
  have e4 : 4 * u * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 + Δ ^ 2 * u +
      Δ * ((1 - a) * E0 - (2 * S - 1) * a)) = (2 * u * Δ + ((1 - a) * E0 - (2 * S - 1) * a)) ^ 2 +
      4 * u * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2) -
      ((1 - a) * E0 - (2 * S - 1) * a) ^ 2 := by ring
  have h5 : 0 < 4 * u * ((1 - a) ^ 2 + (1 - a) * (S * a) + (S * a) ^ 2 + Δ ^ 2 * u +
      Δ * ((1 - a) * E0 - (2 * S - 1) * a)) := by
    rw [e4]
    linarith [sq_nonneg (2 * u * Δ + ((1 - a) * E0 - (2 * S - 1) * a)),
      mul_le_mul_of_nonneg_right hu hA]
  have hu0 : 0 < 4 * u := by linarith
  exact pos_of_mul_pos_right h5 hu0.le

/-- **Convex endpoint alternative**: if `m ≥ 0` and `A₂ ≥ 0`, the scale polynomial `Φ` is convex, so
on `[0, q_m]`, `Φ(q) ≤ max{Φ(0), Φ(q_m)}`. -/
theorem ss_phi_convex_max {x be al u p m qm q : ℝ} (hm : 0 ≤ m) (hA : 0 ≤ ssA2 x be al u)
    (hq : 0 ≤ q) (hqq : q ≤ qm) :
    ssPhi x be al u p m q ≤ max (ssPhi x be al u p m 0) (ssPhi x be al u p m qm) := by
  have key : qm * ssPhi x be al u p m q ≤
      (qm - q) * ssPhi x be al u p m 0 + q * ssPhi x be al u p m qm := by
    have e : (qm - q) * ssPhi x be al u p m 0 + q * ssPhi x be al u p m qm -
        qm * ssPhi x be al u p m q = m * ssA2 x be al u * (q * qm * (qm - q)) := by
      unfold ssPhi; ring
    have : 0 ≤ m * ssA2 x be al u * (q * qm * (qm - q)) :=
      mul_nonneg (mul_nonneg hm hA) (mul_nonneg (mul_nonneg hq (hq.trans hqq)) (by linarith))
    linarith
  rcases eq_or_lt_of_le (hq.trans hqq) with h0 | hpos
  · have : q = 0 := by linarith
    subst this
    exact le_max_left _ _
  · have hmax1 := le_max_left (ssPhi x be al u p m 0) (ssPhi x be al u p m qm)
    have hmax2 := le_max_right (ssPhi x be al u p m 0) (ssPhi x be al u p m qm)
    have h1 : (qm - q) * ssPhi x be al u p m 0 + q * ssPhi x be al u p m qm ≤
        qm * max (ssPhi x be al u p m 0) (ssPhi x be al u p m qm) := by
      have := mul_le_mul_of_nonneg_left hmax1 (by linarith : (0 : ℝ) ≤ qm - q)
      have := mul_le_mul_of_nonneg_left hmax2 hq
      nlinarith
    exact le_of_mul_le_mul_left (key.trans h1) hpos

/-- **The weighted envelope at fixed `p`**: for `p, q > 0`,
`ssF x be al u q (p/q) (log(p/r_A)) m = Φ(q) = C(p) + m/4 + q(L(p) - mA₁) + mq²A₂`. -/
theorem ss_phi_eq {x be al u p q m : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ssF x be al u q (p / q) (log (p / ssRA al be)) m = ssPhi x be al u p m q := by
  unfold ssF ssPhi ssWs ssELs ssCp ssLp
  field_simp
  ring

/-- **Centre stationarity under the opposite-turn envelope**: for `x > 1`, `ρ > 0`,
`ρ(1 + x) ≤ t ≤ 1/(1 + x)`, `v ≤ U(t)`: `E(t, v) ≤ E_* = S(u - 1) + 1/S + ρ(2S - 1)`
(`log(t/t₀) ≥ 2(t - t₀)` for `t ≤ 1/2`). -/
theorem ss_E_le_env {x rho u t v : ℝ} (hx : 1 < x) (hρ : 0 < rho) (ht0 : rho * (1 + x) ≤ t)
    (htr : t ≤ 1 / (1 + x)) (hv : v ≤ m2U t) :
    ssE x rho u t v ≤ ssE0 x u + rho * (2 * (1 + x) - 1) := by
  have hS : 0 < 1 + x := by linarith
  have ht0p : 0 < rho * (1 + x) := by positivity
  have htp : 0 < t := lt_of_lt_of_le ht0p ht0
  have ht2 : t ≤ 1 / 2 := by
    have : 1 / (1 + x) ≤ 1 / 2 := by rw [div_le_div_iff₀ hS (by norm_num)]; linarith
    linarith
  unfold ssE ssE0
  have h1 : (v - 1) / t ≤ (m2U t - 1) / t := div_le_div_of_nonneg_right (by linarith) htp.le
  have h2 : (m2U t - 1) / t = t - 1 := by unfold m2U; field_simp; ring
  have h3 := Real.log_le_sub_one_of_pos (show 0 < rho * (1 + x) / t by positivity)
  have h4 : rho * (1 + x) / t - 1 ≤ 2 * (rho * (1 + x) - t) := by
    rw [div_sub_one htp.ne', div_le_iff₀ htp]
    linarith [mul_nonneg (sub_nonneg.2 ht0) (by linarith : (0 : ℝ) ≤ 1 - 2 * t)]
  linarith

/-- **The central cap in the scale variable**: for `α ≥ 1`,
`x > 0`, `0 < ρ`, `q = α²λρ ≤ q_c ⟺ ρ ≤ 1/(1 + x)²`. -/
theorem ss_q_le_qc_iff {x al rho : ℝ} (hx : 0 < x) (hal : 1 ≤ al) (hρ : 0 < rho) :
    ssQ al rho ≤ ssQc x al ↔ rho ≤ 1 / (1 + x) ^ 2 := by
  have hal0 : 0 < al := by linarith
  have ha2 : 0 < al ^ 2 := by positivity
  have hK : 0 < 1 + rho * (al ^ 2 - 1) := by
    have := mul_nonneg hρ.le (by nlinarith : (0 : ℝ) ≤ al ^ 2 - 1); linarith
  have hP : 0 < x * (x + 2) + al ^ 2 := by positivity
  have e1 : ssQ al rho = al ^ 2 * rho / (1 + rho * (al ^ 2 - 1)) := by
    unfold ssQ ssLam; field_simp
  rw [e1, ssQc, div_le_div_iff₀ hK hP, le_div_iff₀ (by positivity)]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    linarith [mul_pos ha2 (sub_pos.2 hc)]
  · intro h
    linarith [mul_le_mul_of_nonneg_left h ha2.le]

/-- The face condition `q_c ≤ 1/7 ⟺ 6α² ≤ x(x + 2)` for `x > 0`. -/
theorem ss_qc_le_iff {x al : ℝ} (hx : 0 < x) : ssQc x al ≤ 1 / 7 ↔ 6 * al ^ 2 ≤ x * (x + 2) := by
  have hP : 0 < x * (x + 2) + al ^ 2 := by positivity
  unfold ssQc
  rw [div_le_div_iff₀ hP (by norm_num)]
  constructor <;> intro h <;> linarith

end SmoothedOctagon
