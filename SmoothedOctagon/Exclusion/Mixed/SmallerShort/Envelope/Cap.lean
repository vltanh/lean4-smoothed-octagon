module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.LogSecant
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Centre

/-!
# Smaller-short window: the corrected envelope cap

Two-segment monotonicity of `Γ - cR_τ` along the opposite-turn path
`(t, v) → (t, U(t)) → (t₀, U(t₀))`, `t₀ = ρ(1 + x)`, under a bound `c` on the derivative ratio.

## Main API

* `env_root_cap`: the retained root bound `E_L ≤ 3q - J_A`, `J_A = (U(r_A) - u)/r_A`.

* `env_cap`: if at every `s ∈ [t₀, t]` and every pairing `E' ≥ E(t, v)` the derivative ratio
  satisfies `λ(2us - E') ≤ 8cλ²(1 - ρ)²B_τ(s)`, then
  `Γ(t₀, U(t₀)) - cR_τ(t₀, U(t₀)) ≤ Γ(t, v) - cR_τ(t, v)`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- **The retained incoming deficit at the outer root** (`ss_E_le_three` with the incoming norm
at its ceiling `U(r_A)`). -/
theorem env_root_cap {rA τ q u w EL : ℝ} (hrA : 0 < rA) (hrA2 : rA ≤ 1 / 2) (hτ : 2 ≤ τ)
    (hq : 0 < q) (hτq : τ * q ≤ rA) (hw : w ≤ m2U (1 / τ))
    (hEL : EL = (w - 1) * τ + 1 / τ + (u - 1) / rA + rA + 1 - q + log (τ * q / rA)) :
    EL ≤ 3 * q - (m2U rA - u) / rA := by
  have hτ0 : 0 < τ := by linarith
  have h := ss_E_le_three (x := rA) (y := 1 / τ) (ρ := q) (ux := m2U rA) (uy := w)
    (E := EL + (m2U rA - u) / rA) hrA hrA2 (by positivity)
    (by rw [div_le_div_iff₀ hτ0 (by norm_num)]; linarith) hq
    (by rw [mul_one_div, le_div_iff₀ hτ0]; linarith) (by unfold m2U; linarith)
    (by unfold m2U at hw; linarith) (by
      rw [hEL]
      have e1 : q / (rA * (1 / τ)) = τ * q / rA := by field_simp
      have e2 : (1 - w) / (1 / τ) = (1 - w) * τ := by field_simp
      rw [e1, e2]; field_simp; ring)
  linarith

/-- The derivative of the centre pairing along `v = U(s)`: `d/ds E(s, U(s)) = 2 - 1/s`. -/
private theorem env_Eb_deriv {x rho u s : ℝ} (hx : 0 < 1 + x) (hρ : 0 < rho) (hs : 0 < s) :
    HasDerivAt (fun s => ssE x rho u s (m2U s)) (2 - 1 / s) s := by
  have h1 : HasDerivAt (fun s : ℝ => (1 - s + s ^ 2 - 1) / s) 1 s := by
    have := ((((hasDerivAt_id' s).const_sub 1).add ((hasDerivAt_id' s).pow 2)).sub_const 1).div
      (hasDerivAt_id' s) hs.ne'
    convert this using 1
    simp only [Pi.add_apply, Pi.pow_apply]
    field_simp
    ring
  have h2 : HasDerivAt (fun s : ℝ => log (rho * (1 + x) / s)) (-(1 / s)) s := by
    have hc : rho * (1 + x) ≠ 0 := (mul_pos hρ hx).ne'
    have := ((hasDerivAt_const s (rho * (1 + x))).div (hasDerivAt_id' s) hs.ne').log
      (div_pos (mul_pos hρ hx) hs).ne'
    convert this using 1
    simp only [Pi.div_apply]
    field_simp
    ring
  have := ((((h1.const_add ((u - 1) * (1 + x))).add_const (1 + 1 / (1 + x))).add
    (hasDerivAt_id' s)).sub_const rho).add h2
  convert this using 1
  · funext s; unfold ssE m2U; simp only [Pi.add_apply]; ring
  · ring

/-- **The corrected envelope cap**: if at every `s ∈ [t₀, t]` and every pairing `E' ≥ E(t, v)`
the derivative ratio satisfies `λ(2us - E') ≤ 8cλ²(1 - ρ)²B_τ(s)`, then
`Γ(t₀, U(t₀)) - cR_τ(t₀, U(t₀)) ≤ Γ(t, v) - cR_τ(t, v)`. -/
theorem env_cap {x be al rho u τ t v c : ℝ} (hx : 1 < x) (hρ : 0 < rho)
    (hρ1 : rho < 1) (ht0 : rho * (1 + x) ≤ t) (htr : t ≤ 1 / (1 + x)) (hv : v ≤ m2U t)
    (hratio : ∀ s ∈ Icc (rho * (1 + x)) t, ∀ E', ssE x rho u t v ≤ E' →
      ssLam al rho * (2 * u * s - E') ≤ 8 * c * (ssLam al rho * (1 - rho)) ^ 2 *
        (1 + τ * (ssLam al rho * s - ssLam al rho * rho * ssDg x be al))) :
    ssGam rho u (m2U (rho * (1 + x))) (ssE x rho u (rho * (1 + x)) (m2U (rho * (1 + x)))) -
        c * ssR x be al rho u τ (rho * (1 + x)) (m2U (rho * (1 + x))) ≤
      ssGam rho u v (ssE x rho u t v) - c * ssR x be al rho u τ t v := by
  have hS : 0 < 1 + x := by linarith
  have ht0p : 0 < rho * (1 + x) := by positivity
  have htp : 0 < t := lt_of_lt_of_le ht0p ht0
  have ht2 : t < 1 / 2 := by
    calc t ≤ 1 / (1 + x) := htr
      _ < 1 / 2 := by apply one_div_lt_one_div_of_lt (by norm_num); linarith
  have hlam : 0 < ssLam al rho := by
    unfold ssLam; apply div_pos one_pos; nlinarith
  have h1ρ : 0 < 1 - rho := by linarith
  set lam := ssLam al rho with hlamdef
  set d := ssLam al rho * rho * ssDg x be al with hddef
  -- (a) the v-segment at fixed t
  have hva : ssGam rho u (m2U t) (ssE x rho u t (m2U t)) - c * ssR x be al rho u τ t (m2U t) ≤
      ssGam rho u v (ssE x rho u t v) - c * ssR x be al rho u τ t v := by
    set E₁ := ssE x rho u t v with hE₁
    set e := (m2U t - v) / t with he
    have he0 : 0 ≤ e := div_nonneg (by linarith) htp.le
    have hE₂ : ssE x rho u t (m2U t) = E₁ + e := by
      rw [hE₁, he]; unfold ssE; field_simp; ring
    have hU : m2U t = v + e * t := by rw [he]; field_simp; ring
    have hΓ : ssGam rho u (m2U t) (ssE x rho u t (m2U t)) - ssGam rho u v E₁ =
        e * (4 * u * t - 2 * E₁ - e) / (16 * (1 - rho) ^ 2) := by
      rw [hE₂, hU]; unfold ssGam; field_simp; ring
    have hR : ssR x be al rho u τ t (m2U t) - ssR x be al rho u τ t v =
        e * lam * (1 + τ * (lam * t - d)) := by
      unfold ssR ssW ssEL
      rw [hE₂, ← hE₁, hU]
      ring
    have hrat := hratio t ⟨ht0, le_rfl⟩ E₁ le_rfl
    have key : e * (4 * u * t - 2 * E₁ - e) / (16 * (1 - rho) ^ 2) ≤
        c * (e * lam * (1 + τ * (lam * t - d))) := by
      rw [div_le_iff₀ (by positivity)]
      have h2 : 2 * u * t - E₁ ≤ 8 * c * lam * (1 - rho) ^ 2 * (1 + τ * (lam * t - d)) := by
        have : lam * (2 * u * t - E₁) ≤ lam * (8 * c * lam * (1 - rho) ^ 2 *
            (1 + τ * (lam * t - d))) := by
          calc lam * (2 * u * t - E₁) ≤ 8 * c * (lam * (1 - rho)) ^ 2 *
              (1 + τ * (lam * t - d)) := hrat
            _ = lam * (8 * c * lam * (1 - rho) ^ 2 * (1 + τ * (lam * t - d))) := by ring
        exact le_of_mul_le_mul_left this hlam
      have h3 : e * (4 * u * t - 2 * E₁ - e) ≤ e * (2 * (2 * u * t - E₁)) := by
        apply mul_le_mul_of_nonneg_left _ he0; linarith
      have h4 : e * (2 * (2 * u * t - E₁)) ≤
          e * (2 * (8 * c * lam * (1 - rho) ^ 2 * (1 + τ * (lam * t - d)))) := by
        apply mul_le_mul_of_nonneg_left _ he0; linarith
      nlinarith
    have hR' : c * ssR x be al rho u τ t (m2U t) - c * ssR x be al rho u τ t v =
        c * (e * lam * (1 + τ * (lam * t - d))) := by rw [← hR]; ring
    linarith
  -- (b) the t-segment along v = U(s)
  have h16 : (16 * (1 - rho) ^ 2) ≠ 0 := by positivity
  obtain ⟨K, hK⟩ : ∃ K, K = (u - 1) / ssRA al be + ssRA al be + 1 - ssQ al rho +
      log (τ * ssQ al rho / ssRA al be) := ⟨_, rfl⟩
  have hgF : ∀ s, ssGam rho u (m2U s) (ssE x rho u s (m2U s)) -
      c * ssR x be al rho u τ s (m2U s) =
      (4 * u * m2U s - ssE x rho u s (m2U s) ^ 2) / (16 * (1 - rho) ^ 2) -
      c * ((lam ^ 2 * m2U s + d ^ 2 * u - d * lam * ssE x rho u s (m2U s) - 1) * τ + 1 / τ + K -
        (2 * d * u - lam * ssE x rho u s (m2U s))) := by
    intro s
    rw [hK]
    unfold ssGam ssR ssW ssEL
    ring
  have hderiv : ∀ s ∈ Icc (rho * (1 + x)) t, HasDerivAt (fun s =>
      (4 * u * m2U s - ssE x rho u s (m2U s) ^ 2) / (16 * (1 - rho) ^ 2) -
      c * ((lam ^ 2 * m2U s + d ^ 2 * u - d * lam * ssE x rho u s (m2U s) - 1) * τ + 1 / τ + K -
        (2 * d * u - lam * ssE x rho u s (m2U s))))
      (((2 * s - 1) / s) * ((4 * u * s - 2 * ssE x rho u s (m2U s)) / (16 * (1 - rho) ^ 2) -
        c * lam * (1 + τ * (lam * s - d)))) s := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ht0p hs.1
    have hE := env_Eb_deriv (u := u) hS hρ hs0
    have hU : HasDerivAt m2U (2 * s - 1) s := by
      unfold m2U
      have := ((hasDerivAt_id' s).const_sub 1).add ((hasDerivAt_id' s).pow 2)
      convert this using 1
      simp only [Nat.cast_ofNat]; ring
    have hA := ((hU.const_mul (4 * u)).sub (hE.pow 2)).div_const (16 * (1 - rho) ^ 2)
    have hB := (((((hU.const_mul (lam ^ 2)).add_const (d ^ 2 * u)).sub
      (hE.const_mul (d * lam))).sub_const 1).mul_const τ).add_const (1 / τ)
    have hC := (hB.add_const K).sub ((hE.const_mul lam).const_sub (2 * d * u))
    have := hA.sub (hC.const_mul c)
    convert this using 1
    simp only [Nat.cast_ofNat]
    field_simp
    ring
  have hnn : ∀ s ∈ Ioo (rho * (1 + x)) t,
      0 ≤ ((2 * s - 1) / s) * ((4 * u * s - 2 * ssE x rho u s (m2U s)) / (16 * (1 - rho) ^ 2) -
        c * lam * (1 + τ * (lam * s - d))) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ht0p hs.1.le
    have hst : s ≤ t := hs.2.le
    -- E(s, U(s)) ≥ E(t, U(t)) ≥ E(t, v)
    have hEbt : ssE x rho u t (m2U t) ≤ ssE x rho u s (m2U s) := by
      unfold ssE m2U
      have hlog : log (rho * (1 + x) / s) - log (rho * (1 + x) / t) = log (t / s) := by
        rw [← Real.log_div (by positivity) (by positivity)]
        congr 1; field_simp
      have hl := Real.one_sub_inv_le_log_of_pos (div_pos htp hs0)
      have h1 : (1 - s + s ^ 2 - 1) / s = s - 1 := by field_simp; ring
      have h2 : (1 - t + t ^ 2 - 1) / t = t - 1 := by field_simp; ring
      rw [h1, h2]
      have h3 : 1 - (t / s)⁻¹ = (t - s) / t := by field_simp
      rw [h3] at hl
      have h4 : 2 * (t - s) ≤ (t - s) / t := by
        rw [le_div_iff₀ htp]; nlinarith
      linarith
    have hEtv : ssE x rho u t v ≤ ssE x rho u t (m2U t) := by
      unfold ssE
      have : (v - 1) / t ≤ (m2U t - 1) / t := div_le_div_of_nonneg_right (by linarith) htp.le
      linarith
    have hrat := hratio s ⟨hs.1.le, hst⟩ (ssE x rho u s (m2U s)) (hEtv.trans hEbt)
    have hbr : (4 * u * s - 2 * ssE x rho u s (m2U s)) / (16 * (1 - rho) ^ 2) -
        c * lam * (1 + τ * (lam * s - d)) ≤ 0 := by
      have h2 : 2 * u * s - ssE x rho u s (m2U s) ≤
          8 * c * lam * (1 - rho) ^ 2 * (1 + τ * (lam * s - d)) := by
        have : lam * (2 * u * s - ssE x rho u s (m2U s)) ≤ lam * (8 * c * lam * (1 - rho) ^ 2 *
            (1 + τ * (lam * s - d))) := by
          calc lam * (2 * u * s - ssE x rho u s (m2U s)) ≤ 8 * c * (lam * (1 - rho)) ^ 2 *
              (1 + τ * (lam * s - d)) := hrat
            _ = lam * (8 * c * lam * (1 - rho) ^ 2 * (1 + τ * (lam * s - d))) := by ring
        exact le_of_mul_le_mul_left this hlam
      rw [sub_nonpos, div_le_iff₀ (by positivity)]
      nlinarith
    have hneg : (2 * s - 1) / s < 0 := by
      apply div_neg_of_neg_of_pos _ hs0; linarith
    exact mul_nonneg_of_nonpos_of_nonpos hneg.le hbr
  have hseg := ss_le_of_deriv ht0 hderiv hnn
  rw [← hgF, ← hgF] at hseg
  linarith

end SmoothedOctagon
