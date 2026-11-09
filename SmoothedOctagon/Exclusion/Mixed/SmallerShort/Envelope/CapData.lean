module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Interface
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Envelope.Cap

/-!
# Smaller-short window: the corrected envelope cap for the actual data

## Main API

* `env_Rs_phi`: `R*_τ(q) = Φ_{τq}(q)` (`ss_phi_eq` at `p = τq`).
* `env_Rs_dur`: `R*_τ ≤ max{R*_2, R*_2 + (T - 2)(w_* - 3/4)}` for `2 ≤ τ ≤ T = r_A/q`
  (`ss_dur_max`).
* `SmallerShortData.env_rA_pos`, `SmallerShortData.env_rA_lt`, `SmallerShortData.env_q_pos`: `0 < r_A < 1/2`, `q > 0`.
* `SmallerShortData.env_EL_cap`: `E_L ≤ 3q - J_A` at the actual outer root (`env_root_cap`).
* `SmallerShortData.env_cap_data`: if every derivative ratio along the envelope path is at most `c`, i.e.
  `2ub + e ≤ 8c(1 - q)²(1 + τb)` for `b = λs - d`, `s ∈ [t₀, t]`, `e ≤ E_L` (with `1 + τb > 0`
  available), then `Γ_*(q) - cR*_τ(q) ≤ Γ_actual`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- `R*_τ(q) = Φ_p(q)` with `p = τq` (`ss_phi_eq`). -/
theorem env_Rs_phi {x be al u q τ : ℝ} (hq : 0 < q) (hτ : 0 < τ) :
    ssRs x be al u q τ = ssPhi x be al u (τ * q) 0 q := by
  rw [← ss_phi_eq (by positivity) hq]
  unfold ssRs
  rw [mul_div_cancel_right₀ τ hq.ne']

/-- **The duration maximum** (`ss_dur_max`): for `q > 0` and
`2 ≤ τ`, `τq ≤ r_A`, `R*_τ(q) ≤ max{R*_2(q), R*_2(q) + (r_A/q - 2)(w_*(q) - 3/4)}`. -/
theorem env_Rs_dur {x be al u q τ : ℝ} (hq : 0 < q) (hτ : 2 ≤ τ)
    (hτT : τ * q ≤ ssRA al be) :
    ssRs x be al u q τ ≤ max (ssRs x be al u q 2)
      (ssRs x be al u q 2 + (ssRA al be / q - 2) * (ssWs x be al u q - 3 / 4)) := by
  have hT : τ ≤ ssRA al be / q := by rw [le_div_iff₀ hq]; exact hτT
  have h := ss_dur_max (w := ssWs x be al u q) hτ hT
  have hrA : 0 < ssRA al be := lt_of_lt_of_le (by positivity) hτT
  have e1 : log (τ * q / ssRA al be) = log (τ / (ssRA al be / q)) := by
    congr 1; field_simp
  have e2 : log (2 * q / ssRA al be) = log (2 / (ssRA al be / q)) := by
    congr 1; field_simp
  unfold ssRs ssF
  rw [e1, e2]
  rcases max_cases (2 * ssWs x be al u q - 3 / 2 + log (2 / (ssRA al be / q)))
    (2 * ssWs x be al u q - 3 / 2 + log (2 / (ssRA al be / q)) +
      (ssRA al be / q - 2) * (ssWs x be al u q - 3 / 4)) with ⟨hm, _⟩ | ⟨hm, _⟩
  · rw [hm] at h; apply le_max_of_le_left; linarith
  · rw [hm] at h; apply le_max_of_le_right; linarith

namespace SmallerShortData

variable (H : SmallerShortData)

theorem env_rA_pos : 0 < ssRA H.al H.be := by
  have := H.one_le_al; have := H.al_lt_x; have := H.x_le_be
  unfold ssRA; apply div_pos <;> linarith

theorem env_rA_lt : ssRA H.al H.be < 1 / 2 := by
  have := H.one_le_al; have := H.al_lt_x; have := H.x_le_be
  unfold ssRA; rw [div_lt_iff₀ (by linarith)]; linarith

theorem env_lam_pos : 0 < ssLam H.al H.rho := by
  have h1 := H.one_le_al; have h2 := H.rho_pos
  have : 0 ≤ H.rho * (H.al ^ 2 - 1) := mul_nonneg h2.le (by nlinarith)
  unfold ssLam; apply div_pos one_pos; linarith

theorem env_q_pos : 0 < H.q := by
  have := H.env_lam_pos; have := H.one_le_al; have := H.rho_pos
  unfold SmallerShortData.q ssQ; positivity

/-- `E_L ≤ 3q - J_A` at the actual outer root (`env_root_cap`). -/
theorem env_EL_cap : H.EL ≤ 3 * H.q - (m2U (ssRA H.al H.be) - H.u) / ssRA H.al H.be :=
  env_root_cap H.env_rA_pos H.env_rA_lt.le H.two_lt_τ.le H.env_q_pos H.τ_lt.le H.w_le H.root

/-- **The corrected envelope cap for the actual data**: if every derivative ratio along the
envelope path is at most `c`, then `Γ_*(q) - cR*_τ(q) ≤ Γ_actual` (`env_cap` in scale
coordinates). -/
theorem env_cap_data {c : ℝ}
    (hrat : ∀ s ∈ Icc (H.rho * (1 + H.x)) H.t, ∀ e ≤ H.EL,
      0 < 1 + H.τ * (ssLam H.al H.rho * s - ssLam H.al H.rho * H.rho * ssDg H.x H.be H.al) →
      2 * H.u * (ssLam H.al H.rho * s - ssLam H.al H.rho * H.rho * ssDg H.x H.be H.al) + e ≤
        8 * c * (1 - H.q) ^ 2 *
          (1 + H.τ * (ssLam H.al H.rho * s - ssLam H.al H.rho * H.rho * ssDg H.x H.be H.al))) :
    ssGs H.x H.al H.u H.q - c * ssRs H.x H.be H.al H.u H.q H.τ ≤ H.Γ := by
  have hx := H.one_lt_x
  have hal := H.one_le_al
  have hρ := H.rho_pos
  have hlam := H.env_lam_pos
  have hq0 := H.env_q_pos
  have hq1 : H.q < 1 := by have := H.q_lt; unfold SmallerShortData.q; linarith
  have hρ1 : H.rho < 1 := by linarith [H.rho_le]
  have hc := ss_scale_coords (x := H.x) (be := H.be) hal hρ
  have he := ss_env_scale (x := H.x) (be := H.be) (u := H.u) (τ := H.τ) (by linarith) hal hq0 hq1
  have hq : ssQ H.al H.rho = H.q := rfl
  rw [← hq, hc.1] at he
  rw [← hq, ← he.2.2.2, ← he.2.2.1]
  have hlq : ssLam H.al H.rho * (1 - H.rho) = 1 - H.q := by
    unfold SmallerShortData.q ssQ ssLam
    have : 0 ≤ H.rho * (H.al ^ 2 - 1) := mul_nonneg hρ.le (by nlinarith)
    have : 1 + H.rho * (H.al ^ 2 - 1) ≠ 0 := by linarith
    field_simp; ring
  have ht0 : H.rho * (1 + H.x) ≤ H.t := by
    have := H.rho_lt_rt
    have e : 1 / (1 + H.x) * H.t = H.t / (1 + H.x) := by ring
    rw [e, lt_div_iff₀ (by linarith)] at this; linarith
  have hcap := env_cap (c := c) (τ := H.τ) hx hρ hρ1 ht0 H.t_le_r H.v_le (fun s hs E' hE' => by
    have hB := ss_B_factor_pos hx hal H.al_lt_x.le H.x_le_be hρ hs.1 (by linarith [H.two_lt_τ])
      H.τ_lt.le
    have he : 2 * H.u * (ssLam H.al H.rho * H.rho * ssDg H.x H.be H.al) -
        ssLam H.al H.rho * E' ≤ H.EL := by
      rw [H.EL_eq]; unfold ssEL
      have := mul_le_mul_of_nonneg_left hE' hlam.le
      linarith
    have := hrat s hs _ he hB
    rw [hlq]
    linarith)
  rw [← H.E_eq, ← H.Γ_eq, H.root_zero] at hcap
  linarith

end SmallerShortData

end SmoothedOctagon
