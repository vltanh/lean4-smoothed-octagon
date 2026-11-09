module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.Defs

/-!
# Smaller-short window, Casimir floor: closed forms of `Φ` and `Ψ` at the central scale

At `q = q_c = α²/Σ`,
`Σ = x(x + 2) + α²`, the scale `ρ(q_c) = 1/S²` (`S = 1 + x`), and with
`P = S³(u - 1) + 3S - 1` (`= S²E_c`), `D = α² + 2αβ + 1 + 2x - 2βx`, `A = α + β`:

* `Γ_*(q_c) = G = (4uS²(S² - S + 1) - P²)/(16x²(x + 2)²)`,
* `w_*(q_c) = w_c = (S²(S² - S + 1) + D²u - DP)/Σ²`, `E_{L,*}(q_c) = E_L = (2Du - P)/Σ`,
* `Φ = G - (2w_c - 1/2 + (u - 1)A/α + α/A - α²/Σ - E_L + log(2αA/Σ))/7`,
* `Ψ = G - (T(w_c - 3/4) + 1 + (u - 1)A/α + α/A - α²/Σ - E_L + log(2αA/Σ))/7`, `T = Σ/(αA)`.

## Main API

`casClosedG`, `casClosedWc`, `casClosedEL`, `casClosedPhiC`, `casClosedPsiC`, `cas_closed_phi_eq`, `cas_closed_psi_eq`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `P = S³(u - 1) + 3S - 1`, `S = 1 + x`. -/
noncomputable def casClosedP (x u : ℝ) : ℝ := (1 + x) ^ 3 * (u - 1) + 3 * (1 + x) - 1

/-- `G = Γ_*(q_c)`. -/
noncomputable def casClosedG (x u : ℝ) : ℝ :=
  (4 * u * (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) - casClosedP x u ^ 2) /
    (16 * x ^ 2 * (x + 2) ^ 2)

/-- `w_c = w_*(q_c)`. -/
noncomputable def casClosedWc (x be al u : ℝ) : ℝ :=
  ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) + ssDg x be al ^ 2 * u - ssDg x be al * casClosedP x u) /
    (x * (x + 2) + al ^ 2) ^ 2

/-- `E_L = E_{L,*}(q_c)`. -/
noncomputable def casClosedEL (x be al u : ℝ) : ℝ :=
  (2 * ssDg x be al * u - casClosedP x u) / (x * (x + 2) + al ^ 2)

/-- The part of the bracket common to `Φ` and `Ψ`, without the logarithm. -/
noncomputable def casClosedRest (x be al u : ℝ) : ℝ :=
  (u - 1) * (al + be) / al + al / (al + be) - al ^ 2 / (x * (x + 2) + al ^ 2) - casClosedEL x be al u

/-- The closed form of `Φ`. -/
noncomputable def casClosedPhiC (x be al u : ℝ) : ℝ :=
  casClosedG x u - (2 * casClosedWc x be al u - 1 / 2 + casClosedRest x be al u +
    log (2 * al * (al + be) / (x * (x + 2) + al ^ 2))) / 7

/-- The closed form of `Ψ`. -/
noncomputable def casClosedPsiC (x be al u : ℝ) : ℝ :=
  casClosedG x u - ((x * (x + 2) + al ^ 2) / (al * (al + be)) * (casClosedWc x be al u - 3 / 4) + 1 +
    casClosedRest x be al u + log (2 * al * (al + be) / (x * (x + 2) + al ^ 2))) / 7

theorem cas_closed_rho {x al : ℝ} (hx : 0 < x) (hal : 0 < al) :
    ssRhoOf al (ssQc x al) = 1 / (1 + x) ^ 2 := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h2 : (1 + x) ≠ 0 := by positivity
  unfold ssRhoOf ssQc
  have h3 : al ^ 2 - (al ^ 2 - 1) * (al ^ 2 / (x * (x + 2) + al ^ 2)) =
      al ^ 2 * (1 + x) ^ 2 / (x * (x + 2) + al ^ 2) := by
    field_simp; ring
  rw [h3]
  field_simp

theorem cas_closed_G_eq {x al u : ℝ} (hx : 0 < x) (hal : 0 < al) :
    ssGs x al u (ssQc x al) = casClosedG x u := by
  have h2 : (1 + x) ≠ 0 := by positivity
  have h3 : x ≠ 0 := hx.ne'
  have h4 : x + 2 ≠ 0 := by positivity
  unfold ssGs
  rw [cas_closed_rho hx hal]
  unfold m2U ssE0 casClosedG casClosedP
  have h5 : (1 - 1 / (1 + x) ^ 2) = x * (x + 2) / (1 + x) ^ 2 := by field_simp; ring
  rw [h5]
  field_simp
  ring

theorem cas_closed_W_eq {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) :
    ssWs x be al u (ssQc x al) = casClosedWc x be al u := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h2 : (1 + x) ≠ 0 := by positivity
  have h3 : al ≠ 0 := hal.ne'
  unfold ssWs ssA1 ssA2 ssE0 ssQc casClosedWc casClosedP
  field_simp
  ring

theorem cas_closed_EL_eq {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) :
    ssELs x be al u (ssQc x al) = casClosedEL x be al u := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h2 : (1 + x) ≠ 0 := by positivity
  have h3 : al ≠ 0 := hal.ne'
  unfold ssELs ssA3 ssE0 ssQc casClosedEL casClosedP
  field_simp
  ring

theorem cas_closed_log_arg {x be al : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    2 * ssQc x al / ssRA al be = 2 * al * (al + be) / (x * (x + 2) + al ^ 2) := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h3 : al ≠ 0 := hal.ne'
  have h4 : al + be ≠ 0 := by positivity
  unfold ssQc ssRA
  field_simp

/-- `Φ` in closed form. -/
theorem cas_closed_phi_eq {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    casPhi x be al u = casClosedPhiC x be al u := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h3 : al ≠ 0 := hal.ne'
  have h4 : al + be ≠ 0 := by positivity
  unfold casPhi ssRs ssF
  rw [cas_closed_G_eq hx hal, cas_closed_W_eq hx hal, cas_closed_EL_eq hx hal, cas_closed_log_arg hx hal hbe]
  unfold casClosedPhiC casClosedRest ssRA ssQc
  field_simp
  ring

/-- `Ψ` in closed form. -/
theorem cas_closed_psi_eq {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    casPsi x be al u = casClosedPsiC x be al u := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h3 : al ≠ 0 := hal.ne'
  have h4 : al + be ≠ 0 := by positivity
  unfold casPsi
  rw [cas_closed_phi_eq hx hal hbe, cas_closed_W_eq hx hal]
  unfold casClosedPhiC casClosedPsiC ssRA ssQc
  field_simp
  ring

end SmoothedOctagon
