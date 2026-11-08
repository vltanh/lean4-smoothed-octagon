module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S4Defs

/-!
# Heavy leaf `hs4_floor_box`: closed forms of `Φ` and `Ψ` at the central scale

`SMALL_SHAPE_CASIMIR_FLOOR` (10)-(12), inventory HS-S4 R18. At `q = q_c = α²/Σ`,
`Σ = x(x + 2) + α²`, the scale `ρ(q_c) = 1/S²` (`S = 1 + x`), and with
`P = S³(u - 1) + 3S - 1` (`= S²E_c`), `D = α² + 2αβ + 1 + 2x - 2βx`, `A = α + β`:

* `Γ_*(q_c) = G = (4uS²(S² - S + 1) - P²)/(16x²(x + 2)²)`,
* `w_*(q_c) = w_c = (S²(S² - S + 1) + D²u - DP)/Σ²`, `E_{L,*}(q_c) = E_L = (2Du - P)/Σ`,
* `Φ = G - (2w_c - 1/2 + (u - 1)A/α + α/A - α²/Σ - E_L + log(2αA/Σ))/7`,
* `Ψ = G - (T(w_c - 3/4) + 1 + (u - 1)A/α + α/A - α²/Σ - E_L + log(2αA/Σ))/7`, `T = Σ/(αA)`.

## Main API

`hh46S4G`, `hh46S4Wc`, `hh46S4EL`, `hh46S4PhiC`, `hh46S4PsiC`, `hh46_s4_phi_eq`, `hh46_s4_psi_eq`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `P = S³(u - 1) + 3S - 1`, `S = 1 + x`. -/
noncomputable def hh46S4P (x u : ℝ) : ℝ := (1 + x) ^ 3 * (u - 1) + 3 * (1 + x) - 1

/-- `G = Γ_*(q_c)`. -/
noncomputable def hh46S4G (x u : ℝ) : ℝ :=
  (4 * u * (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) - hh46S4P x u ^ 2) /
    (16 * x ^ 2 * (x + 2) ^ 2)

/-- `w_c = w_*(q_c)`. -/
noncomputable def hh46S4Wc (x be al u : ℝ) : ℝ :=
  ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) + hsDg x be al ^ 2 * u - hsDg x be al * hh46S4P x u) /
    (x * (x + 2) + al ^ 2) ^ 2

/-- `E_L = E_{L,*}(q_c)`. -/
noncomputable def hh46S4EL (x be al u : ℝ) : ℝ :=
  (2 * hsDg x be al * u - hh46S4P x u) / (x * (x + 2) + al ^ 2)

/-- The part of the bracket common to `Φ` and `Ψ`, without the logarithm. -/
noncomputable def hh46S4Rest (x be al u : ℝ) : ℝ :=
  (u - 1) * (al + be) / al + al / (al + be) - al ^ 2 / (x * (x + 2) + al ^ 2) - hh46S4EL x be al u

/-- The closed form of `Φ`. -/
noncomputable def hh46S4PhiC (x be al u : ℝ) : ℝ :=
  hh46S4G x u - (2 * hh46S4Wc x be al u - 1 / 2 + hh46S4Rest x be al u +
    log (2 * al * (al + be) / (x * (x + 2) + al ^ 2))) / 7

/-- The closed form of `Ψ`. -/
noncomputable def hh46S4PsiC (x be al u : ℝ) : ℝ :=
  hh46S4G x u - ((x * (x + 2) + al ^ 2) / (al * (al + be)) * (hh46S4Wc x be al u - 3 / 4) + 1 +
    hh46S4Rest x be al u + log (2 * al * (al + be) / (x * (x + 2) + al ^ 2))) / 7

theorem hh46_s4_rho {x al : ℝ} (hx : 0 < x) (hal : 0 < al) :
    hsRhoOf al (hsQc x al) = 1 / (1 + x) ^ 2 := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h2 : (1 + x) ≠ 0 := by positivity
  unfold hsRhoOf hsQc
  have h3 : al ^ 2 - (al ^ 2 - 1) * (al ^ 2 / (x * (x + 2) + al ^ 2)) =
      al ^ 2 * (1 + x) ^ 2 / (x * (x + 2) + al ^ 2) := by
    field_simp; ring
  rw [h3]
  field_simp

theorem hh46_s4_G_eq {x al u : ℝ} (hx : 0 < x) (hal : 0 < al) :
    hsGs x al u (hsQc x al) = hh46S4G x u := by
  have h2 : (1 + x) ≠ 0 := by positivity
  have h3 : x ≠ 0 := hx.ne'
  have h4 : x + 2 ≠ 0 := by positivity
  unfold hsGs
  rw [hh46_s4_rho hx hal]
  unfold m2U hsE0 hh46S4G hh46S4P
  have h5 : (1 - 1 / (1 + x) ^ 2) = x * (x + 2) / (1 + x) ^ 2 := by field_simp; ring
  rw [h5]
  field_simp
  ring

theorem hh46_s4_W_eq {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) :
    hsWs x be al u (hsQc x al) = hh46S4Wc x be al u := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h2 : (1 + x) ≠ 0 := by positivity
  have h3 : al ≠ 0 := hal.ne'
  unfold hsWs hsA1 hsA2 hsE0 hsQc hh46S4Wc hh46S4P
  field_simp
  ring

theorem hh46_s4_EL_eq {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) :
    hsELs x be al u (hsQc x al) = hh46S4EL x be al u := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h2 : (1 + x) ≠ 0 := by positivity
  have h3 : al ≠ 0 := hal.ne'
  unfold hsELs hsA3 hsE0 hsQc hh46S4EL hh46S4P
  field_simp
  ring

theorem hh46_s4_log_arg {x be al : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    2 * hsQc x al / hsRA al be = 2 * al * (al + be) / (x * (x + 2) + al ^ 2) := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h3 : al ≠ 0 := hal.ne'
  have h4 : al + be ≠ 0 := by positivity
  unfold hsQc hsRA
  field_simp

/-- `Φ` in closed form. -/
theorem hh46_s4_phi_eq {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    hs4Phi x be al u = hh46S4PhiC x be al u := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h3 : al ≠ 0 := hal.ne'
  have h4 : al + be ≠ 0 := by positivity
  unfold hs4Phi hsRs hsF
  rw [hh46_s4_G_eq hx hal, hh46_s4_W_eq hx hal, hh46_s4_EL_eq hx hal, hh46_s4_log_arg hx hal hbe]
  unfold hh46S4PhiC hh46S4Rest hsRA hsQc
  field_simp
  ring

/-- `Ψ` in closed form. -/
theorem hh46_s4_psi_eq {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    hs4Psi x be al u = hh46S4PsiC x be al u := by
  have h1 : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  have h3 : al ≠ 0 := hal.ne'
  have h4 : al + be ≠ 0 := by positivity
  unfold hs4Psi
  rw [hh46_s4_phi_eq hx hal hbe, hh46_s4_W_eq hx hal]
  unfold hh46S4PhiC hh46S4PsiC hsRA hsQc
  field_simp
  ring

end SmoothedOctagon
