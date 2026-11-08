module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4Closed
public import SmoothedOctagon.Exclusion.Mixed.Short.Calc

/-!
# Heavy leaf `hs4_floor_box`: the rational surrogates of `Φ` and `Ψ`

The logarithm `log y`, `y = 2αA/Σ`, is bounded above by `L₀ + h - h²/2 + h³/3`, `h = ky - 1`, for
any `k > 0` with `log(1/k) ≤ L₀` (`log(1 + h) ≤ h - h²/2 + h³/3`, `hh46_log_le_taylor3`). This gives
the rational surrogates `hh46S4PhiR ≤ Φ`, `hh46S4PsiR ≤ Ψ`. With `u = nu/du`, the surrogate minus
`1829/10000` is `hh46S4N{Phi,Psi}/hh46S4M`, an identity formal in the atoms `x, α, A = α + β, Σ, S,
U = S² - S + 1, D, Pn = S³(nu - du) + (3S - 1)du` (`hh46_s4_phiR_link`, `hh46_s4_psiR_link`).
The constants `k = 1/y₀` are the values of `1/y` at the two minimizing corners, and `L₀` comes from
three terms of `2 artanh` (`hh46_log_ge_quintic`, inventory HS-S4 R22).

## Main API

`hh46_log_le_taylor3`, `hh46_log_ge_quintic`, `hh46S4Ls`, `hh46S4PhiR`, `hh46S4PsiR`,
`hh46_s4_phiR_le`, `hh46_s4_psiR_le`, `hh46S4NPhi`, `hh46S4NPsi`, `hh46S4M`, `hh46_s4_phiR_link`,
`hh46_s4_psiR_link`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `log t ≤ (t - 1) - (t - 1)²/2 + (t - 1)³/3` for `t > 0` (derivative of the difference
`(t - 1)³/t`). -/
theorem hh46_log_le_taylor3 {t : ℝ} (ht : 0 < t) :
    log t ≤ (t - 1) - (t - 1) ^ 2 / 2 + (t - 1) ^ 3 / 3 := by
  have hd : ∀ s : ℝ, 0 < s → HasDerivAt (fun s => (s - 1) - (s - 1) ^ 2 / 2 + (s - 1) ^ 3 / 3 - log s)
      ((s - 1) ^ 3 / s) s := by
    intro s hs
    have h1 := ((((hasDerivAt_id s).sub_const 1).sub
      ((((hasDerivAt_id s).sub_const 1).pow 2).div_const 2)).add
      ((((hasDerivAt_id s).sub_const 1).pow 3).div_const 3)).sub (Real.hasDerivAt_log hs.ne')
    refine h1.congr_deriv ?_
    simp only [id, Nat.cast_ofNat]
    field_simp
    ring
  rcases le_total 1 t with h | h
  · have := ss_le_of_deriv (f := fun s => (s - 1) - (s - 1) ^ 2 / 2 + (s - 1) ^ 3 / 3 - log s)
      (f' := fun s => (s - 1) ^ 3 / s) h (fun s hs => hd s (by linarith [hs.1]))
      (fun s hs => by have : 0 < s - 1 := by linarith [hs.1]
                      have : 0 < s := by linarith [hs.1]
                      positivity)
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      sub_zero, log_one] at this
    linarith
  · have := ss_le_of_deriv (f := fun s => -((s - 1) - (s - 1) ^ 2 / 2 + (s - 1) ^ 3 / 3 - log s))
      (f' := fun s => -((s - 1) ^ 3 / s)) h (fun s hs => (hd s (by linarith [hs.1])).neg)
      (fun s hs => by
        have h1 : 0 < s := by linarith [hs.1]
        have h2 : (s - 1) ^ 3 ≤ 0 := by
          have : s - 1 ≤ 0 := by linarith [hs.2]
          nlinarith [sq_nonneg (s - 1)]
        have : (s - 1) ^ 3 / s ≤ 0 := div_nonpos_of_nonpos_of_nonneg h2 h1.le
        linarith)
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      sub_zero, log_one] at this
    linarith

/-- Three terms of `2 artanh`: `2(w + w³/3 + w⁵/5) ≤ log z` for `z ≥ 1`, `w = (z - 1)/(z + 1)`
(derivative of the difference `(z - 1)⁶/(z(z + 1)⁶)`). -/
theorem hh46_log_ge_quintic {z : ℝ} (hz : 1 ≤ z) :
    2 * ((z - 1) / (z + 1) + ((z - 1) / (z + 1)) ^ 3 / 3 + ((z - 1) / (z + 1)) ^ 5 / 5) ≤ log z := by
  have h := ss_le_of_deriv
    (f := fun t => log t - 2 * ((t - 1) / (t + 1) + ((t - 1) / (t + 1)) ^ 3 / 3 +
      ((t - 1) / (t + 1)) ^ 5 / 5))
    (f' := fun t => (t - 1) ^ 6 / (t * (t + 1) ^ 6)) hz (fun t ht => ?_) (fun t ht => by
      have : 0 < t := by linarith [ht.1]
      positivity)
  · simp only [log_one, sub_self, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero, mul_zero] at h
    linarith
  have ht : 0 < t := by linarith [ht.1]
  have hw : HasDerivAt (fun t : ℝ => (t - 1) / (t + 1)) (2 / (t + 1) ^ 2) t := by
    have h1 : HasDerivAt (fun t : ℝ => t - 1) 1 t := by simpa using (hasDerivAt_id t).sub_const 1
    have h2 : HasDerivAt (fun t : ℝ => t + 1) 1 t := by simpa using (hasDerivAt_id t).add_const 1
    refine (h1.div h2 (by positivity)).congr_deriv ?_
    field_simp
    ring
  have := (Real.hasDerivAt_log ht.ne').sub (((hw.add (((hw.mul hw).mul hw).div_const 3)).add
    (((((hw.mul hw).mul hw).mul hw).mul hw).div_const 5)).const_mul 2)
  convert this using 1
  · funext s; simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]; ring
  · simp only [Pi.mul_apply]
    field_simp
    ring

/-- `h = k·2α(α + β)/Σ - 1`. -/
noncomputable def hh46S4h (k x be al : ℝ) : ℝ := k * (2 * al * (al + be) / (x * (x + 2) + al ^ 2)) - 1

/-- The logarithm surrogate `L₀ + h - h²/2 + h³/3`. -/
noncomputable def hh46S4Ls (k L0 x be al : ℝ) : ℝ :=
  L0 + hh46S4h k x be al - hh46S4h k x be al ^ 2 / 2 + hh46S4h k x be al ^ 3 / 3

theorem hh46_s4_log_le_Ls {k L0 x be al : ℝ} (hk : 0 < k) (hL : log (1 / k) ≤ L0) (hx : 0 < x)
    (hal : 0 < al) (hbe : 0 < be) :
    log (2 * al * (al + be) / (x * (x + 2) + al ^ 2)) ≤ hh46S4Ls k L0 x be al := by
  have hy : 0 < 2 * al * (al + be) / (x * (x + 2) + al ^ 2) := by positivity
  have hky : 0 < k * (2 * al * (al + be) / (x * (x + 2) + al ^ 2)) := by positivity
  have e : log (2 * al * (al + be) / (x * (x + 2) + al ^ 2)) =
      log (k * (2 * al * (al + be) / (x * (x + 2) + al ^ 2))) + log (1 / k) := by
    rw [← log_mul hky.ne' (by positivity)]
    congr 1
    field_simp
  have h3 := hh46_log_le_taylor3 hky
  unfold hh46S4Ls hh46S4h
  linarith

/-- The surrogate of `Φ`. -/
noncomputable def hh46S4PhiR (k L0 x be al u : ℝ) : ℝ :=
  hh46S4G x u - (2 * hh46S4Wc x be al u - 1 / 2 + hh46S4Rest x be al u + hh46S4Ls k L0 x be al) / 7

/-- The surrogate of `Ψ`. -/
noncomputable def hh46S4PsiR (k L0 x be al u : ℝ) : ℝ :=
  hh46S4G x u - ((x * (x + 2) + al ^ 2) / (al * (al + be)) * (hh46S4Wc x be al u - 3 / 4) + 1 +
    hh46S4Rest x be al u + hh46S4Ls k L0 x be al) / 7

theorem hh46_s4_phiR_le {k L0 x be al u : ℝ} (hk : 0 < k) (hL : log (1 / k) ≤ L0) (hx : 0 < x)
    (hal : 0 < al) (hbe : 0 < be) : hh46S4PhiR k L0 x be al u ≤ hh46S4PhiC x be al u := by
  have := hh46_s4_log_le_Ls hk hL hx hal hbe
  unfold hh46S4PhiR hh46S4PhiC
  linarith

theorem hh46_s4_psiR_le {k L0 x be al u : ℝ} (hk : 0 < k) (hL : log (1 / k) ≤ L0) (hx : 0 < x)
    (hal : 0 < al) (hbe : 0 < be) : hh46S4PsiR k L0 x be al u ≤ hh46S4PsiC x be al u := by
  have := hh46_s4_log_le_Ls hk hL hx hal hbe
  unfold hh46S4PsiR hh46S4PsiC
  linarith

/-- The common denominator `672X²(X + 2)²du²Σ³αA`. -/
noncomputable def hh46S4M (X AL A Sg du : ℝ) : ℝ :=
  16 * 42 * X ^ (2 : ℕ) * (X + 2) ^ (2 : ℕ) * du ^ (2 : ℕ) * Sg ^ (3 : ℕ) * AL * A

theorem hh46_s4_M_pos {X AL A Sg du : ℝ} (hX : 0 < X) (hAL : 0 < AL) (hA : 0 < A) (hSg : 0 < Sg)
    (hdu : 0 < du) : 0 < hh46S4M X AL A Sg du := by
  unfold hh46S4M; positivity

/-- The cleared numerator of `Phi_r - 1829/10000` in the atoms `X = x`, `AL = α`, `A = α + β`,
`Sg = Σ`, `S = 1 + x`, `U = S² - S + 1`, `D`, `Pn = S³(nu - du) + (3S - 1)du` (`u = nu/du`), `k = 1/y₀`,
`L0`; denominator `hh46S4M` (`SMALL_SHAPE_CASIMIR_FLOOR` (10)-(11) with the logarithm surrogate). -/
noncomputable def hh46S4NPhi (X AL A Sg S U D Pn nu du k L0 : ℝ) : ℝ :=
  42 * Sg ^ (3 : ℕ) * AL * A * (4 * nu * du * S ^ (2 : ℕ) * U - Pn ^ (2 : ℕ)) - X ^ (2 : ℕ) * (X + 2) ^ (2 : ℕ) * du * ((76818 / 625) * du * Sg ^ (3 : ℕ) * AL * A + 192 * Sg * AL * A * (S ^ (2 : ℕ) * U * du + D ^ (2 : ℕ) * nu - D * Pn) - 48 * du * Sg ^ (3 : ℕ) * AL * A + 96 * Sg ^ (3 : ℕ) * A ^ (2 : ℕ) * (nu - du) + 96 * du * Sg ^ (3 : ℕ) * AL ^ (2 : ℕ) - 96 * du * Sg ^ (2 : ℕ) * AL ^ (3 : ℕ) * A - 96 * Sg ^ (2 : ℕ) * AL * A * (2 * D * nu - Pn) + 96 * du * AL * A * (L0 * Sg ^ (3 : ℕ) + (2 * k * AL * A - Sg) * Sg ^ (2 : ℕ) - (2 * k * AL * A - Sg) ^ (2 : ℕ) * Sg / 2 + (2 * k * AL * A - Sg) ^ (3 : ℕ) / 3))

/-- The cleared numerator of `Psi_r - 1829/10000` in the atoms `X = x`, `AL = α`, `A = α + β`,
`Sg = Σ`, `S = 1 + x`, `U = S² - S + 1`, `D`, `Pn = S³(nu - du) + (3S - 1)du` (`u = nu/du`), `k = 1/y₀`,
`L0`; denominator `hh46S4M` (`SMALL_SHAPE_CASIMIR_FLOOR` (10)-(11) with the logarithm surrogate). -/
noncomputable def hh46S4NPsi (X AL A Sg S U D Pn nu du k L0 : ℝ) : ℝ :=
  42 * Sg ^ (3 : ℕ) * AL * A * (4 * nu * du * S ^ (2 : ℕ) * U - Pn ^ (2 : ℕ)) - X ^ (2 : ℕ) * (X + 2) ^ (2 : ℕ) * du * ((76818 / 625) * du * Sg ^ (3 : ℕ) * AL * A + 96 * Sg ^ (2 : ℕ) * (S ^ (2 : ℕ) * U * du + D ^ (2 : ℕ) * nu - D * Pn) - 72 * du * Sg ^ (4 : ℕ) + 96 * du * Sg ^ (3 : ℕ) * AL * A + 96 * Sg ^ (3 : ℕ) * A ^ (2 : ℕ) * (nu - du) + 96 * du * Sg ^ (3 : ℕ) * AL ^ (2 : ℕ) - 96 * du * Sg ^ (2 : ℕ) * AL ^ (3 : ℕ) * A - 96 * Sg ^ (2 : ℕ) * AL * A * (2 * D * nu - Pn) + 96 * du * AL * A * (L0 * Sg ^ (3 : ℕ) + (2 * k * AL * A - Sg) * Sg ^ (2 : ℕ) - (2 * k * AL * A - Sg) ^ (2 : ℕ) * Sg / 2 + (2 * k * AL * A - Sg) ^ (3 : ℕ) / 3))

/-- `P = Pn/du` for `u = nu/du`. -/
theorem hh46_s4_P_div {x nu du : ℝ} (hdu : du ≠ 0) :
    hh46S4P x (nu / du) = ((1 + x) ^ 3 * (nu - du) + (3 * (1 + x) - 1) * du) / du := by
  unfold hh46S4P; field_simp; ring

/-- **The surrogate of `Φ` over the common denominator.** -/
theorem hh46_s4_phiR_link {k L0 x be al nu du : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be)
    (hdu : 0 < du) :
    hh46S4PhiR k L0 x be al (nu / du) - 1829 / 10000 =
      hh46S4NPhi x al (al + be) (x * (x + 2) + al ^ 2) (1 + x) ((1 + x) ^ 2 - (1 + x) + 1)
          (hsDg x be al) ((1 + x) ^ 3 * (nu - du) + (3 * (1 + x) - 1) * du) nu du k L0 /
        hh46S4M x al (al + be) (x * (x + 2) + al ^ 2) du := by
  have hM := hh46_s4_M_pos (X := x) (AL := al) (A := al + be) (Sg := x * (x + 2) + al ^ 2) (du := du)
    hx hal (by positivity) (by positivity) hdu
  rw [eq_div_iff hM.ne']
  unfold hh46S4PhiR hh46S4Rest hh46S4G hh46S4Wc hh46S4EL hh46S4Ls hh46S4h
  rw [hh46_s4_P_div hdu.ne']
  have hx0 : x ≠ 0 := hx.ne'
  have hx2 : x + 2 ≠ 0 := by positivity
  have hal0 : al ≠ 0 := hal.ne'
  have hdu0 : du ≠ 0 := hdu.ne'
  have hA : al + be ≠ 0 := by positivity
  have hSg : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  unfold hh46S4M hh46S4NPhi
  generalize ((1 + x) ^ 3 * (nu - du) + (3 * (1 + x) - 1) * du) = Pn
  generalize hsDg x be al = D
  generalize ((1 + x) ^ 2 - (1 + x) + 1) = U
  generalize (1 + x) = S
  generalize hA' : al + be = A at hA ⊢
  generalize hS' : x * (x + 2) + al ^ 2 = Sg at hSg ⊢
  field_simp
  ring

/-- **The surrogate of `Ψ` over the common denominator.** -/
theorem hh46_s4_psiR_link {k L0 x be al nu du : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be)
    (hdu : 0 < du) :
    hh46S4PsiR k L0 x be al (nu / du) - 1829 / 10000 =
      hh46S4NPsi x al (al + be) (x * (x + 2) + al ^ 2) (1 + x) ((1 + x) ^ 2 - (1 + x) + 1)
          (hsDg x be al) ((1 + x) ^ 3 * (nu - du) + (3 * (1 + x) - 1) * du) nu du k L0 /
        hh46S4M x al (al + be) (x * (x + 2) + al ^ 2) du := by
  have hM := hh46_s4_M_pos (X := x) (AL := al) (A := al + be) (Sg := x * (x + 2) + al ^ 2) (du := du)
    hx hal (by positivity) (by positivity) hdu
  rw [eq_div_iff hM.ne']
  unfold hh46S4PsiR hh46S4Rest hh46S4G hh46S4Wc hh46S4EL hh46S4Ls hh46S4h
  rw [hh46_s4_P_div hdu.ne']
  have hx0 : x ≠ 0 := hx.ne'
  have hx2 : x + 2 ≠ 0 := by positivity
  have hal0 : al ≠ 0 := hal.ne'
  have hdu0 : du ≠ 0 := hdu.ne'
  have hA : al + be ≠ 0 := by positivity
  have hSg : x * (x + 2) + al ^ 2 ≠ 0 := by positivity
  unfold hh46S4M hh46S4NPsi
  generalize ((1 + x) ^ 3 * (nu - du) + (3 * (1 + x) - 1) * du) = Pn
  generalize hsDg x be al = D
  generalize ((1 + x) ^ 2 - (1 + x) + 1) = U
  generalize (1 + x) = S
  generalize hA' : al + be = A at hA ⊢
  generalize hS' : x * (x + 2) + al ^ 2 = Sg at hSg ⊢
  field_simp
  ring

end SmoothedOctagon
