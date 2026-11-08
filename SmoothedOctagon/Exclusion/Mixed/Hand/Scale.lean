module

public import SmoothedOctagon.Exclusion.Mixed.Centre
public import SmoothedOctagon.Exclusion.Mixed.Hand.Link
public import SmoothedOctagon.Exclusion.Mixed.Hand.Order

/-!
# Case M2 by hand: the sharpened central scale bounds

The Casimir lower bound at the reverse centre `a` of an actual window, with the competitive cap
`γ² < 9193/50000` (`M2Window.cas_lt`):

* `nh_a_sq`: `a² < 2/3` (`HAND_PROOF_REFINEMENTS` §2);
* `nh_scale_of_t`: if `t ≤ 2/5`, then `a < 4/5` (`MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND`).

In the centre coordinates `r = a/(a + b)`, `t = a/(a + c)`, `ρ = a²/(a² + 4)` (`ρ < rt`),
`γ² = (4uv - E²)/(16(1 - ρ)²)` (`nh_window_cas`). Lowering both incident norms to a floor `μ`
(`nh_lower_norms`) and raising both ratios to a cap `ζ` (`nh_psi_mono`) gives
`γ² ≥ (4μ² - B(ρ)²)/(16(1 - ρ)²)` with `B(ρ) = 1 - ρ + log ρ + 2ψ_μ(ζ)`; the cleared comparison
`φ(ρ) = 4μ² - B(ρ)² - 16·cap·(1 - ρ)²` is increasing (`nh_phi_mono`; Route: its derivative
`2(1 - ρ)(16 cap - B/ρ)` replaces the derivative of the quotient) and positive at the left end of
the excluded interval. For `a < 4/5` the floor is `μ = 94/125` (`nh_turn_floor`, Route: the
explicit rational relaxation of `f_η(q)` with a discriminant in place of the square root of
`EXPLICIT_TURN_NORM_FLOOR`), and the excluded interval is `ρ ∈ [4/29, 3/20)` (the window's
`a² < 12/17` in place of `ρ < 1/7`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- The squared Casimir of the window in centre form: `γ² = (4uv - E²)/(16(1 - ρ)²)`. -/
theorem nh_window_cas (W : M2Window) :
    m2Cas W.a W.u W.v W.h = (4 * W.u * W.v - (m2E W.a W.b W.c W.u W.v) ^ 2) /
      (16 * (1 - W.a ^ 2 / (W.a ^ 2 + 4)) ^ 2) := by
  have ha := W.a_pos
  have hb : 0 < W.b := by linarith [W.a_lt_b]
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hE := m2E_mul W.u W.v ha hb hc
  set E := m2E W.a W.b W.c W.u W.v
  have hh : W.h = (W.a ^ 2 + 4) / 16 * E := by
    rw [W.h_eq]
    unfold m2h
    rw [show (W.a + W.b) * W.u + (W.a + W.c) * W.v - m2Stat W.b W.a W.c = W.a * E by
      rw [hE]; ring]
    field_simp
  unfold m2Cas
  rw [hh]
  have hK : W.a ^ 2 + 4 ≠ 0 := by positivity
  field_simp
  ring

/-- **Lowering both incident norms to `μ`** lowers `4uv - E²`, when `E ≤ 2μr` and `E ≤ 2μt`. -/
theorem nh_lower_norms {r t u v E E0 μ : ℝ} (hr0 : 0 < r) (ht0 : 0 < t) (hu : μ ≤ u) (hv : μ ≤ v)
    (hEr : E ≤ 2 * μ * r) (hEt : E ≤ 2 * μ * t) (hEE0 : E = E0 + (u - μ) / r + (v - μ) / t) :
    4 * μ ^ 2 - E0 ^ 2 ≤ 4 * u * v - E ^ 2 := by
  have hdu : 0 ≤ u - μ := by linarith
  have hdv : 0 ≤ v - μ := by linarith
  have k1 : (u - μ) / r * (2 * E) ≤ 4 * μ * (u - μ) := by
    have e : (u - μ) / r * (2 * E) = (u - μ) * (2 * E / r) := by ring
    have h2Er : 2 * E / r ≤ 4 * μ := by rw [div_le_iff₀ hr0]; linarith
    rw [e]; have := mul_le_mul_of_nonneg_left h2Er hdu; linarith
  have k2 : (v - μ) / t * (2 * E) ≤ 4 * μ * (v - μ) := by
    have e : (v - μ) / t * (2 * E) = (v - μ) * (2 * E / t) := by ring
    have h2Et : 2 * E / t ≤ 4 * μ := by rw [div_le_iff₀ ht0]; linarith
    rw [e]; have := mul_le_mul_of_nonneg_left h2Et hdv; linarith
  have h3 := mul_nonneg hdu hdv
  have h4 := sq_nonneg ((u - μ) / r + (v - μ) / t)
  have e : 4 * u * v - E ^ 2 - (4 * μ ^ 2 - E0 ^ 2) = 4 * ((u - μ) * (v - μ)) +
      4 * μ * (u - μ) + 4 * μ * (v - μ) - (u - μ) / r * (2 * E) - (v - μ) / t * (2 * E) +
      ((u - μ) / r + (v - μ) / t) ^ 2 := by
    rw [hEE0]; ring
  linarith

/-- `ψ_μ(y) = y - (1 - μ)/y - log y` is nondecreasing on `(0, ζ]` for `ζ ≤ 1/2`,
`μ ≤ U(ζ) = 1 - ζ + ζ²` (derivative `(U(y) - μ)/y²`). -/
theorem nh_psi_mono {y ζ μ : ℝ} (hy : 0 < y) (hyζ : y ≤ ζ) (hζ : ζ ≤ 1 / 2)
    (hμ : μ ≤ 1 - ζ + ζ ^ 2) :
    y - (1 - μ) / y - Real.log y ≤ ζ - (1 - μ) / ζ - Real.log ζ := by
  have hmono : MonotoneOn (fun z => z - (1 - μ) / z - Real.log z) (Set.Icc y ζ) := by
    have hd : ∀ z, 0 < z → HasDerivAt (fun z => z - (1 - μ) / z - Real.log z)
        ((z ^ 2 - z + 1 - μ) / z ^ 2) z := by
      intro z hz
      have := ((hasDerivAt_id' z).sub ((hasDerivAt_inv hz.ne').const_mul (1 - μ))).sub
        (Real.hasDerivAt_log hz.ne')
      refine (this.congr_deriv ?_).congr_of_eventuallyEq ?_
      · field_simp; ring
      · filter_upwards with w; simp [div_eq_mul_inv]
    apply monotoneOn_of_deriv_nonneg (convex_Icc y ζ)
    · exact fun z hz => (hd z (lt_of_lt_of_le hy hz.1)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hd z (lt_trans hy hz.1)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := lt_trans hy hz.1
      rw [(hd z hz0).deriv]
      apply div_nonneg _ (by positivity)
      nlinarith [hz.2]
  exact hmono (Set.left_mem_Icc.2 hyζ) (Set.right_mem_Icc.2 hyζ) hyζ

/-- `y - 1/(4y) - log y` is nondecreasing on `(0, ∞)`. -/
theorem nh_phi34_mono {y y' : ℝ} (hy : 0 < y) (hyy : y ≤ y') :
    y - 1 / 4 * y⁻¹ - Real.log y ≤ y' - 1 / 4 * y'⁻¹ - Real.log y' := by
  have hd : ∀ z, 0 < z → HasDerivAt (fun z => z - 1 / 4 * z⁻¹ - Real.log z)
      ((2 * z - 1) ^ 2 / (4 * z ^ 2)) z := by
    intro z hz
    have := ((hasDerivAt_id' z).sub ((hasDerivAt_inv hz.ne').const_mul (1 / 4 : ℝ))).sub
      (Real.hasDerivAt_log hz.ne')
    refine this.congr_deriv ?_
    field_simp; ring
  have hmono : MonotoneOn (fun z => z - 1 / 4 * z⁻¹ - Real.log z) (Set.Icc y y') := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y y')
    · exact fun z hz => (hd z (lt_of_lt_of_le hy hz.1)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hd z (lt_trans hy hz.1)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hd z (lt_trans hy hz.1)).deriv]
      positivity
  exact hmono (Set.left_mem_Icc.2 hyy) (Set.right_mem_Icc.2 hyy) hyy

/-- The lower diagonal bound (`MIXED_REVERSE_CENTRE_SCALE_BOUND` (7)): at the norm floor `3/4`,
`E₀ ≥ 1 + ρ - 1/(8ρ)` for `ρ < rt`, `r, t < 1/2`. -/
theorem nh_E0_lower {r t ρ : ℝ} (hr0 : 0 < r) (ht0 : 0 < t) (hr2 : r < 1 / 2) (ht2 : t < 1 / 2)
    (hρ0 : 0 < ρ) (hρrt : ρ < r * t) (hρ1 : ρ < 1 / 4) :
    1 + ρ - 1 / (8 * ρ) ≤ 1 + r + t - ρ + Real.log (ρ / (r * t)) - 1 / 4 * r⁻¹ - 1 / 4 * t⁻¹ := by
  have hsplit : 1 + r + t - ρ + Real.log (ρ / (r * t)) - 1 / 4 * r⁻¹ - 1 / 4 * t⁻¹ =
      1 - ρ + Real.log ρ + (r - 1 / 4 * r⁻¹ - Real.log r) + (t - 1 / 4 * t⁻¹ - Real.log t) := by
    rw [Real.log_div hρ0.ne' (by positivity), Real.log_mul hr0.ne' ht0.ne']; ring
  rw [hsplit]
  have htr : ρ / r ≤ t := by rw [div_le_iff₀ hr0]; linarith
  have h1 := nh_phi34_mono (show 0 < ρ / r by positivity) htr
  rw [Real.log_div hρ0.ne' hr0.ne'] at h1
  have hr2ρ : 2 * ρ ≤ r := by
    have := mul_lt_mul_of_pos_left ht2 hr0; linarith
  have h4 : 1 - 1 / (4 * ρ) < 0 := by
    rw [sub_neg, lt_div_iff₀ (by positivity)]; linarith
  have hprod : (r - 2 * ρ) * (r - 1 / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have key : 0 ≤ (1 - 1 / (4 * ρ)) * ((r - 2 * ρ) * (r - 1 / 2)) :=
    mul_nonneg_of_nonpos_of_nonpos h4.le hprod
  have e : (1 - 1 / (4 * ρ)) * ((r - 2 * ρ) * (r - 1 / 2)) =
      r * ((r - 1 / 4 * r⁻¹ + (ρ / r - 1 / 4 * (ρ / r)⁻¹)) - 2 * ρ + 1 / (8 * ρ)) := by
    field_simp; ring
  rw [e] at key
  have hk := (mul_nonneg_iff_of_pos_left hr0).1 key
  linarith

/-- `B(ρ) = κ - ρ + log(λρ)` is nondecreasing on `(0, 1]`. -/
theorem nh_B_mono {κ lam ρ ρ' : ℝ} (hl : 0 < lam) (hρ : 0 < ρ) (hρρ : ρ ≤ ρ') (hρ1 : ρ' ≤ 1) :
    κ - ρ + Real.log (lam * ρ) ≤ κ - ρ' + Real.log (lam * ρ') := by
  have hρ' : 0 < ρ' := lt_of_lt_of_le hρ hρρ
  have h := Real.one_sub_inv_le_log_of_pos (show 0 < lam * ρ' / (lam * ρ) by positivity)
  rw [Real.log_div (by positivity) (by positivity)] at h
  have e : (lam * ρ' / (lam * ρ))⁻¹ = ρ / ρ' := by field_simp
  rw [e] at h
  have : (ρ' - ρ) * (1 / ρ' - 1) ≥ 0 := mul_nonneg (by linarith) (by
    rw [sub_nonneg, le_div_iff₀ hρ']; linarith)
  have e2 : (ρ' - ρ) * (1 / ρ' - 1) = (1 - ρ / ρ') - (ρ' - ρ) := by field_simp
  linarith

/-- **The cleared comparison is increasing**: `φ(ρ) = C - B(ρ)² - D(1 - ρ)²`,
`B(ρ) = κ - ρ + log(λρ)`, has derivative `2(1 - ρ)(D - B/ρ) > 0` on `[ρ₀, ρ₁]` when
`B ≤ B_max` there and `B_max < Dρ₀`. -/
theorem nh_phi_mono {C D κ lam ρ0 ρ1 Bmax ρ : ℝ} (hl : 0 < lam) (hD : 0 ≤ D) (hρ0 : 0 < ρ0)
    (hρ01 : ρ0 ≤ ρ)
    (hρ1 : ρ ≤ ρ1) (hρ11 : ρ1 < 1) (hB : κ - ρ1 + Real.log (lam * ρ1) ≤ Bmax)
    (hBD : Bmax < D * ρ0) :
    C - (κ - ρ0 + Real.log (lam * ρ0)) ^ 2 - D * (1 - ρ0) ^ 2 ≤
      C - (κ - ρ + Real.log (lam * ρ)) ^ 2 - D * (1 - ρ) ^ 2 := by
  have hd : ∀ z, 0 < z → HasDerivAt (fun z => C - (κ - z + Real.log (lam * z)) ^ 2 - D * (1 - z) ^ 2)
      (2 * (1 - z) * (D - (κ - z + Real.log (lam * z)) / z)) z := by
    intro z hz
    have h1 : HasDerivAt (fun z => κ - z + Real.log (lam * z)) (-1 + 1 / z) z := by
      have hlz : HasDerivAt (fun z => lam * z) lam z := by
        simpa using (hasDerivAt_id z).const_mul lam
      have := ((hasDerivAt_const z κ).sub (hasDerivAt_id' z)).add (hlz.log (by positivity))
      refine this.congr_deriv ?_
      field_simp; ring
    have h2 : HasDerivAt (fun z : ℝ => 1 - z) (0 - 1) z :=
      (hasDerivAt_const z (1 : ℝ)).sub (hasDerivAt_id' z)
    have := ((hasDerivAt_const z C).sub (h1.pow 2)).sub ((h2.pow 2).const_mul D)
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    field_simp
    ring
  have hmono : MonotoneOn (fun z => C - (κ - z + Real.log (lam * z)) ^ 2 - D * (1 - z) ^ 2)
      (Set.Icc ρ0 ρ1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc ρ0 ρ1)
    · exact fun z hz => (hd z (lt_of_lt_of_le hρ0 hz.1)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hd z (lt_trans hρ0 hz.1)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      have hz0 : 0 < z := lt_trans hρ0 hz.1
      rw [(hd z hz0).deriv]
      apply mul_nonneg (by nlinarith [hz.2])
      have hBz := nh_B_mono (κ := κ) hl hz0 hz.2.le hρ11.le
      rw [sub_nonneg, div_le_iff₀ hz0]
      nlinarith [mul_le_mul_of_nonneg_left hz.1.le hD]
  exact hmono (Set.left_mem_Icc.2 (hρ01.trans hρ1)) ⟨hρ01, hρ1⟩ hρ01

private theorem nh_turn_disc_bp0 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 16320 * a * b ^ 3 + 91200 * a ^ 2 * b ^ 2 + 143040 * a ^ 3 * b + 53760 * a ^ 4 := by positivity

private theorem nh_turn_disc_l0 (η : ℝ) (h0 : (3 / 5) ≤ η) (h1 : η ≤ 1) :
    0 < -((6 + 6 * η ^ 2 - 10 * η - 6 * (94 / 125)) ^ 2 - 4 * (6 - η - 6 * (94 / 125)) * (6 * η ^ 2 - η)) := by
  linear_combination (1 / 250000 : ℝ) * nh_turn_disc_bp0 (5 * η - 3) (5 - 5 * η) (by linarith) (by linarith)

/-- The discriminant of the cleared turn-floor quadratic is negative for `3/5 ≤ η ≤ 1`
(generated Bernstein certificate). -/
theorem nh_turn_disc (η : ℝ) (h0 : (3 / 5) ≤ η) (h1 : η ≤ 1) :
    0 < -((6 + 6 * η ^ 2 - 10 * η - 6 * (94 / 125)) ^ 2 - 4 * (6 - η - 6 * (94 / 125)) * (6 * η ^ 2 - η)) := by
  exact nh_turn_disc_l0 η h0 h1

/-- **The turn floor** (Route for `EXPLICIT_TURN_NORM_FLOOR` (3)): for a turn with
`η = B/(A + B) ≥ 3/5` and `A < P`, `Sec(A, B, P) > 94/125`. -/
theorem nh_turn_floor {A B P : ℝ} (hA : 0 < A) (hB : 0 < B) (hAP : A < P) (hη : 3 / 5 ≤ B / (A + B)) :
    94 / 125 < m2Sec A B P := by
  have hAB : 0 < A + B := by linarith
  set η := B / (A + B) with hηdef
  set q := (P + B) / (A + B) with hqdef
  have hq : 1 < q := by rw [hqdef, lt_div_iff₀ hAB]; linarith
  have hη1 : η ≤ 1 := by rw [hηdef, div_le_one hAB]; linarith
  have hsec : m2Sec A B P = 1 + η ^ 2 / q - η * Real.log q / (q - 1) := by
    rw [m2Sec_of_ne hAP.ne]
    have hPA : P - A ≠ 0 := by linarith
    have hq1 : q - 1 = (P - A) / (A + B) := by rw [hqdef]; field_simp; ring
    rw [hq1, hηdef, hqdef]
    field_simp
  rw [hsec]
  have hL := nh_log_lt_Lp hq
  unfold nhLp at hL
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have h1 : η * Real.log q / (q - 1) < η * ((q ^ 2 + 10 * q + 1) / (6 * q * (q + 1))) := by
    rw [div_lt_iff₀ hq1]
    have : η * Real.log q < η * ((q - 1) * (q ^ 2 + 10 * q + 1) / (6 * q * (q + 1))) :=
      mul_lt_mul_of_pos_left hL (by positivity)
    have e : η * ((q - 1) * (q ^ 2 + 10 * q + 1) / (6 * q * (q + 1))) =
        η * ((q ^ 2 + 10 * q + 1) / (6 * q * (q + 1))) * (q - 1) := by ring
    linarith
  have hd := nh_turn_disc η hη hη1
  -- the cleared quadratic is positive
  have hquad : 0 < (6 - η - 6 * (94 / 125)) * q ^ 2 + (6 + 6 * η ^ 2 - 10 * η - 6 * (94 / 125)) * q
      + (6 * η ^ 2 - η) := by
    have hlead : 0 < 6 - η - 6 * (94 / 125) := by linarith
    nlinarith [sq_nonneg (2 * (6 - η - 6 * (94 / 125)) * q + (6 + 6 * η ^ 2 - 10 * η - 6 * (94 / 125)))]
  have key : 94 / 125 < 1 + η ^ 2 / q - η * ((q ^ 2 + 10 * q + 1) / (6 * q * (q + 1))) := by
    have e : 1 + η ^ 2 / q - η * ((q ^ 2 + 10 * q + 1) / (6 * q * (q + 1))) - 94 / 125 =
        ((6 - η - 6 * (94 / 125)) * q ^ 2 + (6 + 6 * η ^ 2 - 10 * η - 6 * (94 / 125)) * q
          + (6 * η ^ 2 - η)) / (6 * q * (q + 1)) := by
      field_simp; ring
    have : 0 < ((6 - η - 6 * (94 / 125)) * q ^ 2 + (6 + 6 * η ^ 2 - 10 * η - 6 * (94 / 125)) * q
          + (6 * η ^ 2 - η)) / (6 * q * (q + 1)) := div_pos hquad (by positivity)
    linarith
  linarith

/-- The centre data of the window: ratios, norm bounds, the diagonal `E` and its bound
`E < -1 + 2r + 2t - rt`. -/
theorem nh_window_centre (W : M2Window) :
    let r := W.a / (W.a + W.b)
    let t := W.a / (W.a + W.c)
    let ρ := W.a ^ 2 / (W.a ^ 2 + 4)
    0 < r ∧ 0 < t ∧ r ≤ t ∧ t < 1 / 2 ∧ 0 < ρ ∧ ρ < r * t ∧ ρ < 3 / 20 ∧
      W.u ≤ 1 - r + r ^ 2 ∧ W.v ≤ 1 - t + t ^ 2 ∧
      m2E W.a W.b W.c W.u W.v = 1 + r + t - ρ + Real.log (ρ / (r * t)) - (1 - W.u) / r -
        (1 - W.v) / t ∧
      m2E W.a W.b W.c W.u W.v < -1 + 2 * r + 2 * t - r * t := by
  intro r t ρ
  have ha := W.a_pos
  have hb : 0 < W.b := by linarith [W.a_lt_b]
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hK0 : 0 < W.a ^ 2 + 4 := by positivity
  have hr0 : 0 < r := by positivity
  have ht0 : 0 < t := by positivity
  have hrt : r ≤ t := div_le_div_of_nonneg_left ha.le (by positivity) (by linarith [W.c_le_b])
  have ht2 : t < 1 / 2 := by
    show W.a / (W.a + W.c) < 1 / 2
    rw [div_lt_iff₀ (by positivity)]; linarith [W.a_lt_c]
  have hr2 : r < 1 / 2 := lt_of_le_of_lt hrt ht2
  have hρ0 : 0 < ρ := by positivity
  have hρrt : ρ < r * t := by
    show W.a ^ 2 / (W.a ^ 2 + 4) < W.a / (W.a + W.b) * (W.a / (W.a + W.c))
    rw [div_mul_div_comm, div_lt_div_iff₀ hK0 (by positivity)]
    have : 0 < W.a ^ 2 := by positivity
    nlinarith [W.central]
  have hρ3 : ρ < 3 / 20 := by
    show W.a ^ 2 / (W.a ^ 2 + 4) < 3 / 20
    rw [div_lt_iff₀ hK0]; linarith [W.scale]
  have hUr : W.u ≤ 1 - r + r ^ 2 := by
    have h := W.u_le; rw [m2g_eq_m2U (by positivity)] at h; exact h
  have hUt : W.v ≤ 1 - t + t ^ 2 := by
    have h := W.v_le; rw [m2g_eq_m2U (by positivity)] at h; exact h
  have hE : m2E W.a W.b W.c W.u W.v = 1 + r + t - ρ + Real.log (ρ / (r * t)) - (1 - W.u) / r -
      (1 - W.v) / t := rfl
  refine ⟨hr0, ht0, hrt, ht2, hρ0, hρrt, hρ3, hUr, hUt, hE, ?_⟩
  rw [hE]
  have hℓ1 : -ρ + Real.log (ρ / (r * t)) < -(r * t) := by
    have hx : 0 < ρ / (r * t) := by positivity
    have hl := Real.log_le_sub_one_of_pos hx
    have hx1 : ρ / (r * t) < 1 := (div_lt_one (by positivity)).2 hρrt
    have hrt1 : r * t < 1 := by have := mul_lt_mul'' hr2 ht2 hr0.le ht0.le; linarith
    have e : ρ = ρ / (r * t) * (r * t) := by field_simp
    have : (1 - ρ / (r * t)) * (1 - r * t) > 0 := mul_pos (by linarith) (by linarith)
    nlinarith
  have hur : 1 - r ≤ (1 - W.u) / r := by
    rw [le_div_iff₀ hr0]; nlinarith
  have hvt : 1 - t ≤ (1 - W.v) / t := by
    rw [le_div_iff₀ ht0]; nlinarith
  linarith

/-- `log(5/3) > 1/2`. -/
theorem nh_log_five_thirds : (1 / 2 : ℝ) < Real.log (5 / 3) := by
  have := nh_log_one_add_gt (x := 2 / 3) (by norm_num)
  norm_num at this ⊢
  linarith

/-- **The sharpened central scale** `a² < 2/3` (`HAND_PROOF_REFINEMENTS` §2). -/
theorem nh_a_sq (W : M2Window) : W.a ^ 2 < 2 / 3 := by
  obtain ⟨hr0, ht0, hrt, ht2, hρ0, hρrt, hρ3, hUr, hUt, hE, hEb⟩ := nh_window_centre W
  set r := W.a / (W.a + W.b) with hr
  set t := W.a / (W.a + W.c) with ht
  set ρ := W.a ^ 2 / (W.a ^ 2 + 4) with hρ
  have ha := W.a_pos
  have hb : 0 < W.b := by linarith [W.a_lt_b]
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hK0 : 0 < W.a ^ 2 + 4 := by positivity
  have hu34 : 3 / 4 ≤ W.u := W.u_eq ▸ m2Sec_ge ha hb (by linarith [W.a_lt_p])
  have hv34 : 3 / 4 ≤ W.v := W.v_eq ▸ m2Sec_ge ha hc (by linarith [W.a_lt_d])
  have hcas := W.cas_lt
  rw [nh_window_cas] at hcas
  set E := m2E W.a W.b W.c W.u W.v with hEdef
  by_contra hcon
  push Not at hcon
  have hρ7 : 1 / 7 ≤ ρ := by
    rw [hρ, le_div_iff₀ hK0]; linarith
  have hr2 : r < 1 / 2 := lt_of_le_of_lt hrt ht2
  -- lower the norms to `3/4`
  set E0 := 1 + r + t - ρ + Real.log (ρ / (r * t)) - 1 / 4 * r⁻¹ - 1 / 4 * t⁻¹ with hE0
  have hEE0 : E = E0 + (W.u - 3 / 4) / r + (W.v - 3 / 4) / t := by
    rw [hE, hE0]; field_simp; ring
  have hEr : E ≤ 2 * (3 / 4) * r := by
    have : (2 - r) * (t - 1 / 2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    nlinarith
  have hEt : E ≤ 2 * (3 / 4) * t := by
    have : (2 - t) * (r - 1 / 2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    nlinarith
  have hlow := nh_lower_norms hr0 ht0 hu34 hv34 hEr hEt hEE0
  have hρ14 : ρ < 1 / 4 := by linarith
  have hE0pos : 0 < E0 := by
    have := nh_E0_lower hr0 ht0 hr2 ht2 hρ0 hρrt hρ14
    have h8 : 1 / (8 * ρ) ≤ 7 / 8 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  -- raise the ratios to `1/2`
  have hE0B : E0 ≤ 1 - ρ + Real.log (4 * ρ) := by
    have h1 := nh_phi34_mono hr0 hr2.le
    have h2 := nh_phi34_mono ht0 ht2.le
    have hφ : (1 / 2 : ℝ) - 1 / 4 * (1 / 2)⁻¹ - Real.log (1 / 2) = Real.log 2 := by
      rw [one_div, Real.log_inv]; norm_num
    rw [hφ] at h1 h2
    have e1 : E0 = 1 - ρ + Real.log ρ + (r - 1 / 4 * r⁻¹ - Real.log r) +
        (t - 1 / 4 * t⁻¹ - Real.log t) := by
      rw [hE0, Real.log_div hρ0.ne' (by positivity), Real.log_mul hr0.ne' ht0.ne']; ring
    have e2 : Real.log (4 * ρ) = 2 * Real.log 2 + Real.log ρ := by
      rw [Real.log_mul (by norm_num) hρ0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [e1, e2]; linarith
  -- the comparison function is increasing on `[1/7, 3/20]` and positive at `1/7`
  have hl35 : Real.log (4 * (3 / 20)) ≤ -(1 / 2) := by
    have := nh_log_five_thirds
    rw [show (4 : ℝ) * (3 / 20) = (5 / 3)⁻¹ by norm_num, Real.log_inv]; linarith
  have hphi := nh_phi_mono (C := 9 / 4) (D := 16 * (9193 / 50000)) (κ := 1) (lam := 4)
    (ρ0 := 1 / 7) (ρ1 := 3 / 20) (Bmax := 7 / 20) (ρ := ρ) (by norm_num) (by norm_num)
    (by norm_num) hρ7 hρ3.le (by norm_num) (by linarith) (by norm_num)
  have hl74 : (450606 / 805255 : ℝ) < Real.log (7 / 4) := by
    have := nh_log_one_add_gt3 (x := 3 / 4) (by norm_num)
    norm_num at this ⊢; linarith
  have hl74' : Real.log (7 / 4) ≤ 3 / 4 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 / 4 by norm_num); linarith
  have hB7 : 1 - 1 / 7 + Real.log (4 * (1 / 7)) = 6 / 7 - Real.log (7 / 4) := by
    rw [show (4 : ℝ) * (1 / 7) = (7 / 4)⁻¹ by norm_num, Real.log_inv]; ring
  rw [hB7] at hphi
  have hB7sq : (6 / 7 - Real.log (7 / 4)) ^ 2 ≤ (6 / 7 - 450606 / 805255) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have hphi0 : 0 < 9 / 4 - (6 / 7 - Real.log (7 / 4)) ^ 2 - 16 * (9193 / 50000) * (1 - 1 / 7) ^ 2 := by
    have : (0 : ℝ) < 9 / 4 - (6 / 7 - 450606 / 805255) ^ 2 - 16 * (9193 / 50000) * (1 - 1 / 7) ^ 2 := by
      norm_num
    linarith
  -- conclude `γ² > cap`
  have hE0sq : E0 ^ 2 ≤ (1 - ρ + Real.log (4 * ρ)) ^ 2 := pow_le_pow_left₀ hE0pos.le hE0B 2
  have h1ρ : 0 < 1 - ρ := by linarith
  have hge : 16 * (9193 / 50000) * (1 - ρ) ^ 2 < 4 * W.u * W.v - E ^ 2 := by
    linarith
  have hρK : 1 - W.a ^ 2 / (W.a ^ 2 + 4) = 1 - ρ := rfl
  rw [hρK] at hcas
  have : 9193 / 50000 < (4 * W.u * W.v - E ^ 2) / (16 * (1 - ρ) ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  linarith

/-- **The conditional scale bound** (`MIXED_NONSHORT_CONDITIONAL_SCALE_BOUND`): if
`t = a/(a + c) ≤ 2/5`, then `a < 4/5`. -/
theorem nh_scale_of_t (W : M2Window) (ht25 : W.a / (W.a + W.c) ≤ 2 / 5) : W.a < 4 / 5 := by
  obtain ⟨hr0, ht0, hrt, ht2, hρ0, hρrt, hρ3, hUr, hUt, hE, hEb⟩ := nh_window_centre W
  set r := W.a / (W.a + W.b) with hr
  set t := W.a / (W.a + W.c) with ht
  set ρ := W.a ^ 2 / (W.a ^ 2 + 4) with hρ
  have ha := W.a_pos
  have hb : 0 < W.b := by linarith [W.a_lt_b]
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hK0 : 0 < W.a ^ 2 + 4 := by positivity
  -- the turn floors
  have h1r : W.b / (W.a + W.b) = 1 - r := by rw [hr]; field_simp; ring
  have h1t : W.c / (W.a + W.c) = 1 - t := by rw [ht]; field_simp; ring
  have hu : (94 / 125 : ℝ) ≤ W.u := by
    rw [W.u_eq]
    exact (nh_turn_floor ha hb W.a_lt_p (by rw [h1r]; linarith)).le
  have hv : (94 / 125 : ℝ) ≤ W.v := by
    rw [W.v_eq]
    exact (nh_turn_floor ha hc W.a_lt_d (by rw [h1t]; linarith)).le
  have hcas := W.cas_lt
  rw [nh_window_cas] at hcas
  set E := m2E W.a W.b W.c W.u W.v with hEdef
  by_contra hcon
  push Not at hcon
  have hρ4 : 4 / 29 ≤ ρ := by
    rw [hρ, le_div_iff₀ hK0]; nlinarith
  have hr2 : r ≤ 2 / 5 := hrt.trans ht25
  -- lower the norms to `(94 / 125 : ℝ)`
  set E0 := 1 + r + t - ρ + Real.log (ρ / (r * t)) - (1 - (94 / 125 : ℝ)) / r - (1 - (94 / 125 : ℝ)) / t with hE0
  have hEE0 : E = E0 + (W.u - (94 / 125 : ℝ)) / r + (W.v - (94 / 125 : ℝ)) / t := by
    rw [hE, hE0]; field_simp; ring
  have hEr : E ≤ 2 * (94 / 125 : ℝ) * r := by
    have : 0 ≤ (2 / 5 - r) * (62 / 125 - t) := mul_nonneg (by linarith) (by linarith)
    have e : -1 + 2 * r + 2 * t - r * t - 2 * (94 / 125 : ℝ) * r =
        (-1 + 2 * t + 2 / 5 * (62 / 125 - t)) - (2 / 5 - r) * (62 / 125 - t) := by ring
    linarith
  have hEt : E ≤ 2 * (94 / 125 : ℝ) * t := by
    have : 0 ≤ (2 / 5 - t) * (62 / 125 - r) := mul_nonneg (by linarith) (by linarith)
    have e : -1 + 2 * r + 2 * t - r * t - 2 * (94 / 125 : ℝ) * t =
        (-1 + 2 * r + 2 / 5 * (62 / 125 - r)) - (2 / 5 - t) * (62 / 125 - r) := by ring
    linarith
  have hlow := nh_lower_norms hr0 ht0 hu hv hEr hEt hEE0
  have hE0pos : 0 < E0 := by
    have hρ14 : ρ < 1 / 4 := by linarith
    have := nh_E0_lower hr0 ht0 (by linarith) (by linarith) hρ0 hρrt hρ14
    have h8 : 1 / (8 * ρ) ≤ 29 / 32 := by rw [div_le_iff₀ (by positivity)]; linarith
    have e : E0 = (1 + r + t - ρ + Real.log (ρ / (r * t)) - 1 / 4 * r⁻¹ - 1 / 4 * t⁻¹) +
        ((94 / 125 : ℝ) - 3 / 4) * (1 / r + 1 / t) := by rw [hE0]; field_simp; ring
    have : 0 ≤ ((94 / 125 : ℝ) - 3 / 4) * (1 / r + 1 / t) := mul_nonneg (by norm_num) (by positivity)
    linarith
  -- raise the ratios to `2/5`
  have hE0B : E0 ≤ 14 / 25 - ρ + Real.log (25 / 4 * ρ) := by
    have h1 := nh_psi_mono (μ := 94 / 125) hr0 hr2 (by norm_num) (by norm_num)
    have h2 := nh_psi_mono (μ := 94 / 125) ht0 ht25 (by norm_num) (by norm_num)
    have e1 : E0 = 1 - ρ + Real.log ρ + (r - (1 - (94 / 125 : ℝ)) / r - Real.log r) +
        (t - (1 - (94 / 125 : ℝ)) / t - Real.log t) := by
      rw [hE0, Real.log_div hρ0.ne' (by positivity), Real.log_mul hr0.ne' ht0.ne']; ring
    have e2 : Real.log (25 / 4 * ρ) = 2 * Real.log (5 / 2) + Real.log ρ := by
      rw [Real.log_mul (by norm_num) hρ0.ne', show (25 / 4 : ℝ) = (5 / 2) ^ 2 by norm_num,
        Real.log_pow]
      push_cast; ring
    have e3 : (2 / 5 : ℝ) - (1 - (94 / 125 : ℝ)) / (2 / 5) - Real.log (2 / 5) = -(11 / 50) + Real.log (5 / 2) := by
      rw [show (2 / 5 : ℝ) = (5 / 2)⁻¹ by norm_num, Real.log_inv]; norm_num
    rw [e3] at h1 h2
    rw [e1, e2]; linarith
  -- the comparison function
  have hl1615 : (2 / 31 : ℝ) < Real.log (16 / 15) := by
    have := nh_log_one_add_gt (x := 1 / 15) (by norm_num)
    norm_num at this ⊢; linarith
  have hphi := nh_phi_mono (C := 4 * (94 / 125 : ℝ) ^ 2) (D := 16 * (9193 / 50000)) (κ := 14 / 25)
    (lam := 25 / 4) (ρ0 := 4 / 29) (ρ1 := 3 / 20) (Bmax := 41 / 100 - 2 / 31) (ρ := ρ)
    (by norm_num) (by norm_num) (by norm_num) hρ4 hρ3.le (by norm_num) (by
      rw [show (25 / 4 : ℝ) * (3 / 20) = (16 / 15)⁻¹ by norm_num, Real.log_inv]; linarith)
    (by norm_num)
  have hl2925 : (4 / 27 : ℝ) < Real.log (29 / 25) := by
    have := nh_log_one_add_gt (x := 4 / 25) (by norm_num)
    norm_num at this ⊢; linarith
  have hl2925' : Real.log (29 / 25) ≤ 4 / 25 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 29 / 25 by norm_num); linarith
  have hB4 : 14 / 25 - 4 / 29 + Real.log (25 / 4 * (4 / 29)) = 306 / 725 - Real.log (29 / 25) := by
    rw [show (25 / 4 : ℝ) * (4 / 29) = (29 / 25)⁻¹ by norm_num, Real.log_inv]; ring
  rw [hB4] at hphi
  have hB4sq : (306 / 725 - Real.log (29 / 25)) ^ 2 ≤ (306 / 725 - 4 / 27) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have hphi0 : 0 < 4 * (94 / 125 : ℝ) ^ 2 - (306 / 725 - Real.log (29 / 25)) ^ 2 -
      16 * (9193 / 50000) * (1 - 4 / 29) ^ 2 := by
    have : (0 : ℝ) < 4 * (94 / 125 : ℝ) ^ 2 - (306 / 725 - 4 / 27) ^ 2 - 16 * (9193 / 50000) * (1 - 4 / 29) ^ 2 := by
      norm_num
    linarith
  have hE0sq : E0 ^ 2 ≤ (14 / 25 - ρ + Real.log (25 / 4 * ρ)) ^ 2 := pow_le_pow_left₀ hE0pos.le hE0B 2
  have h1ρ : 0 < 1 - ρ := by linarith
  have hge : 16 * (9193 / 50000) * (1 - ρ) ^ 2 < 4 * W.u * W.v - E ^ 2 := by
    linarith
  have hρK : 1 - W.a ^ 2 / (W.a ^ 2 + 4) = 1 - ρ := rfl
  rw [hρK] at hcas
  have : 9193 / 50000 < (4 * W.u * W.v - E ^ 2) / (16 * (1 - ρ) ^ 2) := by
    rw [lt_div_iff₀ (by positivity)]; linarith
  linarith

end SmoothedOctagon
