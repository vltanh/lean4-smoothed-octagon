module

public import SmoothedOctagon.Exclusion.Mixed.Frames
public import SmoothedOctagon.Exclusion.Mixed.Window
public import SmoothedOctagon.Exclusion.MinimumStructure

/-!
# Case M2: reverse centres and their scale bound

At a centre `k` of a reverse run (switches `k - 2` forward, `k - 1`, `k` reverse, `k + 1`
forward) of a mixed normal vertex period, the covector calculus gives the scalar data of an
`M2Centre`: the turn secants of the neighbouring turns, the reverse switching inequalities, centre
stationarity and the Gram determinant, with `Γ` the squared Casimir of the period. If
`Γ < 23/125`, then `ρ = a²/(a² + 4) < 3/20`, i.e. `a² < 12/17`: lowering both incident norms to
`3/4`, then raising both neighbour ratios to `1/2` gives
`γ² > G(ρ) = (9/4 - B(ρ)²)/(16(1 - ρ)²)`, `B(ρ) = 1 - ρ + log(4ρ)`, and a rational lower bound
of `G` exceeds `23/125` on `[3/20, 1/4)`.

## Main API

* `m2E_mul`: `a E = (p + a) u_i + (a + n) u_o - C_a` (centre stationarity in pairing form).
* `m2_centre`: the `M2Centre` of a reverse centre.
* `m2_scale`: `Γ < 23/125 → a² < 12/17`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- Centre stationarity in pairing form: `a · m2E a p n ui uo = (p + a) ui + (a + n) uo - C_a`. -/
theorem m2E_mul {a p n : ℝ} (ui uo : ℝ) (ha : 0 < a) (hp : 0 < p) (hn : 0 < n) :
    a * m2E a p n ui uo = (p + a) * ui + (a + n) * uo - m2Stat p a n := by
  have hK : 0 < a ^ 2 + 4 := by positivity
  have hX : a ^ 2 / (a ^ 2 + 4) / (a / (a + p) * (a / (a + n))) = (p + a) * (a + n) / (a ^ 2 + 4) := by
    field_simp; ring
  unfold m2E m2Stat
  rw [hX]
  have h1 : a + p ≠ 0 := by positivity
  have h2 : a + n ≠ 0 := by positivity
  have h3 : p + a ≠ 0 := by positivity
  field_simp
  ring

/-- **The data of a reverse centre**, from the factor formulas, centre stationarity, the turn
secants, the reverse switching inequalities and the reverse run `k - 1, k` of the period. -/
theorem m2_centre (P : NormalPeriod) (K : P.M2Calculus) (hmix : P.rep.IsMixed) {k : ℤ}
    (h2 : P.costateCycle.m2Fwd (k - 2)) (h1 : ¬ P.costateCycle.m2Fwd (k - 1))
    (h0 : ¬ P.costateCycle.m2Fwd k) (h3 : P.costateCycle.m2Fwd (k + 1)) :
    ∃ D : M2Centre, D.pp = P.costateCycle.act (k - 2) ∧ D.p = P.costateCycle.act (k - 1) ∧
      D.a = P.costateCycle.act k ∧ D.n = P.costateCycle.act (k + 1) ∧
      D.nn = P.costateCycle.act (k + 2) ∧ D.Γ = K.Γ := by
  set C := P.costateCycle with hC
  have hact : ∀ j, P.activeMargin j = C.act j := fun j => (P.costateCycle_m_lab j).symm
  have hrev : ∀ j, ¬ C.m2Fwd j → P.rep.IsReverse j := fun j hj =>
    (P.rep.m2_fwd_or_rev j).resolve_left hj
  have hrun : P.rep.IsReverseRun (k - 1) 2 := by
    refine ⟨by norm_num, ?_, ?_, fun j hj1 hj2 => hrev j ?_⟩
    · rw [show k - 1 - 1 = k - 2 by ring]; exact h2
    · rw [show k - 1 + ((2 : ℕ) : ℤ) = k + 1 by push_cast; ring]; exact h3
    · have : j = k - 1 ∨ j = k := by push_cast at hj2; omega
      rcases this with rfl | rfl
      · exact h1
      · exact h0
  obtain ⟨-, hpp, hp, hn, hnn⟩ := reverseRun_two_and_centre_min P hmix hrun
  simp only [hact, show k - 1 + 1 = k by ring, show k - 1 - 1 = k - 2 by ring,
    show k - 1 + 2 = k + 1 by ring, show k - 1 + 3 = k + 2 by ring] at hpp hp hn hnn
  have ha := C.act_pos k
  have hp0 := C.act_pos (k - 1)
  have hn0 := C.act_pos (k + 1)
  have hq := C.m2_factor_rr h1 h0
  have hq1 := C.one_lt_q k
  have hq0 := C.q_pos k
  have hK : 0 < C.act k ^ 2 + 4 := by positivity
  -- the two incident norms, in the centre frame
  have hui : C.m2Norm K.M (k - 1) = 8 * K.M k 1 0 / (C.act (k - 1) + C.act k) ^ 2 := by
    have := C.m2_norm_next K.transport (k - 1)
    simp only [h1, ↓reduceIte, sub_add_cancel] at this
    exact this
  have huo : C.m2Norm K.M k = -8 * K.M k 0 1 / (C.q k ^ 2 * (C.act k + C.act (k + 1)) ^ 2) := by
    unfold CostateCycle.m2Norm; simp only [h0, ↓reduceIte]
  -- stationarity, secants, switching inequalities
  have hst := K.stat k (iff_of_false h1 h0)
  have hs1 := (K.secant (k - 1)
    (by rw [show k - 1 - 1 = k - 2 by ring]; exact fun h => h1 (h.1 h2))).2
  rw [show k - 1 - 1 = k - 2 by ring, sub_add_cancel] at hs1
  have hs2 := (K.secant (k + 1) (by rw [add_sub_cancel_right]; exact fun h => h0 (h.2 h3))).1
  rw [add_sub_cancel_right, show k + 1 + 1 = k + 2 by ring] at hs2
  have hr1 := K.rev_le (k - 1) h1
  rw [sub_add_cancel, m2g_comm] at hr1
  have hr0 := K.rev_le k h0
  have htr := K.trace_eq k
  have hdet := K.det_eq k
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet
  refine ⟨⟨C.act (k - 2), C.act (k - 1), C.act k, C.act (k + 1), C.act (k + 2),
    C.m2Norm K.M (k - 1), C.m2Norm K.M k, 16 * K.M k 0 0 / (C.act k ^ 2 + 4), K.Γ, ha, hp, hn,
    C.act_pos _, C.act_pos _, ?_, ?_, hs2, hr1, hr0, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · -- the reverse factor
    have : 0 < (C.act (k - 1) + C.act k) * (C.act k + C.act (k + 1)) := by positivity
    nlinarith
  · rw [hs1, m2Sec_comm]
  · -- centre stationarity
    have hm := m2E_mul (C.m2Norm K.M (k - 1)) (C.m2Norm K.M k) ha hp0 hn0
    rw [← hst] at hm
    have : C.act k * (16 * K.M k 0 0 / (C.act k ^ 2 + 4)) =
        C.act k * m2E (C.act k) (C.act (k - 1)) (C.act (k + 1)) (C.m2Norm K.M (k - 1))
          (C.m2Norm K.M k) := by
      rw [hm, show C.act (k - 1) + C.act k = C.act k + C.act (k - 1) by ring]
      field_simp
      ring
    exact mul_left_cancel₀ ha.ne' this
  · -- the Gram determinant
    rw [hui, huo, ← hdet]
    unfold m2Gam
    have hs : 0 < C.act (k - 1) + C.act k := by positivity
    have ht : 0 < C.act k + C.act (k + 1) := by positivity
    have e11 : K.M k 1 1 = -K.M k 0 0 := by linarith
    rw [e11]
    have hqe : C.q k = (C.act k ^ 2 + 4) / ((C.act (k - 1) + C.act k) * (C.act k + C.act (k + 1))) := by
      rw [eq_div_iff (by positivity)]; exact hq
    rw [hqe]
    field_simp
    ring

/-- A function with nonnegative derivative on `(0, ∞)` is monotone there. -/
private lemma m2_mono_of_deriv {f f' : ℝ → ℝ} {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hd : ∀ z, 0 < z → HasDerivAt f (f' z) z) (hnn : ∀ z, 0 < z → 0 ≤ f' z) : f x ≤ f y := by
  have hmono : MonotoneOn f (Set.Ici x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici x)
    · exact fun z hz => (hd z (lt_of_lt_of_le hx hz)).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ici] at hz
      exact (hd z (lt_trans hx hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Ici] at hz
      rw [(hd z (lt_trans hx hz)).deriv]
      exact hnn z (lt_trans hx hz)
  exact hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hxy) hxy

/-- `y ↦ y - 1/(4y) - log y` is nondecreasing on `(0, ∞)` (its derivative is
`(2y - 1)²/(4y²)`). -/
private lemma m2_phi_mono {y y' : ℝ} (hy : 0 < y) (hyy : y ≤ y') :
    y - 1 / 4 * y⁻¹ - Real.log y ≤ y' - 1 / 4 * y'⁻¹ - Real.log y' := by
  refine m2_mono_of_deriv (f := fun z => z - 1 / 4 * z⁻¹ - Real.log z)
    (f' := fun z => (2 * z - 1) ^ 2 / (4 * z ^ 2)) hy hyy (fun z hz => ?_) (fun z hz => by positivity)
  have := ((hasDerivAt_id' z).sub ((hasDerivAt_inv hz.ne').const_mul (1 / 4 : ℝ))).sub
    (Real.hasDerivAt_log hz.ne')
  refine this.congr_deriv ?_
  field_simp
  ring

/-- `log x ≤ 2(x - 1)/(x + 1)` for `0 < x ≤ 1`. -/
private lemma m2_log_le_pade {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x ≤ 2 * (x - 1) / (x + 1) := by
  have h := m2_mono_of_deriv (f := fun z => Real.log z - 2 * (z - 1) / (z + 1))
    (f' := fun z => (z - 1) ^ 2 / (z * (z + 1) ^ 2)) hx hx1 (fun z hz => ?_)
    (fun z hz => by positivity)
  · simp only [Real.log_one, sub_self] at h
    linarith
  have h1 : HasDerivAt (fun z : ℝ => 2 * (z - 1)) 2 z := by
    simpa using ((hasDerivAt_id z).sub_const 1).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun z : ℝ => z + 1) 1 z := by simpa using (hasDerivAt_id z).add_const 1
  have := (Real.hasDerivAt_log hz.ne').sub (h1.div h2 (by positivity))
  refine this.congr_deriv ?_
  field_simp
  ring

/-- The switch threshold is at least `3/4`. -/
theorem m2g_ge {a b : ℝ} (h : 0 < a + b) : 3 / 4 ≤ m2g a b := by
  unfold m2g
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (a - b)]

/-- **Every turn secant is at least `3/4`**: it is the average of
`g_B = 3/4 + (x - B)²/(4(B + x)²)`. -/
theorem m2Sec_ge {A B P : ℝ} (hA : 0 < A) (hB : 0 < B) (hP : 0 < P) : 3 / 4 ≤ m2Sec A B P := by
  wlog hlt : A < P generalizing A P
  · rcases eq_or_lt_of_le (not_lt.1 hlt) with h | h
    · rw [h, m2Sec_self]; exact m2g_ge (by linarith)
    · rw [m2Sec_comm]; exact this hP hA h
  rw [m2Sec_of_ne hlt.ne]
  have hmono := m2_mono_of_deriv (f := fun z => z / 4 - B * Real.log (B + z) - B ^ 2 / (B + z))
    (f' := fun z => (z - B) ^ 2 / (4 * (B + z) ^ 2)) hA hlt.le (fun z hz => ?_)
    (fun z hz => by positivity)
  · have hPA : 0 < P - A := by linarith
    rw [Real.log_div (by positivity) (by positivity)]
    have e : B / (P - A) * (Real.log (P + B) - Real.log (A + B)) =
        B * (Real.log (B + P) - Real.log (B + A)) / (P - A) := by
      rw [add_comm P B, add_comm A B]; ring
    rw [e, show (1 : ℝ) + B ^ 2 / ((A + B) * (P + B)) - B * (Real.log (B + P) - Real.log (B + A)) /
        (P - A) = 3 / 4 + ((P / 4 - B * Real.log (B + P) - B ^ 2 / (B + P)) -
          (A / 4 - B * Real.log (B + A) - B ^ 2 / (B + A))) / (P - A) by
      field_simp; ring]
    have : 0 ≤ ((P / 4 - B * Real.log (B + P) - B ^ 2 / (B + P)) -
        (A / 4 - B * Real.log (B + A) - B ^ 2 / (B + A))) / (P - A) :=
      div_nonneg (by linarith) hPA.le
    linarith
  have hBz : 0 < B + z := by linarith
  have h1 : HasDerivAt (fun z : ℝ => B + z) 1 z := by simpa using (hasDerivAt_id z).const_add B
  have := (((hasDerivAt_id' z).div_const 4).sub ((h1.log hBz.ne').const_mul B)).sub
    ((hasDerivAt_const z (B ^ 2)).div h1 hBz.ne')
  refine this.congr_deriv ?_
  field_simp
  ring

/-- The rational separation: on `[3/20, 1/4)`,
`(9/4 - B̂²)/(16(1 - ρ)²) ≥ 23/125`, `B̂ = (-4ρ² + 11ρ - 1)/(4ρ + 1)`, cleared of denominators. -/
private lemma m2_scale_poly {ρ : ℝ} (h0 : 3 / 20 ≤ ρ) (h1 : ρ < 1 / 4) :
    368 * (1 - ρ) ^ 2 * (4 * ρ + 1) ^ 2 ≤
      125 * (9 / 4 * (4 * ρ + 1) ^ 2 - (-4 * ρ ^ 2 + 11 * ρ - 1) ^ 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, ρ = 3 / 20 + s := ⟨ρ - 3 / 20, by ring⟩
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 / 10 := by linarith
  have h2 : 0 ≤ s * (53284 / 125 - 103337 / 25 * s) := mul_nonneg hs0 (by linarith)
  have h3 : 0 ≤ s ^ 3 * (75496 / 5 - 7888 * s) := mul_nonneg (pow_nonneg hs0 3) (by linarith)
  nlinarith

/-- Lowering both norms to `3/4` lowers `4uv - E²`, when `E < 3r/2`, `E < 3t/2`. -/
private lemma m2_lower_norms {r t u v E E0 : ℝ} (hr0 : 0 < r) (ht0 : 0 < t) (hu : 3 / 4 ≤ u)
    (hv : 3 / 4 ≤ v) (hEr : E < 3 / 2 * r) (hEt : E < 3 / 2 * t)
    (hEE0 : E = E0 + (u - 3 / 4) / r + (v - 3 / 4) / t) :
    9 / 4 - E0 ^ 2 ≤ 4 * u * v - E ^ 2 := by
  have hdu : 0 ≤ u - 3 / 4 := by linarith
  have hdv : 0 ≤ v - 3 / 4 := by linarith
  have k1 : (u - 3 / 4) / r * (2 * E) ≤ 3 * (u - 3 / 4) := by
    have e : (u - 3 / 4) / r * (2 * E) = (u - 3 / 4) * (2 * E / r) := by ring
    have h2Er : 2 * E / r < 3 := by rw [div_lt_iff₀ hr0]; linarith
    rw [e]; have := mul_le_mul_of_nonneg_left h2Er.le hdu; linarith
  have k2 : (v - 3 / 4) / t * (2 * E) ≤ 3 * (v - 3 / 4) := by
    have e : (v - 3 / 4) / t * (2 * E) = (v - 3 / 4) * (2 * E / t) := by ring
    have h2Et : 2 * E / t < 3 := by rw [div_lt_iff₀ ht0]; linarith
    rw [e]; have := mul_le_mul_of_nonneg_left h2Et.le hdv; linarith
  have h3 := mul_nonneg hdu hdv
  have h4 := sq_nonneg ((u - 3 / 4) / r + (v - 3 / 4) / t)
  have e : 4 * u * v - E ^ 2 - (9 / 4 - E0 ^ 2) = 4 * ((u - 3 / 4) * (v - 3 / 4)) +
      3 * (u - 3 / 4) + 3 * (v - 3 / 4) - (u - 3 / 4) / r * (2 * E) - (v - 3 / 4) / t * (2 * E) +
      ((u - 3 / 4) / r + (v - 3 / 4) / t) ^ 2 := by
    rw [hEE0]; ring
  linarith

/-- At the lower norm corner, `0 < E₀ ≤ B̂(ρ)` for `3/20 ≤ ρ < rt`, `r, t < 1/2` (raise both
neighbour ratios to `1/2`, then use `log x ≤ 2(x - 1)/(x + 1)`). -/
private lemma m2_E0_bounds {r t ρ : ℝ} (hr0 : 0 < r) (ht0 : 0 < t) (hr2 : r < 1 / 2)
    (ht2 : t < 1 / 2) (hρrt : ρ < r * t) (hρ : 3 / 20 ≤ ρ) :
    0 < 1 + r + t - ρ + Real.log (ρ / (r * t)) - 1 / 4 * r⁻¹ - 1 / 4 * t⁻¹ ∧
      1 + r + t - ρ + Real.log (ρ / (r * t)) - 1 / 4 * r⁻¹ - 1 / 4 * t⁻¹ ≤
        1 - ρ + 2 * (4 * ρ - 1) / (4 * ρ + 1) := by
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : ρ < 1 / 4 := by
    have := mul_lt_mul'' hr2 ht2 hr0.le ht0.le; linarith
  have hsplit : 1 + r + t - ρ + Real.log (ρ / (r * t)) - 1 / 4 * r⁻¹ - 1 / 4 * t⁻¹ =
      1 - ρ + Real.log ρ + (r - 1 / 4 * r⁻¹ - Real.log r) + (t - 1 / 4 * t⁻¹ - Real.log t) := by
    rw [Real.log_div hρ0.ne' (by positivity), Real.log_mul hr0.ne' ht0.ne']; ring
  rw [hsplit]
  have hφhalf : (1 / 2 : ℝ) - 1 / 4 * (1 / 2)⁻¹ - Real.log (1 / 2) = Real.log 2 := by
    rw [one_div, Real.log_inv]; norm_num
  constructor
  · have htr : ρ / r ≤ t := by rw [div_le_iff₀ hr0]; linarith
    have h1 := m2_phi_mono (show 0 < ρ / r by positivity) htr
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
    have h8 : 1 / (8 * ρ) ≤ 5 / 6 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  · have h1 := m2_phi_mono hr0 hr2.le
    have h2 := m2_phi_mono ht0 ht2.le
    rw [hφhalf] at h1 h2
    have h4 := m2_log_le_pade (show 0 < 4 * ρ by positivity) (by linarith)
    have e4 : Real.log (4 * ρ) = 2 * Real.log 2 + Real.log ρ := by
      rw [Real.log_mul (by norm_num) hρ0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast; ring
    rw [e4] at h4
    linarith

/-- **The reverse-centre scale bound**: a centre with `Γ < 23/125` has `a² < 12/17`. -/
theorem m2_scale (D : M2Centre) (hcap : D.Γ < 23 / 125) : D.a ^ 2 < 12 / 17 := by
  obtain ⟨pp, p, a, n, nn, u, v, E, Γ, ha, hap, han, hpp, hnn, hfac, hu, hv, hule, hvle, hE,
    hΓ⟩ := D
  simp only at hcap ⊢
  have hp : 0 < p := by linarith
  have hn : 0 < n := by linarith
  have hu34 : 3 / 4 ≤ u := hu ▸ m2Sec_ge ha hp hpp
  have hv34 : 3 / 4 ≤ v := hv ▸ m2Sec_ge ha hn hnn
  have hK0 : 0 < a ^ 2 + 4 := by positivity
  have hUr : u ≤ 1 - a / (a + p) + (a / (a + p)) ^ 2 := by
    have e := m2g_eq_m2U (show 0 < a + p by linarith)
    rw [e] at hule; exact hule
  have hUt : v ≤ 1 - a / (a + n) + (a / (a + n)) ^ 2 := by
    have e := m2g_eq_m2U (show 0 < a + n by linarith)
    rw [e] at hvle; exact hvle
  have hρrt : a ^ 2 / (a ^ 2 + 4) < a / (a + p) * (a / (a + n)) := by
    rw [div_mul_div_comm, div_lt_div_iff₀ hK0 (by positivity)]
    have : 0 < a ^ 2 := by positivity
    nlinarith
  have hr0 : 0 < a / (a + p) := by positivity
  have ht0 : 0 < a / (a + n) := by positivity
  have hr2 : a / (a + p) < 1 / 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have ht2 : a / (a + n) < 1 / 2 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have hgoal : a ^ 2 < 12 / 17 ↔ a ^ 2 / (a ^ 2 + 4) < 3 / 20 := by
    rw [div_lt_iff₀ hK0]; constructor <;> intro h <;> linarith
  rw [hgoal]
  have hE' : E = 1 + a / (a + p) + a / (a + n) - a ^ 2 / (a ^ 2 + 4) +
      Real.log (a ^ 2 / (a ^ 2 + 4) / (a / (a + p) * (a / (a + n)))) -
      (1 - u) / (a / (a + p)) - (1 - v) / (a / (a + n)) := hE
  have hΓ' : Γ = (4 * u * v - E ^ 2) / (16 * (1 - a ^ 2 / (a ^ 2 + 4)) ^ 2) := hΓ
  have hρ0 : 0 < a ^ 2 / (a ^ 2 + 4) := by positivity
  clear hE hΓ hu hv hule hvle hfac hgoal
  generalize a / (a + p) = r at *
  generalize a / (a + n) = t at *
  generalize a ^ 2 / (a ^ 2 + 4) = ρ at *
  have hρ1 : ρ < 1 / 4 := by
    have := mul_lt_mul'' hr2 ht2 hr0.le ht0.le; linarith
  -- `E < 3r/2`, `E < 3t/2`
  have hℓ1 : -ρ + Real.log (ρ / (r * t)) < -(r * t) := by
    have hx : 0 < ρ / (r * t) := by positivity
    have hl := Real.log_le_sub_one_of_pos hx
    have hx1 : ρ / (r * t) < 1 := (div_lt_one (by positivity)).2 hρrt
    have hrt1 : r * t < 1 := by have := mul_lt_mul'' hr2 ht2 hr0.le ht0.le; linarith
    have e : ρ = ρ / (r * t) * (r * t) := by field_simp
    have : (1 - ρ / (r * t)) * (1 - r * t) > 0 := mul_pos (by linarith) (by linarith)
    nlinarith
  have hur : 1 - r ≤ (1 - u) / r := by
    rw [le_div_iff₀ hr0]; have : (1 - r) * r = r - r ^ 2 := by ring
    linarith
  have hvt : 1 - t ≤ (1 - v) / t := by
    rw [le_div_iff₀ ht0]; have : (1 - t) * t = t - t ^ 2 := by ring
    linarith
  have hEbar : E < -1 + 2 * r + 2 * t - r * t := by rw [hE']; linarith
  have hEr : E < 3 / 2 * r := by
    have : (2 - r) * (t - 1 / 2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    nlinarith
  have hEt : E < 3 / 2 * t := by
    have : (2 - t) * (r - 1 / 2) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    nlinarith
  by_contra hcon
  push Not at hcon
  obtain ⟨hE0pos, hup⟩ := m2_E0_bounds hr0 ht0 hr2 ht2 hρrt hcon
  have hEE0 : E = (1 + r + t - ρ + Real.log (ρ / (r * t)) - 1 / 4 * r⁻¹ - 1 / 4 * t⁻¹) +
      (u - 3 / 4) / r + (v - 3 / 4) / t := by
    rw [hE']; field_simp; ring
  have hlow := m2_lower_norms hr0 ht0 hu34 hv34 hEr hEt hEE0
  have hB : 1 - ρ + 2 * (4 * ρ - 1) / (4 * ρ + 1) = (-4 * ρ ^ 2 + 11 * ρ - 1) / (4 * ρ + 1) := by
    have : 0 < 4 * ρ + 1 := by positivity
    field_simp; ring
  rw [hB] at hup
  have hBh := pow_le_pow_left₀ hE0pos.le hup 2
  have hpoly := m2_scale_poly hcon hρ1
  have h41 : 0 < 4 * ρ + 1 := by positivity
  have h1ρ : 0 < 1 - ρ := by linarith
  have hB2 : ((-4 * ρ ^ 2 + 11 * ρ - 1) / (4 * ρ + 1)) ^ 2 ≤ 9 / 4 - 368 / 125 * (1 - ρ) ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    linarith
  have hcap' : 23 / 125 ≤ Γ := by
    rw [hΓ', le_div_iff₀ (by positivity)]
    linarith
  linarith

end SmoothedOctagon
