module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Basic

/-!
# Hand proof of the smaller-short case: the first-contact barrier argument

The barrier comparison behind the equal-secant orders of `ShortHand/Order.lean` (the strong lower
order, the global and small-shape upper orders and the rational quadratic order). In the
normalized coordinates of
`ss_order_norm` (`ℓ = 1/x`, `p₁ = α/β`, `q₁ = x/β`, `avg(p, q) = Sec(p, 1, q)`,
`g = ss_gB 1`), a barrier is a differentiable `P` with `P(1) = 1/x`, and its comparison function is
`Φ(z) = avg(P z, z) - avg(1/x, 1/z)`. At a contact (a zero of `Φ`, common average `u`),
`Φ'(z)(z - P z)z(x - z) = κ(z) = -P'(z)(g(P z) - u)z(x - z) - (u - g(z))((2z - P z)x - z²)`, so the
sign of the contact inequality decides the sign of `Φ'`, and `hs_first_contact` gives the sign of
`Φ` on `(q₁, 1)`.

## Main API

* `hsoPhi`, `hso_phi_eq`, `hso_phi_hasDerivAt`: the comparison function, its value and derivative.
* `hso_core`: the sign of `sΦ` on `(a, 1)` from the sign of `sκ` at contacts.
* `hso_order_lower`: `P(q₁) ≤ p₁` for a lower barrier (including the case where the barrier meets
  the diagonal, excluded as in `ss_order_norm`).
* `hso_order_upper`: `p₁ ≤ P(q₁)` for an upper barrier below the diagonal.
* `hso_avg_anti`, `hso_eta`, `hso_norm_eq`: secant facts; `hso_lower_alg`, `hso_upper_alg`: the
  contact inequality from a gap ratio and a contact polynomial.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real Filter Topology

/-- The comparison function of a barrier `P` in the normalized coordinates of `ss_order_norm`:
`Φ(z) = (F(z) - F(P z))/(z - P z) - (F(1/z) - F(1/x))/(1/z - 1/x)`, `F = ss_FB 1`. -/
noncomputable def hsoPhi (P : ℝ → ℝ) (x z : ℝ) : ℝ :=
  (ss_FB 1 z - ss_FB 1 (P z)) / (z - P z) - (ss_FB 1 z⁻¹ - ss_FB 1 x⁻¹) / (z⁻¹ - x⁻¹)

theorem hso_inv_lt {x z : ℝ} (hx : 1 < x) (hz0 : 0 < z) (hz : z ≤ 1) : x⁻¹ < z⁻¹ :=
  inv_strictAnti₀ hz0 (lt_of_le_of_lt hz hx)

/-- For `0 < P z < z ≤ 1 < x`, `Φ(z) = avg(P z, z) - avg(1/x, 1/z)`. -/
theorem hso_phi_eq {P : ℝ → ℝ} {x z : ℝ} (hx : 1 < x) (hP : 0 < P z) (hPz : P z < z)
    (hz : z ≤ 1) : hsoPhi P x z = m2Sec (P z) 1 z - m2Sec x⁻¹ 1 z⁻¹ := by
  have hz0 : 0 < z := hP.trans hPz
  have e2 := ss_sec_mul hP one_pos hz0
  have e1 := ss_sec_mul (inv_pos.2 (by linarith : (0:ℝ) < x)) one_pos (inv_pos.2 hz0)
  have d2 : z - P z ≠ 0 := (sub_pos.2 hPz).ne'
  have d1 : z⁻¹ - x⁻¹ ≠ 0 := (sub_pos.2 (hso_inv_lt hx hz0 hz)).ne'
  unfold hsoPhi
  rw [← e2, ← e1, mul_div_cancel_left₀ _ d2, mul_div_cancel_left₀ _ d1]

theorem hso_phi_hasDerivAt {P : ℝ → ℝ} {P'z x z : ℝ} (hx : 1 < x) (hP : 0 < P z) (hPz : P z < z)
    (hz : z ≤ 1) (hd : HasDerivAt P P'z z) :
    HasDerivAt (hsoPhi P x)
      (((ss_gB 1 z - ss_gB 1 (P z) * P'z) * (z - P z) - (ss_FB 1 z - ss_FB 1 (P z)) * (1 - P'z)) /
          (z - P z) ^ 2 -
        (ss_gB 1 z⁻¹ * (-(z ^ 2)⁻¹) * (z⁻¹ - x⁻¹) - (ss_FB 1 z⁻¹ - ss_FB 1 x⁻¹) * (-(z ^ 2)⁻¹)) /
          (z⁻¹ - x⁻¹) ^ 2) z := by
  have hz0 : 0 < z := hP.trans hPz
  have d2 : z - P z ≠ 0 := (sub_pos.2 hPz).ne'
  have d1 : z⁻¹ - x⁻¹ ≠ 0 := (sub_pos.2 (hso_inv_lt hx hz0 hz)).ne'
  have hc := (ss_FB_hasDerivAt one_pos hP).comp z hd
  have hN2 := (ss_FB_hasDerivAt one_pos hz0).sub hc
  have hD2 := (hasDerivAt_id' z).sub hd
  have hN1 := ((ss_FB_hasDerivAt one_pos (inv_pos.2 hz0)).comp z
    (hasDerivAt_inv hz0.ne')).sub_const (ss_FB 1 x⁻¹)
  have hD1 := (hasDerivAt_inv hz0.ne').sub_const x⁻¹
  have := (hN2.div hD2 d2).sub (hN1.div hD1 d1)
  convert this using 1
  · funext w
    simp only [hsoPhi, Pi.sub_apply, Pi.div_apply, Function.comp_apply]
  · simp only [Pi.sub_apply, Function.comp_apply]

/-- The derivative of `Φ` at a zero, cleared: with `u` the common average,
`Φ'(z)(z - p)z(x - z) = -P'(z)(g(p) - u)z(x - z) - (u - g(z))((2z - p)x - z²)`. -/
theorem hso_deriv_alg {x z p P'z u gz gp : ℝ} (hx0 : 0 < x) (hz0 : 0 < z) (hzx : z < x)
    (hpz : p < z) :
    (((gz - gp * P'z) * (z - p) - ((z - p) * u) * (1 - P'z)) / (z - p) ^ 2 -
      (gz * (-(z ^ 2)⁻¹) * (z⁻¹ - x⁻¹) - ((z⁻¹ - x⁻¹) * u) * (-(z ^ 2)⁻¹)) /
        (z⁻¹ - x⁻¹) ^ 2) * ((z - p) * z * (x - z)) =
      -P'z * (gp - u) * z * (x - z) - (u - gz) * ((2 * z - p) * x - z ^ 2) := by
  have d2 : z - p ≠ 0 := (sub_pos.2 hpz).ne'
  have d1 : z⁻¹ - x⁻¹ ≠ 0 := (sub_pos.2 (inv_strictAnti₀ hz0 hzx)).ne'
  have d3 : x - z ≠ 0 := (sub_pos.2 hzx).ne'
  field_simp
  ring

/-- **The barrier core**: if `s κ(z) < 0` at every contact `z ∈ (a, 1]` (a zero of `Φ`), where
`κ = -P'(z)(g(P z) - u)z(x - z) - (u - g(z))((2z - P z)x - z²)`, then `s Φ > 0` on `(a, 1)`
(`hs_first_contact`; `s = 1` for a lower barrier, `s = -1` for an upper one). -/
theorem hso_neg_of {s D w k : ℝ} (hw : 0 < w) (h : D * w = k) (hk : s * k < 0) : s * D < 0 := by
  by_contra hc
  push Not at hc
  have h1 : s * D * w < 0 := by rw [mul_assoc, h]; exact hk
  have := mul_nonneg hc hw.le
  linarith

theorem hso_core {x a s : ℝ} {P P' : ℝ → ℝ} (hx : 1 < x) (ha : a < 1) (hs0 : s ≠ 0)
    (hP1 : P 1 = x⁻¹)
    (hPd : ∀ z ∈ Icc a 1, HasDerivAt P (P' z) z) (hPpos : ∀ z ∈ Icc a 1, 0 < P z)
    (hPlt : ∀ z ∈ Icc a 1, P z < z)
    (hc : ∀ z ∈ Ioc a 1, m2Sec (P z) 1 z = m2Sec x⁻¹ 1 z⁻¹ →
      s * (-P' z * (ss_gB 1 (P z) - m2Sec (P z) 1 z) * z * (x - z) -
        (m2Sec (P z) 1 z - ss_gB 1 z) * ((2 * z - P z) * x - z ^ 2)) < 0) :
    ∀ z ∈ Ioo a 1, 0 < s * hsoPhi P x z := by
  have hD : ∀ z ∈ Icc a 1, HasDerivAt (fun z => s * hsoPhi P x z) (s *
      ((((ss_gB 1 z - ss_gB 1 (P z) * P' z) * (z - P z) -
        (ss_FB 1 z - ss_FB 1 (P z)) * (1 - P' z)) / (z - P z) ^ 2 -
        (ss_gB 1 z⁻¹ * (-(z ^ 2)⁻¹) * (z⁻¹ - x⁻¹) - (ss_FB 1 z⁻¹ - ss_FB 1 x⁻¹) * (-(z ^ 2)⁻¹)) /
          (z⁻¹ - x⁻¹) ^ 2))) z := fun z hz =>
    (hso_phi_hasDerivAt hx (hPpos z hz) (hPlt z hz) hz.2 (hPd z hz)).const_mul s
  refine hs_first_contact (Φ := fun z => s * hsoPhi P x z) ha
    (fun z hz => (hD z hz).continuousAt.continuousWithinAt) ?_ ?_
  · simp only [hsoPhi, hP1, inv_one, sub_self, mul_zero]
  intro z hz hzero
  have hz' : z ∈ Icc a 1 := Ioc_subset_Icc_self hz
  have hP := hPpos z hz'
  have hPz := hPlt z hz'
  have hz0 : 0 < z := hP.trans hPz
  have hx0 : 0 < x := by linarith
  have hzx : z < x := lt_of_le_of_lt hz.2 hx
  refine ⟨_, ?_, hD z hz'⟩
  -- at a zero the two averages agree
  have hΦ0 : hsoPhi P x z = 0 := by
    rcases mul_eq_zero.1 hzero with h | h
    · exact absurd h hs0
    · exact h
  rw [hso_phi_eq hx hP hPz hz.2, sub_eq_zero] at hΦ0
  have key := hc z hz hΦ0
  have e2 := ss_sec_mul hP one_pos hz0
  have e1 := ss_sec_mul (inv_pos.2 hx0) one_pos (inv_pos.2 hz0)
  rw [← hΦ0] at e1
  rw [← e2, ← e1, ss_gB_inv hz0]
  have halg := hso_deriv_alg (P'z := P' z) (u := m2Sec (P z) 1 z) (gz := ss_gB 1 z)
    (gp := ss_gB 1 (P z)) hx0 hz0 hzx hPz
  have hpos : 0 < (z - P z) * z * (x - z) := by
    have := sub_pos.2 hPz; have := sub_pos.2 hzx; positivity
  exact hso_neg_of hpos halg key

/-- `avg(·, q)` strictly decreases in the left end: `avg(p', q) < avg(p, q)` for
`0 < p < p' < q ≤ 1`. -/
theorem hso_avg_anti {p p' q : ℝ} (hp : 0 < p) (hpp : p < p') (hpq : p' < q) (hq : q ≤ 1) :
    m2Sec p' 1 q < m2Sec p 1 q := by
  have hp' : 0 < p' := hp.trans hpp
  have hq0 : 0 < q := hp'.trans hpq
  have hadd := ss_sec_add hp one_pos hp' hq0
  have hA := ss_sec_gt_right (B := 1) hp hpp (by linarith)
  have hB := ss_sec_le_left hp' hpq.le hq
  have k1 := mul_lt_mul_of_pos_left hA (sub_pos.2 hpp)
  have k2 := mul_le_mul_of_nonneg_left hB (sub_pos.2 hpq).le
  have k3 := mul_le_mul_of_nonneg_left hB (sub_pos.2 hpp).le
  by_contra h
  push Not at h
  have k4 := mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ q - p)
  linarith

/-- The gap `η₁ = avg(1/x, 1/z) - g(z)` is positive on `[q₁, 1]` (`ss_eta_mono`, as in
`ss_order_norm`). -/
theorem hso_eta {ℓ p₁ q₁ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hp : 0 < p₁) (hpq : p₁ < q₁)
    (hq1 : q₁ ≤ 1) (heq : m2Sec ℓ 1 q₁⁻¹ = m2Sec p₁ 1 q₁) :
    ∀ z ∈ Icc q₁ 1, ss_gB 1 z < m2Sec ℓ 1 z⁻¹ := by
  intro q hq
  have hq₁ : 0 < q₁ := hp.trans hpq
  have hq0 : 0 < q := hq₁.trans_le hq.1
  have h0 : ss_gB 1 q₁ < m2Sec ℓ 1 q₁⁻¹ := heq ▸ ss_sec_gt_right hp hpq hq1
  have hK : 1 ≤ q⁻¹ := (one_le_inv₀ hq0).2 hq.2
  have hKK : q⁻¹ ≤ q₁⁻¹ := inv_anti₀ hq₁ hq.1
  have hm := ss_eta_mono hℓ hℓ1 hK hKK
  rw [ss_gB_inv hq₁, ss_gB_inv hq0] at hm
  have hd₁ : 0 < q₁⁻¹ - ℓ := by have := (one_le_inv₀ hq₁).2 hq1; linarith
  have hd : 0 < q⁻¹ - ℓ := by linarith
  have hpos : 0 < (q₁⁻¹ - ℓ) * (m2Sec ℓ 1 q₁⁻¹ - ss_gB 1 q₁) := mul_pos hd₁ (by linarith)
  have := (mul_pos_iff_of_pos_left hd).1 (lt_of_lt_of_le hpos hm)
  linarith

/-- The closed form of `avg(1/x, 1/z)`. -/
theorem hso_G_eq {x z : ℝ} (hx : 1 < x) (hz0 : 0 < z) (hz : z ≤ 1) :
    (ss_FB 1 z⁻¹ - ss_FB 1 x⁻¹) / (z⁻¹ - x⁻¹) = m2Sec x⁻¹ 1 z⁻¹ := by
  have e1 := ss_sec_mul (inv_pos.2 (by linarith : (0:ℝ) < x)) one_pos (inv_pos.2 hz0)
  rw [← e1, mul_div_cancel_left₀ _ (sub_pos.2 (hso_inv_lt hx hz0 hz)).ne']

theorem hso_ge_of_within {f : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hf : ContinuousWithinAt f (Ioo a b) a) (h : ∀ z ∈ Ioo a b, c ≤ f z) : c ≤ f a := by
  have : (𝓝[Ioo a b] a).NeBot := mem_closure_iff_nhdsWithin_neBot.1
    (by rw [closure_Ioo hab.ne]; exact left_mem_Icc.2 hab.le)
  exact ge_of_tendsto hf (eventually_nhdsWithin_of_forall h)

/-- **Lower barrier**: a barrier `P` through `P(1) = 1/x` whose contacts below the diagonal all
satisfy the strict contact inequality lies below the actual normalized point: `P(q₁) ≤ p₁`. -/
theorem hso_order_lower {x p₁ q₁ : ℝ} {P P' : ℝ → ℝ} (hx : 1 < x) (hp : 0 < p₁) (hpq : p₁ < q₁)
    (hq1 : q₁ ≤ 1) (heq : m2Sec x⁻¹ 1 q₁⁻¹ = m2Sec p₁ 1 q₁) (hP1 : P 1 = x⁻¹)
    (hPd : ∀ z ∈ Icc q₁ 1, HasDerivAt P (P' z) z) (hPpos : ∀ z ∈ Icc q₁ 1, 0 < P z)
    (hc : ∀ z ∈ Ioc q₁ 1, P z < z → m2Sec (P z) 1 z = m2Sec x⁻¹ 1 z⁻¹ →
      -P' z * (ss_gB 1 (P z) - m2Sec (P z) 1 z) * z * (x - z) <
        (m2Sec (P z) 1 z - ss_gB 1 z) * ((2 * z - P z) * x - z ^ 2)) :
    P q₁ ≤ p₁ := by
  have hx0 : 0 < x := by linarith
  have hℓ : 0 < x⁻¹ := inv_pos.2 hx0
  have hℓ1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hq₁ : 0 < q₁ := hp.trans hpq
  have hη := hso_eta hℓ hℓ1 hp hpq hq1 heq
  have hcore : ∀ a, q₁ ≤ a → a < 1 → (∀ z ∈ Icc a 1, P z < z) →
      ∀ z ∈ Ioo a 1, 0 < hsoPhi P x z := by
    intro a ha ha1 hlt z hz
    have h := hso_core (s := 1) (P' := P') hx ha1 one_ne_zero hP1
      (fun w hw => hPd w ⟨ha.trans hw.1, hw.2⟩) (fun w hw => hPpos w ⟨ha.trans hw.1, hw.2⟩) hlt
      (fun w hw hw0 => by
        have := hc w ⟨lt_of_le_of_lt ha hw.1, hw.2⟩ (hlt w (Ioc_subset_Icc_self hw)) hw0
        linarith) z hz
    linarith
  have hq₁I : q₁ ∈ Icc q₁ 1 := ⟨le_rfl, hq1⟩
  by_cases hall : ∀ z ∈ Icc q₁ 1, P z < z
  · have hΦ : 0 ≤ hsoPhi P x q₁ := by
      rcases hq1.lt_or_eq with hlt | heq1
      · exact hso_ge_of_within hlt (hso_phi_hasDerivAt hx (hPpos q₁ hq₁I) (hall q₁ hq₁I) hq1
          (hPd q₁ hq₁I)).continuousAt.continuousWithinAt
          (fun z hz => (hcore q₁ le_rfl hlt hall z hz).le)
      · subst heq1
        simp [hsoPhi, hP1]
    rw [hso_phi_eq hx (hPpos q₁ hq₁I) (hall q₁ hq₁I) hq1, heq] at hΦ
    by_contra hcon
    push Not at hcon
    have := hso_avg_anti hp hcon (hall q₁ hq₁I) hq1
    linarith
  · -- the barrier meets the diagonal at a last point `q_s < 1`: impossible
    exfalso
    push Not at hall
    obtain ⟨z₀, hz₀, hz₀P⟩ := hall
    have hcP : ContinuousOn (fun z => P z - z) (Icc q₁ 1) := fun z hz =>
      ((hPd z hz).continuousAt.sub continuousAt_id).continuousWithinAt
    have hSc : IsClosed (Icc q₁ 1 ∩ (fun z => P z - z) ⁻¹' Ici 0) :=
      hcP.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hne : (Icc q₁ 1 ∩ (fun z => P z - z) ⁻¹' Ici 0).Nonempty :=
      ⟨z₀, hz₀, by simp only [mem_preimage, mem_Ici]; linarith⟩
    have hbdd : BddAbove (Icc q₁ 1 ∩ (fun z => P z - z) ⁻¹' Ici 0) := ⟨1, fun z hz => hz.1.2⟩
    have hqsS := hSc.csSup_mem hne hbdd
    set qs := sSup (Icc q₁ 1 ∩ (fun z => P z - z) ⁻¹' Ici 0) with hqs
    have hqsP : qs ≤ P qs := by
      have := hqsS.2; simp only [mem_preimage, mem_Ici] at this; linarith
    have hqs1 : qs < 1 := by
      refine lt_of_le_of_ne hqsS.1.2 fun h => ?_
      rw [h, hP1] at hqsP
      linarith
    have hqs0 : 0 < qs := hq₁.trans_le hqsS.1.1
    have hgt : ∀ z ∈ Ioc qs 1, P z < z := fun z hz => by
      by_contra hcon
      push Not at hcon
      have hzS : z ∈ Icc q₁ 1 ∩ (fun z => P z - z) ⁻¹' Ici 0 :=
        ⟨⟨hqsS.1.1.trans hz.1.le, hz.2⟩, by simp only [mem_preimage, mem_Ici]; linarith⟩
      have := le_csSup hbdd hzS
      linarith [hz.1]
    have hsub : ∀ z ∈ Ioo qs 1, z ∈ Icc q₁ 1 := fun z hz => ⟨hqsS.1.1.trans hz.1.le, hz.2.le⟩
    have hpos : ∀ z ∈ Ioo qs 1, 0 < hsoPhi P x z := fun z hz =>
      hcore ((qs + z) / 2) (by linarith [hqsS.1.1, hz.1]) (by linarith [hz.2])
        (fun w hw => hgt w ⟨by linarith [hw.1, hz.1], hw.2⟩) z ⟨by linarith [hz.1], hz.2⟩
    have : (𝓝[Ioo qs 1] qs).NeBot := mem_closure_iff_nhdsWithin_neBot.1
      (by rw [closure_Ioo hqs1.ne]; exact left_mem_Icc.2 hqs1.le)
    -- `P(q_s) = q_s`
    have hPq : P qs ≤ qs := by
      have hc1 : ContinuousWithinAt (fun z => P z - z) (Ioo qs 1) qs :=
        ((hPd qs hqsS.1).continuousAt.sub continuousAt_id).continuousWithinAt
      have := le_of_tendsto hc1 (eventually_nhdsWithin_of_forall fun z hz =>
        (sub_neg.2 (hgt z ⟨hz.1, hz.2.le⟩)).le)
      linarith
    -- `avg(1/x, 1/q_s) ≤ g(P q_s)` in the limit
    have hG : ContinuousAt (fun z => (ss_FB 1 z⁻¹ - ss_FB 1 x⁻¹) / (z⁻¹ - x⁻¹)) qs :=
      ((((ss_FB_hasDerivAt one_pos (inv_pos.2 hqs0)).comp qs (hasDerivAt_inv hqs0.ne')).sub_const
        (ss_FB 1 x⁻¹)).div ((hasDerivAt_inv hqs0.ne').sub_const x⁻¹)
        (sub_pos.2 (hso_inv_lt hx hqs0 hqs1.le)).ne').continuousAt
    have hH : ContinuousWithinAt (fun z => ss_gB 1 (P z)) (Ioo qs 1) qs :=
      ((ss_gB_hasDerivAt (by linarith : 0 < P qs)).continuousAt.comp
        (hPd qs hqsS.1).continuousAt).continuousWithinAt
    have hlim := le_of_tendsto_of_tendsto hG.continuousWithinAt hH
      (eventually_nhdsWithin_of_forall fun z hz => by
        have hzI := hsub z hz
        have hz0 : 0 < z := hqs0.trans hz.1
        have hPz := hgt z ⟨hz.1, hz.2.le⟩
        have h1 := hpos z hz
        rw [hso_phi_eq hx (hPpos z hzI) hPz hz.2.le] at h1
        have h2 := ss_sec_le_left (hPpos z hzI) hPz.le hz.2.le
        show (ss_FB 1 z⁻¹ - ss_FB 1 x⁻¹) / (z⁻¹ - x⁻¹) ≤ ss_gB 1 (P z)
        rw [hso_G_eq hx hz0 hz.2.le]
        linarith)
    simp only at hlim
    rw [hso_G_eq hx hqs0 hqs1.le, show P qs = qs by linarith] at hlim
    have := hη qs hqsS.1
    linarith

/-- **Upper barrier**: a barrier `P` below the diagonal on `[q₁, 1]`, through `P(1) = 1/x`,
whose contacts all satisfy the reversed strict contact inequality lies above the actual
normalized point: `p₁ ≤ P(q₁)`. -/
theorem hso_order_upper {x p₁ q₁ : ℝ} {P P' : ℝ → ℝ} (hx : 1 < x) (hpq : p₁ < q₁)
    (hq1 : q₁ ≤ 1) (heq : m2Sec x⁻¹ 1 q₁⁻¹ = m2Sec p₁ 1 q₁) (hP1 : P 1 = x⁻¹)
    (hPd : ∀ z ∈ Icc q₁ 1, HasDerivAt P (P' z) z) (hPpos : ∀ z ∈ Icc q₁ 1, 0 < P z)
    (hPlt : ∀ z ∈ Icc q₁ 1, P z < z)
    (hc : ∀ z ∈ Ioc q₁ 1, m2Sec (P z) 1 z = m2Sec x⁻¹ 1 z⁻¹ →
      (m2Sec (P z) 1 z - ss_gB 1 z) * ((2 * z - P z) * x - z ^ 2) <
        -P' z * (ss_gB 1 (P z) - m2Sec (P z) 1 z) * z * (x - z)) :
    p₁ ≤ P q₁ := by
  have hq₁I : q₁ ∈ Icc q₁ 1 := ⟨le_rfl, hq1⟩
  have hΦ : hsoPhi P x q₁ ≤ 0 := by
    rcases hq1.lt_or_eq with hlt | heq1
    · have h := hso_ge_of_within (f := fun z => -hsoPhi P x z) (c := 0) hlt
        (hso_phi_hasDerivAt hx (hPpos q₁ hq₁I) (hPlt q₁ hq₁I) hq1
          (hPd q₁ hq₁I)).continuousAt.neg.continuousWithinAt
        (fun z hz => by
          have := hso_core (s := -1) (P' := P') hx hlt (by norm_num) hP1 hPd hPpos hPlt
            (fun w hw hw0 => by have := hc w hw hw0; linarith) z hz
          linarith)
      linarith
    · subst heq1
      simp [hsoPhi, hP1]
  rw [hso_phi_eq hx (hPpos q₁ hq₁I) (hPlt q₁ hq₁I) hq1, heq] at hΦ
  by_contra hcon
  push Not at hcon
  have := hso_avg_anti (hPpos q₁ hq₁I) hcon hpq hq1
  linarith

/-- **The normalized equal-secant equation** (as in `ss_order`): `Sec(1, x, β) = Sec(α, β, x)`
becomes `avg(1/x, β/x) = avg(α/β, x/β)`. -/
theorem hso_norm_eq {x al be : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be)
    (heq : m2Sec 1 x be = m2Sec al be x) : m2Sec x⁻¹ 1 (x / be)⁻¹ = m2Sec (al / be) 1 (x / be) := by
  have s1 : m2Sec 1 x be = m2Sec x⁻¹ 1 (x / be)⁻¹ := by
    rw [← ss_sec_scale (c := 1 / x) (by positivity) one_pos hx hbe]
    congr 1 <;> field_simp
  have s2 : m2Sec al be x = m2Sec (al / be) 1 (x / be) := by
    rw [m2Sec_comm, ← ss_sec_scale (c := 1 / be) (by positivity) hx hbe hal, m2Sec_comm]
    congr 1 <;> field_simp
  rw [← s1, ← s2, heq]

/-- **The lower contact inequality** from a gap ratio `Nξ < (W - N)η` and a contact polynomial
`B(W - N) ≤ NM`: `Bξ < ηM`. -/
theorem hso_lower_alg {N W M η ξ B : ℝ} (hgap : N * ξ < (W - N) * η) (hcon : B * (W - N) ≤ N * M)
    (hM : 0 < M) (hξ : 0 ≤ ξ) (hη : 0 < η) (hN : 0 ≤ N) : B * ξ < η * M := by
  have hWN : 0 < W - N := by
    by_contra h
    push Not at h
    have := mul_nonpos_of_nonpos_of_nonneg h hη.le
    have := mul_nonneg hN hξ
    linarith
  have k1 := mul_lt_mul_of_pos_right hgap hM
  have k2 := mul_le_mul_of_nonneg_left hcon hξ
  by_contra h
  push Not at h
  have k3 := mul_le_mul_of_nonneg_left h hWN.le
  linarith

/-- **The upper contact inequality** from a gap ratio `Zη < N'ξ` and a contact polynomial
`N'M < BZ`: `ηM < Bξ`. -/
theorem hso_upper_alg {Np Z M η ξ B : ℝ} (hgap : Z * η < Np * ξ) (hcon : Np * M < B * Z)
    (hM : 0 < M) (hξ : 0 ≤ ξ) (hZ : 0 < Z) : η * M < B * ξ := by
  have k1 := mul_lt_mul_of_pos_right hgap hM
  have k2 := mul_le_mul_of_nonneg_left hcon.le hξ
  by_contra h
  push Not at h
  have k3 := mul_le_mul_of_nonneg_left h hZ.le
  linarith

end SmoothedOctagon
