module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Gap

/-!
# Case M2, smaller-short side: the strengthened bridge order (S)

For a short bridge `a < C ≤ B`, `A < C` whose two turn secants agree, `Sec(a, C, B) = Sec(A, B, C)`,
the strengthened order (S) `A ≥ aB/C + (2/7)(B - C)` holds.

In the normalized coordinates `ℓ = a/C`, `q = C/B`, `p = A/B` of `g(s) = 1 - s/(1 + s)²`, the
comparison function `Φ(q) = avg(p_S(q), q) - avg(ℓ, 1/q)` with `p_S(q) = ℓ + (2/7)(1 - q)` is shown
to be antitone on `[q₁, 1]` directly: its derivative is
`[g(q) + (2/7)g(p_S) - (9/7)avg₂]/(q - p_S) - η₁/(q²(1/q - ℓ))`, nonpositive by the gap ratio
`9 avg(p, q) ≥ 7g(q) + 2g(p)` (from the Padé bound for the logarithm) and by
`η₁ = avg(ℓ, 1/q) - g(q) > 0` (`(K - ℓ)(avg(ℓ, K) - g(K))` decreases for `K ≥ 1`). Since `Φ(1) = 0`,
`Φ(q₁) ≥ 0`, which is (S); the alternative `p_S(q₁) ≥ q₁` is excluded by continuity at the crossing
`p_S = q`, where `Φ ≥ 0` would force `η₁ ≤ 0`.

## Main API

* `ss_sec_scale`: `Sec(cA, cB, cP) = Sec(A, B, P)`.
* `ss_gap_ratio`: `7g(q) + 2g(p) ≤ 9 Sec(p, 1, q)` for `0 < p < q ≤ 1`.
* `ss_order_norm`: the normalized strengthened order.
* `ss_order`: `aB/C + (2/7)(B - C) ≤ A` for an actual short bridge.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- **Homogeneity of the secant.** -/
theorem ss_sec_scale {c A B P : ℝ} (hc : 0 < c) (hA : 0 < A) (hB : 0 < B) (hP : 0 < P) :
    m2Sec (c * A) (c * B) (c * P) = m2Sec A B P := by
  by_cases h : A = P
  · subst h
    rw [m2Sec_self, m2Sec_self]
    unfold m2g
    have : A + B ≠ 0 := by positivity
    field_simp
  have h' : c * A ≠ c * P := fun e => h (mul_left_cancel₀ hc.ne' e)
  rw [m2Sec_of_ne h, m2Sec_of_ne h']
  have hAB : A + B ≠ 0 := by positivity
  have hPB : P + B ≠ 0 := by positivity
  have hPA : P - A ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have e1 : (c * P + c * B) / (c * A + c * B) = (P + B) / (A + B) := by
    field_simp
  rw [e1]
  field_simp

/-- `g(1/s) = g(s)`. -/
theorem ss_gB_inv {s : ℝ} (hs : 0 < s) : ss_gB 1 s⁻¹ = ss_gB 1 s := by
  unfold ss_gB
  have : 1 + s ≠ 0 := by positivity
  field_simp
  ring

/-- `g'(s) = (s - 1)/(1 + s)³`. -/
theorem ss_gB_hasDerivAt {s : ℝ} (hs : 0 < s) : HasDerivAt (ss_gB 1) ((s - 1) / (1 + s) ^ 3) s := by
  have h1 : HasDerivAt (fun t : ℝ => 1 + t) 1 s := by simpa using (hasDerivAt_id s).const_add 1
  have h2 : HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + s)) s := by
    have := h1.mul h1
    convert this using 1
    · funext t; simp only [Pi.mul_apply]; ring
    · ring
  have := (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id' s).const_mul 1 |>.div h2
    (by positivity))
  convert this using 1
  · funext t; simp only [ss_gB, Pi.sub_apply, Pi.div_apply]
  · have : 1 + s ≠ 0 := by positivity
    field_simp
    ring

/-- **The gap ratio**: for `0 < p < q ≤ 1`, `η/ξ ≥ 2/7` with `η = avg - g(q)`, `ξ = g(p) - avg`,
i.e. `7g(q) + 2g(p) ≤ 9 avg(p, q)`. -/
theorem ss_gap_ratio {p q : ℝ} (hp : 0 < p) (hpq : p < q) (hq : q ≤ 1) :
    7 * ss_gB 1 q + 2 * ss_gB 1 p ≤ 9 * m2Sec p 1 q := by
  have hupper := ss_gap_ratio_upper hp hpq hq
  have hright : 0 < m2Sec p 1 q - ss_gB 1 q := sub_pos.mpr (ss_sec_gt_right hp hpq hq)
  obtain ⟨_, hden⟩ := ss_gap_limit_pos
  have hlog := ss_log_le_pade3 (z := 2) (by norm_num)
  norm_num at hlog
  have hcap : (Real.log 2 - 1 / 2) / (3 / 4 - Real.log 2) ≤ 7 / 2 := by
    rw [div_le_iff₀ hden]
    linarith only [hlog]
  have hbound := lt_of_lt_of_le hupper hcap
  rw [div_lt_iff₀ hright] at hbound
  linarith only [hbound]

/-- **The turn-norm gap decreases along the continuation**: for `ℓ < 1 ≤ K`,
`(K - ℓ)(avg(ℓ, K) - g(K))` is nonincreasing in `K` (its derivative is `-(K - ℓ) g'(K) ≤ 0`). -/
theorem ss_eta_mono {ℓ K K₁ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hK : 1 ≤ K) (hKK : K ≤ K₁) :
    (K₁ - ℓ) * (m2Sec ℓ 1 K₁ - ss_gB 1 K₁) ≤ (K - ℓ) * (m2Sec ℓ 1 K - ss_gB 1 K) := by
  have hK0 : 0 < K := by linarith
  have hK₁ : 0 < K₁ := by linarith
  have hm := ss_le_of_deriv (x := K) (y := K₁)
    (f := fun t => -(ss_FB 1 t - ss_FB 1 ℓ - (t - ℓ) * ss_gB 1 t))
    (f' := fun t => (t - ℓ) * ((t - 1) / (1 + t) ^ 3)) hKK
    (fun t ht => by
      have ht0 : 0 < t := by linarith [ht.1]
      have := (((ss_FB_hasDerivAt one_pos ht0).sub_const (ss_FB 1 ℓ)).sub
        (((hasDerivAt_id' t).sub_const ℓ).mul (ss_gB_hasDerivAt ht0))).neg
      convert this using 1
      ring)
    (fun t ht => by
      have : 0 ≤ t - ℓ := by linarith [ht.1]
      have : 0 ≤ t - 1 := by linarith [ht.1]
      have : 0 < 1 + t := by linarith [ht.1]
      positivity)
  have e1 := ss_sec_mul hℓ one_pos hK0
  have e2 := ss_sec_mul hℓ one_pos hK₁
  have : (K - ℓ) * (m2Sec ℓ 1 K - ss_gB 1 K) = ss_FB 1 K - ss_FB 1 ℓ - (K - ℓ) * ss_gB 1 K := by
    rw [mul_sub, e1]
  have : (K₁ - ℓ) * (m2Sec ℓ 1 K₁ - ss_gB 1 K₁) = ss_FB 1 K₁ - ss_FB 1 ℓ - (K₁ - ℓ) * ss_gB 1 K₁ := by
    rw [mul_sub, e2]
  linarith

/-- **The strengthened order (S), normalized**: with `g = ss_gB 1` and `avg(p, q) = Sec(p, 1, q)`,
if `0 < ℓ < 1`, `0 < p₁ < q₁ ≤ 1` and `avg(ℓ, 1/q₁) = avg(p₁, q₁)`, then
`p₁ ≥ ℓ + (2/7)(1 - q₁)`. -/
theorem ss_order_norm {ℓ p₁ q₁ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ < 1) (hp : 0 < p₁) (hpq : p₁ < q₁)
    (hq1 : q₁ ≤ 1) (heq : m2Sec ℓ 1 q₁⁻¹ = m2Sec p₁ 1 q₁) : ℓ + 2 / 7 * (1 - q₁) ≤ p₁ := by
  have hq₁ : 0 < q₁ := by linarith
  -- the gap `η₁` stays positive on `[q₁, 1]`
  have hη : ∀ q, q₁ ≤ q → q ≤ 1 → ss_gB 1 q < m2Sec ℓ 1 q⁻¹ := by
    intro q hq hq'
    have hq0 : 0 < q := by linarith
    have h0 : ss_gB 1 q₁ < m2Sec ℓ 1 q₁⁻¹ := heq ▸ ss_sec_gt_right hp hpq hq1
    have hK : 1 ≤ q⁻¹ := (one_le_inv₀ hq0).2 hq'
    have hKK : q⁻¹ ≤ q₁⁻¹ := inv_anti₀ hq₁ hq
    have hm := ss_eta_mono hℓ hℓ1 hK hKK
    rw [ss_gB_inv hq₁, ss_gB_inv hq0] at hm
    have hd₁ : 0 < q₁⁻¹ - ℓ := by linarith
    have hd : 0 < q⁻¹ - ℓ := by linarith
    have hpos : 0 < (q₁⁻¹ - ℓ) * (m2Sec ℓ 1 q₁⁻¹ - ss_gB 1 q₁) := mul_pos hd₁ (by linarith)
    have := (mul_pos_iff_of_pos_left hd).1 (lt_of_lt_of_le hpos hm)
    linarith
  set qs := (7 * ℓ + 2) / 9 with hqs
  have hqs1 : qs < 1 := by rw [hqs]; linarith
  have hqs0 : 0 < qs := by positivity
  -- the comparison function and its closed form
  have hpS : ∀ z, z ≤ 1 → 0 < ℓ + 2 / 7 * (1 - z) := fun z hz => by nlinarith
  have hD2 : ∀ z, qs < z → 0 < z - (ℓ + 2 / 7 * (1 - z)) := fun z hz => by rw [hqs] at hz; linarith
  have hD1 : ∀ z, 0 < z → z ≤ 1 → 0 < z⁻¹ - ℓ := fun z hz hz' => by
    have := (one_le_inv₀ hz).2 hz'; linarith
  have hN1d : ∀ z, 0 < z → HasDerivAt (fun z => ss_FB 1 z⁻¹ - ss_FB 1 ℓ)
      (ss_gB 1 z⁻¹ * (-(z ^ 2)⁻¹)) z := fun z hz =>
    ((ss_FB_hasDerivAt one_pos (inv_pos.2 hz)).comp z (hasDerivAt_inv hz.ne')).sub_const _
  have hD1d : ∀ z, 0 < z → HasDerivAt (fun z : ℝ => z⁻¹ - ℓ) (-(z ^ 2)⁻¹) z := fun z hz =>
    (hasDerivAt_inv hz.ne').sub_const ℓ
  have hpSd : ∀ z : ℝ, HasDerivAt (fun z : ℝ => ℓ + 2 / 7 * (1 - z)) (-(2 / 7)) z := fun z => by
    have := (((hasDerivAt_id' z).const_sub 1).const_mul (2 / 7 : ℝ)).const_add ℓ
    convert this using 1; ring
  have key : ∀ q, q₁ ≤ q → qs < q → q ≤ 1 →
      m2Sec ℓ 1 q⁻¹ ≤ m2Sec (ℓ + 2 / 7 * (1 - q)) 1 q := by
    intro q hq hqq hq'
    have hΦ : ∀ z, qs < z → z ≤ 1 →
        (ss_FB 1 z - ss_FB 1 (ℓ + 2 / 7 * (1 - z))) / (z - (ℓ + 2 / 7 * (1 - z))) -
          (ss_FB 1 z⁻¹ - ss_FB 1 ℓ) / (z⁻¹ - ℓ) =
        m2Sec (ℓ + 2 / 7 * (1 - z)) 1 z - m2Sec ℓ 1 z⁻¹ := by
      intro z hz hz'
      have hz0 : 0 < z := by linarith
      have e2 := ss_sec_mul (hpS z hz') one_pos hz0
      have e1 := ss_sec_mul hℓ one_pos (inv_pos.2 hz0)
      rw [← e2, ← e1, mul_div_cancel_left₀ _ (hD2 z hz).ne',
        mul_div_cancel_left₀ _ (hD1 z hz0 hz').ne']
    have hmono := ss_le_of_deriv (x := q) (y := 1)
      (f := fun z => -((ss_FB 1 z - ss_FB 1 (ℓ + 2 / 7 * (1 - z))) / (z - (ℓ + 2 / 7 * (1 - z))) -
          (ss_FB 1 z⁻¹ - ss_FB 1 ℓ) / (z⁻¹ - ℓ)))
      (f' := fun z => -((((ss_gB 1 z - ss_gB 1 (ℓ + 2 / 7 * (1 - z)) * (-(2 / 7))) *
            (z - (ℓ + 2 / 7 * (1 - z))) -
            (ss_FB 1 z - ss_FB 1 (ℓ + 2 / 7 * (1 - z))) * (1 - -(2 / 7))) /
              (z - (ℓ + 2 / 7 * (1 - z))) ^ 2) -
          ((ss_gB 1 z⁻¹ * (-(z ^ 2)⁻¹) * (z⁻¹ - ℓ) - (ss_FB 1 z⁻¹ - ss_FB 1 ℓ) * (-(z ^ 2)⁻¹)) /
            (z⁻¹ - ℓ) ^ 2))) hq'
      (fun z hz => by
        have hzq : qs < z := lt_of_lt_of_le hqq hz.1
        have hz0 : 0 < z := by linarith
        have hc := (ss_FB_hasDerivAt one_pos (hpS z hz.2)).comp z (hpSd z)
        have hN2d := (ss_FB_hasDerivAt one_pos hz0).sub hc
        have hD2d := (hasDerivAt_id' z).sub (hpSd z)
        have := ((hN2d.div hD2d (hD2 z hzq).ne').sub
          ((hN1d z hz0).div (hD1d z hz0) (hD1 z hz0 hz.2).ne')).neg
        convert this using 1
        · funext w
          simp only [Pi.neg_apply, Pi.sub_apply, Pi.div_apply, Function.comp_apply]
        · simp only [Pi.sub_apply, Function.comp_apply])
      (fun z hz => by
        have hzq : qs < z := lt_of_lt_of_le hqq hz.1.le
        have hz0 : 0 < z := by linarith
        have hz1 : z ≤ 1 := hz.2.le
        have hgap := ss_gap_ratio (hpS z hz1) (by linarith [hD2 z hzq]) hz1
        have hηz := hη z (le_trans hq hz.1.le) hz1
        have e2 := ss_sec_mul (hpS z hz1) one_pos hz0
        have e1 := ss_sec_mul hℓ one_pos (inv_pos.2 hz0)
        have d2 := hD2 z hzq
        have d1 := hD1 z hz0 hz1
        rw [ss_gB_inv hz0]
        set a2 := m2Sec (ℓ + 2 / 7 * (1 - z)) 1 z
        set a1 := m2Sec ℓ 1 z⁻¹
        set D2 := z - (ℓ + 2 / 7 * (1 - z))
        set D1 := z⁻¹ - ℓ
        rw [← e2, ← e1]
        have e : -((((ss_gB 1 z - ss_gB 1 (ℓ + 2 / 7 * (1 - z)) * (-(2 / 7))) * D2 -
            D2 * a2 * (1 - -(2 / 7))) / D2 ^ 2) -
            ((ss_gB 1 z * (-(z ^ 2)⁻¹) * D1 - D1 * a1 * (-(z ^ 2)⁻¹)) / D1 ^ 2)) =
            (9 / 7 * a2 - ss_gB 1 z - 2 / 7 * ss_gB 1 (ℓ + 2 / 7 * (1 - z))) / D2 +
              (z ^ 2)⁻¹ * (a1 - ss_gB 1 z) / D1 := by
          field_simp
          ring
        rw [e]
        have t1 : 0 ≤ (9 / 7 * a2 - ss_gB 1 z - 2 / 7 * ss_gB 1 (ℓ + 2 / 7 * (1 - z))) / D2 :=
          div_nonneg (by linarith) d2.le
        have t2 : 0 ≤ (z ^ 2)⁻¹ * (a1 - ss_gB 1 z) / D1 :=
          div_nonneg (mul_nonneg (by positivity) (by linarith)) d1.le
        linarith)
    have h1 : (ss_FB 1 1 - ss_FB 1 (ℓ + 2 / 7 * (1 - 1))) / (1 - (ℓ + 2 / 7 * (1 - 1))) -
        (ss_FB 1 1⁻¹ - ss_FB 1 ℓ) / (1⁻¹ - ℓ) = 0 := by
      simp only [sub_self, mul_zero, add_zero, inv_one]
    have hq0 := hΦ q hqq hq'
    linarith
  rcases lt_or_ge qs q₁ with hcase | hcase
  · -- `p_S(q₁) < q₁`: compare the averages over `[p₁, q₁]` and `[p_S, q₁]`
    have h1 := key q₁ le_rfl hcase hq1
    rw [heq] at h1
    by_contra hcon
    push Not at hcon
    have hpS0 := hpS q₁ hq1
    have hpSq : ℓ + 2 / 7 * (1 - q₁) < q₁ := by linarith [hD2 q₁ hcase]
    have hadd := ss_sec_add hp one_pos hpS0 hq₁
    have hA := ss_sec_gt_right (B := 1) hp hcon (by linarith)
    have hB := ss_sec_le_left hpS0 hpSq.le hq1
    have k1 : (ℓ + 2 / 7 * (1 - q₁) - p₁) * ss_gB 1 (ℓ + 2 / 7 * (1 - q₁)) <
        (ℓ + 2 / 7 * (1 - q₁) - p₁) * m2Sec p₁ 1 (ℓ + 2 / 7 * (1 - q₁)) :=
      mul_lt_mul_of_pos_left hA (by linarith)
    have k2 : (q₁ - (ℓ + 2 / 7 * (1 - q₁))) * m2Sec (ℓ + 2 / 7 * (1 - q₁)) 1 q₁ ≤
        (q₁ - (ℓ + 2 / 7 * (1 - q₁))) * ss_gB 1 (ℓ + 2 / 7 * (1 - q₁)) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    have k3 : (q₁ - p₁) * m2Sec p₁ 1 q₁ ≤ (q₁ - p₁) * m2Sec (ℓ + 2 / 7 * (1 - q₁)) 1 q₁ :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith
  · -- `p_S(q₁) ≥ q₁` is impossible: at the crossing `q_s`, `Φ ≥ 0` would force `η₁(q_s) ≤ 0`
    exfalso
    have hη0 := hη qs hcase hqs1.le
    have hle : ∀ z ∈ Ioo qs 1, m2Sec ℓ 1 z⁻¹ ≤ ss_gB 1 (ℓ + 2 / 7 * (1 - z)) := by
      intro z hz
      have := key z (le_trans hcase hz.1.le) hz.1 hz.2.le
      exact this.trans (ss_sec_le_left (hpS z hz.2.le) (by linarith [hD2 z hz.1]) hz.2.le)
    have hcl : closure (Ioo qs 1) = Icc qs 1 := closure_Ioo hqs1.ne
    have hFc : ContinuousOn (fun z => m2Sec ℓ 1 z⁻¹) (closure (Ioo qs 1)) := by
      rw [hcl]
      refine ContinuousOn.congr (f := fun z => (ss_FB 1 z⁻¹ - ss_FB 1 ℓ) / (z⁻¹ - ℓ)) ?_ ?_
      · intro z hz
        have hz0 : 0 < z := by linarith [hz.1]
        exact ((hN1d z hz0).div (hD1d z hz0)
          (hD1 z hz0 hz.2).ne').continuousAt.continuousWithinAt
      · intro z hz
        have hz0 : 0 < z := by linarith [hz.1]
        have e1 := ss_sec_mul hℓ one_pos (inv_pos.2 hz0)
        simp only
        rw [← e1, mul_div_cancel_left₀ _ (hD1 z hz0 hz.2).ne']
    have hGc : ContinuousOn (fun z => ss_gB 1 (ℓ + 2 / 7 * (1 - z))) (closure (Ioo qs 1)) := by
      rw [hcl]
      intro z hz
      exact ((ss_gB_hasDerivAt (hpS z hz.2)).comp z (hpSd z)).continuousAt.continuousWithinAt
    have hx := le_on_closure hle hFc hGc (by rw [hcl]; exact left_mem_Icc.2 hqs1.le)
    have e : ℓ + 2 / 7 * (1 - qs) = qs := by rw [hqs]; ring
    simp only [e] at hx
    linarith

/-- **The strengthened order (S)**: for a short bridge `a < C ≤ B`, `0 < A < C` with equal turn
secants `Sec(a, C, B) = Sec(C, B, A)`, `aB/C + (2/7)(B - C) ≤ A`. -/
theorem ss_order {a A B C : ℝ} (ha : 0 < a) (haC : a < C) (hA : 0 < A) (hAC : A < C)
    (hCB : C ≤ B) (heq : m2Sec a C B = m2Sec C B A) : a * B / C + 2 / 7 * (B - C) ≤ A := by
  have hC : 0 < C := by linarith
  have hB : 0 < B := by linarith
  have s1 : m2Sec a C B = m2Sec (a / C) 1 (C / B)⁻¹ := by
    have := ss_sec_scale (c := 1 / C) (by positivity) ha hC hB
    rw [← this]
    congr 1 <;> field_simp
  have s2 : m2Sec C B A = m2Sec (A / B) 1 (C / B) := by
    rw [m2Sec_comm]
    have := ss_sec_scale (c := 1 / B) (by positivity) hA hB hC
    rw [← this]
    congr 1 <;> field_simp
  rw [s1, s2] at heq
  have h := ss_order_norm (div_pos ha hC) ((div_lt_one hC).2 haC) (div_pos hA hB)
    (div_lt_div_of_pos_right hAC hB) ((div_le_one hB).2 hCB) heq
  have e : a * B / C + 2 / 7 * (B - C) = B * (a / C + 2 / 7 * (1 - C / B)) := by
    field_simp
  rw [e]
  have := mul_le_mul_of_nonneg_left h hB.le
  rwa [mul_div_cancel₀ _ hB.ne'] at this

end SmoothedOctagon
