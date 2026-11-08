module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S3Leaves
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandCentral
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3HandOuter

/-!
# Gate S3: the displacement bound `δ < 1/19`

On `2 ≤ x ≤ 13/6` a displacement `δ = β/x - 1 ≥ 1/19` is excluded: the weighted envelope is
nonnegative at the actual root, the scale reduction carries a nonnegative duration test to the scale
`q* = min{q_c, 1/7}`, and the central or outer face sign contradicts it. The leaves are in
`S3Leaves.lean`; the central and outer face signs are the hand proofs `hs3_central_alpha_proof`
(`Heavy/S3HandCentral.lean`) and `hs3_outer_face_proof` (`Heavy/S3HandOuter.lean`). Both are stated
on the caller's shapes: the central sign assumes the central cap `6α² ≤ x(x + 2)`, the outer sign
assumes `x(x + 2) ≤ 6α²` and the lower short-order slope `g ≥ 8/(9x + 8)`.

## Main API

* `HsData.s3`, `M2Short.hs_S3`: on `2 ≤ x ≤ 13/6`, `δ = β/x - 1 < 1/19`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### Gate S3 -/

/-- `D > 0` on the S3 domain:
`D ≥ 5α² - 4αx + 1 + 2x ≥ 6 - 2x` from `β < 2α`. -/
private lemma hs3_D_pos {x be al : ℝ} (hx2 : x ≤ 13 / 6) (hal : 1 ≤ al)
    (hax : al ≤ x) (hb2 : be < 2 * al) : 0 < hsDg x be al := by
  rw [hsDg]
  have h1 : be * (x - al) ≤ 2 * al * (x - al) := mul_le_mul_of_nonneg_right hb2.le (by linarith)
  have h2 : 0 ≤ (al - 1) * (5 * al + 5 - 4 * x) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- `V̄(x) ≤ 19/25` on `2 ≤ x ≤ 13/6`. -/
private lemma hs3_Vbar_le {x : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) : hsVbar x ≤ 19 / 25 := by
  rw [hsVbar]
  have : 2 * (x - 1) ^ 2 / ((x + 1) * (35 * x + 13)) ≤ 1 / 100 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-- The duration weight at `τ = 2` stays below `T + 1` (`kT² - (k + 16)T + 24 > 0`, with
discriminant `k² - 64k + 256 < 0` for `9/2 ≤ k ≤ 59/6`). -/
private lemma hs3_n0_le {k T : ℝ} (hk : 9 / 2 ≤ k) (hk' : k ≤ 59 / 6) (hT : 0 < T) :
    2 + 4 * (4 - 3 * (2 / T)) / k ≤ T + 1 := by
  have hk0 : 0 < k := by linarith
  have e : 2 + 4 * (4 - 3 * (2 / T)) / k = (2 * k * T + 16 * T - 24) / (k * T) := by
    field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  have h4 : 0 ≤ (2 * k * T - (k + 16)) ^ 2 := sq_nonneg _
  have h5 : 0 ≤ (k - 9 / 2) * (59 / 6 - k) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The central boundary stays in the central-beta domain: for `α > a_min(x)` and `6α² ≤ x(x + 2)`:
`b(x, α) ≤ 2α`, `b(x, α) ≤ x + 5x(α - 1)/13` and `α ≤ (5x + 4)/12 ≤ 89/72`. -/
private lemma hs3_b_facts {x al : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hamin : hs3amin x < al)
    (h6 : 6 * al ^ 2 ≤ x * (x + 2)) :
    hs3b x al ≤ 2 * al ∧ hs3b x al ≤ x + 5 * x * (al - 1) / 13 ∧ al ≤ 89 / 72 := by
  rw [hs3amin] at hamin
  have h36 : 0 < 15 * x + 36 := by linarith
  have hal1 : 1 ≤ al := by
    have : 1 ≤ (15 * x + 511) / 475 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  have hB : 25 * x / (15 * x + 36) ≤ 5 * x / 13 := by
    rw [div_le_div_iff₀ h36 (by norm_num)]; nlinarith
  have hb' : hs3b x al ≤ x + 5 * x * (al - 1) / 13 := by
    rw [hs3b]
    have := mul_le_mul_of_nonneg_right hB (by linarith : (0 : ℝ) ≤ al - 1)
    have e : 5 * x / 13 * (al - 1) = 5 * x * (al - 1) / 13 := by ring
    linarith
  refine ⟨?_, hb', ?_⟩
  · rw [hs3b]
    have e : (2 * al - (x + 25 * x / (15 * x + 36) * (al - 1))) * (15 * x + 36) =
        al * (5 * x + 72) - 15 * x ^ 2 - 11 * x := by field_simp; ring
    have h1 : (15 * x + 511) * (5 * x + 72) ≤ 475 * al * (5 * x + 72) := by
      have : 15 * x + 511 ≤ 475 * al := by
        rw [div_lt_iff₀ (by norm_num)] at hamin; linarith
      nlinarith
    have h2 : 0 ≤ (2 * al - (x + 25 * x / (15 * x + 36) * (al - 1))) * (15 * x + 36) := by
      rw [e]; nlinarith
    have := nonneg_of_mul_nonneg_left h2 h36
    linarith
  · have := hs3_al_le (by linarith) h6
    linarith

/-- Raising the incoming norm in both duration tests (`hs3_uslope` with `n₀, n₁ ≤ T + 1`). -/
private lemma hs3_gate_us {x be al u ub qs : ℝ} (h1 : 2 ≤ x) (h2 : x ≤ 13 / 6) (h108 : 108 / 95 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hD0 : 0 < hsDg x be al) (hDQ : hsDg x be al < al * (al + be))
    (hD3 : hsDg x be al < 3 * al ^ 2) (hrA3 : 1 / 3 < hsRA al be) (hrA13 : hsRA al be ≤ 13 / 30)
    (hqs0 : 0 < qs) (hqs7 : qs ≤ 1 / 7) (hub : u ≤ ub) :
    hs3F0 x be al u qs ≤ hs3F0 x be al ub qs ∧ hs3F1 x be al u qs ≤ hs3F1 x be al ub qs := by
  have hk0 : 0 < 5 * al - 1 := by linarith
  have hk4 : 4 ≤ 5 * al - 1 := by linarith
  have hrA0 : 0 < hsRA al be := by linarith
  have hT : 0 < hsRA al be / qs := by positivity
  have hn0 : 0 ≤ 2 + 4 * (4 - 3 * (2 * qs / hsRA al be)) / (5 * al - 1) := by
    have : 2 * qs / hsRA al be ≤ 1 := by rw [div_le_one hrA0]; linarith
    have : 0 ≤ 4 * (4 - 3 * (2 * qs / hsRA al be)) / (5 * al - 1) := div_nonneg (by linarith) hk0.le
    linarith
  have hn0T : 2 + 4 * (4 - 3 * (2 * qs / hsRA al be)) / (5 * al - 1) ≤ hsRA al be / qs + 1 := by
    have h := hs3_n0_le (k := 5 * al - 1) (T := hsRA al be / qs) (by linarith) (by linarith) hT
    have e : 2 / (hsRA al be / qs) = 2 * qs / hsRA al be := by field_simp
    rwa [e] at h
  have h4k : 4 / (5 * al - 1) ≤ 1 := by rw [div_le_one hk0]; exact hk4
  exact ⟨hs3_uslope h1 h2 (by linarith) hax hxb hD0 hDQ hD3 hqs0 hqs7 hrA13 hn0 hn0T hub,
    hs3_uslope h1 h2 (by linarith) hax hxb hD0 hDQ hD3 hqs0 hqs7 hrA13 (by positivity)
      (by linarith) hub⟩

/-- **The scale reduction**: if the weighted envelope `Φ` at the actual normalized
duration `p = τq` is nonnegative at the actual scale `q` and negative at `0`, then at every scale
`q* ∈ [q, 1/7]` one of the duration tests is nonnegative. -/
private lemma hs3_gate_max {x be al u q τ qs : ℝ} (h1 : 2 ≤ x) (h2 : x ≤ 13 / 6) (hal1 : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hrA3 : 1 / 3 < hsRA al be) (hu34 : 3 / 4 ≤ u)
    (hu1925 : u ≤ 19 / 25) (hD0 : 0 < hsDg x be al) (hD3 : hsDg x be al < 3 * al ^ 2)
    (h108 : 108 / 95 ≤ al) (hq0 : 0 < q) (hτ2 : 2 ≤ τ) (hpr : τ * q ≤ hsRA al be)
    (hG : 0 ≤ hsPhi x be al u (τ * q) (4 * (4 - 3 * (τ * q / hsRA al be)) / (5 * al - 1)) q)
    (hΦ0 : hsPhi x be al u (τ * q) (4 * (4 - 3 * (τ * q / hsRA al be)) / (5 * al - 1)) 0 < 0)
    (hA2 : 0 < hsA2 x be al u) (hqs0 : 0 < qs) (hqs7 : qs ≤ 1 / 7) (hqqs : q ≤ qs) :
    0 ≤ max (hs3F0 x be al u qs) (hs3F1 x be al u qs) := by
  have hbe0 : 0 < be := by linarith
  have hk0 : 0 < 5 * al - 1 := by linarith
  have hp0 : 0 < τ * q := by positivity
  have h2qp : 2 * q ≤ τ * q := by nlinarith
  have h2qs : 2 * qs ≤ hsRA al be := by linarith
  have hm0 : 0 ≤ 4 * (4 - 3 * (τ * q / hsRA al be)) / (5 * al - 1) := by
    have : τ * q / hsRA al be ≤ 1 := by rw [div_le_one (by linarith)]; exact hpr
    exact div_nonneg (by linarith) hk0.le
  generalize τ * q = p at hp0 h2qp hpr hG hΦ0 hm0
  generalize hm : 4 * (4 - 3 * (p / hsRA al be)) / (5 * al - 1) = m at hG hΦ0 hm0
  have hconv := hs_phi_convex_max (x := x) (be := be) (al := al) (u := u) (p := p)
    (qm := min qs (p / 2)) hm0 hA2.le hq0.le (le_min hqqs (by linarith))
  have hΦm : 0 ≤ hsPhi x be al u p m (min qs (p / 2)) := by
    by_contra hneg
    have := max_lt hΦ0 (not_le.mp hneg)
    linarith
  rcases lt_or_ge (p / 2) qs with hlt | hge
  · rw [min_eq_right hlt.le] at hΦm
    have e := hs_phi_eq (x := x) (be := be) (al := al) (u := u) (m := m) hp0
      (by positivity : (0 : ℝ) < p / 2)
    have e2 : p / (p / 2) = 2 := by field_simp
    rw [e2] at e
    have hc := hs3_tau2_cont (u := u) (q₁ := p / 2) (q₂ := qs) h1 h2 (by linarith) hax hxb
      hrA3.le hu34 hu1925 hD0 hD3 (by positivity) hlt hqs7
    have e3 : 2 * (p / 2) = p := by ring
    rw [e3, hm] at hc
    have hd := hs3_dur (x := x) (u := u) (τ := 2) hal1 hbe0 hqs0 le_rfl h2qs
    linarith
  · rw [min_eq_left hge] at hΦm
    have e := hs_phi_eq (x := x) (be := be) (al := al) (u := u) (m := m) hp0 hqs0
    have hτ' : 2 ≤ p / qs := by rw [le_div_iff₀ hqs0]; linarith
    have hd := hs3_dur (x := x) (u := u) (τ := p / qs) hal1 hbe0 hqs0 hτ'
      (by rw [div_mul_cancel₀ _ hqs0.ne']; exact hpr)
    rw [div_mul_cancel₀ _ hqs0.ne', hm] at hd
    linarith

/-- **The central face** `q* = q_c ≤ 1/7`: both duration tests are negative,
`F_i(u) ≤ F_i(ū(x, β)) ≤ F_i(ū(x, b), b) < 0`, by the central ceiling, the monotonicity in `β` and
the central sign `hs3_central_alpha_proof`. -/
private lemma hs3_gate_central {x be al u : ℝ} (h1 : 2 ≤ x) (h2 : x ≤ 13 / 6) (hal1 : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hδ : 1 / 19 ≤ be / x - 1)
    (hQ : 1 + ((4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) + 1 / 23) * (be / x - 1) ≤ al)
    (h108 : 108 / 95 ≤ al) (hb2a : be < 2 * al) (hDQ : hsDg x be al < al * (al + be))
    (hD3 : hsDg x be al < 3 * al ^ 2) (hrA13 : hsRA al be ≤ 13 / 30) (hu : u = m2Sec 1 x be)
    (hqc7 : hsQc x al ≤ 1 / 7) (hM : 0 ≤ max (hs3F0 x be al u (hsQc x al)) (hs3F1 x be al u (hsQc x al))) :
    False := by
  have hx0 : 0 < x := by linarith
  have hqc0 : 0 < hsQc x al := by rw [hsQc]; positivity
  have h6 : 6 * al ^ 2 ≤ x * (x + 2) := (hs_qc_le_iff hx0).1 hqc7
  obtain ⟨hamin, hbb⟩ := hs3_central_straight h1 h2 hδ hQ
  obtain ⟨hb2, hb2', -⟩ := hs3_b_facts h1 h2 hamin h6
  have hb20 : 20 * x / 19 ≤ be := by
    rw [div_le_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left hδ hx0.le
    have e : x * (be / x - 1) = be - x := by field_simp
    linarith
  have hb' : be ≤ x + 5 * x * (al - 1) / 13 := hbb.le.trans hb2'
  have hrA3 : 1 / 3 < hsRA al be := by
    rw [hsRA, lt_div_iff₀ (by linarith)]; linarith
  have huc : u ≤ hsUCB x be := by rw [hu]; exact hs3_central_ceiling h1 h2 h108 h6 hb20 hb'
  obtain ⟨hu0, hu1⟩ := hs3_gate_us h1 h2 h108 hax hxb (hs3_D_pos h2 hal1 hax hb2a) hDQ hD3
    hrA3 hrA13 hqc0 hqc7 huc
  obtain ⟨hβ0, hβ1⟩ := hs3_beta_mono h1 h2 h108 h6 hb20 hbb.le hb2 hb2'
  obtain ⟨hF0, hF1⟩ := hs3_central_alpha_proof h1 h2 hamin.le h6
  have := max_lt (hu0.trans_lt (hβ0.trans_lt hF0)) (hu1.trans_lt (hβ1.trans_lt hF1))
  linarith

/-- **The outer face** `q* = 1/7 < q_c`: both duration tests are negative, by the outer ceiling and
the outer sign `hs3_outer_face_proof` on the enclosing outer domain. -/
private lemma hs3_gate_outer {x be al u : ℝ} (h1 : 2 ≤ x) (h2 : x ≤ 13 / 6) (hal1 : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hδ : 1 / 19 ≤ be / x - 1)
    (hU : x * (9 * x + 8 * al) / (9 * x + 8) ≤ be)
    (hQ : 1 + ((4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) + 1 / 23) * (be / x - 1) ≤ al)
    (h108 : 108 / 95 ≤ al) (hb2a : be < 2 * al) (hDQ : hsDg x be al < al * (al + be))
    (hD3 : hsDg x be al < 3 * al ^ 2) (hrA13 : hsRA al be ≤ 13 / 30) (hu : u = m2Sec 1 x be)
    (hqc7 : 1 / 7 < hsQc x al) (hM : 0 ≤ max (hs3F0 x be al u (1 / 7)) (hs3F1 x be al u (1 / 7))) :
    False := by
  have hx0 : 0 < x := by linarith
  have h6 : x * (x + 2) ≤ 6 * al ^ 2 := by
    rw [hsQc, lt_div_iff₀ (by positivity)] at hqc7
    linarith
  obtain ⟨-, -, hg2⟩ := hs3_outer_enclose h1 h2 hax h6 hU hδ hQ
  have hα1 : 0 < al - 1 := by linarith
  -- the retained lower short-order slope `g ≥ 8/(9x + 8)`
  have hg8 : 8 / (9 * x + 8) ≤ (be / x - 1) / (al - 1) := by
    have hU' : x * (9 * x + 8 * al) ≤ be * (9 * x + 8) := by
      rwa [div_le_iff₀ (by positivity)] at hU
    have hbx : be = x * (1 + (be / x - 1)) := by field_simp; ring
    rw [hbx, mul_assoc] at hU'
    have h9 : 9 * x + 8 * al ≤ (1 + (be / x - 1)) * (9 * x + 8) := le_of_mul_le_mul_left hU' hx0
    rw [div_le_div_iff₀ (by positivity) hα1]
    linarith
  have hbg : x * (1 + (be / x - 1) / (al - 1) * (al - 1)) = be := by
    rw [div_mul_cancel₀ _ hα1.ne']; field_simp; ring
  have hbo : be ≤ x + 5 * x * (x - 1) / 13 := by
    have hc : 13 / 5 ≤ (4 * x ^ 2 + 11 * x + 1) / (7 * x + 1) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have h13 : 13 / 5 * (be / x - 1) ≤ al - 1 := by
      have := mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ be / x - 1)
      have : 0 ≤ 1 / 23 * (be / x - 1) := by positivity
      nlinarith
    have e : x * (be / x - 1) = be - x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h13 hx0.le]
  have hrA3 : 1 / 3 < hsRA al be := by
    rw [hsRA, lt_div_iff₀ (by linarith)]; linarith
  have huo : u ≤ hsUO x be := by rw [hu]; exact hs3_outer_ceiling h1 h2 hxb hbo
  obtain ⟨hu0, hu1⟩ := hs3_gate_us h1 h2 h108 hax hxb (hs3_D_pos h2 hal1 hax hb2a) hDQ hD3
    hrA3 hrA13 (by norm_num) le_rfl huo
  obtain ⟨hF0, hF1⟩ := hs3_outer_face_proof h1 h2 hal1 hax h6 hg8 hg2
  rw [hbg] at hF0 hF1
  have := max_lt (hu0.trans_lt hF0) (hu1.trans_lt hF1)
  linarith

namespace HsData

variable (H : HsData)

/-- The order inputs of gate S3 at the actual shape (`hs_strong_order`, `hs_upper_order_98`,
`hs_quad_order` with `δ²/(1 + 4δ) ≥ δ/23` for `δ ≥ 1/19`). -/
private lemma hs3_orders (h1 : 2 ≤ H.x) (h2 : H.x ≤ 13 / 6) (hδ : 1 / 19 ≤ H.be / H.x - 1) :
    1 + (4 * H.x ^ 2 + 11 * H.x + 1) / (7 * H.x + 1) * (H.be / H.x - 1) ≤ H.al ∧
      H.x * (9 * H.x + 8 * H.al) / (9 * H.x + 8) ≤ H.be ∧
      1 + ((4 * H.x ^ 2 + 11 * H.x + 1) / (7 * H.x + 1) + 1 / 23) * (H.be / H.x - 1) ≤ H.al := by
  have hx0 : 0 < H.x := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have h := H.strong_order
    have e : H.be / H.x + hsKs H.x * (H.be - H.x) =
        1 + (4 * H.x ^ 2 + 11 * H.x + 1) / (7 * H.x + 1) * (H.be / H.x - 1) := by
      rw [hsKs]; field_simp; ring
    linarith
  · have h := mul_le_mul_of_nonneg_left (H.upper_order_98 (by linarith)) (by linarith : 0 ≤ 8 * H.x)
    have e : 8 * H.x * (H.be / H.x + 9 / 8 * (H.be - H.x)) = 8 * H.be + 9 * H.x * (H.be - H.x) := by
      field_simp
    rw [div_le_iff₀ (by linarith)]
    linarith
  · have h := hs_quad_order h1 h2 H.one_le_al H.al_lt_x H.x_le_be (H.u_eq.symm.trans H.u_eq')
    have : (H.be / H.x - 1) / 23 ≤ (H.be / H.x - 1) ^ 2 / (1 + 4 * (H.be / H.x - 1)) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
    linarith

/-- `q = ρ_A > 0` at the actual data. -/
private lemma hs3_q_pos : 0 < hsQ H.al H.rho := by
  have hden : 0 < 1 + H.rho * (H.al ^ 2 - 1) := by
    have : 0 ≤ H.al ^ 2 - 1 := by nlinarith [H.one_le_al]
    have := H.rho_pos
    positivity
  have hLam : 0 < hsLam H.al H.rho := by rw [hsLam]; exact one_div_pos.mpr hden
  rw [hsQ]
  have := H.one_le_al
  exact mul_pos (mul_pos (by positivity) hLam) H.rho_pos

/-- **The weighted envelope at the actual root**: `0 ≤ Φ(q)` at `p = τq`,
`m = 4(4 - 3p/r_A)/(5α - 1)` (`root_zero`, `w ≥ 3/4`, `hs_env_weighted` with `hs3_B_pos`,
`hs_env_scale`, `hs_phi_eq`). -/
private lemma hs3_env (h1 : 2 ≤ H.x) :
    0 ≤ hsPhi H.x H.be H.al H.u (H.τ * hsQ H.al H.rho)
      (4 * (4 - 3 * (H.τ * hsQ H.al H.rho / hsRA H.al H.be)) / (5 * H.al - 1)) (hsQ H.al H.rho) := by
  have hx1 : 1 < H.x := H.one_lt_x
  have hx0 : 0 < H.x := by linarith
  have hal1 : 1 ≤ H.al := H.one_le_al
  have hq0 := H.hs3_q_pos
  have hq7 : hsQ H.al H.rho < 1 / 7 := H.q_lt_seventh
  have hτ2 : 2 < H.τ := H.two_lt_τ
  have hτT : H.τ * hsQ H.al H.rho < hsRA H.al H.be := H.τ_lt
  have hrA0 : 0 < hsRA H.al H.be := by
    rw [hsRA]; have := H.x_le_be; apply div_pos <;> linarith
  have hk0 : 0 < 5 * H.al - 1 := by linarith
  have hm0 : 0 ≤ 4 * (4 - 3 * (H.τ * hsQ H.al H.rho / hsRA H.al H.be)) / (5 * H.al - 1) := by
    have : H.τ * hsQ H.al H.rho / hsRA H.al H.be ≤ 1 := by rw [div_le_one hrA0]; exact hτT.le
    apply div_nonneg _ hk0.le
    linarith
  have ht0 : H.rho * (1 + H.x) ≤ H.t := by
    have h := H.rho_lt_rt
    rw [one_div_mul_eq_div, lt_div_iff₀ (by linarith)] at h
    exact h.le
  have henv := hs_env_weighted (u := H.u) (τ := H.τ)
    (m := 4 * (4 - 3 * (H.τ * hsQ H.al H.rho / hsRA H.al H.be)) / (5 * H.al - 1))
    hx1 hal1 H.rho_pos ht0 H.t_le_r H.v_le
    (fun s hs => hs3_B_pos h1 hal1 H.al_lt_x.le H.x_le_be H.rho_pos hs.1 hτ2.le hτT.le)
  rw [H.root_zero, ← H.w_eq] at henv
  have hρq : hsRhoOf H.al (hsQ H.al H.rho) = H.rho :=
    (hs_scale_coords (x := H.x) (be := H.be) hal1 H.rho_pos).1
  obtain ⟨e1, -, e3, -⟩ := hs_env_scale (x := H.x) (be := H.be) (al := H.al) (u := H.u)
    (q := hsQ H.al H.rho) (τ := H.τ) hx0 hal1 hq0 (by linarith)
  rw [hρq] at e1 e3
  rw [e1, e3] at henv
  have hw : 0 ≤ 4 * (4 - 3 * (H.τ * hsQ H.al H.rho / hsRA H.al H.be)) / (5 * H.al - 1) *
      (H.w - 3 / 4) := mul_nonneg hm0 (by linarith [H.w_ge])
  have e := hs_phi_eq (x := H.x) (be := H.be) (al := H.al) (u := H.u)
    (m := 4 * (4 - 3 * (H.τ * hsQ H.al H.rho / hsRA H.al H.be)) / (5 * H.al - 1))
    (by positivity : 0 < H.τ * hsQ H.al H.rho) hq0
  have e2 : H.τ * hsQ H.al H.rho / hsQ H.al H.rho = H.τ := by field_simp
  rw [e2] at e
  rw [← e]
  unfold hsRs at henv
  unfold hsF at henv ⊢
  linarith

/-- **Gate S3**: for `2 ≤ x ≤ 13/6`,
`δ < 1/19`.
Proof: if `δ ≥ 1/19`: `strong_order`, `upper_order_98`, `hs_quad_order`, `hs3_shape`,
`hs_D_lt_Q`, `u_le_V`, `hs_V_le_Vbar` give the shape bounds; `root_zero`, `w_ge`,
`hs_env_weighted` (`hs3_B_pos`) give `0 ≤ G*_τ`; `hs_phi_eq`, `hs_A2_pos`, `hs_phi_convex_max`,
`hs3_zero_neg`, `q_le_qc`, `q_lt_seventh`, `hs3_tau2_cont` reach `q*`; `hs3_dur`, `hs3_uslope`; then
the central face (`hs_qc_le_iff`, `hs3_central_straight`, `hs3_central_ceiling`, `hs3_beta_mono`,
`hs3_central_alpha`) or the outer face (`hs3_outer_enclose`, `hs3_outer_ceiling`, `hs3_outer_face`)
contradicts. -/
theorem s3 (h1 : 2 ≤ H.x) (h2 : H.x ≤ 13 / 6) : H.δ < 1 / 19 := by
  by_contra hcon
  have hδ : 1 / 19 ≤ H.be / H.x - 1 := not_lt.mp hcon
  have hx1 : 1 < H.x := H.one_lt_x
  have hal1 : 1 ≤ H.al := H.one_le_al
  have hax : H.al < H.x := H.al_lt_x
  have hxb : H.x ≤ H.be := H.x_le_be
  obtain ⟨hL, hU, hQ⟩ := H.hs3_orders h1 h2 hδ
  obtain ⟨h108, hb2a, hrA3, hrA13⟩ := hs3_shape h1 h2 hal1 hax.le hxb hδ hL hU
  obtain ⟨hDQ, hD3⟩ := hs_D_lt_Q h1 hal1 hax.le hU
  have hu34 : 3 / 4 ≤ H.u := H.u_ge_34
  have hu1925 : H.u ≤ 19 / 25 :=
    H.u_le_V.trans ((hs_V_le_Vbar hx1).trans (hs3_Vbar_le h1 h2))
  have hq0 : 0 < hsQ H.al H.rho := H.hs3_q_pos
  have hτ2 : 2 < H.τ := H.two_lt_τ
  have hτT : H.τ * hsQ H.al H.rho < hsRA H.al H.be := H.τ_lt
  have hG := H.hs3_env h1
  have hΦ0 := hs3_zero_neg h1 h2 (by linarith) hax.le hxb hU hrA3 hrA13 hu34 H.u_le_rA hDQ
    (by positivity) hτT.le
  have hmax := fun qs hqs0 hqs7 hqqs => hs3_gate_max h1 h2 hal1 hax.le hxb hrA3 hu34 hu1925
    (hs3_D_pos h2 hal1 hax.le hb2a) hD3 h108 hq0 hτ2.le hτT.le hG hΦ0
    (hs_A2_pos h1 (by linarith) hal1 hu34 (by linarith)) (qs := qs) hqs0 hqs7 hqqs
  rcases le_or_gt (hsQc H.x H.al) (1 / 7) with hqc7 | hqc7
  · exact hs3_gate_central h1 h2 hal1 hax.le hxb hδ hQ h108 hb2a hDQ hD3 hrA13 H.u_eq hqc7
      (hmax (hsQc H.x H.al) (lt_of_lt_of_le hq0 H.q_le_qc) hqc7 H.q_le_qc)
  · exact hs3_gate_outer h1 h2 hal1 hax.le hxb hδ hU hQ h108 hb2a hDQ hD3 hrA13 H.u_eq hqc7
      (hmax (1 / 7) (by norm_num) le_rfl H.q_lt_seventh.le)

end HsData

/-- **Gate S3 for the actual window**: given `2 ≤ C/a ≤ 13/6`, `B/C - 1 < 1/19`. -/
theorem M2Short.hs_S3 (D : M2Short) (h1 : 2 ≤ D.C / D.a) (h2 : D.C / D.a ≤ 13 / 6) :
    D.B / D.C - 1 < 1 / 19 := by
  have h := D.toHs.s3 (by rwa [D.toHs_x]) (by rwa [D.toHs_x])
  rwa [D.toHs_δ] at h

end SmoothedOctagon
