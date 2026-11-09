module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Score

/-!
# Smaller-short window, cost: the four endpoint curves decrease in the displacement

At fixed `R` and `e`, write the cancelled
score as `G₀(d) - κ F h²`. The radical
correction `κ F h²` increases in `d` (`cost_corr_mono`), and on a displacement interval `[l, h]` the
derivative of the four main terms is at most the endpoint recipe `M₁ + M₂ + M₃ + M₄`
(`cost_G0d_le`), each factor being replaced by its value at the appropriate end of the interval.

## Main API

* `costTd`, `costvd`, `costzd`, `costG0`, `costG0d`, `costM`.
* `cost_G0_deriv`, `cost_G0d_le`, `cost_G0_anti`, `cost_corr_mono`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-! ### Derivatives in `d` -/

/-- `t_d = -2(e - 1)(1 - R²)/B²`. -/
noncomputable def costTd (e d r : ℝ) : ℝ := -(2 * (e - 1) * (1 - r ^ 2)) / costBd e d r ^ 2

/-- `v_d = 4H_f(R)(-R(1 + R)/2 + 19(1 + R)²d/42)`. -/
noncomputable def costvd (d r : ℝ) : ℝ :=
  4 * (costHf r * (-(r * (1 + r)) / 2 + 19 * (1 + r) ^ 2 * d / 42))

/-- `z_d = (1 + 2R)/(3(1 - R)) - 3d`. -/
noncomputable def costzd (d r : ℝ) : ℝ := (1 + 2 * r) / (3 * (1 - r)) - 3 * d

/-- The four main terms of the cancelled score. -/
noncomputable def costG0 (e d r : ℝ) : ℝ :=
  jetk r + jetk (costT r d e) + costv d r * (jetg r + jetg (costT r d e)) -
    1 / 8 * (costZU r d * (jetp r + jetp (costT r d e))) +
    1 / 8 * (costv d r * costZU r d * (jetq r + jetq (costT r d e)))

/-- The `d`-derivative of `costG0`. -/
noncomputable def costG0d (e d r : ℝ) : ℝ :=
  jetk1 (costT r d e) * costTd e d r +
    (costvd d r * (jetg r + jetg (costT r d e)) +
      costv d r * (jetg1 (costT r d e) * costTd e d r)) -
    1 / 8 * (costzd d r * (jetp r + jetp (costT r d e)) +
      costZU r d * (jetp1 (costT r d e) * costTd e d r)) +
    1 / 8 * ((costvd d r * costZU r d + costv d r * costzd d r) * (jetq r + jetq (costT r d e)) +
      costv d r * costZU r d * (jetq1 (costT r d e) * costTd e d r))

/-- **The endpoint recipe** `M₁ + M₂ + M₃ + M₄` on `[l, h]`: the derivative `costG0d` of the four
main terms with each factor evaluated at `l` or at `h`. -/
noncomputable def costM (e r l h : ℝ) : ℝ :=
  jetk1 (costT r l e) * costTd e l r +
    (costvd h r * (jetg r + jetg (costT r h e)) +
      costv h r * (jetg1 (costT r l e) * costTd e h r)) -
    1 / 8 * (costzd h r * (jetp r + jetp (costT r h e)) +
      costZU r h * (jetp1 (costT r l e) * costTd e l r)) +
    1 / 8 * (costvd h r * costZU r l * (jetq r + jetq (costT r l e)) +
      costv l r * costzd l r * (jetq r + jetq (costT r h e)) +
      costv l r * costZU r h * (jetq1 (costT r l e) * costTd e l r))

theorem cost_G0_eq (e d r : ℝ) :
    costScore e d r = costG0 e d r - costkap e d * (costcF r * (costh e d r * costh e d r)) := rfl

theorem cost_Td_deriv {e d r : ℝ} (hB : costBd e d r ≠ 0) :
    HasDerivAt (fun d => costT r d e) (costTd e d r) d := by
  have hN : HasDerivAt (fun d : ℝ => 2 * r + ((e + 1) * r - (e - 1)) * d)
      (((e + 1) * r - (e - 1)) * 1) d := ((hasDerivAt_id' d).const_mul _).const_add _
  have hBd : HasDerivAt (fun d : ℝ => 2 + (e + 1 - (e - 1) * r) * d)
      ((e + 1 - (e - 1) * r) * 1) d := ((hasDerivAt_id' d).const_mul _).const_add _
  refine (hN.fun_div hBd hB).congr_deriv ?_
  unfold costTd
  rw [show (2 + (e + 1 - (e - 1) * r) * d) = costBd e d r from rfl]
  field_simp
  unfold costBd
  ring

theorem cost_vd_deriv (d r : ℝ) : HasDerivAt (fun d => costv d r) (costvd d r) d := by
  have := ((((hasDerivAt_id' d).const_mul (r * (1 + r))).div_const 2).const_sub (r ^ 2)).fun_add
    ((((hasDerivAt_pow 2 d).const_mul (19 * (1 + r) ^ 2)).div_const 84))
  have := (this.const_mul (costHf r)).const_mul 4
  refine this.congr_deriv ?_
  unfold costvd
  push_cast
  ring

theorem cost_zd_deriv {d r : ℝ} : HasDerivAt (fun d => costZU r d) (costzd d r) d := by
  have := (((hasDerivAt_id' d).const_mul ((1 + 2 * r) / (3 * (1 - r)))).const_add
    (2 * r ^ 2 * (1 + r) / (3 - r))).fun_sub ((hasDerivAt_pow 2 d).const_mul (3 / 2))
  refine this.congr_deriv ?_
  unfold costzd
  push_cast
  ring

/-- The derivative of the four main terms in `d`. -/
theorem cost_G0_deriv {e d r : ℝ} (hB : costBd e d r ≠ 0) :
    HasDerivAt (fun d => costG0 e d r) (costG0d e d r) d := by
  have hT := cost_Td_deriv (r := r) hB
  have hv := cost_vd_deriv d r
  have hz := cost_zd_deriv (d := d) (r := r)
  have hk := (jet_k_jet (costT r d e)).1.comp d hT
  have hg := (jet_g_jet (costT r d e)).1.comp d hT
  have hp := (jet_p_jet (costT r d e)).1.comp d hT
  have hq := (jet_q_jet (costT r d e)).1.comp d hT
  have := ((((hk.const_add (jetk r)).fun_add (hv.fun_mul (hg.const_add (jetg r)))).fun_sub
    ((hz.fun_mul (hp.const_add (jetp r))).const_mul (1 / 8))).fun_add
    (((hv.fun_mul hz).fun_mul (hq.const_add (jetq r))).const_mul (1 / 8)))
  refine this.congr_deriv ?_
  unfold costG0d
  simp only [Function.comp_apply]

/-! ### The endpoint recipe -/

/-- The term-by-term comparison behind the endpoint recipe, in abstract variables. -/
theorem cost_G0d_abs {k1T k1Tl Td Tdl Tdh vd vdh v vh vl G Gh g1T g1Tl zd zdh zdl P Ph z zh zl
    p1T p1Tl Q Ql Qh q1T q1Tl : ℝ}
    (a1 : k1Tl ≤ k1T) (a2 : k1T ≤ 0) (b1 : Tdl ≤ Td) (b2 : Td ≤ Tdh) (b3 : Tdh ≤ 0)
    (c1 : vd ≤ vdh) (c2 : vdh ≤ 0) (d1 : 0 ≤ Gh) (d2 : Gh ≤ G) (e1 : 0 ≤ vh) (e2 : vh ≤ v)
    (e3 : v ≤ vl) (f1 : 0 ≤ g1Tl) (f2 : g1Tl ≤ g1T) (g1 : 0 ≤ zdh) (g2 : zdh ≤ zd) (g3 : zd ≤ zdl)
    (h1 : 0 ≤ Ph) (h2 : Ph ≤ P) (i1 : 0 ≤ zl) (i2 : zl ≤ z) (i3 : z ≤ zh) (j1 : 0 ≤ p1T)
    (j2 : p1T ≤ p1Tl) (k1 : 0 ≤ Ql) (k2 : Ql ≤ Q) (k3 : Q ≤ Qh) (l1 : q1Tl ≤ q1T) (l2 : q1T ≤ 0) :
    k1T * Td + (vd * G + v * (g1T * Td)) - 1 / 8 * (zd * P + z * (p1T * Td)) +
        1 / 8 * ((vd * z + v * zd) * Q + v * z * (q1T * Td)) ≤
      k1Tl * Tdl + (vdh * Gh + vh * (g1Tl * Tdh)) - 1 / 8 * (zdh * Ph + zh * (p1Tl * Tdl)) +
        1 / 8 * (vdh * zl * Ql + vl * zdl * Qh + vl * zh * (q1Tl * Tdl)) := by
  have t1 : (-k1T) * (-Td) ≤ (-k1Tl) * (-Tdl) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have t2 : vd * G ≤ vdh * Gh :=
    (mul_le_mul_of_nonneg_right c1 (d1.trans d2)).trans (mul_le_mul_of_nonpos_left d2 c2)
  have t3 : vh * g1Tl * (-Tdh) ≤ v * g1T * (-Td) :=
    mul_le_mul (mul_le_mul e2 f2 f1 (e1.trans e2)) (by linarith) (by linarith)
      (mul_nonneg (e1.trans e2) (f1.trans f2))
  have t4 : zdh * Ph ≤ zd * P := mul_le_mul g2 h2 h1 (g1.trans g2)
  have t5 : z * p1T * (-Td) ≤ zh * p1Tl * (-Tdl) :=
    mul_le_mul (mul_le_mul i3 j2 j1 (i1.trans (i2.trans i3))) (by linarith) (by linarith)
      (mul_nonneg (i1.trans (i2.trans i3)) (j1.trans j2))
  have t6 : (-vdh) * zl * Ql ≤ (-vd) * z * Q :=
    mul_le_mul (mul_le_mul (by linarith) i2 i1 (by linarith)) k2 k1
      (mul_nonneg (by linarith) (i1.trans i2))
  have t7 : v * zd * Q ≤ vl * zdl * Qh :=
    mul_le_mul (mul_le_mul e3 g3 (g1.trans g2) ((e1.trans e2).trans e3)) k3 (k1.trans k2)
      (mul_nonneg ((e1.trans e2).trans e3) ((g1.trans g2).trans g3))
  have t8 : v * z * ((-q1T) * (-Td)) ≤ vl * zh * ((-q1Tl) * (-Tdl)) :=
    mul_le_mul (mul_le_mul e3 i3 (i1.trans i2) ((e1.trans e2).trans e3))
      (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith))
      (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg ((e1.trans e2).trans e3) (i1.trans (i2.trans i3)))
  have r1 : k1T * Td = (-k1T) * (-Td) := by ring
  have r2 : k1Tl * Tdl = (-k1Tl) * (-Tdl) := by ring
  have r3 : v * (g1T * Td) = -(v * g1T * (-Td)) := by ring
  have r4 : vh * (g1Tl * Tdh) = -(vh * g1Tl * (-Tdh)) := by ring
  have r5 : z * (p1T * Td) = -(z * p1T * (-Td)) := by ring
  have r6 : zh * (p1Tl * Tdl) = -(zh * p1Tl * (-Tdl)) := by ring
  have r7 : (vd * z + v * zd) * Q = -((-vd) * z * Q) + v * zd * Q := by ring
  have r8 : vdh * zl * Ql = -((-vdh) * zl * Ql) := by ring
  have r9 : v * z * (q1T * Td) = v * z * ((-q1T) * (-Td)) := by ring
  have r10 : vl * zh * (q1Tl * Tdl) = vl * zh * ((-q1Tl) * (-Tdl)) := by ring
  rw [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10]
  linarith

section Curves

variable {e r : ℝ}

/-- Monotonicity of the factors in `d`, on `0 ≤ d₁ ≤ d₂ ≤ 1/19`. -/
theorem cost_d_mono (he : 13 / 5 ≤ e) (_he' : e ≤ 3) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19)
    {d₁ d₂ : ℝ} (h0 : 0 ≤ d₁) (h12 : d₁ ≤ d₂) (h2 : d₂ ≤ 1 / 19) :
    costT r d₂ e ≤ costT r d₁ e ∧ costTd e d₁ r ≤ costTd e d₂ r ∧ costTd e d₂ r ≤ 0 ∧
      costv d₂ r ≤ costv d₁ r ∧ 0 ≤ costv d₂ r ∧ costvd d₁ r ≤ costvd d₂ r ∧ costvd d₂ r ≤ 0 ∧
      costZU r d₁ ≤ costZU r d₂ ∧ 0 ≤ costZU r d₁ ∧ costzd d₂ r ≤ costzd d₁ r ∧
      0 ≤ costzd d₂ r := by
  have hB1 := cost_B_pos (e := e) (d := d₁) (r := r) h0 (by linarith) (by linarith)
  have hB2 := cost_B_pos (e := e) (d := d₂) (r := r) (h0.trans h12) (by linarith) (by linarith)
  have hC : 0 ≤ e + 1 - (e - 1) * r := by nlinarith
  have hBB : costBd e d₁ r ≤ costBd e d₂ r := by
    unfold costBd; nlinarith
  have hK : 0 ≤ 2 * (e - 1) * (1 - r ^ 2) := by
    have : 0 ≤ 1 - r ^ 2 := by nlinarith
    have : 0 ≤ e - 1 := by linarith
    positivity
  have hHf : 0 < costHf r := by unfold costHf; positivity
  have hz1 : 5 / 6 ≤ (1 + 2 * r) / (3 * (1 - r)) := by
    rw [le_div_iff₀ (by nlinarith)]; nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cost_T_eq_div, cost_T_eq_div, div_le_div_iff₀ (by linarith) (by linarith)]
    unfold costNd costBd
    have : 0 ≤ 2 * (d₂ - d₁) * ((e - 1) * (1 - r ^ 2)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by nlinarith))
    nlinarith
  · unfold costTd
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := pow_le_pow_left₀ (by linarith) hBB 2
    nlinarith
  · unfold costTd
    apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · unfold costv costQn
    have : 0 ≤ (d₂ - d₁) * (r * (1 + r) / 2 - 19 * (1 + r) ^ 2 * (d₁ + d₂) / 84) := by
      apply mul_nonneg (by linarith)
      have : (1 + r) ^ 2 * (d₁ + d₂) ≤ (26 / 19) ^ 2 * (2 / 19) :=
        mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by linarith) (by linarith)
          (by norm_num)
      nlinarith
    nlinarith
  · exact (cost_v_bounds (h0.trans h12) h2 hr hr').1
  · unfold costvd
    have : 19 * (1 + r) ^ 2 * d₁ / 42 ≤ 19 * (1 + r) ^ 2 * d₂ / 42 := by
      have : 0 ≤ (1 + r) ^ 2 := by positivity
      nlinarith
    nlinarith
  · unfold costvd
    apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    apply mul_nonpos_of_nonneg_of_nonpos hHf.le
    have : (1 + r) ^ 2 * d₂ ≤ (26 / 19) ^ 2 * (1 / 19) :=
      mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 2) h2 (by linarith) (by norm_num)
    nlinarith
  · unfold costZU
    have : 0 ≤ (d₂ - d₁) * ((1 + 2 * r) / (3 * (1 - r)) - 3 / 2 * (d₁ + d₂)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · exact (by linarith [(cost_z_bounds h0 (h12.trans h2) hr hr').1] : (0 : ℝ) ≤ costZU r d₁)
  · unfold costzd; linarith
  · unfold costzd; linarith

/-- Monotonicity of the primitive functions on the angle interval `[9/31, 7/19]`. -/
theorem cost_a_mono {a b : ℝ} (ha : 9 / 31 ≤ a) (hab : a ≤ b) (hb : b ≤ 7 / 19) :
    jetk1 b ≤ jetk1 a ∧ jetg a ≤ jetg b ∧ jetg1 b ≤ jetg1 a ∧ jetp a ≤ jetp b ∧
      jetp1 a ≤ jetp1 b ∧ jetq b ≤ jetq a ∧ jetq1 b ≤ jetq1 a := by
  refine ⟨jet_anti_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (jet_k_jet x).2)
      (fun x hx => (jet_k2_le hx.1 hx.2).trans (by norm_num)) ha hab hb,
    jet_mono_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (jet_g_jet x).1)
      (fun x hx => (jet_g_bounds hx.1 hx.2).2.2.1.le) ha hab hb,
    jet_anti_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (jet_g_jet x).2)
      (fun x hx => (jet_g_bounds hx.1 hx.2).2.2.2.2.2) ha hab hb,
    jet_mono_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (jet_p_jet x).1)
      (fun x hx => le_trans (by norm_num) (jet_p_bounds hx.1 hx.2).2.1) ha hab hb,
    jet_mono_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (jet_p_jet x).2)
      (fun x hx => le_trans (by norm_num) (jet_p_bounds hx.1 hx.2).2.2.2) ha hab hb,
    jet_anti_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (jet_q_jet x).1)
      (fun x hx => (jet_q_bounds (by linarith [hx.1]) (by linarith [hx.2])).2.2.1) ha hab hb,
    jet_anti_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (jet_q_jet x).2)
      (fun x hx => (jet_q_bounds (by linarith [hx.1]) (by linarith [hx.2])).2.2.2) ha hab hb⟩

/-- **The endpoint recipe bounds the derivative**: on `0 ≤ l ≤ d ≤ h ≤ 1/19`,
`∂_d G₀ ≤ M₁ + M₂ + M₃ + M₄`. -/
theorem cost_G0d_le (he : 13 / 5 ≤ e) (he' : e ≤ 3) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19)
    {l d h : ℝ} (hl : 0 ≤ l) (hld : l ≤ d) (hdh : d ≤ h) (hh : h ≤ 1 / 19) :
    costG0d e d r ≤ costM e r l h := by
  have hd0 : 0 ≤ d := hl.trans hld
  obtain ⟨A1, A2, -, A4, -, -, -, A8, A9, A10, -⟩ :=
    cost_d_mono he he' hr hr' hl hld (hdh.trans hh)
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, -, B10, B11⟩ := cost_d_mono he he' hr hr' hd0 hdh hh
  have hTl := cost_T_bounds he he' hl (hld.trans (hdh.trans hh)) hr hr'
  have hTd := cost_T_bounds he he' hd0 (hdh.trans hh) hr hr'
  have hTh := cost_T_bounds he he' (hd0.trans hdh) hh hr hr'
  have Tl1 := hTl.1
  have Tl2 : costT r l e ≤ 7 / 19 := hTl.2.1.trans hr'
  have Td1 := hTd.1
  have Td2 : costT r d e ≤ 7 / 19 := hTd.2.1.trans hr'
  have Th1 := hTh.1
  have Th2 : costT r h e ≤ 7 / 19 := hTh.2.1.trans hr'
  have mdl := cost_a_mono Td1 A1 Tl2
  have mhd := cost_a_mono Th1 B1 Td2
  have hr1 : 9 / 31 ≤ r := by linarith
  unfold costG0d costM
  exact cost_G0d_abs mdl.1 (jet_k1_neg Td1 Td2).le A2 B2 B3 B6 B7
    (add_nonneg (jet_g_bounds hr1 hr').1.le (jet_g_bounds Th1 Th2).1.le)
    (by linarith [mhd.2.1]) B5 B4 A4 (jet_g_bounds Tl1 Tl2).2.2.1.le mdl.2.2.1 B11 B10 A10
    (add_nonneg (jet_p_bounds hr1 hr').1.le (jet_p_bounds Th1 Th2).1.le)
    (by linarith [mhd.2.2.2.1]) A9 A8 B8 (le_trans (by norm_num) (jet_p_bounds Td1 Td2).2.1)
    mdl.2.2.2.2.1
    (add_nonneg (jet_q_bounds (a := r) (by linarith) (by linarith)).1.le
      (jet_q_bounds (a := costT r l e) (by linarith) (by linarith)).1.le)
    (by linarith [mdl.2.2.2.2.2.1]) (by linarith [mhd.2.2.2.2.2.1]) mdl.2.2.2.2.2.2
    (jet_q_bounds (a := costT r d e) (by linarith) (by linarith)).2.2.1


/-! ### The radical correction increases in `d` -/

/-- `H_d = 2(e + 1) - (e - 1)(R + 1/R)`. -/
noncomputable def costHd (e r : ℝ) : ℝ := 2 * (e + 1) - (e - 1) * (r + 1 / r)

/-- `J_d = 6BC + 2NE`. -/
noncomputable def costJdd (e d r : ℝ) : ℝ :=
  6 * costBd e d r * (e + 1 - (e - 1) * r) + 2 * costNd e d r * ((e + 1) * r - (e - 1))

/-- `h_d = H_d/J - H J_d/J²`. -/
noncomputable def costhd (e d r : ℝ) : ℝ :=
  costHd e r / costJd e d r - costH e d r * costJdd e d r / costJd e d r ^ 2

/-- `κ_d = 161(e - 1)²d(4 + 11d)/(432(2 + 11d)²)`. -/
noncomputable def costkapd (e d : ℝ) : ℝ :=
  161 * (e - 1) ^ 2 * (d * (4 + 11 * d)) / (432 * (2 + 11 * d) ^ 2)

/-- **The correction increases in `d`**: `κ F h²` is nondecreasing on `[0, 1/19]`. -/
theorem cost_corr_mono (he : 13 / 5 ≤ e) (he' : e ≤ 3) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19)
    {d₁ d₂ : ℝ} (h0 : 0 ≤ d₁) (h12 : d₁ ≤ d₂) (h2 : d₂ ≤ 1 / 19) :
    costkap e d₁ * (costcF r * (costh e d₁ r * costh e d₁ r)) ≤
      costkap e d₂ * (costcF r * (costh e d₂ r * costh e d₂ r)) := by
  have hr0 : 0 < r := by linarith
  have hHd : 0 ≤ costHd e r := by
    unfold costHd
    have : r + 1 / r ≤ 10 / 3 := by
      have e1 : r + 1 / r = (r * r + 1) / r := by field_simp
      rw [e1, div_le_iff₀ hr0]
      nlinarith
    nlinarith
  have hF := (cost_cF_bounds hr hr').1
  refine jet_mono_of (a := 0) (b := 1 / 19)
    (f := fun d => costkap e d * (costcF r * (costh e d r * costh e d r)))
    (f₁ := fun d => costkapd e d * (costcF r * (costh e d r * costh e d r)) +
      costkap e d * (costcF r * (costhd e d r * costh e d r + costh e d r * costhd e d r)))
    (fun d hd => ?_) (fun d hd => ?_) h0 h12 h2
  · have hB := cost_B_pos (e := e) (d := d) (r := r) hd.1 (by linarith) (by linarith)
    have hJ : costJd e d r ≠ 0 := by
      unfold costJd; nlinarith [sq_nonneg (costNd e d r)]
    have hH : HasDerivAt (fun d => costH e d r) (costHd e r) d := by
      have := (((hasDerivAt_id' d).const_mul (2 * (e + 1))).const_add 4).fun_sub
        (((hasDerivAt_id' d).const_mul (e - 1)).mul_const (r + 1 / r))
      refine this.congr_deriv ?_
      unfold costHd
      ring
    have hBd : HasDerivAt (fun d : ℝ => 2 + (e + 1 - (e - 1) * r) * d)
        ((e + 1 - (e - 1) * r) * 1) d := ((hasDerivAt_id' d).const_mul _).const_add _
    have hN : HasDerivAt (fun d : ℝ => 2 * r + ((e + 1) * r - (e - 1)) * d)
        (((e + 1) * r - (e - 1)) * 1) d := ((hasDerivAt_id' d).const_mul _).const_add _
    have hJd : HasDerivAt (fun d => costJd e d r) (costJdd e d r) d := by
      refine ((hBd.fun_pow 2).const_mul 3 |>.fun_add (hN.fun_pow 2)).congr_deriv ?_
      unfold costJdd costBd costNd
      push_cast
      ring
    have hh : HasDerivAt (fun d => costh e d r) (costhd e d r) d := by
      refine (hH.fun_div hJd hJ).congr_deriv ?_
      unfold costhd
      field_simp
    have hk : HasDerivAt (fun d => costkap e d) (costkapd e d) d := by
      have h2 : (432 * (2 + 11 * d)) ≠ 0 := by linarith [hd.1]
      have := ((hasDerivAt_pow 2 d).const_mul (161 * (e - 1) ^ 2)).fun_div
        ((((hasDerivAt_id' d).const_mul 11).const_add 2).const_mul 432) h2
      refine this.congr_deriv ?_
      unfold costkapd
      have : (2 + 11 * d) ≠ 0 := by linarith [hd.1]
      push_cast
      field_simp
      ring
    exact hk.fun_mul ((hh.fun_mul hh).const_mul (costcF r))
  · obtain ⟨hd0, hd1⟩ := hd
    have hB := cost_B_pos (e := e) (d := d) (r := r) hd0 (by linarith) (by linarith)
    have hBu : costBd e d r ≤ 42 / 19 := by
      unfold costBd
      have : (e + 1 - (e - 1) * r) * d ≤ 4 * (1 / 19) :=
        mul_le_mul (by nlinarith) hd1 hd0 (by norm_num)
      linarith
    have hNp : 0 ≤ costNd e d r := by
      unfold costNd
      have hE : -2 / 3 ≤ (e + 1) * r - (e - 1) := by nlinarith
      nlinarith
    have hJ : 12 ≤ costJd e d r := by
      unfold costJd; nlinarith [sq_nonneg (costNd e d r)]
    have hJdd : costJdd e d r ≤ 54 := by
      unfold costJdd
      have a : 6 * costBd e d r * (e + 1 - (e - 1) * r) ≤ 6 * (42 / 19) * 4 :=
        mul_le_mul (by linarith) (by nlinarith) (by nlinarith) (by norm_num)
      have b : 2 * costNd e d r * ((e + 1) * r - (e - 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)
      linarith
    have hH : 4 ≤ costH e d r := by
      have e1 : costH e d r = 4 + d * costHd e r := by unfold costH costHd; ring
      rw [e1]
      have := mul_nonneg hd0 hHd
      linarith
    -- the bracket `(4 + 11d)h + 2d(2 + 11d)h_d ≥ 0`
    have hX : 0 ≤ 2 * d * (2 + 11 * d) := by positivity
    have hX' : 2 * d * (2 + 11 * d) ≤ 3 / 10 := by nlinarith
    have hJ0 : 0 < costJd e d r := by linarith
    have key : 0 ≤ (4 + 11 * d) * costh e d r + 2 * d * (2 + 11 * d) * costhd e d r := by
      have e1 : (4 + 11 * d) * costh e d r + 2 * d * (2 + 11 * d) * costhd e d r =
          ((4 + 11 * d) * costH e d r * costJd e d r + 2 * d * (2 + 11 * d) *
            (costHd e r * costJd e d r - costH e d r * costJdd e d r)) / costJd e d r ^ 2 := by
        unfold costh costhd
        field_simp
      rw [e1]
      apply div_nonneg _ (by positivity)
      have a : 0 ≤ 2 * d * (2 + 11 * d) * (costHd e r * costJd e d r) :=
        mul_nonneg hX (mul_nonneg hHd hJ0.le)
      have b : 2 * d * (2 + 11 * d) * (costH e d r * costJdd e d r) ≤
          3 / 10 * (costH e d r * 54) := by
        have : costH e d r * costJdd e d r ≤ costH e d r * 54 :=
          mul_le_mul_of_nonneg_left hJdd (by linarith)
        rcases le_total 0 (costH e d r * costJdd e d r) with h | h
        · exact mul_le_mul hX' this h (by norm_num)
        · have : 2 * d * (2 + 11 * d) * (costH e d r * costJdd e d r) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hX h
          nlinarith
      have c : 4 * costH e d r * 12 ≤ (4 + 11 * d) * costH e d r * costJd e d r := by
        have : 4 * costH e d r ≤ (4 + 11 * d) * costH e d r := by nlinarith
        exact mul_le_mul this hJ (by norm_num) (by nlinarith)
      nlinarith
    have e2 : costkapd e d * (costcF r * (costh e d r * costh e d r)) +
        costkap e d * (costcF r * (costhd e d r * costh e d r + costh e d r * costhd e d r)) =
        costcF r * (161 * (e - 1) ^ 2 * d * costh e d r / (432 * (2 + 11 * d) ^ 2)) *
          ((4 + 11 * d) * costh e d r + 2 * d * (2 + 11 * d) * costhd e d r) := by
      unfold costkapd costkap
      have : (2 + 11 * d) ≠ 0 := by linarith
      field_simp
      ring
    show 0 ≤ costkapd e d * (costcF r * (costh e d r * costh e d r)) +
      costkap e d * (costcF r * (costhd e d r * costh e d r + costh e d r * costhd e d r))
    rw [e2]
    have hh0 : 0 ≤ costh e d r := by unfold costh; exact div_nonneg (by linarith) hJ0.le
    exact mul_nonneg (mul_nonneg hF (by positivity)) key

/-! ### The four curves and the conclusion -/

/-- A nonpositive endpoint recipe makes `G₀` nonincreasing on `[l, h]`. -/
theorem cost_G0_anti (he : 13 / 5 ≤ e) (he' : e ≤ 3) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19)
    {l h : ℝ} (hl : 0 ≤ l) (hh : h ≤ 1 / 19) (hM : costM e r l h ≤ 0) {u v : ℝ} (hu : l ≤ u)
    (huv : u ≤ v) (hv : v ≤ h) : costG0 e v r ≤ costG0 e u r := by
  have hB : ∀ x ∈ Icc l h, costBd e x r ≠ 0 := fun x hx => by
    have := cost_B_pos (e := e) (d := x) (r := r) (hl.trans hx.1) (by linarith) (by linarith)
    exact (by linarith : (0 : ℝ) < costBd e x r).ne'
  exact jet_anti_of (a := l) (b := h) (fun x hx => cost_G0_deriv (hB x hx))
    (fun x hx => (cost_G0d_le he he' hr hr' hl hx.1 hx.2 hh).trans hM) hu huv hv

/-- At fixed `R`, the cancelled score at `d` dominates its value at `d = 1/19` once `G₀` does. -/
theorem cost_score_dmono (he : 13 / 5 ≤ e) (he' : e ≤ 3) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19)
    {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) (hG : costG0 e (1 / 19) r ≤ costG0 e d r) :
    costScore e (1 / 19) r ≤ costScore e d r := by
  rw [cost_G0_eq, cost_G0_eq]
  have := cost_corr_mono he he' hr hr' hd hd' le_rfl
  linarith

end Curves

end SmoothedOctagon
