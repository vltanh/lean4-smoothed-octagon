module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6HandR

/-!
# Gate S6, hand proof: the four endpoint curves decrease in the displacement

`archive/lighter-proofs/SHORT_COST_CONCAVITY.md` §4 (replacing `SMALL_SHAPE_COST_EXCLUSION`
(26)-(31)). At fixed `R` and `e`, write the cancelled score as `G₀(d) - κ F h²`. The radical
correction `κ F h²` increases in `d` (`hl46_corr_mono`), and on a displacement interval `[l, h]` the
derivative of the four main terms is at most the endpoint recipe `M₁ + M₂ + M₃ + M₄` of note (21)
(`hl46_G0d_le`), each factor being replaced by its value at the appropriate end of the interval.

## Main API

* `hl46Td`, `hl46vd`, `hl46zd`, `hl46G0`, `hl46G0d`, `hl46M`.
* `hl46_G0_deriv`, `hl46_G0d_le`, `hl46_G0_anti`, `hl46_corr_mono`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-! ### Derivatives in `d` -/

/-- `t_d = -2(e - 1)(1 - R²)/B²`. -/
noncomputable def hl46Td (e d r : ℝ) : ℝ := -(2 * (e - 1) * (1 - r ^ 2)) / hl46Bd e d r ^ 2

/-- `v_d = 4H_f(R)(-R(1 + R)/2 + 19(1 + R)²d/42)`. -/
noncomputable def hl46vd (d r : ℝ) : ℝ :=
  4 * (hl46Hf r * (-(r * (1 + r)) / 2 + 19 * (1 + r) ^ 2 * d / 42))

/-- `z_d = (1 + 2R)/(3(1 - R)) - 3d`. -/
noncomputable def hl46zd (d r : ℝ) : ℝ := (1 + 2 * r) / (3 * (1 - r)) - 3 * d

/-- The four main terms of the cancelled score. -/
noncomputable def hl46G0 (e d r : ℝ) : ℝ :=
  hl46k r + hl46k (hs6T r d e) + hl46v d r * (hl46g r + hl46g (hs6T r d e)) -
    1 / 8 * (hs6ZU r d * (hl46p r + hl46p (hs6T r d e))) +
    1 / 8 * (hl46v d r * hs6ZU r d * (hl46q r + hl46q (hs6T r d e)))

/-- The `d`-derivative of `hl46G0`. -/
noncomputable def hl46G0d (e d r : ℝ) : ℝ :=
  hl46k1 (hs6T r d e) * hl46Td e d r +
    (hl46vd d r * (hl46g r + hl46g (hs6T r d e)) +
      hl46v d r * (hl46g1 (hs6T r d e) * hl46Td e d r)) -
    1 / 8 * (hl46zd d r * (hl46p r + hl46p (hs6T r d e)) +
      hs6ZU r d * (hl46p1 (hs6T r d e) * hl46Td e d r)) +
    1 / 8 * ((hl46vd d r * hs6ZU r d + hl46v d r * hl46zd d r) * (hl46q r + hl46q (hs6T r d e)) +
      hl46v d r * hs6ZU r d * (hl46q1 (hs6T r d e) * hl46Td e d r))

/-- **The endpoint recipe** `M₁ + M₂ + M₃ + M₄` of note (21) on `[l, h]`. -/
noncomputable def hl46M (e r l h : ℝ) : ℝ :=
  hl46k1 (hs6T r l e) * hl46Td e l r +
    (hl46vd h r * (hl46g r + hl46g (hs6T r h e)) +
      hl46v h r * (hl46g1 (hs6T r l e) * hl46Td e h r)) -
    1 / 8 * (hl46zd h r * (hl46p r + hl46p (hs6T r h e)) +
      hs6ZU r h * (hl46p1 (hs6T r l e) * hl46Td e l r)) +
    1 / 8 * (hl46vd h r * hs6ZU r l * (hl46q r + hl46q (hs6T r l e)) +
      hl46v l r * hl46zd l r * (hl46q r + hl46q (hs6T r h e)) +
      hl46v l r * hs6ZU r h * (hl46q1 (hs6T r l e) * hl46Td e l r))

theorem hl46_G0_eq (e d r : ℝ) :
    hl46S6F e d r = hl46G0 e d r - hl46kap e d * (hl46cF r * (hl46h e d r * hl46h e d r)) := rfl

theorem hl46_Td_deriv {e d r : ℝ} (hB : hl46Bd e d r ≠ 0) :
    HasDerivAt (fun d => hs6T r d e) (hl46Td e d r) d := by
  have hN : HasDerivAt (fun d : ℝ => 2 * r + ((e + 1) * r - (e - 1)) * d)
      (((e + 1) * r - (e - 1)) * 1) d := ((hasDerivAt_id' d).const_mul _).const_add _
  have hBd : HasDerivAt (fun d : ℝ => 2 + (e + 1 - (e - 1) * r) * d)
      ((e + 1 - (e - 1) * r) * 1) d := ((hasDerivAt_id' d).const_mul _).const_add _
  refine (hN.fun_div hBd hB).congr_deriv ?_
  unfold hl46Td
  rw [show (2 + (e + 1 - (e - 1) * r) * d) = hl46Bd e d r from rfl]
  field_simp
  unfold hl46Bd
  ring

theorem hl46_vd_deriv (d r : ℝ) : HasDerivAt (fun d => hl46v d r) (hl46vd d r) d := by
  have := ((((hasDerivAt_id' d).const_mul (r * (1 + r))).div_const 2).const_sub (r ^ 2)).fun_add
    ((((hasDerivAt_pow 2 d).const_mul (19 * (1 + r) ^ 2)).div_const 84))
  have := (this.const_mul (hl46Hf r)).const_mul 4
  refine this.congr_deriv ?_
  unfold hl46vd
  push_cast
  ring

theorem hl46_zd_deriv {d r : ℝ} : HasDerivAt (fun d => hs6ZU r d) (hl46zd d r) d := by
  have := (((hasDerivAt_id' d).const_mul ((1 + 2 * r) / (3 * (1 - r)))).const_add
    (2 * r ^ 2 * (1 + r) / (3 - r))).fun_sub ((hasDerivAt_pow 2 d).const_mul (3 / 2))
  refine this.congr_deriv ?_
  unfold hl46zd
  push_cast
  ring

/-- The derivative of the four main terms in `d`. -/
theorem hl46_G0_deriv {e d r : ℝ} (hB : hl46Bd e d r ≠ 0) :
    HasDerivAt (fun d => hl46G0 e d r) (hl46G0d e d r) d := by
  have hT := hl46_Td_deriv (r := r) hB
  have hv := hl46_vd_deriv d r
  have hz := hl46_zd_deriv (d := d) (r := r)
  have hk := (hl46_k_jet (hs6T r d e)).1.comp d hT
  have hg := (hl46_g_jet (hs6T r d e)).1.comp d hT
  have hp := (hl46_p_jet (hs6T r d e)).1.comp d hT
  have hq := (hl46_q_jet (hs6T r d e)).1.comp d hT
  have := ((((hk.const_add (hl46k r)).fun_add (hv.fun_mul (hg.const_add (hl46g r)))).fun_sub
    ((hz.fun_mul (hp.const_add (hl46p r))).const_mul (1 / 8))).fun_add
    (((hv.fun_mul hz).fun_mul (hq.const_add (hl46q r))).const_mul (1 / 8)))
  refine this.congr_deriv ?_
  unfold hl46G0d
  simp only [Function.comp_apply]

/-! ### The endpoint recipe -/

/-- The term-by-term comparison behind note (21), in abstract variables. -/
theorem hl46_G0d_abs {k1T k1Tl Td Tdl Tdh vd vdh v vh vl G Gh g1T g1Tl zd zdh zdl P Ph z zh zl
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

/-- Monotonicity of the factors in `d` (note §4), on `0 ≤ d₁ ≤ d₂ ≤ 1/19`. -/
theorem hl46_d_mono (he : 13 / 5 ≤ e) (_he' : e ≤ 3) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19)
    {d₁ d₂ : ℝ} (h0 : 0 ≤ d₁) (h12 : d₁ ≤ d₂) (h2 : d₂ ≤ 1 / 19) :
    hs6T r d₂ e ≤ hs6T r d₁ e ∧ hl46Td e d₁ r ≤ hl46Td e d₂ r ∧ hl46Td e d₂ r ≤ 0 ∧
      hl46v d₂ r ≤ hl46v d₁ r ∧ 0 ≤ hl46v d₂ r ∧ hl46vd d₁ r ≤ hl46vd d₂ r ∧ hl46vd d₂ r ≤ 0 ∧
      hs6ZU r d₁ ≤ hs6ZU r d₂ ∧ 0 ≤ hs6ZU r d₁ ∧ hl46zd d₂ r ≤ hl46zd d₁ r ∧
      0 ≤ hl46zd d₂ r := by
  have hB1 := hl46_B_pos (e := e) (d := d₁) (r := r) h0 (by linarith) (by linarith)
  have hB2 := hl46_B_pos (e := e) (d := d₂) (r := r) (h0.trans h12) (by linarith) (by linarith)
  have hC : 0 ≤ e + 1 - (e - 1) * r := by nlinarith
  have hBB : hl46Bd e d₁ r ≤ hl46Bd e d₂ r := by
    unfold hl46Bd; nlinarith
  have hK : 0 ≤ 2 * (e - 1) * (1 - r ^ 2) := by
    have : 0 ≤ 1 - r ^ 2 := by nlinarith
    have : 0 ≤ e - 1 := by linarith
    positivity
  have hHf : 0 < hl46Hf r := by unfold hl46Hf; positivity
  have hz1 : 5 / 6 ≤ (1 + 2 * r) / (3 * (1 - r)) := by
    rw [le_div_iff₀ (by nlinarith)]; nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hl46_T_eq, hl46_T_eq, div_le_div_iff₀ (by linarith) (by linarith)]
    unfold hl46Nd hl46Bd
    have : 0 ≤ 2 * (d₂ - d₁) * ((e - 1) * (1 - r ^ 2)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by nlinarith))
    nlinarith
  · unfold hl46Td
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := pow_le_pow_left₀ (by linarith) hBB 2
    nlinarith
  · unfold hl46Td
    apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · unfold hl46v hl46Qn
    have : 0 ≤ (d₂ - d₁) * (r * (1 + r) / 2 - 19 * (1 + r) ^ 2 * (d₁ + d₂) / 84) := by
      apply mul_nonneg (by linarith)
      have : (1 + r) ^ 2 * (d₁ + d₂) ≤ (26 / 19) ^ 2 * (2 / 19) :=
        mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by linarith) (by linarith)
          (by norm_num)
      nlinarith
    nlinarith
  · exact (hl46_v_bounds (h0.trans h12) h2 hr hr').1
  · unfold hl46vd
    have : 19 * (1 + r) ^ 2 * d₁ / 42 ≤ 19 * (1 + r) ^ 2 * d₂ / 42 := by
      have : 0 ≤ (1 + r) ^ 2 := by positivity
      nlinarith
    nlinarith
  · unfold hl46vd
    apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    apply mul_nonpos_of_nonneg_of_nonpos hHf.le
    have : (1 + r) ^ 2 * d₂ ≤ (26 / 19) ^ 2 * (1 / 19) :=
      mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) 2) h2 (by linarith) (by norm_num)
    nlinarith
  · unfold hs6ZU
    have : 0 ≤ (d₂ - d₁) * ((1 + 2 * r) / (3 * (1 - r)) - 3 / 2 * (d₁ + d₂)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  · exact (by linarith [(hl46_z_bounds h0 (h12.trans h2) hr hr').1] : (0 : ℝ) ≤ hs6ZU r d₁)
  · unfold hl46zd; linarith
  · unfold hl46zd; linarith

/-- Monotonicity of the primitive functions on the angle interval `[9/31, 7/19]`. -/
theorem hl46_a_mono {a b : ℝ} (ha : 9 / 31 ≤ a) (hab : a ≤ b) (hb : b ≤ 7 / 19) :
    hl46k1 b ≤ hl46k1 a ∧ hl46g a ≤ hl46g b ∧ hl46g1 b ≤ hl46g1 a ∧ hl46p a ≤ hl46p b ∧
      hl46p1 a ≤ hl46p1 b ∧ hl46q b ≤ hl46q a ∧ hl46q1 b ≤ hl46q1 a := by
  refine ⟨hl46_anti_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (hl46_k_jet x).2)
      (fun x hx => (hl46_k2_le hx.1 hx.2).trans (by norm_num)) ha hab hb,
    hl46_mono_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (hl46_g_jet x).1)
      (fun x hx => (hl46_g_bounds hx.1 hx.2).2.2.1.le) ha hab hb,
    hl46_anti_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (hl46_g_jet x).2)
      (fun x hx => (hl46_g_bounds hx.1 hx.2).2.2.2.2.2) ha hab hb,
    hl46_mono_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (hl46_p_jet x).1)
      (fun x hx => le_trans (by norm_num) (hl46_p_bounds hx.1 hx.2).2.1) ha hab hb,
    hl46_mono_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (hl46_p_jet x).2)
      (fun x hx => le_trans (by norm_num) (hl46_p_bounds hx.1 hx.2).2.2.2) ha hab hb,
    hl46_anti_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (hl46_q_jet x).1)
      (fun x hx => (hl46_q_bounds (by linarith [hx.1]) (by linarith [hx.2])).2.2.1) ha hab hb,
    hl46_anti_of (a := 9 / 31) (b := 7 / 19) (fun x _ => (hl46_q_jet x).2)
      (fun x hx => (hl46_q_bounds (by linarith [hx.1]) (by linarith [hx.2])).2.2.2) ha hab hb⟩

/-- **The endpoint recipe bounds the derivative** (note (21)): on `0 ≤ l ≤ d ≤ h ≤ 1/19`,
`∂_d G₀ ≤ M₁ + M₂ + M₃ + M₄`. -/
theorem hl46_G0d_le (he : 13 / 5 ≤ e) (he' : e ≤ 3) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19)
    {l d h : ℝ} (hl : 0 ≤ l) (hld : l ≤ d) (hdh : d ≤ h) (hh : h ≤ 1 / 19) :
    hl46G0d e d r ≤ hl46M e r l h := by
  have hd0 : 0 ≤ d := hl.trans hld
  obtain ⟨A1, A2, -, A4, -, -, -, A8, A9, A10, -⟩ :=
    hl46_d_mono he he' hr hr' hl hld (hdh.trans hh)
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, -, B10, B11⟩ := hl46_d_mono he he' hr hr' hd0 hdh hh
  have hTl := hl46_T_bounds he he' hl (hld.trans (hdh.trans hh)) hr hr'
  have hTd := hl46_T_bounds he he' hd0 (hdh.trans hh) hr hr'
  have hTh := hl46_T_bounds he he' (hd0.trans hdh) hh hr hr'
  have Tl1 := hTl.1
  have Tl2 : hs6T r l e ≤ 7 / 19 := hTl.2.1.trans hr'
  have Td1 := hTd.1
  have Td2 : hs6T r d e ≤ 7 / 19 := hTd.2.1.trans hr'
  have Th1 := hTh.1
  have Th2 : hs6T r h e ≤ 7 / 19 := hTh.2.1.trans hr'
  have mdl := hl46_a_mono Td1 A1 Tl2
  have mhd := hl46_a_mono Th1 B1 Td2
  have hr1 : 9 / 31 ≤ r := by linarith
  unfold hl46G0d hl46M
  exact hl46_G0d_abs mdl.1 (hl46_k1_neg Td1 Td2).le A2 B2 B3 B6 B7
    (add_nonneg (hl46_g_bounds hr1 hr').1.le (hl46_g_bounds Th1 Th2).1.le)
    (by linarith [mhd.2.1]) B5 B4 A4 (hl46_g_bounds Tl1 Tl2).2.2.1.le mdl.2.2.1 B11 B10 A10
    (add_nonneg (hl46_p_bounds hr1 hr').1.le (hl46_p_bounds Th1 Th2).1.le)
    (by linarith [mhd.2.2.2.1]) A9 A8 B8 (le_trans (by norm_num) (hl46_p_bounds Td1 Td2).2.1)
    mdl.2.2.2.2.1
    (add_nonneg (hl46_q_bounds (a := r) (by linarith) (by linarith)).1.le
      (hl46_q_bounds (a := hs6T r l e) (by linarith) (by linarith)).1.le)
    (by linarith [mdl.2.2.2.2.2.1]) (by linarith [mhd.2.2.2.2.2.1]) mdl.2.2.2.2.2.2
    (hl46_q_bounds (a := hs6T r d e) (by linarith) (by linarith)).2.2.1


/-! ### The radical correction increases in `d` -/

/-- `H_d = 2(e + 1) - (e - 1)(R + 1/R)`. -/
noncomputable def hl46Hd (e r : ℝ) : ℝ := 2 * (e + 1) - (e - 1) * (r + 1 / r)

/-- `J_d = 6BC + 2NE`. -/
noncomputable def hl46Jdd (e d r : ℝ) : ℝ :=
  6 * hl46Bd e d r * (e + 1 - (e - 1) * r) + 2 * hl46Nd e d r * ((e + 1) * r - (e - 1))

/-- `h_d = H_d/J - H J_d/J²`. -/
noncomputable def hl46hd (e d r : ℝ) : ℝ :=
  hl46Hd e r / hl46Jd e d r - hl46H e d r * hl46Jdd e d r / hl46Jd e d r ^ 2

/-- `κ_d = 161(e - 1)²d(4 + 11d)/(432(2 + 11d)²)`. -/
noncomputable def hl46kapd (e d : ℝ) : ℝ :=
  161 * (e - 1) ^ 2 * (d * (4 + 11 * d)) / (432 * (2 + 11 * d) ^ 2)

/-- **The correction increases in `d`** (note §4): `κ F h²` is nondecreasing on `[0, 1/19]`. -/
theorem hl46_corr_mono (he : 13 / 5 ≤ e) (he' : e ≤ 3) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19)
    {d₁ d₂ : ℝ} (h0 : 0 ≤ d₁) (h12 : d₁ ≤ d₂) (h2 : d₂ ≤ 1 / 19) :
    hl46kap e d₁ * (hl46cF r * (hl46h e d₁ r * hl46h e d₁ r)) ≤
      hl46kap e d₂ * (hl46cF r * (hl46h e d₂ r * hl46h e d₂ r)) := by
  have hr0 : 0 < r := by linarith
  have hHd : 0 ≤ hl46Hd e r := by
    unfold hl46Hd
    have : r + 1 / r ≤ 10 / 3 := by
      have e1 : r + 1 / r = (r * r + 1) / r := by field_simp
      rw [e1, div_le_iff₀ hr0]
      nlinarith
    nlinarith
  have hF := (hl46_cF_bounds hr hr').1
  refine hl46_mono_of (a := 0) (b := 1 / 19)
    (f := fun d => hl46kap e d * (hl46cF r * (hl46h e d r * hl46h e d r)))
    (f₁ := fun d => hl46kapd e d * (hl46cF r * (hl46h e d r * hl46h e d r)) +
      hl46kap e d * (hl46cF r * (hl46hd e d r * hl46h e d r + hl46h e d r * hl46hd e d r)))
    (fun d hd => ?_) (fun d hd => ?_) h0 h12 h2
  · have hB := hl46_B_pos (e := e) (d := d) (r := r) hd.1 (by linarith) (by linarith)
    have hJ : hl46Jd e d r ≠ 0 := by
      unfold hl46Jd; nlinarith [sq_nonneg (hl46Nd e d r)]
    have hH : HasDerivAt (fun d => hl46H e d r) (hl46Hd e r) d := by
      have := (((hasDerivAt_id' d).const_mul (2 * (e + 1))).const_add 4).fun_sub
        (((hasDerivAt_id' d).const_mul (e - 1)).mul_const (r + 1 / r))
      refine this.congr_deriv ?_
      unfold hl46Hd
      ring
    have hBd : HasDerivAt (fun d : ℝ => 2 + (e + 1 - (e - 1) * r) * d)
        ((e + 1 - (e - 1) * r) * 1) d := ((hasDerivAt_id' d).const_mul _).const_add _
    have hN : HasDerivAt (fun d : ℝ => 2 * r + ((e + 1) * r - (e - 1)) * d)
        (((e + 1) * r - (e - 1)) * 1) d := ((hasDerivAt_id' d).const_mul _).const_add _
    have hJd : HasDerivAt (fun d => hl46Jd e d r) (hl46Jdd e d r) d := by
      refine ((hBd.fun_pow 2).const_mul 3 |>.fun_add (hN.fun_pow 2)).congr_deriv ?_
      unfold hl46Jdd hl46Bd hl46Nd
      push_cast
      ring
    have hh : HasDerivAt (fun d => hl46h e d r) (hl46hd e d r) d := by
      refine (hH.fun_div hJd hJ).congr_deriv ?_
      unfold hl46hd
      field_simp
    have hk : HasDerivAt (fun d => hl46kap e d) (hl46kapd e d) d := by
      have h2 : (432 * (2 + 11 * d)) ≠ 0 := by linarith [hd.1]
      have := ((hasDerivAt_pow 2 d).const_mul (161 * (e - 1) ^ 2)).fun_div
        ((((hasDerivAt_id' d).const_mul 11).const_add 2).const_mul 432) h2
      refine this.congr_deriv ?_
      unfold hl46kapd
      have : (2 + 11 * d) ≠ 0 := by linarith [hd.1]
      push_cast
      field_simp
      ring
    exact hk.fun_mul ((hh.fun_mul hh).const_mul (hl46cF r))
  · obtain ⟨hd0, hd1⟩ := hd
    have hB := hl46_B_pos (e := e) (d := d) (r := r) hd0 (by linarith) (by linarith)
    have hBu : hl46Bd e d r ≤ 42 / 19 := by
      unfold hl46Bd
      have : (e + 1 - (e - 1) * r) * d ≤ 4 * (1 / 19) :=
        mul_le_mul (by nlinarith) hd1 hd0 (by norm_num)
      linarith
    have hNp : 0 ≤ hl46Nd e d r := by
      unfold hl46Nd
      have hE : -2 / 3 ≤ (e + 1) * r - (e - 1) := by nlinarith
      nlinarith
    have hJ : 12 ≤ hl46Jd e d r := by
      unfold hl46Jd; nlinarith [sq_nonneg (hl46Nd e d r)]
    have hJdd : hl46Jdd e d r ≤ 54 := by
      unfold hl46Jdd
      have a : 6 * hl46Bd e d r * (e + 1 - (e - 1) * r) ≤ 6 * (42 / 19) * 4 :=
        mul_le_mul (by linarith) (by nlinarith) (by nlinarith) (by norm_num)
      have b : 2 * hl46Nd e d r * ((e + 1) * r - (e - 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)
      linarith
    have hH : 4 ≤ hl46H e d r := by
      have e1 : hl46H e d r = 4 + d * hl46Hd e r := by unfold hl46H hl46Hd; ring
      rw [e1]
      have := mul_nonneg hd0 hHd
      linarith
    -- the bracket `(4 + 11d)h + 2d(2 + 11d)h_d ≥ 0`
    have hX : 0 ≤ 2 * d * (2 + 11 * d) := by positivity
    have hX' : 2 * d * (2 + 11 * d) ≤ 3 / 10 := by nlinarith
    have hJ0 : 0 < hl46Jd e d r := by linarith
    have key : 0 ≤ (4 + 11 * d) * hl46h e d r + 2 * d * (2 + 11 * d) * hl46hd e d r := by
      have e1 : (4 + 11 * d) * hl46h e d r + 2 * d * (2 + 11 * d) * hl46hd e d r =
          ((4 + 11 * d) * hl46H e d r * hl46Jd e d r + 2 * d * (2 + 11 * d) *
            (hl46Hd e r * hl46Jd e d r - hl46H e d r * hl46Jdd e d r)) / hl46Jd e d r ^ 2 := by
        unfold hl46h hl46hd
        field_simp
      rw [e1]
      apply div_nonneg _ (by positivity)
      have a : 0 ≤ 2 * d * (2 + 11 * d) * (hl46Hd e r * hl46Jd e d r) :=
        mul_nonneg hX (mul_nonneg hHd hJ0.le)
      have b : 2 * d * (2 + 11 * d) * (hl46H e d r * hl46Jdd e d r) ≤
          3 / 10 * (hl46H e d r * 54) := by
        have : hl46H e d r * hl46Jdd e d r ≤ hl46H e d r * 54 :=
          mul_le_mul_of_nonneg_left hJdd (by linarith)
        rcases le_total 0 (hl46H e d r * hl46Jdd e d r) with h | h
        · exact mul_le_mul hX' this h (by norm_num)
        · have : 2 * d * (2 + 11 * d) * (hl46H e d r * hl46Jdd e d r) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hX h
          nlinarith
      have c : 4 * hl46H e d r * 12 ≤ (4 + 11 * d) * hl46H e d r * hl46Jd e d r := by
        have : 4 * hl46H e d r ≤ (4 + 11 * d) * hl46H e d r := by nlinarith
        exact mul_le_mul this hJ (by norm_num) (by nlinarith)
      nlinarith
    have e2 : hl46kapd e d * (hl46cF r * (hl46h e d r * hl46h e d r)) +
        hl46kap e d * (hl46cF r * (hl46hd e d r * hl46h e d r + hl46h e d r * hl46hd e d r)) =
        hl46cF r * (161 * (e - 1) ^ 2 * d * hl46h e d r / (432 * (2 + 11 * d) ^ 2)) *
          ((4 + 11 * d) * hl46h e d r + 2 * d * (2 + 11 * d) * hl46hd e d r) := by
      unfold hl46kapd hl46kap
      have : (2 + 11 * d) ≠ 0 := by linarith
      field_simp
      ring
    show 0 ≤ hl46kapd e d * (hl46cF r * (hl46h e d r * hl46h e d r)) +
      hl46kap e d * (hl46cF r * (hl46hd e d r * hl46h e d r + hl46h e d r * hl46hd e d r))
    rw [e2]
    have hh0 : 0 ≤ hl46h e d r := by unfold hl46h; exact div_nonneg (by linarith) hJ0.le
    exact mul_nonneg (mul_nonneg hF (by positivity)) key

/-! ### The four curves and the conclusion -/

/-- A nonpositive endpoint recipe makes `G₀` nonincreasing on `[l, h]`. -/
theorem hl46_G0_anti (he : 13 / 5 ≤ e) (he' : e ≤ 3) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19)
    {l h : ℝ} (hl : 0 ≤ l) (hh : h ≤ 1 / 19) (hM : hl46M e r l h ≤ 0) {u v : ℝ} (hu : l ≤ u)
    (huv : u ≤ v) (hv : v ≤ h) : hl46G0 e v r ≤ hl46G0 e u r := by
  have hB : ∀ x ∈ Icc l h, hl46Bd e x r ≠ 0 := fun x hx => by
    have := hl46_B_pos (e := e) (d := x) (r := r) (hl.trans hx.1) (by linarith) (by linarith)
    exact (by linarith : (0 : ℝ) < hl46Bd e x r).ne'
  exact hl46_anti_of (a := l) (b := h) (fun x hx => hl46_G0_deriv (hB x hx))
    (fun x hx => (hl46_G0d_le he he' hr hr' hl hx.1 hx.2 hh).trans hM) hu huv hv

/-- At fixed `R`, the cancelled score at `d` dominates its value at `d = 1/19` once `G₀` does. -/
theorem hl46_S6F_dmono (he : 13 / 5 ≤ e) (he' : e ≤ 3) (hr : 1 / 3 ≤ r) (hr' : r ≤ 7 / 19)
    {d : ℝ} (hd : 0 ≤ d) (hd' : d ≤ 1 / 19) (hG : hl46G0 e (1 / 19) r ≤ hl46G0 e d r) :
    hl46S6F e (1 / 19) r ≤ hl46S6F e d r := by
  rw [hl46_G0_eq, hl46_G0_eq]
  have := hl46_corr_mono he he' hr hr' hd hd' le_rfl
  linarith

end Curves

end SmoothedOctagon
