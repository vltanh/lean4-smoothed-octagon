module

public import SmoothedOctagon.Period.Costate

/-!
# The reverse-four principle

`GLOBAL_REVERSE_PERIOD_EXCLUSION` (1) and `MIXED_GLOBAL_MINIMUM_STRUCTURE` (11). Four consecutive
pieces `k, …, k + 3` of a normal vertex period with three reverse switches between them (labels
`i, i - 1, i + 1, i`) cannot have the active margin of piece `k + 2`, nor that of piece `k + 1`, at
most the other three.

Route: the needle (first-variation) identity GRPE (24) is replaced by an exact identity between the
costate coordinates of `Period/Costate.lean` at the three interior switches. For the third
position, with margins `(P, Q, Z)` at the first interior switch (labels `i, i + 1, i - 1`), factors
`b, c` of the two interior pieces, `A, B` the margins `p_{i+1}, p_i` at the second switch,
`σ_j = 2α_j + β_j = p_j H_j`: the four vanishing active Hamiltonians and `⟨Λ_R, X⟩ = 0` give
`B (c - 1) σ_{i+1} + b (A (c - 1) + Z (b - 1)) σ_i' = -√3 Z N` (σ at the first and second interior
switch), with `N` the cost derivative GRPE (18). Both left Hamiltonians are `≤ 0` by the maximum
principle; under the minimum hypothesis `N < 0` (GRPE (20)-(23)). The second position uses the
needles `σ_{i-1}` at the third and `σ_i` at the second interior switch, with coefficients
`(b - 1) B` and `c (A (c - 1) + Z (b - 1))`, and the reflected `N`; this replaces the reflection
argument MGMS §§1-4.

## Main API

* `cstEta t = t - 1 - log t`, `cstZeta t = t log t - t + 1`, `cstRevN A B Z b c` (GRPE (18)).
* `cst_eta_pos`, `cst_log_pade` (`(t² + 4t + 1) log t > 3 (t² - 1)`), `cstRevN_neg` (GRPE (23)).
* `cst_rev4_third_identity`, `cst_rev4_second_identity`: the exact costate identities.
* `CostateCycle.reverse_four_third`, `CostateCycle.reverse_four_second`: the reverse-four
  principle in both interior positions.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set

/-! ### Elementary inequalities -/

/-- `η(t) = t - 1 - log t`. -/
noncomputable def cstEta (t : ℝ) : ℝ := t - 1 - Real.log t

/-- `ζ(t) = t log t - t + 1`. -/
noncomputable def cstZeta (t : ℝ) : ℝ := t * Real.log t - t + 1

theorem cst_eta_pos {t : ℝ} (ht : 1 < t) : 0 < cstEta t := by
  have := Real.log_lt_sub_one_of_pos (by linarith) ht.ne'
  rw [cstEta]; linarith

/-- The Padé bound `log t > 3 (t² - 1)/(t² + 4t + 1)` for `t > 1` (GRPE (20)). -/
theorem cst_log_pade {t : ℝ} (ht : 1 < t) : 3 * (t ^ 2 - 1) < (t ^ 2 + 4 * t + 1) * Real.log t := by
  set ψ : ℝ → ℝ := fun x ↦ Real.log x - 3 * (x ^ 2 - 1) / (x ^ 2 + 4 * x + 1) with hψ
  have hden : ∀ x : ℝ, 0 < x → 0 < x ^ 2 + 4 * x + 1 := fun x hx ↦ by positivity
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt ψ ((x - 1) ^ 4 / (x * (x ^ 2 + 4 * x + 1) ^ 2)) x := by
    intro x hx
    have h1 := Real.hasDerivAt_log hx.ne'
    have hn : HasDerivAt (fun x : ℝ ↦ 3 * (x ^ 2 - 1)) (3 * (2 * x)) x := by
      simpa using (((hasDerivAt_pow 2 x).sub_const 1).const_mul 3)
    have hdn : HasDerivAt (fun x : ℝ ↦ x ^ 2 + 4 * x + 1) (2 * x + 4) x := by
      have := ((hasDerivAt_pow 2 x).add ((hasDerivAt_id x).const_mul 4)).add_const 1
      simpa using this
    have h2 := hn.div hdn (hden x hx).ne'
    refine (h1.sub h2).congr_deriv ?_
    have := (hden x hx).ne'
    field_simp
    ring
  have hmono : StrictMonoOn ψ (Ici 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 1) ?_ ?_
    · intro x hx
      exact (hd x (lt_of_lt_of_le one_pos hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx1 : 1 < x := hx
      have hx0 : 0 < x := lt_trans one_pos hx1
      rw [(hd x hx0).deriv]
      have : 0 < (x - 1) ^ 4 := by
        have : 0 < x - 1 := by linarith
        positivity
      have := hden x hx0
      positivity
  have h := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 ht.le) ht
  simp only [hψ, Real.log_one] at h
  have hd1 := hden t (by linarith)
  norm_num at h
  rw [div_lt_iff₀ hd1] at h
  linarith

theorem cst_zeta_gt {t : ℝ} (ht : 1 < t) : (2 * t + 1) * cstEta t < (t + 2) * cstZeta t := by
  have := cst_log_pade ht
  simp only [cstEta, cstZeta]
  nlinarith

theorem cst_eta_lt_zeta {t : ℝ} (ht : 1 < t) : cstEta t < cstZeta t := by
  have h1 := cst_zeta_gt ht
  have h2 := cst_eta_pos ht
  nlinarith

/-- The cost derivative `N` of GRPE (18). -/
noncomputable def cstRevN (A B Z b c : ℝ) : ℝ :=
  b * (b - 1) * A * (A * c * cstEta c - B * cstZeta c) +
    (c - 1) * (b * A * (B + b * Z) * cstEta b - B * (b * A + Z) * cstZeta b)

/-- **GRPE (23).** Under the minimum hypothesis GRPE (7), `N < 0`. -/
theorem cstRevN_neg {A B Z b c : ℝ} (hb : 1 < b) (hc : 1 < c) (hA : 0 < A) (hZ : 0 < Z)
    (hZA : A ≤ Z) (hB1 : b * A + (b - 1) * Z ≤ B) (hB2 : (2 * c - 1) * A ≤ B) :
    cstRevN A B Z b c < 0 := by
  have ηb := cst_eta_pos hb
  have ηc := cst_eta_pos hc
  have ζb := cst_zeta_gt hb
  have ζc := cst_zeta_gt hc
  have lb := cst_eta_lt_zeta hb
  have lc := cst_eta_lt_zeta hc
  set eb := cstEta b
  set ec := cstEta c
  set zb := cstZeta b
  set zc := cstZeta c
  have hBpos : 0 < B := by nlinarith
  -- the first bracket
  have hT1 : A * c * ec - B * zc < 0 := by
    have h1 : c * A < B := by nlinarith
    have h2 : c * A * ec < c * A * zc := by
      have : 0 < c * A := by positivity
      nlinarith
    nlinarith
  -- the second bracket, at the smallest admissible `B`
  set B0 := b * A + (b - 1) * Z with hB0
  have hT2 : b * A * (B + b * Z) * eb - B * (b * A + Z) * zb ≤
      b * A * (B0 + b * Z) * eb - B0 * (b * A + Z) * zb := by
    have hcoef : b * A * eb - (b * A + Z) * zb ≤ 0 := by
      have : 0 < b * A := by positivity
      nlinarith
    nlinarith
  have hT3 : b * A * (B0 + b * Z) * eb - B0 * (b * A + Z) * zb < 0 := by
    have hpos : 0 < b ^ 2 * A ^ 2 + b ^ 2 * A * Z + (b - 1) * Z ^ 2 := by
      have : 0 < b - 1 := by linarith
      positivity
    have key : (b + 2) * (b * A * (B0 + b * Z) * eb - B0 * (b * A + Z) * zb) <
        -((b - 1) * eb * (b ^ 2 * A ^ 2 + 2 * b * Z * (Z - A) + Z ^ 2)) := by
      have e : B0 * (b * A + Z) = b ^ 2 * A ^ 2 + b ^ 2 * A * Z + (b - 1) * Z ^ 2 := by
        rw [hB0]; ring
      have h1 : (b ^ 2 * A ^ 2 + b ^ 2 * A * Z + (b - 1) * Z ^ 2) * ((2 * b + 1) * eb) <
          (b ^ 2 * A ^ 2 + b ^ 2 * A * Z + (b - 1) * Z ^ 2) * ((b + 2) * zb) :=
        mul_lt_mul_of_pos_left ζb hpos
      have h2 : (b + 2) * (b * A * (B0 + b * Z) * eb - B0 * (b * A + Z) * zb) =
          b * A * (b * A + (2 * b - 1) * Z) * (b + 2) * eb -
            (b ^ 2 * A ^ 2 + b ^ 2 * A * Z + (b - 1) * Z ^ 2) * ((b + 2) * zb) := by
        rw [e, hB0]; ring
      rw [h2]
      nlinarith
    have hnn : 0 ≤ (b - 1) * eb * (b ^ 2 * A ^ 2 + 2 * b * Z * (Z - A) + Z ^ 2) := by
      have : 0 ≤ Z - A := by linarith
      have : 0 ≤ b - 1 := by linarith
      positivity
    have hb2 : 0 < b + 2 := by linarith
    nlinarith
  have hc1 : 0 < c - 1 := by linarith
  have hbA : 0 < b * (b - 1) * A := by
    have : 0 < b - 1 := by linarith
    positivity
  simp only [cstRevN]
  have := mul_neg_of_pos_of_neg hbA hT1
  have := mul_neg_of_pos_of_neg hc1 (lt_of_le_of_lt hT2 hT3)
  linarith

/-! ### The exact costate identities -/

/-- **The reverse-four identity, third position.** The costate coordinates `x, y` (`α, β`) at the
first interior switch of a window with labels `i, i - 1, i + 1, i` (margins `(P, Q, Z)` in the
label order `i, i + 1, i - 1`), transported over the factors `b, c` of the two interior pieces
(`u, v` at the second switch, `r, s` at the third), with the four vanishing active Hamiltonians and
`⟨Λ_R, X⟩ = 0`, satisfy
`B (c - 1) σ_{i+1} + b (A (c - 1) + Z (b - 1)) σ'_i = -√3 Z N(A, B, Z, b, c)`. -/
theorem cst_rev4_third_identity {P Q Z b c A B x0 x1 x2 y0 y1 y2 u0 u1 u2 v0 v1 v2 r0 r1 s0 s1 : ℝ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hA : A = (Z + Q) / b - Z) (hB : B = (Z + P) * b - Z)
    (hu2 : u2 = x2 + costateAct Z P Q b)
    (hu0 : u0 = b ^ 2 * (x2 + x0) + costateAGrow Z P b - u2)
    (hu1 : u1 = b⁻¹ ^ 2 * (x2 + x1) + costateADecr Z Q b - u2)
    (hv2 : v2 = y2 - 2 * costateAct Z P Q b)
    (hv0 : v0 = b * (y2 + y0) + costateBGrow Z P b - v2)
    (hv1 : v1 = b⁻¹ * (y2 + y1) + costateBDecr Z Q b - v2)
    (hr1 : r1 = u1 + costateAct A Z B c)
    (hr0 : r0 = c⁻¹ ^ 2 * (u1 + u0) + costateADecr A B c - r1)
    (hs1 : s1 = v1 - 2 * costateAct A Z B c)
    (hs0 : s0 = c⁻¹ * (v1 + v0) + costateBDecr A B c - s1)
    (h1 : 2 * x0 + y0 = 0) (h2 : 2 * x2 + y2 = 0) (h3 : 2 * u1 + v1 = 0) (h4 : 2 * r0 + s0 = 0)
    (h5 : y0 * (Q + Z) + y1 * (P + Z) + y2 * (P + Q) = 0) :
    B * (c - 1) * (2 * x1 + y1) + b * (A * (c - 1) + Z * (b - 1)) * (2 * u0 + v0) =
      -(√3 * Z * cstRevN A B Z b c) := by
  subst hu2 hv2
  subst hu0 hu1 hv0 hv1
  subst hr1 hs1
  subst hr0 hs0
  subst hA hB
  linear_combination (norm := skip)
    (b ^ 2 * (c - 1) * (Q - Z * b + Z)) * h1 +
    ((b - 1) * (b + 1) * (c - 1) * (P * b + Q)) * h2 +
    (b * (c - 1) * (P * b ^ 2 + Z * b ^ 2 + Z * b * c - Z * c - Z)) * h3 +
    (Z * b * c ^ 2 * (b - 1)) * h4 +
    (-(b * (b - 1) * (c - 1))) * h5
  simp only [costateAct, costateAGrow, costateADecr, costateBGrow, costateBDecr, cstRevN, cstEta,
    cstZeta]
  field_simp
  ring

/-- **The reverse-four identity, second position.** With the notation of
`cst_rev4_third_identity` and `r2, s2` the coordinates of label `i - 1` at the third switch:
`(b - 1) B σ''_{i-1} + c (A (c - 1) + Z (b - 1)) σ'_i = -√3 A N(Z, B, A, c, b)`. -/
theorem cst_rev4_second_identity
    {P Q Z b c A B x0 x1 x2 y0 y1 y2 u0 u1 u2 v0 v1 v2 r0 r1 r2 s0 s1 s2 : ℝ}
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hA : A = (Z + Q) / b - Z) (hB : B = (Z + P) * b - Z)
    (hu2 : u2 = x2 + costateAct Z P Q b)
    (hu0 : u0 = b ^ 2 * (x2 + x0) + costateAGrow Z P b - u2)
    (hu1 : u1 = b⁻¹ ^ 2 * (x2 + x1) + costateADecr Z Q b - u2)
    (hv2 : v2 = y2 - 2 * costateAct Z P Q b)
    (hv0 : v0 = b * (y2 + y0) + costateBGrow Z P b - v2)
    (hv1 : v1 = b⁻¹ * (y2 + y1) + costateBDecr Z Q b - v2)
    (hr1 : r1 = u1 + costateAct A Z B c)
    (hr0 : r0 = c⁻¹ ^ 2 * (u1 + u0) + costateADecr A B c - r1)
    (hr2 : r2 = c ^ 2 * (u1 + u2) + costateAGrow A Z c - r1)
    (hs1 : s1 = v1 - 2 * costateAct A Z B c)
    (hs0 : s0 = c⁻¹ * (v1 + v0) + costateBDecr A B c - s1)
    (hs2 : s2 = c * (v1 + v2) + costateBGrow A Z c - s1)
    (h1 : 2 * x0 + y0 = 0) (h2 : 2 * x2 + y2 = 0) (h3 : 2 * u1 + v1 = 0) (h4 : 2 * r0 + s0 = 0)
    (h5 : y0 * (Q + Z) + y1 * (P + Z) + y2 * (P + Q) = 0) :
    (b - 1) * B * (2 * r2 + s2) + c * (A * (c - 1) + Z * (b - 1)) * (2 * u0 + v0) =
      -(√3 * A * cstRevN Z B A c b) := by
  subst hr2 hs2
  subst hu2 hv2
  subst hu0 hu1 hv0 hv1
  subst hr1 hs1
  subst hr0 hs0
  subst hA hB
  linear_combination (norm := skip)
    (-(b * c * (c - 1) * (-Q + Z * b - Z))) * h1 +
    (c * (b - 1) * (P * b ^ 2 * c + Q * b * c - Q * b + Q * c - Q + Z * b ^ 2 - Z * b * c +
      Z * c - Z) / b) * h2 +
    ((b - 1) * (c - 1) * (c + 1) * (P * b + Z * b + Z * c - Z)) * h3 +
    (Z * c ^ 3 * (b - 1)) * h4 +
    (-(c * (b - 1) * (c - 1))) * h5
  simp only [costateAct, costateAGrow, costateADecr, costateBGrow, costateBDecr, cstRevN, cstEta,
    cstZeta]
  field_simp
  ring

/-! ### The reverse-four principle on a costate cycle -/

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

/-- The data of a reverse window `k, k + 1, k + 2, k + 3` (labels `i, i - 1, i + 1, i`): the
transport over its two interior pieces, the vanishing active Hamiltonians and `⟨Λ_R, X⟩ = 0`, in
the variables of `cst_rev4_third_identity`. -/
private theorem rev4_data (k : ℤ) (h0 : C.lab (k + 1) = C.lab k - 1)
    (h1 : C.lab (k + 2) = C.lab (k + 1) - 1) (h2 : C.lab (k + 3) = C.lab (k + 2) - 1)
    {P Q Z b c A B x0 x1 x2 y0 y1 y2 u0 u1 u2 v0 v1 v2 r0 r1 r2 s0 s1 s2 : ℝ}
    (eP : C.m (k + 1) (C.lab k) = P) (eQ : C.m (k + 1) (C.lab k + 1) = Q)
    (eZ : C.m (k + 1) (C.lab k - 1) = Z) (eb : C.q (k + 1) = b) (ec : C.q (k + 2) = c)
    (eA : C.m (k + 2) (C.lab k + 1) = A) (eB : C.m (k + 2) (C.lab k) = B)
    (ex0 : C.α (k + 1) (C.lab k) = x0) (ex1 : C.α (k + 1) (C.lab k + 1) = x1)
    (ex2 : C.α (k + 1) (C.lab k - 1) = x2) (ey0 : C.β (k + 1) (C.lab k) = y0)
    (ey1 : C.β (k + 1) (C.lab k + 1) = y1) (ey2 : C.β (k + 1) (C.lab k - 1) = y2)
    (eu0 : C.α (k + 2) (C.lab k) = u0) (eu1 : C.α (k + 2) (C.lab k + 1) = u1)
    (eu2 : C.α (k + 2) (C.lab k - 1) = u2) (ev0 : C.β (k + 2) (C.lab k) = v0)
    (ev1 : C.β (k + 2) (C.lab k + 1) = v1) (ev2 : C.β (k + 2) (C.lab k - 1) = v2)
    (er0 : C.α (k + 3) (C.lab k) = r0) (er1 : C.α (k + 3) (C.lab k + 1) = r1)
    (er2 : C.α (k + 3) (C.lab k - 1) = r2) (es0 : C.β (k + 3) (C.lab k) = s0)
    (es1 : C.β (k + 3) (C.lab k + 1) = s1) (es2 : C.β (k + 3) (C.lab k - 1) = s2) :
    (A = (Z + Q) / b - Z ∧ B = (Z + P) * b - Z ∧
      u2 = x2 + costateAct Z P Q b ∧
      u0 = b ^ 2 * (x2 + x0) + costateAGrow Z P b - u2 ∧
      u1 = b⁻¹ ^ 2 * (x2 + x1) + costateADecr Z Q b - u2 ∧
      v2 = y2 - 2 * costateAct Z P Q b ∧
      v0 = b * (y2 + y0) + costateBGrow Z P b - v2 ∧
      v1 = b⁻¹ * (y2 + y1) + costateBDecr Z Q b - v2 ∧
      r1 = u1 + costateAct A Z B c ∧
      r0 = c⁻¹ ^ 2 * (u1 + u0) + costateADecr A B c - r1 ∧
      r2 = c ^ 2 * (u1 + u2) + costateAGrow A Z c - r1 ∧
      s1 = v1 - 2 * costateAct A Z B c ∧
      s0 = c⁻¹ * (v1 + v0) + costateBDecr A B c - s1 ∧
      s2 = c * (v1 + v2) + costateBGrow A Z c - s1) ∧
    (2 * x0 + y0 = 0 ∧ 2 * x2 + y2 = 0 ∧ 2 * u1 + v1 = 0 ∧ 2 * r0 + s0 = 0 ∧
      y0 * (Q + Z) + y1 * (P + Z) + y2 * (P + Q) = 0) ∧
    (C.act k = P ∧ C.act (k + 1) = Z ∧ C.act (k + 2) = A ∧ C.act (k + 3) = (A + B) / c - A) ∧
    (2 * x1 + y1 ≤ 0 ∧ 2 * u0 + v0 ≤ 0 ∧ 2 * r2 + s2 ≤ 0) := by
  subst eP eQ eZ eb ec eA eB ex0 ex1 ex2 ey0 ey1 ey2 eu0 eu1 eu2 ev0 ev1 ev2 er0 er1 er2 es0 es1 es2
  set i := C.lab k with hi
  have e1 : i - 1 + 1 = i := sub_add_cancel i 1
  have e2 : i - 1 - 1 = i + 1 := cst_fin_sub_one_sub_one i
  have e3 : i + 1 + 1 = i - 1 := cst_fin_add_one_add_one i
  have e4 : i + 1 - 1 = i := add_sub_cancel_right i 1
  have l1 : C.lab (k + 1) = i - 1 := h0
  have l2 : C.lab (k + 2) = i + 1 := by rw [h1, l1, e2]
  have l3 : C.lab (k + 3) = i := by rw [h2, l2, e4]
  obtain ⟨M0, -, -, -, -, -, -, -, -⟩ := C.transport k (i := i) rfl
  obtain ⟨M1, M2, M3, T1, T2, T3, T4, T5, T6⟩ := C.transport (k + 1) l1
  obtain ⟨N1, -, N3, U1, U2, U3, U4, U5, U6⟩ := C.transport (k + 2) l2
  rw [show k + 1 + 1 = k + 2 by ring] at M1 M2 M3 T1 T2 T3 T4 T5 T6
  rw [show k + 2 + 1 = k + 3 by ring] at N1 N3 U1 U2 U3 U4 U5 U6
  simp only [e1, e2] at M1 M2 M3 T1 T2 T3 T4 T5 T6
  simp only [e3, e4] at N1 N3 U1 U2 U3 U4 U5 U6
  rw [M1] at U1 U2 U4 U5
  have hs1 := C.sig_act_succ k
  have hs2 := C.sig_act (k + 1)
  have hs3 := C.sig_act (k + 2)
  have hs4 := C.sig_act (k + 3)
  rw [l1] at hs2
  rw [l2] at hs3
  rw [l3] at hs4
  simp only [sig] at hs1
  refine ⟨⟨M3, M2, T1, by linarith, by linarith, T4, by linarith, by linarith, U1, by linarith,
    by linarith, U4, by linarith, by linarith⟩, ⟨hs1, hs2, hs3, hs4, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨C.sig_le (k + 1) (i + 1), C.sig_le (k + 2) i, C.sig_le (k + 3) (i - 1)⟩⟩
  · have := C.perp_rot (k + 1) i
    linear_combination this
  · simp only [act]; rw [← M0]
  · simp only [act, l1]
  · simp only [act, l2]
  · simp only [act, l3]; rw [N3]

/-- **The reverse-four principle, third position** (GRPE (1)). In a window of four pieces with
three reverse switches, the active margin of the third piece is not at most the other three. -/
theorem reverse_four_third (k : ℤ) (h0 : C.lab (k + 1) = C.lab k - 1)
    (h1 : C.lab (k + 2) = C.lab (k + 1) - 1) (h2 : C.lab (k + 3) = C.lab (k + 2) - 1) :
    ¬ (C.act (k + 2) ≤ C.act k ∧ C.act (k + 2) ≤ C.act (k + 1) ∧
      C.act (k + 2) ≤ C.act (k + 3)) := by
  rintro ⟨m0, m1, m3⟩
  obtain ⟨⟨hA, hB, hu2, hu0, hu1, hv2, hv0, hv1, hr1, hr0, -, hs1, hs0, -⟩,
    ⟨z1, z2, z3, z4, z5⟩, ⟨a0, a1, a2, a3⟩, ⟨n1, n2, -⟩⟩ :=
    C.rev4_data k h0 h1 h2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl
  have hb := C.one_lt_q (k + 1)
  have hc := C.one_lt_q (k + 2)
  have key := cst_rev4_third_identity (by positivity) (by positivity) hA hB hu2 hu0 hu1 hv2 hv0
    hv1 hr1 hr0 hs1 hs0 z1 z2 z3 z4 z5
  clear hu2 hu0 hu1 hv2 hv0 hv1 hr1 hr0 hs1 hs0 z1 z2 z3 z4 z5
  have hApos : 0 < C.m (k + 2) (C.lab k + 1) := by rw [← a2]; exact C.act_pos _
  have hZpos : 0 < C.m (k + 1) (C.lab k - 1) := by rw [← a1]; exact C.act_pos _
  have hPpos : 0 < C.m (k + 1) (C.lab k) := by rw [← a0]; exact C.act_pos _
  rw [a0, a2] at m0
  rw [a1, a2] at m1
  rw [a2, a3] at m3
  clear a0 a1 a2 a3
  generalize C.m (k + 2) (C.lab k + 1) = A at *
  generalize C.m (k + 2) (C.lab k) = B at *
  generalize C.m (k + 1) (C.lab k - 1) = Z at *
  generalize C.m (k + 1) (C.lab k) = P at *
  generalize C.q (k + 1) = b at *
  generalize C.q (k + 2) = c at *
  generalize 2 * C.α (k + 1) (C.lab k + 1) + C.β (k + 1) (C.lab k + 1) = σ₁ at *
  generalize 2 * C.α (k + 2) (C.lab k) + C.β (k + 2) (C.lab k) = σ₂ at *
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hBpos : 0 < B := by
    have e : B = (b - 1) * Z + b * P := by rw [hB]; ring
    have : 0 < b - 1 := by linarith
    rw [e]; positivity
  -- the minimum hypothesis GRPE (7)
  have hB1 : b * A + (b - 1) * Z ≤ B := by
    have := mul_le_mul_of_nonneg_left m0 hb0.le
    rw [hB]; linarith
  have hB2 : (2 * c - 1) * A ≤ B := by
    rw [le_sub_iff_add_le, le_div_iff₀ hc0] at m3
    linarith
  have hN := cstRevN_neg hb hc hApos hZpos m1 hB1 hB2
  have hw1 : 0 ≤ B * (c - 1) := by
    have : 0 < c - 1 := by linarith
    positivity
  have hw2 : 0 ≤ b * (A * (c - 1) + Z * (b - 1)) := by
    have : 0 < c - 1 := by linarith
    have : 0 < b - 1 := by linarith
    positivity
  have h3 : (0 : ℝ) < √3 := by positivity
  have p1 := mul_pos (mul_pos h3 hZpos) (neg_pos.2 hN)
  have p2 := mul_nonpos_of_nonneg_of_nonpos hw1 n1
  have p3 := mul_nonpos_of_nonneg_of_nonpos hw2 n2
  linarith

/-- **The reverse-four principle, second position** (MGMS (11)). In a window of four pieces with
three reverse switches, the active margin of the second piece is not at most the other three.
Route: a direct costate identity (`cst_rev4_second_identity`) replaces the reflection of
MGMS §§1-4. -/
theorem reverse_four_second (k : ℤ) (h0 : C.lab (k + 1) = C.lab k - 1)
    (h1 : C.lab (k + 2) = C.lab (k + 1) - 1) (h2 : C.lab (k + 3) = C.lab (k + 2) - 1) :
    ¬ (C.act (k + 1) ≤ C.act k ∧ C.act (k + 1) ≤ C.act (k + 2) ∧
      C.act (k + 1) ≤ C.act (k + 3)) := by
  rintro ⟨m0, m2, m3⟩
  obtain ⟨⟨hA, hB, hu2, hu0, hu1, hv2, hv0, hv1, hr1, hr0, hr2, hs1, hs0, hs2⟩,
    ⟨z1, z2, z3, z4, z5⟩, ⟨a0, a1, a2, a3⟩, ⟨-, n2, n3⟩⟩ :=
    C.rev4_data k h0 h1 h2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl
  have hb := C.one_lt_q (k + 1)
  have hc := C.one_lt_q (k + 2)
  have key := cst_rev4_second_identity (by positivity) (by positivity) hA hB hu2 hu0 hu1 hv2 hv0
    hv1 hr1 hr0 hr2 hs1 hs0 hs2 z1 z2 z3 z4 z5
  clear hu2 hu0 hu1 hv2 hv0 hv1 hr1 hr0 hr2 hs1 hs0 hs2 z1 z2 z3 z4 z5
  have hApos : 0 < C.m (k + 2) (C.lab k + 1) := by rw [← a2]; exact C.act_pos _
  have hZpos : 0 < C.m (k + 1) (C.lab k - 1) := by rw [← a1]; exact C.act_pos _
  have hPpos : 0 < C.m (k + 1) (C.lab k) := by rw [← a0]; exact C.act_pos _
  rw [a0, a1] at m0
  rw [a1, a2] at m2
  rw [a1, a3] at m3
  clear a0 a1 a2 a3
  generalize C.m (k + 2) (C.lab k + 1) = A at *
  generalize C.m (k + 2) (C.lab k) = B at *
  generalize C.m (k + 1) (C.lab k - 1) = Z at *
  generalize C.m (k + 1) (C.lab k) = P at *
  generalize C.q (k + 1) = b at *
  generalize C.q (k + 2) = c at *
  generalize 2 * C.α (k + 3) (C.lab k - 1) + C.β (k + 3) (C.lab k - 1) = σ₃ at *
  generalize 2 * C.α (k + 2) (C.lab k) + C.β (k + 2) (C.lab k) = σ₂ at *
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  -- the reflected minimum hypothesis
  have hB1 : c * Z + (c - 1) * A ≤ B := by
    rw [le_sub_iff_add_le, le_div_iff₀ hc0] at m3
    linarith
  have hB2 : (2 * b - 1) * Z ≤ B := by
    have := mul_le_mul_of_nonneg_left m0 hb0.le
    rw [hB]; linarith
  have hBpos : 0 < B := by
    have : 0 < (2 * b - 1) * Z := by
      have : 0 < 2 * b - 1 := by linarith
      positivity
    linarith
  have hN := cstRevN_neg hc hb hZpos hApos m2 hB1 hB2
  have hw1 : 0 ≤ (b - 1) * B := by
    have : 0 < b - 1 := by linarith
    positivity
  have hw2 : 0 ≤ c * (A * (c - 1) + Z * (b - 1)) := by
    have : 0 < c - 1 := by linarith
    have : 0 < b - 1 := by linarith
    positivity
  have h3 : (0 : ℝ) < √3 := by positivity
  have p1 := mul_pos (mul_pos h3 hApos) (neg_pos.2 hN)
  have p2 := mul_nonpos_of_nonneg_of_nonpos hw1 n3
  have p3 := mul_nonpos_of_nonneg_of_nonpos hw2 n2
  linarith

end CostateCycle

end SmoothedOctagon
