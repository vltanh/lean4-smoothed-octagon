module

public import SmoothedOctagon.Terminal.Words
public import SmoothedOctagon.Terminal.Analysis.FourDensity

/-!
# Terminal comparison: four pieces

A closed cycle with the octagon word `2 0 1 2` has factors `(1/a, 1/b, 1/a, 1/b)` with `a, b > 0`,
`a² + b² = 1` (tangent closure), initial margins `(A, B, C)/√N` with `A = 2(s - 1)`,
`B = 2(1 - a + b)`, `C = 2(1 + a - b)`, `s = a + b`, `N = (s - 1)(s + 3)` (state closure), and raw
cost `8 δ(a, b)`, `δ(a, b) = [4s(s - 1) + 2(1 + a)(1 - b) log a + 2(1 - a)(1 + b) log b]/N`. The
density inequality `δ(a, b) ≥ δ_oct`, with equality only at `a = b`, is proved in
`Terminal/Analysis/FourDensity`.

* `Term.four_closure`: the tangent closure of the word `2 0 1 2` forces `r = p`, `z = q`,
  `p²q² = p² + q²`.
* `Term.Cycle.four_param`: the parametrization of a four-piece cycle (closure, forced state, cost).
* `Term.fourDensity`, `Term.fourPiece_density_ge`, `Term.fourPiece_density_eq`: the density
  inequality and its equality case, from `ra_four_density` (`Terminal/Analysis/FourDensity`).
* `Term.Cycle.four_rawCost_ge`: `8 δ_oct ≤ rawCost`.
-/

@[expose] public section

namespace SmoothedOctagon

namespace Term

open SmoothedPolygons

/-- The density `δ(a, b)` of the four-piece family. -/
noncomputable def fourDensity (a b : ℝ) : ℝ :=
  (4 * (a + b) * (a + b - 1) + 2 * (1 + a) * (1 - b) * Real.log a +
    2 * (1 - a) * (1 + b) * Real.log b) / ((a + b - 1) * (a + b + 3))

private lemma octagonDensity_eq_four :
    octagonDensity = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) := by
  rw [octagonDensity, ra_sqrt32, ra_sqrt8]

/-- **The four-piece density inequality**: `δ(a, b) ≥ δ_oct` on the quarter circle. It reduces to
the monotonicity of `x ↦ (2x + c) log x/(1 - x)`, `c = 2 + 2ab` (see `ra_four_density`). -/
theorem fourPiece_density_ge {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1) :
    octagonDensity ≤ fourDensity a b := by
  rw [octagonDensity_eq_four]
  exact (ra_four_density ha hb hab).1

/-- **Equality in the four-piece density inequality** only at `a = b`. -/
theorem fourPiece_density_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1)
    (h : fourDensity a b = octagonDensity) : a = b := by
  rw [octagonDensity_eq_four] at h
  exact (ra_four_density ha hb hab).2 h

private lemma tm_entries {M : Mat2} (h : M = triR) :
    M 0 0 = 0 ∧ M 0 1 = 1 ∧ M 1 0 = -1 ∧ M 1 1 = 1 := by
  subst h; simp [triR]

/-- Tangent closure for the octagon word `2 0 1 2`. -/
theorem four_closure {p q r z : ℝ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hz : 1 < z)
    (h : triFactor 2 p * (triFactor 0 q * (triFactor 1 r * triFactor 2 z)) = triR) :
    r = p ∧ z = q ∧ p ^ 2 * q ^ 2 = p ^ 2 + q ^ 2 := by
  have p0 : 0 < p := by linarith
  have q0 : 0 < q := by linarith
  have r0 : 0 < r := by linarith
  have z0 : 0 < z := by linarith
  obtain ⟨e00, e01, e10, e11⟩ := tm_entries h
  simp [triFactor, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  field_simp at e00 e01 e10 e11
  have hE00 : r ^ 2 + z ^ 2 - r ^ 2 * z ^ 2 = 0 := by
    rcases e00 with h | h | h
    · linarith
    · linarith
    · linarith
  have hH : p * z = q * r := by
    have : r * (q * r - p * z) = 0 := by linear_combination q * hE00 + z * e01
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hT : q ^ 2 * r ^ 2 * (q ^ 2 * r ^ 2 - q ^ 2 - r ^ 2) = 0 := by
    linear_combination (-z) * e11 - q ^ 2 * hE00 -
      ((p * z + q * r) * (q ^ 2 * r ^ 2 - q ^ 2 - r ^ 2) + q * r) * hH
  have hT3 : q ^ 2 * r ^ 2 - q ^ 2 - r ^ 2 = 0 := by
    rcases mul_eq_zero.1 hT with h | h
    · nlinarith [mul_pos q0 r0]
    · exact h
  have hqz : q = z := by
    have : (q ^ 2 - z ^ 2) * (r ^ 2 - 1) = 0 := by linear_combination hT3 + hE00
    rcases mul_eq_zero.1 this with h | h
    · nlinarith
    · nlinarith
  subst hqz
  have hpr : r = p := by
    have := hH
    rw [mul_comm] at this
    exact (mul_left_cancel₀ q0.ne' this).symm
  subst hpr
  exact ⟨rfl, rfl, by linarith⟩

/-- State closure for the octagon word, linear part: the twist forces `C x₀ = A x₂` and
`C x₁ = B x₂`. -/
private lemma four_lin {a b x0 x1 x2 m10 m11 m12 m21 m22 m32 m41 m42 : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hs : 1 < a + b)
    (s0g : m10 = (x2 + x0) * a⁻¹ - x2) (s0d : m11 = (x2 + x1) * a - x2) (s0a : m12 = x2)
    (s1g : m21 = (m10 + m11) * b⁻¹ - m10) (s1d : m22 = (m10 + m12) * b - m10)
    (s2g : m32 = (m21 + m22) * a⁻¹ - m21) (s3d : m41 = (m32 + m21) * b - m32)
    (s3a : m42 = m32) (tw1 : m41 = x0) (tw2 : m42 = x1) :
    2 * (1 + a - b) * x0 = 2 * (a + b - 1) * x2 ∧
      2 * (1 + a - b) * x1 = 2 * (1 - a + b) * x2 := by
  have key1 : a ^ 2 * b * (m41 - x0) = -(a + b - 1) * (-a ^ 2 * x1 - a ^ 2 * x2 + a * b * x0 -
      a * b * x2 + 2 * a * x2 - b ^ 2 * x0 - b ^ 2 * x2 + 2 * b * x0 + 2 * b * x2 - x0 - x2) := by
    simp only [s3d, s2g, s1g, s1d, s0g, s0d, s0a]
    field_simp
    ring
  have key2 : a ^ 2 * b * (m42 - x1) = (a + b - 1) * (-a ^ 2 * x1 - a ^ 2 * x2 +
      2 * a * x2 + b * x0 + b * x2 - x0 - x2) := by
    simp only [s3a, s2g, s1g, s1d, s0g, s0d, s0a]
    field_simp
    ring
  rw [tw1, sub_self, mul_zero] at key1
  rw [tw2, sub_self, mul_zero] at key2
  have hP1 : -a ^ 2 * x1 - a ^ 2 * x2 + a * b * x0 - a * b * x2 + 2 * a * x2 - b ^ 2 * x0 -
      b ^ 2 * x2 + 2 * b * x0 + 2 * b * x2 - x0 - x2 = 0 := by
    rcases mul_eq_zero.1 key1.symm with h | h
    · exfalso; linarith
    · exact h
  have hP2 : -a ^ 2 * x1 - a ^ 2 * x2 + 2 * a * x2 + b * x0 + b * x2 - x0 - x2 = 0 := by
    rcases mul_eq_zero.1 key2.symm with h | h
    · exfalso; linarith
    · exact h
  constructor
  · have : b * (2 * (1 + a - b) * x0 - 2 * (a + b - 1) * x2) = 0 := by
      linear_combination 2 * hP1 - 2 * hP2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hb.ne'
    · linarith
  · have : a ^ 2 * b * (2 * (1 + a - b) * x1 - 2 * (1 - a + b) * x2) = 0 := by
      linear_combination 2 * (b - 1) * hP1 - 2 * (a * b - b ^ 2 + 2 * b - 1) * hP2
    rcases mul_eq_zero.1 this with h | h
    · exfalso; have : 0 < a ^ 2 * b := by positivity
      linarith
    · linarith

/-- State closure for the octagon word, scale: with the quadric, the initial margins are
`(A, B, C)/√N`. -/
private lemma four_scale {a b x0 x1 x2 : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1)
    (_ha1 : a < 1) (hb1 : b < 1) (hs : 1 < a + b) (hx2pos : 0 < x2)
    (e0 : 2 * (1 + a - b) * x0 = 2 * (a + b - 1) * x2)
    (e1 : 2 * (1 + a - b) * x1 = 2 * (1 - a + b) * x2)
    (hq4 : x0 * x1 + x1 * x2 + x2 * x0 = 4) :
    x0 = 2 * (a + b - 1) / √((a + b - 1) * (a + b + 3)) ∧
      x1 = 2 * (1 - a + b) / √((a + b - 1) * (a + b + 3)) ∧
      x2 = 2 * (1 + a - b) / √((a + b - 1) * (a + b + 3)) := by
  have hC : 0 < 2 * (1 + a - b) := by linarith
  have hN : 0 < (a + b - 1) * (a + b + 3) := by nlinarith
  have hx2sq : x2 ^ 2 * ((a + b - 1) * (a + b + 3)) = (2 * (1 + a - b)) ^ 2 := by
    linear_combination ((2 * (1 + a - b)) ^ 2 / 4) * hq4 -
      ((2 * (1 - a + b) * x2 + 2 * (1 + a - b) * x2) / 4) * e0 -
      ((2 * (1 + a - b) * x0 + 2 * (1 + a - b) * x2) / 4) * e1 + 2 * x2 ^ 2 * hab
  have hsN : 0 < √((a + b - 1) * (a + b + 3)) := Real.sqrt_pos.2 hN
  have hsN2 : √((a + b - 1) * (a + b + 3)) ^ 2 = (a + b - 1) * (a + b + 3) :=
    Real.sq_sqrt hN.le
  have hx2' : x2 * √((a + b - 1) * (a + b + 3)) = 2 * (1 + a - b) := by
    have h := hx2sq
    rw [← hsN2, ← mul_pow] at h
    exact (pow_left_inj₀ (by positivity) hC.le two_ne_zero).1 h
  have hx2 : x2 = 2 * (1 + a - b) / √((a + b - 1) * (a + b + 3)) := by
    rw [eq_div_iff hsN.ne', hx2']
  refine ⟨?_, ?_, hx2⟩
  · rw [hx2] at e0
    field_simp at e0 ⊢
    nlinarith
  · rw [hx2] at e1
    field_simp at e1 ⊢
    nlinarith

/-- The raw cost of a vertex piece with margins `λ(C, A, B)`, `C + A = 4a`, `C + B = 4`, and
factor `a⁻¹`. -/
private lemma four_arc {a l A B C : ℝ} (ha : a ≠ 0) (hCA : C + A = 4 * a) (hCB : C + B = 4) :
    rawArc (l * C) (l * A) (l * B) a⁻¹ = l ^ 2 * (C * (8 * (1 - a) + C * Real.log a)) := by
  rw [rawArc, Real.log_inv, inv_inv]
  have e1 : l * C + l * A = l * (4 * a) := by rw [← hCA]; ring
  have e2 : l * C + l * B = l * 4 := by rw [← hCB]; ring
  rw [e1, e2]
  field_simp
  ring

/-- The four-piece raw cost. -/
private lemma four_cost {a b l : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1)
    (hl : l ^ 2 * ((a + b - 1) * (a + b + 3)) = 1) (hN : 0 < (a + b - 1) * (a + b + 3)) :
    rawArc (l * (2 * (1 + a - b))) (l * (2 * (a + b - 1))) (l * (2 * (1 - a + b))) a⁻¹ +
      rawArc (l * (2 * (1 - a + b))) (l * (2 * (a + b - 1))) (l * (2 * (1 + a - b))) b⁻¹ +
      rawArc (l * (2 * (1 + a - b))) (l * (2 * (a + b - 1))) (l * (2 * (1 - a + b))) a⁻¹ +
      rawArc (l * (2 * (1 - a + b))) (l * (2 * (a + b - 1))) (l * (2 * (1 + a - b))) b⁻¹ =
      8 * fourDensity a b := by
  rw [four_arc ha.ne' (by ring) (by ring), four_arc hb.ne' (by ring) (by ring), fourDensity,
    ← mul_div_assoc, eq_div_iff hN.ne']
  linear_combination (2 * (2 * (1 + a - b) * (8 * (1 - a) + 2 * (1 + a - b) * Real.log a) +
    2 * (1 - a + b) * (8 * (1 - b) + 2 * (1 - a + b) * Real.log b))) * hl +
    (8 * Real.log a + 8 * Real.log b - 64) * hab

namespace Cycle

/-- **The four-piece cycles**: tangent closure forces the factors `(1/a, 1/b, 1/a, 1/b)` with
`a² + b² = 1`, state closure forces the initial margins `(A, B, C)/√N`, and the raw cost is
`8 δ(a, b)`. -/
theorem four_param (c : Cycle 4) (h0 : c.lab 0 = 2) (h1 : c.lab 1 = 0) (h2 : c.lab 2 = 1)
    (h3 : c.lab 3 = 2) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = 1 ∧
      c.q 0 = a⁻¹ ∧ c.q 1 = b⁻¹ ∧ c.q 2 = a⁻¹ ∧ c.q 3 = b⁻¹ ∧
      c.m 0 0 = 2 * (a + b - 1) / √((a + b - 1) * (a + b + 3)) ∧
      c.m 0 1 = 2 * (1 - a + b) / √((a + b - 1) * (a + b + 3)) ∧
      c.m 0 2 = 2 * (1 + a - b) / √((a + b - 1) * (a + b + 3)) ∧
      c.rawCost = 8 * fourDensity a b := by
  -- tangent closure
  have hcl := c.closure 0
  simp only [List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, Matrix.mul_one, List.nil_append] at hcl
  simp only [Matrix.mul_assoc, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add, h0, h1, h2,
    h3] at hcl
  obtain ⟨hr, hz, hpq⟩ := four_closure (c.one_lt_q 0) (c.one_lt_q 1) (c.one_lt_q 2)
    (c.one_lt_q 3) hcl
  set a := (c.q 0)⁻¹ with ha_def
  set b := (c.q 1)⁻¹ with hb_def
  have hp1 := c.one_lt_q 0
  have hq1 := c.one_lt_q 1
  have ha : 0 < a := by positivity
  have hb : 0 < b := by positivity
  have ha1 : a < 1 := inv_lt_one_of_one_lt₀ hp1
  have hb1 : b < 1 := inv_lt_one_of_one_lt₀ hq1
  have hab : a ^ 2 + b ^ 2 = 1 := by
    rw [ha_def, hb_def, inv_pow, inv_pow]
    field_simp
    linarith
  have hs : 1 < a + b := by nlinarith [mul_pos ha hb]
  have hq0 : c.q 0 = a⁻¹ := by rw [ha_def, inv_inv]
  have hq1' : c.q 1 = b⁻¹ := by rw [hb_def, inv_inv]
  have hq2 : c.q 2 = a⁻¹ := by rw [hr, hq0]
  have hq3 : c.q 3 = b⁻¹ := by rw [hz, hq1']
  clear_value a b
  -- the one-arc margin maps and the twist
  have s0a := c.m_act 0
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, h0] at s0a
  have s0g := c.m_grow 0
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, h0, hq0, show (2 : Fin 3) + 1 = 0 from rfl] at s0g
  have s0d := c.m_decr 0
  simp only [show (0 : ℤ) + 1 = 1 by norm_num, h0, hq0, show (2 : Fin 3) - 1 = 1 from rfl, div_inv_eq_mul] at s0d
  have s1a := c.m_act 1
  simp only [show (1 : ℤ) + 1 = 2 by norm_num, h1] at s1a
  have s1g := c.m_grow 1
  simp only [show (1 : ℤ) + 1 = 2 by norm_num, h1, hq1', show (0 : Fin 3) + 1 = 1 from rfl] at s1g
  have s1d := c.m_decr 1
  simp only [show (1 : ℤ) + 1 = 2 by norm_num, h1, hq1', show (0 : Fin 3) - 1 = 2 from rfl, div_inv_eq_mul] at s1d
  have s2a := c.m_act 2
  simp only [show (2 : ℤ) + 1 = 3 by norm_num, h2] at s2a
  have s2g := c.m_grow 2
  simp only [show (2 : ℤ) + 1 = 3 by norm_num, h2, hq2, show (1 : Fin 3) + 1 = 2 from rfl] at s2g
  have s2d := c.m_decr 2
  simp only [show (2 : ℤ) + 1 = 3 by norm_num, h2, hq2, show (1 : Fin 3) - 1 = 0 from rfl, div_inv_eq_mul] at s2d
  have s3a := c.m_act 3
  simp only [show (3 : ℤ) + 1 = 4 by norm_num, h3] at s3a
  have s3g := c.m_grow 3
  simp only [show (3 : ℤ) + 1 = 4 by norm_num, h3, hq3, show (2 : Fin 3) + 1 = 0 from rfl] at s3g
  have s3d := c.m_decr 3
  simp only [show (3 : ℤ) + 1 = 4 by norm_num, h3, hq3, show (2 : Fin 3) - 1 = 1 from rfl, div_inv_eq_mul] at s3d
  have tw0 := c.m_add 0 0
  have tw1 := c.m_add 0 1
  have tw2 := c.m_add 0 2
  simp only [show ((0:ℤ) + ((4:ℕ):ℤ)) = 4 by norm_num, show (0 : Fin 3) - 1 = 2 from rfl,
    show (1 : Fin 3) - 1 = 0 from rfl, show (2 : Fin 3) - 1 = 1 from rfl] at tw0 tw1 tw2
  obtain ⟨e0, e1⟩ := four_lin ha hb hs s0g s0d s0a s1g s1d s2g (s2a ▸ s3d) s3a tw1 tw2
  obtain ⟨hx0, hx1, hx2⟩ := four_scale ha hb hab ha1 hb1 hs (c.m_pos 0 2) e0 e1 (c.m_quad 0)
  refine ⟨a, b, ha, hb, hab, hq0, hq1', hq2, hq3, hx0, hx1, hx2, ?_⟩
  -- the cost
  have hN : 0 < (a + b - 1) * (a + b + 3) := mul_pos (by linarith) (by linarith)
  have hsN : 0 < √((a + b - 1) * (a + b + 3)) := Real.sqrt_pos.2 hN
  set l := (√((a + b - 1) * (a + b + 3)))⁻¹ with hl_def
  have hl : l ^ 2 * ((a + b - 1) * (a + b + 3)) = 1 := by
    rw [hl_def, inv_pow, Real.sq_sqrt hN.le, inv_mul_cancel₀ hN.ne']
  have hx0' : c.m 0 0 = l * (2 * (a + b - 1)) := by rw [hx0, hl_def]; ring
  have hx1' : c.m 0 1 = l * (2 * (1 - a + b)) := by rw [hx1, hl_def]; ring
  have hx2' : c.m 0 2 = l * (2 * (1 + a - b)) := by rw [hx2, hl_def]; ring
  have ha0 := ha.ne'
  have hb0 := hb.ne'
  have m10 : c.m 1 0 = l * (2 * (1 - a + b)) := by rw [s0g, hx0', hx2']; field_simp; ring
  have m11 : c.m 1 1 = l * (2 * (a + b - 1)) := by rw [s0d, hx1', hx2']; ring
  have m12 : c.m 1 2 = l * (2 * (1 + a - b)) := by rw [s0a, hx2']
  have m20 : c.m 2 0 = l * (2 * (1 - a + b)) := by rw [s1a, m10]
  have m21 : c.m 2 1 = l * (2 * (1 + a - b)) := by rw [s1g, m10, m11]; field_simp; ring
  have m22 : c.m 2 2 = l * (2 * (a + b - 1)) := by rw [s1d, m10, m12]; ring
  have m31 : c.m 3 1 = l * (2 * (1 + a - b)) := by rw [s2a, m21]
  have m32 : c.m 3 2 = l * (2 * (1 - a + b)) := by rw [s2g, m21, m22]; field_simp; ring
  have m30 : c.m 3 0 = l * (2 * (a + b - 1)) := by rw [s2d, m21, m20]; ring
  rw [← four_cost ha hb hab hl hN]
  simp only [Cycle.rawCost, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Cycle.arc,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, h0, h1, h2, h3, hq0, hq1', hq2, hq3,
    show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) - 1 = 1 from rfl,
    show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) - 1 = 2 from rfl,
    show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) - 1 = 0 from rfl,
    m10, m11, m12, m20, m21, m22, m30, m31, m32]
  rw [← hx0', ← hx1', ← hx2']

/-- **Four-piece bound**: `8 δ_oct ≤ rawCost` for the octagon word. -/
theorem four_rawCost_ge (c : Cycle 4) (h0 : c.lab 0 = 2) (h1 : c.lab 1 = 0) (h2 : c.lab 2 = 1)
    (h3 : c.lab 3 = 2) : 8 * octagonDensity ≤ c.rawCost := by
  obtain ⟨a, b, ha, hb, hab, -, -, -, -, -, -, -, hcost⟩ := c.four_param h0 h1 h2 h3
  rw [hcost]
  linarith [fourPiece_density_ge ha hb hab]

end Cycle

end Term

end SmoothedOctagon
