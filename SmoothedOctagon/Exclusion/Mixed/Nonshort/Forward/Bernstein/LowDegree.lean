module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Bernstein

/-!
# Case M2, forward successor: further Bernstein lemmas

The generic lemmas of `Nonshort/Forward/Bernstein` used only by the small-gap certificates (same conventions).
-/

@[expose] public section

namespace SmoothedOctagon

/-- A Bernstein form of degree 2 with positive coefficients is positive. -/
theorem nsfBernPos2 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) :
    0 < c0 * b ^ (2 : ℕ) + c1 * a * b + c2 * a ^ (2 : ℕ) := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c2 * a ^ (2 : ℕ) := by positivity
    have h'' : 0 ≤ c0 * b ^ (2 : ℕ) + c1 * a * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ (2 : ℕ) := by positivity
    have h'' : 0 ≤ c1 * a * b + c2 * a ^ (2 : ℕ) := by positivity
    linarith

/-- A Bernstein form of degree 3 with positive coefficients is positive. -/
theorem nsfBernPos3 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) :
    0 < c0 * b ^ (3 : ℕ) + c1 * a * b ^ (2 : ℕ) + c2 * a ^ (2 : ℕ) * b + c3 * a ^ (3 : ℕ) := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c3 * a ^ (3 : ℕ) := by positivity
    have h'' : 0 ≤ c0 * b ^ (3 : ℕ) + c1 * a * b ^ (2 : ℕ) + c2 * a ^ (2 : ℕ) * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ (3 : ℕ) := by positivity
    have h'' : 0 ≤ c1 * a * b ^ (2 : ℕ) + c2 * a ^ (2 : ℕ) * b + c3 * a ^ (3 : ℕ) := by positivity
    linarith

/-- Bernstein positivity of degree 7 on `[0, g]`, with abstract coefficients. -/
theorem nsfBern0g7 {g y c0 c1 c2 c3 c4 c5 c6 c7 : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ g) (hg : 0 < g)
    (hb0 : 0 < c0)
    (hb1 : 0 < 7 * c0 + c1 * g)
    (hb2 : 0 < 21 * c0 + 6 * c1 * g + c2 * g ^ (2 : ℕ))
    (hb3 : 0 < 35 * c0 + 15 * c1 * g + 5 * c2 * g ^ (2 : ℕ) + c3 * g ^ (3 : ℕ))
    (hb4 : 0 < 35 * c0 + 20 * c1 * g + 10 * c2 * g ^ (2 : ℕ) + 4 * c3 * g ^ (3 : ℕ) + c4 * g ^ (4 : ℕ))
    (hb5 : 0 < 21 * c0 + 15 * c1 * g + 10 * c2 * g ^ (2 : ℕ) + 6 * c3 * g ^ (3 : ℕ) + 3 * c4 * g ^ (4 : ℕ) + c5 * g ^ (5 : ℕ))
    (hb6 : 0 < 7 * c0 + 6 * c1 * g + 5 * c2 * g ^ (2 : ℕ) + 4 * c3 * g ^ (3 : ℕ) + 3 * c4 * g ^ (4 : ℕ) + 2 * c5 * g ^ (5 : ℕ) + c6 * g ^ (6 : ℕ))
    (hb7 : 0 < c0 + c1 * g + c2 * g ^ (2 : ℕ) + c3 * g ^ (3 : ℕ) + c4 * g ^ (4 : ℕ) + c5 * g ^ (5 : ℕ) + c6 * g ^ (6 : ℕ) + c7 * g ^ (7 : ℕ)) :
    0 < c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ) + c5 * y ^ (5 : ℕ) + c6 * y ^ (6 : ℕ) + c7 * y ^ (7 : ℕ) := by
  have hpos := nsfBernPos7 (a := y) (b := g - y) h0 (by linarith) (by linarith) hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  have e : g ^ (7 : ℕ) * (c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ) + c5 * y ^ (5 : ℕ) + c6 * y ^ (6 : ℕ) + c7 * y ^ (7 : ℕ)) = (c0) * (g - y) ^ (7 : ℕ) + (7 * c0 + c1 * g) * y * (g - y) ^ (6 : ℕ) + (21 * c0 + 6 * c1 * g + c2 * g ^ (2 : ℕ)) * y ^ (2 : ℕ) * (g - y) ^ (5 : ℕ) + (35 * c0 + 15 * c1 * g + 5 * c2 * g ^ (2 : ℕ) + c3 * g ^ (3 : ℕ)) * y ^ (3 : ℕ) * (g - y) ^ (4 : ℕ) + (35 * c0 + 20 * c1 * g + 10 * c2 * g ^ (2 : ℕ) + 4 * c3 * g ^ (3 : ℕ) + c4 * g ^ (4 : ℕ)) * y ^ (4 : ℕ) * (g - y) ^ (3 : ℕ) + (21 * c0 + 15 * c1 * g + 10 * c2 * g ^ (2 : ℕ) + 6 * c3 * g ^ (3 : ℕ) + 3 * c4 * g ^ (4 : ℕ) + c5 * g ^ (5 : ℕ)) * y ^ (5 : ℕ) * (g - y) ^ (2 : ℕ) + (7 * c0 + 6 * c1 * g + 5 * c2 * g ^ (2 : ℕ) + 4 * c3 * g ^ (3 : ℕ) + 3 * c4 * g ^ (4 : ℕ) + 2 * c5 * g ^ (5 : ℕ) + c6 * g ^ (6 : ℕ)) * y ^ (6 : ℕ) * (g - y) + (c0 + c1 * g + c2 * g ^ (2 : ℕ) + c3 * g ^ (3 : ℕ) + c4 * g ^ (4 : ℕ) + c5 * g ^ (5 : ℕ) + c6 * g ^ (6 : ℕ) + c7 * g ^ (7 : ℕ)) * y ^ (7 : ℕ) := by ring
  rw [← e] at hpos
  exact pos_of_mul_pos_right hpos (by positivity)

/-- Bernstein positivity of degree 2 on `[0, 1/30]`, with abstract coefficients. -/
theorem nsfBernI2_0_1_1_30 {y c0 c1 c2 : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ (1 / 30))
    (hb0 : 0 < c0)
    (hb1 : 0 < 2 * c0 + (1 / 30) * c1)
    (hb2 : 0 < c0 + (1 / 30) * c1 + (1 / 900) * c2) :
    0 < c0 + c1 * y + c2 * y ^ (2 : ℕ) := by
  have hpos := nsfBernPos2 (a := (y - 0)) (b := ((1 / 30) - y)) (by linarith) (by linarith) (by linarith) hb0 hb1 hb2
  have e : ((1 / 30) : ℝ) ^ (2 : ℕ) * (c0 + c1 * y + c2 * y ^ (2 : ℕ)) = (c0) * ((1 / 30) - y) ^ (2 : ℕ) + (2 * c0 + (1 / 30) * c1) * (y - 0) * ((1 / 30) - y) + (c0 + (1 / 30) * c1 + (1 / 900) * c2) * (y - 0) ^ (2 : ℕ) := by ring
  rw [← e] at hpos
  exact pos_of_mul_pos_right hpos (by norm_num)

/-- Bernstein positivity of degree 3 on `[0, 1]`, with abstract coefficients. -/
theorem nsfBernI3_0_1_1_1 {y c0 c1 c2 c3 : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1)
    (hb0 : 0 < c0)
    (hb1 : 0 < 3 * c0 + c1)
    (hb2 : 0 < 3 * c0 + 2 * c1 + c2)
    (hb3 : 0 < c0 + c1 + c2 + c3) :
    0 < c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) := by
  have hpos := nsfBernPos3 (a := (y - 0)) (b := (1 - y)) (by linarith) (by linarith) (by linarith) hb0 hb1 hb2 hb3
  have e : (1 : ℝ) ^ (3 : ℕ) * (c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ)) = (c0) * (1 - y) ^ (3 : ℕ) + (3 * c0 + c1) * (y - 0) * (1 - y) ^ (2 : ℕ) + (3 * c0 + 2 * c1 + c2) * (y - 0) ^ (2 : ℕ) * (1 - y) + (c0 + c1 + c2 + c3) * (y - 0) ^ (3 : ℕ) := by ring
  rw [← e] at hpos
  exact pos_of_mul_pos_right hpos (by norm_num)

theorem nsfZgenTr3 {a b y c0 c1 c2 c3 : ℝ} (ha : a ≠ 0) :
    (c0 * (b) ^ (3 : ℕ)) + (c1 * (a) * (b) ^ (2 : ℕ)) * (y * (b) / (a)) + (c2 * (a) ^ (2 : ℕ) * (b)) * (y * (b) / (a)) ^ (2 : ℕ) + (c3 * (a) ^ (3 : ℕ)) * (y * (b) / (a)) ^ (3 : ℕ) = (b) ^ (3 : ℕ) * (c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ)) := by
  field_simp

end SmoothedOctagon
