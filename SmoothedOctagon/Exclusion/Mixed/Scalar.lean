module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Case M2: the scalar functions of the smaller-turn window

The real functions of the smaller-turn window, of the costate calculus (cost derivative, turn
secant, switch threshold) and of the missing-control floor, used by every M2 module. Norms are
*eight times* switch norms; pairings at a reverse centre are *sixteen times* cross pairings.

* `m2U x = 1 - x + x²` (the incident ceiling `U`).
* `m2g a b = (a² + ab + b²)/(a + b)²`: the switch threshold of a switch between active margins `a`
  and `b` (`8 d ≥ m2g` at a forward switch, `8 d ≤ m2g` at a reverse one);
  `m2g a b = m2U (a/(a + b)) = g_a(b) = g_b(a)` (`m2g_eq_m2U`, `m2g_comm`).
* `m2Sec A B P`: the turn secant, the average of `g_B` over `[A, P]`, with its continuous
  value `g_B(A)` at `A = P`.
* `m2F x q`: the missing-control floor (for every `x`, see `Mixed/Interface`).
* `m2Stat p a n`: four times the cost derivative at a same-sign arc, so that
  `C_a = m2Stat b a c` and `C_d = m2Stat c d r`.
* The window formulas: `m2h` (central diagonal), `m2wOf` (transported norm),
  `m2hd`, `m2Root` (the root function `R_d`), `m2Next` (the next transported norm `t`),
  `m2Cas` (the squared Casimir `γ² = uvK²/64 - h²`).
-/

@[expose] public section

namespace SmoothedOctagon

/-- `U(x) = 1 - x + x²`. -/
noncomputable def m2U (x : ℝ) : ℝ := 1 - x + x ^ 2

/-- The switch threshold `(a² + ab + b²)/(a + b)²`. -/
noncomputable def m2g (a b : ℝ) : ℝ := (a ^ 2 + a * b + b ^ 2) / (a + b) ^ 2

/-- **The turn secant**: for `A ≠ P`,
`Sec(A, B, P) = 1 + B²/((A + B)(P + B)) - (B/(P - A)) log((P + B)/(A + B))`, the average of
`g_B(x) = 1 - Bx/(B + x)²` over `[A, P]`; at `A = P` its continuous value `g_B(A)`. -/
noncomputable def m2Sec (A B P : ℝ) : ℝ :=
  if A = P then m2g A B
  else 1 + B ^ 2 / ((A + B) * (P + B)) - B / (P - A) * Real.log ((P + B) / (A + B))

/-- **The missing-control floor**: `F_x(q) = 1 + x²q - xq log q/(q - 1)`,
`F_x(1) = U(x)`. -/
noncomputable def m2F (x q : ℝ) : ℝ :=
  if q = 1 then m2U x else 1 + x ^ 2 * q - x * q * Real.log q / (q - 1)

/-- Four times the cost derivative at a same-sign arc with active margin `a` and neighbours `p`,
`n`: `p + a + n - a²(1/(p + a) + 1/(a + n)) + a³/K - a log((p + a)(a + n)/K)`,
`K = a² + 4`. -/
noncomputable def m2Stat (p a n : ℝ) : ℝ :=
  p + a + n - a ^ 2 * (1 / (p + a) + 1 / (a + n)) + a ^ 3 / (a ^ 2 + 4)
    - a * Real.log ((p + a) * (a + n) / (a ^ 2 + 4))

/-- The central diagonal `h = (K/(16a))(S u + T v - C_a)` with `S = a + b`, `T = a + c`. -/
noncomputable def m2h (a b c u v : ℝ) : ℝ :=
  (a ^ 2 + 4) / (16 * a) * ((a + b) * u + (a + c) * v - m2Stat b a c)

/-- `Y = W² - T² = (c + d)² - (a + c)²`. -/
noncomputable def m2Y (a c d : ℝ) : ℝ := (c + d) ^ 2 - (a + c) ^ 2

/-- The diagonal at `d`, `h_d = h + vY/8`. -/
noncomputable def m2hd (a c d v h : ℝ) : ℝ := h + v * m2Y a c d / 8

/-- The transported norm `w = (uK² + 16hY + vY²)/Q²`, `K = a² + 4`, `Q = d² + 4`. -/
noncomputable def m2wOf (a c d u v h : ℝ) : ℝ :=
  ((a ^ 2 + 4) ^ 2 * u + 16 * h * m2Y a c d + v * m2Y a c d ^ 2) / (d ^ 2 + 4) ^ 2

/-- **The root function** `R_d = C_d - Wv - Zw + 16 d h_d/Q`, with `w = m2wOf`. -/
noncomputable def m2Root (a c d r u v h : ℝ) : ℝ :=
  m2Stat c d r - (c + d) * v - (d + r) * m2wOf a c d u v h + 16 * d * m2hd a c d v h / (d ^ 2 + 4)

/-- The next transported norm `t = (Q²v - 16 h_d Z² + w Z⁴)/K_r²`, `Z = d + r`,
`K_r = r² + 4`. -/
noncomputable def m2Next (a c d r u v h : ℝ) : ℝ :=
  ((d ^ 2 + 4) ^ 2 * v - 16 * m2hd a c d v h * (d + r) ^ 2 + m2wOf a c d u v h * (d + r) ^ 4) /
    (r ^ 2 + 4) ^ 2

/-- The squared Casimir `γ² = det U_a = uvK²/64 - h²`. -/
noncomputable def m2Cas (a u v h : ℝ) : ℝ := u * v * (a ^ 2 + 4) ^ 2 / 64 - h ^ 2

theorem m2g_comm (a b : ℝ) : m2g a b = m2g b a := by
  unfold m2g; ring_nf

theorem m2g_eq_m2U {a b : ℝ} (h : 0 < a + b) : m2g a b = m2U (a / (a + b)) := by
  unfold m2g m2U
  field_simp
  ring

theorem m2Sec_self (A B : ℝ) : m2Sec A B A = m2g A B := by simp [m2Sec]

theorem m2Sec_of_ne {A B P : ℝ} (h : A ≠ P) :
    m2Sec A B P =
      1 + B ^ 2 / ((A + B) * (P + B)) - B / (P - A) * Real.log ((P + B) / (A + B)) := by
  simp [m2Sec, h]

/-- The secant is symmetric in its outer arguments. -/
theorem m2Sec_comm (A B P : ℝ) : m2Sec A B P = m2Sec P B A := by
  by_cases h : A = P
  · subst h; rfl
  rw [m2Sec_of_ne h, m2Sec_of_ne (Ne.symm h)]
  have hAP : P - A ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have hPA : A - P ≠ 0 := sub_ne_zero.2 h
  rw [show (A + B) / (P + B) = ((P + B) / (A + B))⁻¹ by rw [inv_div], Real.log_inv,
    show A - P = -(P - A) by ring, div_neg]
  ring

theorem m2F_of_ne {x q : ℝ} (h : q ≠ 1) :
    m2F x q = 1 + x ^ 2 * q - x * q * Real.log q / (q - 1) := by
  simp [m2F, h]

end SmoothedOctagon
