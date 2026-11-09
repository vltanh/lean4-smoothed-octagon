module

public import SmoothedOctagon.Period.Defs

/-!
# Case F, scalar part: definitions and the window data

The scalar objects of the all-forward exclusion, in the dimensionless variables of the
global-minimum window `(p, b, a, c, d)`: `U = 4/a²`, `z = b/a`, `w = c/a`, `P = p/a`, `D = d/a`,
`S = 1 + z`, `T = 1 + w`, `K = 1 + U`, `Z = z² + U`, `W = w² + U`.

## Main API

* `ff_G a b` (the edge function, `8J = ∑ G(a_i, a_{i+1})`), `ff_g2 U x y = G(ax, ay)/a²`
  (`ff_G_mul`), `ff_fac x y z = (x + y)(y + z)/(y² + 4)` (the factor of an arc).
* `ff_f r = (r - r⁻¹)/2 - log r`, `ff_F x r = 1 + x² r - x r log r/(r - 1)` (the exterior floor).
* Physical row data of the stationarity rows: `ff_Cph` (four times a cost derivative), `ff_Mn`,
  `ff_Mm`, `ff_Mal`.
* Dimensionless row data: `ff_q`, `ff_A`, `ff_B`, `ff_alpha`, `ff_n`, `ff_m`, `ff_hd`
  (`h = (P + z)(1 + z)/(z² + U)`), the Casimir `ff_cas`.
* Centered data (the left row about the floor value `3/4`): `ff_Phi`, `ff_e0`, `ff_r`, `ff_L`, the
  residuals `ff_resS` (`𝓔_Σ`), `ff_resV` (`𝓔_v`), and the neighbour residual `ff_resN`.
* `ff_Win`: the physical window data that the period supplies; `ff_Dim`: its dimensionless form,
  with the reflection `ff_Dim.swap`.
-/

@[expose] public section

namespace SmoothedOctagon

/-! ### Edge function and factors -/

/-- The edge function
`G(a, b) = 3ab - 4 - (a² + b²) log(a + b) + (a² log(a² + 4) + b² log(b² + 4))/2`; the cost of an
all-forward period is `C = (√12/8) ∑ G(a_i, a_{i+1})`. -/
noncomputable def ff_G (a b : ℝ) : ℝ :=
  3 * a * b - 4 - (a ^ 2 + b ^ 2) * Real.log (a + b) +
    (a ^ 2 * Real.log (a ^ 2 + 4) + b ^ 2 * Real.log (b ^ 2 + 4)) / 2

/-- The dimensionless edge function `G(ax, ay)/a²` with `U = 4/a²` (`g_U(x) = ff_g2 U 1 x`). -/
noncomputable def ff_g2 (U x y : ℝ) : ℝ :=
  3 * x * y - U - (x ^ 2 + y ^ 2) * Real.log (x + y) +
    (x ^ 2 * Real.log (x ^ 2 + U) + y ^ 2 * Real.log (y ^ 2 + U)) / 2

/-- The factor `q = (x + y)(y + z)/(y² + 4)` of an arc with active margin `y` between arcs with
active margins `x` and `z` (all switches forward). -/
noncomputable def ff_fac (x y z : ℝ) : ℝ := (x + y) * (y + z) / (y ^ 2 + 4)

/-- `f(r) = (r - r⁻¹)/2 - log r`. -/
noncomputable def ff_f (r : ℝ) : ℝ := (r - r⁻¹) / 2 - Real.log r

/-- The exterior floor `F_x(r) = 1 + x² r - x r log r/(r - 1)`, used for `r > 1`. -/
noncomputable def ff_F (x r : ℝ) : ℝ := 1 + x ^ 2 * r - x * r * Real.log r / (r - 1)

/-! ### Physical row data -/

/-- Four times the cost derivative at an active margin `y` with neighbours `x`, `z`:
`A = Cph b a c`, `B = Cph p b a`, `C = Cph a c d`. -/
noncomputable def ff_Cph (x y z : ℝ) : ℝ :=
  x + y + z - y ^ 2 * (1 / (x + y) + 1 / (y + z)) + y ^ 3 / (y ^ 2 + 4) -
    y * Real.log (ff_fac x y z)

/-- The coefficient `M₁₁ = s²(4 - ab)(h - 1)/(a K_b)` of the left row, with `s = a + b`. -/
noncomputable def ff_Mn (a b h : ℝ) : ℝ := (a + b) ^ 2 * (4 - a * b) * (h - 1) / (a * (b ^ 2 + 4))

/-- The coefficient `M₁₂ = K²{a(q - 1) + (h - 1)(sq - a)}/(a s K_b)` of the left row. -/
noncomputable def ff_Mm (a b q h : ℝ) : ℝ :=
  (a ^ 2 + 4) ^ 2 * (a * (q - 1) + (h - 1) * ((a + b) * q - a)) / (a * (a + b) * (b ^ 2 + 4))

/-- The coefficient `K(hs - b)/(a K_b)` of `A` in the left row `R_L`. -/
noncomputable def ff_Mal (a b h : ℝ) : ℝ := (a ^ 2 + 4) * (h * (a + b) - b) / (a * (b ^ 2 + 4))

/-! ### Dimensionless row data -/

/-- `q = ST/K`. -/
noncomputable def ff_q (U z w : ℝ) : ℝ := (1 + z) * (1 + w) / (1 + U)

/-- The exterior factor `h = (P + z)(1 + z)/(z² + U)`. -/
noncomputable def ff_hd (U z P : ℝ) : ℝ := (P + z) * (1 + z) / (z ^ 2 + U)

/-- `A = 1 + z + w - 1/S - 1/T + 1/K - log q`. -/
noncomputable def ff_A (U z w : ℝ) : ℝ :=
  1 + z + w - 1 / (1 + z) - 1 / (1 + w) + 1 / (1 + U) - Real.log (ff_q U z w)

/-- `B = Zh/S + 1 - z²S/(Zh) - z²/S + z³/Z - z log h`. -/
noncomputable def ff_B (U z h : ℝ) : ℝ :=
  (z ^ 2 + U) * h / (1 + z) + 1 - z ^ 2 * (1 + z) / ((z ^ 2 + U) * h) - z ^ 2 / (1 + z) +
    z ^ 3 / (z ^ 2 + U) - z * Real.log h

/-- `α = K(hS - z)/Z`. -/
noncomputable def ff_alpha (U z h : ℝ) : ℝ := (1 + U) * (h * (1 + z) - z) / (z ^ 2 + U)

/-- `n = S²(U - z)(h - 1)/Z`. -/
noncomputable def ff_n (U z h : ℝ) : ℝ := (1 + z) ^ 2 * (U - z) * (h - 1) / (z ^ 2 + U)

/-- `m = (K²/(SZ)){q - 1 + (h - 1)(qS - 1)}`. -/
noncomputable def ff_m (U z w h : ℝ) : ℝ :=
  (1 + U) ^ 2 / ((1 + z) * (z ^ 2 + U)) *
    (ff_q U z w - 1 + (h - 1) * (ff_q U z w * (1 + z) - 1))

/-- The Casimir `γ² = K²(4uv - E²)/(16U²)`. -/
noncomputable def ff_cas (U u v E : ℝ) : ℝ := (1 + U) ^ 2 * (4 * u * v - E ^ 2) / (16 * U ^ 2)

/-! ### Centered data -/

/-- `Φ = f(S/2) + f(T/2) + f(4/K)`. -/
noncomputable def ff_Phi (U z w : ℝ) : ℝ := ff_f ((1 + z) / 2) + ff_f ((1 + w) / 2) + ff_f (4 / (1 + U))

/-- `e₀ = 1 - K/8 + 1/K`. -/
noncomputable def ff_e0 (U : ℝ) : ℝ := 1 - (1 + U) / 8 + 1 / (1 + U)

/-- The centered residual `r` of the left row, with `d = 3 - U`, `x = z - 1`, `H = h - 1`. -/
noncomputable def ff_r (U z w h : ℝ) : ℝ :=
  ((3 - U) * (z - 1) * ((3 - U) + 2 * (z - 1)) +
      (h - 1) * ((3 - U) ^ 2 * ((z - 1) ^ 2 + 4 * (z - 1) + 2) + 8 * (3 - U) * (z - 1) * z +
        2 * (z - 1) ^ 2 * (8 + 4 * (z - 1) - (z - 1) ^ 2))) / (8 * (1 + z) * (z ^ 2 + U)) +
    (h - 1) ^ 2 * z * ((3 - U) + 4 * (z - 1) + (z - 1) ^ 2) / (2 * h * (z ^ 2 + U)) +
    (1 + U) * (1 + (1 + z) * (h - 1)) / (z ^ 2 + U) * ff_Phi U z w - z * ff_f h

/-- The centered floor `L(z, h) = x(x + 2zH)/(4S²) + (zh/S) f(h)/H`; `F_{z/S}(h) = 3/4 + L(z, h)`.
-/
noncomputable def ff_L (z h : ℝ) : ℝ :=
  (z - 1) * ((z - 1) + 2 * z * (h - 1)) / (4 * (1 + z) ^ 2) + z * h / (1 + z) * (ff_f h / (h - 1))

/-- The sum residual `𝓔_Σ = r - n/35 - (m - n) L(w, I)`, `I = T²/W`. -/
noncomputable def ff_resS (U z w h : ℝ) : ℝ :=
  ff_r U z w h - ff_n U z h / 35 -
    (ff_m U z w h - ff_n U z h) * ff_L w ((1 + w) ^ 2 / (w ^ 2 + U))

/-- The larger-norm residual `𝓔_v = r - n L(z, h) - m/64`. -/
noncomputable def ff_resV (U z w h : ℝ) : ℝ :=
  ff_r U z w h - ff_n U z h * ff_L z h - ff_m U z w h / 64

/-- The neighbour residual `𝓔 = αA - B - n F_{z/S}(h) - m F_{w/T}(T²/W)`. -/
noncomputable def ff_resN (U z w h : ℝ) : ℝ :=
  ff_alpha U z h * ff_A U z w - ff_B U z h - ff_n U z h * ff_F (z / (1 + z)) h -
    ff_m U z w h * ff_F (w / (1 + w)) ((1 + w) ^ 2 / (w ^ 2 + U))

/-! ### The window data -/

/-- **The physical window data** of a global minimum `a` of an all-forward competitive normal period
with `N ≥ 7`: the five consecutive active margins `(p, b, a, c, d)`, the normal multiplier's
coordinates `(u, v, E)` in the central prefix frame (`u = 8 d_{-1}`, `v = 8 d_0`, `E = 16 e_0`), the
three stationarity rows, the two exterior floors, the seven-entry cost bound (with `n = N - 7`
further copies of `G(a, a)`) and the Casimir cap `γ² ≤ 23/125` (`wire_gam2_cap` gives the sharper
`γ² < 9193/50000`; the weaker cap suffices). -/
structure ff_Win where
  a : ℝ
  p : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  u : ℝ
  v : ℝ
  E : ℝ
  a_pos : 0 < a
  a_le_p : a ≤ p
  a_le_b : a ≤ b
  a_le_c : a ≤ c
  a_le_d : a ≤ d
  pb_lt : p * b < 4
  ab_lt : a * b < 4
  ac_lt : a * c < 4
  cd_lt : c * d < 4
  one_lt_h : 1 < ff_fac p b a
  one_lt_q : 1 < ff_fac b a c
  one_lt_k : 1 < ff_fac a c d
  row0 : (a + b) * u + (a + c) * v - a * E = ff_Cph b a c
  rowL : ff_Mn a b (ff_fac p b a) * u + ff_Mm a b (ff_fac b a c) (ff_fac p b a) * v =
    ff_Mal a b (ff_fac p b a) * ff_Cph b a c - ff_Cph p b a
  rowR : ff_Mm a c (ff_fac b a c) (ff_fac a c d) * u + ff_Mn a c (ff_fac a c d) * v =
    ff_Mal a c (ff_fac a c d) * ff_Cph b a c - ff_Cph a c d
  floorL : ff_F (b / (a + b)) (ff_fac p b a) ≤ u
  floorR : ff_F (c / (a + c)) (ff_fac a c d) ≤ v
  cost : ∃ n : ℕ, √3 / 4 * (ff_G a p + ff_G p b + ff_G b a + ff_G a c + ff_G c d + ff_G d a +
    (n + 1) * ff_G a a) ≤ octagonCost
  cap : (a ^ 2 + 4) ^ 2 * (4 * u * v - E ^ 2) / 256 ≤ 23 / 125

/-- **The dimensionless window data**: `U = 4/a²`, `z = b/a`, `w = c/a`, `P = p/a`,
`D = d/a`, with `h = ff_hd U z P`, `k = ff_hd U w D`, `q = ff_q U z w`. -/
structure ff_Dim where
  a : ℝ
  U : ℝ
  z : ℝ
  w : ℝ
  P : ℝ
  D : ℝ
  u : ℝ
  v : ℝ
  E : ℝ
  a_pos : 0 < a
  U_eq : U = 4 / a ^ 2
  one_le_z : 1 ≤ z
  one_le_w : 1 ≤ w
  one_le_P : 1 ≤ P
  one_le_D : 1 ≤ D
  Pz_lt : P * z < U
  z_lt : z < U
  w_lt : w < U
  wD_lt : w * D < U
  one_lt_h : 1 < ff_hd U z P
  one_lt_q : 1 < ff_q U z w
  one_lt_k : 1 < ff_hd U w D
  row0 : (1 + z) * u + (1 + w) * v - E = ff_A U z w
  rowL : ff_n U z (ff_hd U z P) * u + ff_m U z w (ff_hd U z P) * v =
    ff_alpha U z (ff_hd U z P) * ff_A U z w - ff_B U z (ff_hd U z P)
  rowR : ff_m U w z (ff_hd U w D) * u + ff_n U w (ff_hd U w D) * v =
    ff_alpha U w (ff_hd U w D) * ff_A U z w - ff_B U w (ff_hd U w D)
  floorL : ff_F (z / (1 + z)) (ff_hd U z P) ≤ u
  floorR : ff_F (w / (1 + w)) (ff_hd U w D) ≤ v
  cost : ∃ n : ℕ, √3 / 4 * (ff_G a (a * P) + ff_G (a * P) (a * z) + ff_G (a * z) a +
    ff_G a (a * w) + ff_G (a * w) (a * D) + ff_G (a * D) a + (n + 1) * ff_G a a) ≤ octagonCost
  cap : ff_cas U u v E ≤ 23 / 125

namespace ff_Dim

variable (W : ff_Dim)

theorem ff_q_comm (U z w : ℝ) : ff_q U z w = ff_q U w z := by unfold ff_q; ring

theorem ff_A_comm (U z w : ℝ) : ff_A U z w = ff_A U w z := by
  unfold ff_A; rw [ff_q_comm]; ring

theorem ff_G_comm (x y : ℝ) : ff_G x y = ff_G y x := by unfold ff_G; rw [add_comm x y]; ring

/-- The reflection `(z, P, u) ↔ (w, D, v)` of the window (an algebraic symmetry of the equations of
the same lift). -/
def swap : ff_Dim where
  a := W.a
  U := W.U
  z := W.w
  w := W.z
  P := W.D
  D := W.P
  u := W.v
  v := W.u
  E := W.E
  a_pos := W.a_pos
  U_eq := W.U_eq
  one_le_z := W.one_le_w
  one_le_w := W.one_le_z
  one_le_P := W.one_le_D
  one_le_D := W.one_le_P
  Pz_lt := by rw [mul_comm]; exact W.wD_lt
  z_lt := W.w_lt
  w_lt := W.z_lt
  wD_lt := by rw [mul_comm]; exact W.Pz_lt
  one_lt_h := W.one_lt_k
  one_lt_q := by rw [ff_q_comm]; exact W.one_lt_q
  one_lt_k := W.one_lt_h
  row0 := by rw [ff_A_comm]; linear_combination W.row0
  rowL := by rw [ff_A_comm]; linear_combination W.rowR
  rowR := by rw [ff_A_comm]; linear_combination W.rowL
  floorL := W.floorR
  floorR := W.floorL
  cost := by
    obtain ⟨n, hn⟩ := W.cost
    refine ⟨n, le_trans (le_of_eq ?_) hn⟩
    rw [ff_G_comm (W.a * W.D) (W.a * W.w), ff_G_comm (W.a * W.w) W.a,
      ff_G_comm (W.a * W.P) (W.a * W.z), ff_G_comm (W.a * W.z) W.a,
      ff_G_comm W.a (W.a * W.D), ff_G_comm W.a (W.a * W.P)]
    ring
  cap := by
    have h : ff_cas W.U W.v W.u W.E = ff_cas W.U W.u W.v W.E := by unfold ff_cas; ring
    rw [h]; exact W.cap

end ff_Dim

end SmoothedOctagon
