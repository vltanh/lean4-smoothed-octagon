module

public import SmoothedOctagon.Exclusion.Mixed.Scalar
public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Point

/-!
# Case M2: the scalar data of the windows

The scalar data that case M2 extracts from one actual period, as structures of real numbers with
their necessary conditions as fields. The period-level modules (`Mixed/Centre`,
`Mixed/Extraction`) produce them; the scalar exclusions (`Mixed/Comparison`, `Mixed/Nonshort/Reverse`,
`Mixed/Nonshort/Forward`, `Mixed/SmallerShort`) consume them, so the scalar arguments
are independent of the period-level argument.

* `m2E`, `m2Gam`: the centre pairing and the squared Casimir at a reverse centre.
* `M2Centre`: a reverse centre.
* `M2Window`: the smaller-nonshort window `0(p), 1(b), 0(a), 2(c), 0(d), 1(r)`, with its order,
  star, factor and log-concavity conditions, the compact-domain bounds, the reverse-centre scale
  bound, the turn secants, switching inequalities and floors, the stationarity and transport
  identities and the Casimir bounds; `M2Window.ForwardNext`, `M2Window.ReverseNext`: the two
  alternatives for the first actual switch after `r`.
* `M2Short`: the smaller-short window, with the chosen turn outgoing, with its transport to the
  next reverse centre, the middle-switch slack and the window-defect inequality.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The centre pairing (sixteen times the cross pairing `e`, `E = 16 h/K`) at a reverse centre
with active margin `a`, neighbours `p` (before) and `n` (after) and incident norms `ui`, `uo`:
`E = 1 + r + t - ρ + log(ρ/(rt)) - (1 - ui)/r -
(1 - uo)/t` with `r = a/(a + p)`, `t = a/(a + n)`, `ρ = a²/(a² + 4)`. -/
noncomputable def m2E (a p n ui uo : ℝ) : ℝ :=
  1 + a / (a + p) + a / (a + n) - a ^ 2 / (a ^ 2 + 4) +
    Real.log (a ^ 2 / (a ^ 2 + 4) / (a / (a + p) * (a / (a + n)))) -
    (1 - ui) / (a / (a + p)) - (1 - uo) / (a / (a + n))

/-- The squared Casimir at a reverse centre, `γ² = (4 ui uo - E²)/(16 (1 - ρ)²)`. -/
noncomputable def m2Gam (a ui uo E : ℝ) : ℝ :=
  (4 * ui * uo - E ^ 2) / (16 * (1 - a ^ 2 / (a ^ 2 + 4)) ^ 2)

/-- **A reverse centre**: active margin `a`,
neighbours `p`, `n` (turns), their far neighbours `pp`, `nn`, incident norms `ui`, `uo` (the turn
secants), the centre pairing `E` and the squared Casimir `Γ`. -/
structure M2Centre where
  pp : ℝ
  p : ℝ
  a : ℝ
  n : ℝ
  nn : ℝ
  ui : ℝ
  uo : ℝ
  E : ℝ
  Γ : ℝ
  a_pos : 0 < a
  /-- The strict centre minimum. -/
  a_lt_p : a < p
  a_lt_n : a < n
  pp_pos : 0 < pp
  nn_pos : 0 < nn
  /-- The positive reverse factor `K/((a + p)(a + n)) > 1`. -/
  factor : (a + p) * (a + n) < a ^ 2 + 4
  /-- The turn secants. -/
  ui_eq : ui = m2Sec a p pp
  uo_eq : uo = m2Sec a n nn
  /-- The reverse switching inequalities. -/
  ui_le : ui ≤ m2g a p
  uo_le : uo ≤ m2g a n
  /-- Centre stationarity. -/
  E_eq : E = m2E a p n ui uo
  /-- The Gram determinant. -/
  Γ_eq : Γ = m2Gam a ui uo E

/-- **The smaller-nonshort window**. Consecutive actual pieces with labels and
active margins `0(p), 1(b), 0(a), 2(c), 0(d), 1(r)` (switch signs `+, -, -, +, +`), where `a` is a
global minimum of the active margins at a reverse centre and `c` is the smaller adjacent turn;
`u, v` are the turn norms at `b` and `c`, `h` the central diagonal and `w` the norm of the switch
`d → r`, all from the same actual multiplier. -/
structure M2Window where
  p : ℝ
  b : ℝ
  a : ℝ
  c : ℝ
  d : ℝ
  r : ℝ
  u : ℝ
  v : ℝ
  h : ℝ
  w : ℝ
  a_pos : 0 < a
  /-- The order of the active margins: `a` is a global minimum and `c` is the smaller turn. -/
  a_lt_b : a < b
  a_lt_c : a < c
  c_le_b : c ≤ b
  a_lt_p : a < p
  a_lt_d : a < d
  a_le_r : a ≤ r
  /-- Strict star at the five switches. -/
  star_pb : p * b < 4
  star_ab : a * b < 4
  star_ac : a * c < 4
  star_cd : c * d < 4
  star_dr : d * r < 4
  /-- The same-sign factors: `K/(ST) > 1`, `q = WZ/Q > 1`. -/
  central : (a + b) * (a + c) < a ^ 2 + 4
  factor_d : d ^ 2 + 4 < (c + d) * (d + r)
  /-- Three-arc log-concavity on `a, c, d`. -/
  logconc : a * d < c ^ 2
  /-- The compact-domain bounds (minimum margin `m = 2/15`). -/
  a_ge : 2 / 15 ≤ a
  margin_cd : c * d + 2 / 15 * (c + d) ≤ 4
  margin_dr : d * r + 2 / 15 * (d + r) ≤ 4
  d_le : d ≤ 8
  r_le : r ≤ 8
  pair_ac : 1 / 2 ≤ a + c
  pair_cd : 1 / 2 ≤ c + d
  pair_dr : 1 / 2 ≤ d + r
  /-- The reverse-centre scale bound. -/
  scale : a ^ 2 < 12 / 17
  /-- The turn secants. -/
  u_eq : u = m2Sec a b p
  v_eq : v = m2Sec a c d
  /-- The switching inequalities (weak forms). -/
  u_ge : m2g p b ≤ u
  u_le : u ≤ m2g a b
  v_le : v ≤ m2g a c
  v_ge : m2g c d ≤ v
  w_ge : m2g d r ≤ w
  /-- The missing-control floors at the doubly forward piece `d`. -/
  v_floor : m2F (d / (c + d)) ((c + d) * (d + r) / (d ^ 2 + 4)) ≤ v
  w_floor : m2F (d / (d + r)) ((c + d) * (d + r) / (d ^ 2 + 4)) ≤ w
  /-- Central stationarity. -/
  h_eq : h = m2h a b c u v
  /-- The transport of the multiplier to the switch `d → r`. -/
  w_eq : w = m2wOf a c d u v h
  /-- Stationarity at the first forward piece `d` (the root equation `R_d = 0`). -/
  root : m2Root a c d r u v h = 0
  /-- The Casimir bounds `27/256 < γ² < 9193/50000`. -/
  cas_lt : m2Cas a u v h < 9193 / 50000
  cas_gt : 27 / 256 < m2Cas a u v h

namespace M2Window

variable (W : M2Window)

/-- The transported norm `t` of the switch after `r`. -/
noncomputable def t : ℝ := m2Next W.a W.c W.d W.r W.u W.v W.h

/-- **The next switch is forward**: the switch after `r` is forward, to an active margin `s ≥ a`;
the piece `r` then has both incident switches forward, factor `q_r = (d + r)(r + s)/(r² + 4) > 1`,
outgoing norm `t ≥ g_r(s)` and the missing-control floors. -/
def ForwardNext : Prop :=
  ∃ s : ℝ, W.a ≤ s ∧ W.r * s < 4 ∧ W.r ^ 2 + 4 < (W.d + W.r) * (W.r + s) ∧
    m2g W.r s ≤ W.t ∧
    m2F (W.r / (W.d + W.r)) ((W.d + W.r) * (W.r + s) / (W.r ^ 2 + 4)) ≤ W.w ∧
    m2F (W.r / (W.r + s)) ((W.d + W.r) * (W.r + s) / (W.r ^ 2 + 4)) ≤ W.t

/-- **The next switch is reverse**: the switch after `r` is reverse, to the next reverse centre
with active margin `A ≥ a`; the turn `r` has factor `(d + r)/(r + A) > 1`, secant
`w = Sec(A, r, d)`, outgoing reverse inequality `w ≤ g_r(A)` and log-concavity `A d < r²`. -/
def ReverseNext : Prop :=
  ∃ A : ℝ, W.a ≤ A ∧ A < W.d ∧ A * W.d < W.r ^ 2 ∧ W.w = m2Sec A W.r W.d ∧ W.w ≤ m2g W.r A

end M2Window

/-- **The smaller-short window**, with the chosen turn outgoing (after reflecting the period if
necessary). Consecutive actual pieces with active margins `pb, b, a, C, B, A, Pf` (pieces
`m - 2, …, m + 4`; switch signs `+, -, -, +, -, -, +`): `a` a global minimum at a reverse
centre, `C ≤ b` the smaller adjacent turn with a short forward run, `B` the other turn of the
short bridge, `A` the next reverse centre and `Pf` its far neighbour. Norms: `u` of the three
bridge switches `a|C`, `C|B`, `B|A`; `v` of the switch `b|a`; `w` of `A|Pf`; pairings `E` at `a`,
`EL` at `A`; squared Casimir `Γ`. The reduced coordinates are `x = C/a`, `β = B/a`, `α = A/a`,
`r = 1/(1 + x)`, `δ = β/x - 1`, `ρ = a²/(a² + 4)`. -/
structure M2Short where
  pb : ℝ
  b : ℝ
  a : ℝ
  C : ℝ
  B : ℝ
  A : ℝ
  Pf : ℝ
  u : ℝ
  v : ℝ
  w : ℝ
  E : ℝ
  EL : ℝ
  Γ : ℝ
  a_pos : 0 < a
  /-- Global minimality and the strict centre minima at `a` and `A`. -/
  a_lt_b : a < b
  a_lt_C : a < C
  a_le_A : a ≤ A
  a_le_pb : a ≤ pb
  A_lt_B : A < B
  A_lt_Pf : A < Pf
  /-- The smaller turn. -/
  C_le_b : C ≤ b
  /-- The turn `B` has factor `(C + B)/(B + A) > 1`. -/
  A_lt_C : A < C
  /-- Strict star at the six switches. -/
  star_pb : pb * b < 4
  star_ab : a * b < 4
  star_aC : a * C < 4
  star_CB : C * B < 4
  star_BA : B * A < 4
  star_APf : A * Pf < 4
  /-- The two reverse-centre factors. -/
  central : (a + b) * (a + C) < a ^ 2 + 4
  central_A : (B + A) * (A + Pf) < A ^ 2 + 4
  /-- Compact domain and the reverse-centre scale bound at `a` and `A`. -/
  a_ge : 2 / 15 ≤ a
  scale : a ^ 2 < 12 / 17
  scale_A : A ^ 2 < 12 / 17
  /-- The turn secants. -/
  u_eq : u = m2Sec a C B
  u_eq' : u = m2Sec C B A
  v_eq : v = m2Sec a b pb
  /-- The switching inequalities. -/
  u_le : u ≤ m2g a C
  u_ge : m2g C B ≤ u
  u_le' : u ≤ m2g B A
  v_le : v ≤ m2g a b
  v_ge : m2g pb b ≤ v
  w_le : w ≤ m2g A Pf
  /-- `w` is a turn norm (the switch `A → Pf` enters the turn `Pf`), so `w ≥ 3/4`. -/
  w_ge : 3 / 4 ≤ w
  /-- Centre stationarity at `a` and at `A`. -/
  E_eq : E = m2E a b C v u
  EL_eq : EL = m2E A B Pf u w
  /-- The Gram determinant at `a` and at `A`, and the Casimir bounds. -/
  Γ_eq : Γ = m2Gam a v u E
  Γ_eq' : Γ = m2Gam A u w EL
  cas_lt : Γ < 9193 / 50000
  cas_gt : 27 / 256 < Γ
  /-- The same-lift transport to `A`: with `λ = K_a/K_A`,
  `D = α² + 2αβ + 1 + 2x - 2βx`, `d = λρD`: `w = λ²v + d²u - dλE`, `EL = 2du - λE`. -/
  w_transport :
    w = ((a ^ 2 + 4) / (A ^ 2 + 4)) ^ 2 * v +
      ((a ^ 2 + 4) / (A ^ 2 + 4) * (a ^ 2 / (a ^ 2 + 4)) *
        ((A / a) ^ 2 + 2 * (A / a) * (B / a) + 1 + 2 * (C / a) - 2 * (B / a) * (C / a))) ^ 2 * u -
      (a ^ 2 + 4) / (A ^ 2 + 4) * (a ^ 2 / (a ^ 2 + 4)) *
        ((A / a) ^ 2 + 2 * (A / a) * (B / a) + 1 + 2 * (C / a) - 2 * (B / a) * (C / a)) *
        ((a ^ 2 + 4) / (A ^ 2 + 4)) * E
  EL_transport :
    EL = 2 * ((a ^ 2 + 4) / (A ^ 2 + 4) * (a ^ 2 / (a ^ 2 + 4)) *
        ((A / a) ^ 2 + 2 * (A / a) * (B / a) + 1 + 2 * (C / a) - 2 * (B / a) * (C / a))) * u -
      (a ^ 2 + 4) / (A ^ 2 + 4) * E
  /-- The middle-switch slack `N_mid ≥ 0` (the missing control at the forward switch
  `C → B`). -/
  mid : 0 ≤ (⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩ :
    SmallerShort.Point).fmid
  /-- The window-defect inequality and the modulus filter of the two-turn window, written with
  the traces `𝒜`, `ℬ`, `T_κ` and turn cost `C_br` of `SmallerShort.Point` at the
  actual coordinates. -/
  defect :
    let pt : SmallerShort.Point :=
      ⟨a / (a + C), B / C - 1, A / a, a ^ 2 / (a ^ 2 + 4), v, E⟩
    2 * pt.Tk ≤ pt.AA ∧ 0 < pt.BB ∧ pt.BB < pt.AA ∧ 4 * pt.Tk ≤ pt.AA + pt.BB ∧
      pt.cost + (pt.kap + 3 / 2) * (Real.pi / 3 - Real.arctan (Real.sqrt 3 * pt.BB / pt.AA)) ≤
        octagonCost

end SmoothedOctagon
