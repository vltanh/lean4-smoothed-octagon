module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Case M2, smaller-nonshort branch: the four boundary covers

The four directed-interval covers of the smaller-nonshort branch, stated as the propositions their
runs certify. The proof no longer uses them: gate H-N of `archive/notes/HAND_PROOF_STATUS.md` is
closed by hand, and only the scalar definitions below are used, by the M2 chart lemmas and the
interval library. All four fed `MIXED_GLOBAL_NONSHORT_PERIOD_EXCLUSION`.

* `CertNonshortReverse` (Cert-REV): `mixed_nonshort_reverse_boundary_interval_certificate.cpp`
  (branch 1), consumed by `MIXED_NONSHORT_REVERSE_BOUNDARY_EXCLUSION`; `a ∈ [2/15, 17/20]`;
  106134 nodes, 53068 leaves, maximum depth 26.
* `CertNonshortLowA` (Cert-LOWA): `mixed_nonshort_low_a_boundary_interval_certificate.cpp`
  (branch 2), consumed by `MIXED_NONSHORT_LOW_A_BOUNDARY_EXCLUSION`; `a ∈ [2/15, 1/2]`;
  74772 nodes, 37387 leaves, maximum depth 23.
* `CertNonshortForwardLower` (Cert-FWD0): `mixed_nonshort_forward_boundary_interval_certificate.cpp`
  (branch 0, lower endpoint `w*`), consumed by `MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION`;
  `a ∈ [1/2, 17/20]`; 37940 nodes, 18971 leaves, maximum depth 27.
* `CertNonshortForwardUpper` (Cert-FWD1): the same caller (branch 1, upper endpoint `w_cap`),
  consumed by `MIXED_NONSHORT_FORWARD_BOUNDARY_EXCLUSION`; `a ∈ [1/2, 17/20]`; 60976 nodes,
  30489 leaves, maximum depth 32.

All callers are in `archive/explorations/`. Each run has 2 roots, one per chart, with the same box:
`a` in its root, `c ∈ [2/15, 2]`, `ε ∈ [1/32, 15]`, `l₀ = 0` exactly, and the free weight
`ℓ ∈ [0, 1]`; chart 1 has `(l₁, l₂) = (1, ℓ)` and chart 2 has `(l₁, l₂) = (ℓ, 1)` (`main` and
`evaluate`, lines 84-87).
Records: `archive/explorations/mixed_nonshort_*_result.json` and `archive/explorations/results/*.log`.

## What a run certifies

The engine (`certified_mpfr_interval.hpp`) uses 80-bit MPFR with directed rounding and
second-order jets; roots are entered with outward-rounded endpoints. Each node is contracted
(`contract`, three sweeps) by consequences of the residuals `g₁, …, g₆, g₁₁, g₁₂, g₁₃` and, in
chart 2, `g₁₆`; it is a leaf (reason 1) if contraction empties it or if the natural enclosure of one
of `g₀, …, g₆, g₁₁, …, g₁₅`, chart-2 `g₁₆`, or `r` (`basic_empty`; `r ≥ a > 0` follows from
`g₅ ≥ 0` since `g₅ = W(r - a)`) is negative. Otherwise it is a leaf if the natural or Taylor upper
bound of one residual is negative (reason `10 + index`), or if a fresh Taylor upper bound of
`∑ wₖ gₖ` is negative for exact dyadic weights `wₖ ∈ 2⁻²⁰ ℕ ∩ [0, 1]` proposed by a
floating-point LP (reason 60; `certified_lp_proposal.hpp`). The LP only proposes weights: the
certified fact is still that no point of the box has all residuals `≥ 0`. Domain errors (a
denominator interval containing `0`, a negative argument of `H` or `log`) cause bisection, never a
leaf. Lean's `x / 0 = 0` and `log` agree with the program wherever it evaluated a residual.

The residual list is `needed` in `evaluate` (lines 113-125 of the reverse caller): the sixteen
common residuals `g₀, …, g₁₅`, then `g₁₆` in chart 2 only, then the caller's extra residuals.
-/

@[expose] public section

namespace SmoothedOctagon.Certificates

namespace Nonshort

/-- `H(z) = (log(1 + z) - z + z²/2)/z³`, with `H(0) = 1/3` (`Hpoint`, `Hbounds`, `Hfun`, lines
18-45 of each caller). The callers enclose it for `z ≥ 0` by the series
`H(z) = 2/(1 + z) · ∑ₙ ηⁿ/((n + 1)(n + 2)(n + 3))`, `η = z/(1 + z)`, for `z ≤ 1/8` and by this
closed form otherwise. -/
noncomputable def Hlog (z : ℝ) : ℝ :=
  if z = 0 then 1 / 3 else (Real.log (1 + z) - z + z ^ 2 / 2) / z ^ 3

/-- `centered_polynomial_cancelled(a, c, eps, l0, l1, l2)`
(`archive/explorations/mixed_nonshort_coefficients.hpp`, lines 5-67), the cancelled centred polynomial
`∑_{i=2}^{8} Pᵢ/(a + c)³ · eps^(i-2)`, transcribed term by term. -/
noncomputable def centeredPolynomialCancelled (a c eps l0 l1 l2 : ℝ) : ℝ :=
  let cx0 := a ^ 2
  let cx1 := a * c
  let cx2 := 2 * cx1
  let cx3 := cx0 + cx2 - 4
  let cx4 := c * l1
  let cx5 := l2 ^ 3
  let cx6 := cx0 + 4
  let cx7 := a + c
  let cx8 := l1 ^ 3
  let cx9 := c * cx8
  let cx10 := cx7 * cx9
  let cx11 := l1 ^ 2
  let cx12 := cx3 * l0
  let cx13 := l2 ^ 2
  let cx14 := 2 * cx12
  let cx15 := cx7 * l2
  let cx16 := a * l1
  let cx17 := 6 * cx12 * cx15 * cx16
  let cx18 := 4 * a
  let cx19 := 3 * cx0
  let cx20 := l0 ^ 2
  let cx21 := cx20 * l2
  let cx22 := 8 * cx1
  let cx23 := cx13 * cx16
  let cx24 := a ^ 3
  let cx25 := 4 * c
  let cx26 := c * cx19 + cx25
  let cx27 := cx16 * cx20
  let cx28 := 12 * c
  let cx29 := c ^ 2
  let cx30 := 8 * cx29
  let cx31 := c * cx0
  let cx32 := cx11 * l2
  let cx33 := cx29 + 4
  let cx34 := 3 * a
  let cx35 := 2 * c
  let cx36 := cx25 + cx34
  let cx37 := a * cx14
  let cx38 := 5 * cx24
  let cx39 := 12 * a
  let cx40 := l1 * l2
  let cx41 := a * cx40
  let cx42 := 8 * c
  let cx43 := a * cx29
  let cx44 := 10 * a ^ 4
  let cx45 := c ^ 3
  let cx46 := 8 * a
  let cx47 := c * cx24
  let cx48 := cx0 * cx29
  let cx49 := cx27 * cx6
  let cx50 := cx25 + cx38
  let cx51 := cx21 * cx6
  let cx52 := cx11 * cx15
  let C2 := -cx3 * (a * (l0 + l2) + cx4) ^ 2
  let C3 := -c * cx32 * (a * cx30 - 16 * a + 6 * cx24 - cx28 + 15 * cx31) - cx0 * cx13 * cx14
    - cx0 * cx21 * (c * cx18 + cx19 - 4) + cx0 * cx5 * cx6 - cx10 * (cx1 + 4)
    - cx11 * cx12 * cx2 - cx17 - cx23 * cx7 * (5 * cx0 + cx22 - 12)
    - cx27 * (-cx18 + cx24 + cx26)
  let C4 := a * cx5 * l1 * (cx26 + cx38 + cx39) - cx1 * cx11 * cx20 * cx6
    - cx1 * cx33 * l1 ^ 4
    - cx11 * cx13 * (-12 * cx0 - 24 * cx1 - cx30 + cx44 + cx45 * cx46 + 30 * cx47 + 29 * cx48)
    - 2 * cx13 * cx20 * cx24 * cx7 - cx14 * cx23 * (cx34 + cx35)
    - cx20 * cx41 * (cx18 + cx28 + 7 * cx31 + cx38) - cx32 * cx36 * cx37
    - cx9 * l2 * (7 * cx24 + 18 * cx31 + cx42 + 9 * cx43)
  let C5 := cx40 * (a * cx13 * l1 * (cx0 * cx28 + 10 * cx24 + cx29 * cx34 + cx39 + cx42)
    - cx11 * cx37 * cx7 - cx15 * cx18 * cx20 * (cx0 + 2) - cx17
    - cx32 * (13 * a * cx45 - 4 * cx0 - cx22 + 4 * cx29 + cx44 + 33 * cx47 + 38 * cx48)
    - cx36 * cx49 - cx9 * (11 * cx31 + 7 * cx43 + cx46 + cx50))
  let C6 := cx52 * (a * cx13 * l1 * (10 * cx0 + cx22 + cx33) - 3 * cx1 * cx7 * cx8
    - cx14 * cx41 - cx32 * (14 * cx31 + 10 * cx43 + cx50) - cx34 * cx51 - cx49)
  let C7 := a * cx15 * cx8 * (-cx10 + cx13 * cx7 * l1 * (5 * a + cx35) - cx51
    - cx52 * (a + cx25))
  let C8 := a * cx13 * cx7 ^ 2 * l1 ^ 5 * (-cx4 + cx7 * l2)
  ((((((C8 * eps + C7) * eps + C6) * eps + C5) * eps + C4) * eps + C3) * eps + C2)

/-- The six coordinates of `evaluate` (lines 83-88 of each caller): `a, c, eps` and the three
weights `l0, l1, l2`. The covers use `l0 = 0`. -/
structure Point where
  /-- `a`. -/
  a : ℝ
  /-- `c`. -/
  c : ℝ
  /-- `eps = ε'`. -/
  eps : ℝ
  /-- `l0`. -/
  l0 : ℝ
  /-- `l1`. -/
  l1 : ℝ
  /-- `l2`. -/
  l2 : ℝ

/-- Chart 1 (`chart == 1`, line 86): `(l0, l1, l2) = (0, 1, ℓ)`. -/
def chart1 (a c eps ell : ℝ) : Point := ⟨a, c, eps, 0, 1, ell⟩

/-- Chart 2 (`chart == 2`, line 87): `(l0, l1, l2) = (0, ℓ, 1)`. -/
def chart2 (a c eps ell : ℝ) : Point := ⟨a, c, eps, 0, ell, 1⟩

namespace Point

/-- `z0 = eps·l0` (line 88). -/
noncomputable def z0 (p : Point) : ℝ := p.eps * p.l0

/-- `z1 = eps·l1 = δ₁` (line 88). -/
noncomputable def z1 (p : Point) : ℝ := p.eps * p.l1

/-- `z2 = eps·l2 = δ₂` (line 88). -/
noncomputable def z2 (p : Point) : ℝ := p.eps * p.l2

/-- `K = a² + 4` (line 88). -/
noncomputable def K (p : Point) : ℝ := p.a ^ 2 + 4

/-- `T0 = a + c` (line 88). -/
noncomputable def T0 (p : Point) : ℝ := p.a + p.c

/-- `S = K/(T0(1 + z0))` (line 89). -/
noncomputable def S (p : Point) : ℝ := p.K / (p.T0 * (1 + p.z0))

/-- `d = a + T0·z1` (line 89). -/
noncomputable def d (p : Point) : ℝ := p.a + p.T0 * p.z1

/-- `W = T0(1 + z1)` (line 89). -/
noncomputable def W (p : Point) : ℝ := p.T0 * (1 + p.z1)

/-- `Q = d² + 4` (line 89). -/
noncomputable def Q (p : Point) : ℝ := p.d ^ 2 + 4

/-- `q = 1 + z2` (line 90). -/
noncomputable def q (p : Point) : ℝ := 1 + p.z2

/-- `Z = Qq/W` (line 90). -/
noncomputable def Z (p : Point) : ℝ := p.Q * p.q / p.W

/-- `r = Z - d` (line 90). -/
noncomputable def r (p : Point) : ℝ := p.Z - p.d

/-- `Y = W² - T0²` (line 90). -/
noncomputable def Y (p : Point) : ℝ := p.W ^ 2 - p.T0 ^ 2

/-- `N = dW - qY` (line 90). -/
noncomputable def N (p : Point) : ℝ := p.d * p.W - p.q * p.Y

/-- `H0 = H(z0)` (line 91). -/
noncomputable def H0 (p : Point) : ℝ := Hlog p.z0

/-- `H1 = H(z1)` (line 91). -/
noncomputable def H1 (p : Point) : ℝ := Hlog p.z1

/-- `H2 = H(z2)` (line 91). -/
noncomputable def H2 (p : Point) : ℝ := Hlog p.z2

/-- `Bv = c(4 - a²) + 8a + a·z1(c² + 4) + z2·T0(z1 + 2)(K + a·T0·z1(z1 + 2))` (line 92). -/
noncomputable def Bv (p : Point) : ℝ :=
  p.c * (4 - p.a ^ 2) + 8 * p.a + p.a * p.z1 * (p.c ^ 2 + 4)
    + p.z2 * p.T0 * (p.z1 + 2) * (p.K + p.a * p.T0 * p.z1 * (p.z1 + 2))

/-- `base = centered_polynomial_cancelled/(2aQ(1 + z1)²q)` (line 93). -/
noncomputable def base (p : Point) : ℝ :=
  centeredPolynomialCancelled p.a p.c p.eps p.l0 p.l1 p.l2 / (2 * p.a * p.Q * (1 + p.z1) ^ 2 * p.q)

/-- `phi = base - eps·K·N·l0³·H0/(QW) + eps·c·T0·l1³·Bv·H1/(aQW) - eps·d·l2³·H2` (line 94). -/
noncomputable def phi (p : Point) : ℝ :=
  p.base - p.eps * p.K * p.N * p.l0 ^ 3 * p.H0 / (p.Q * p.W)
    + p.eps * p.c * p.T0 * p.l1 ^ 3 * p.Bv * p.H1 / (p.a * p.Q * p.W)
    - p.eps * p.d * p.l2 ^ 3 * p.H2

/-- `D1 = K²/(aQW(1 + z0))·(a(l0 + l2) + c·l1 + a·eps·l0·l2 + T0·eps·l1·l2(2 + eps·l1))`
(line 95). -/
noncomputable def D1 (p : Point) : ℝ :=
  p.K ^ 2 / (p.a * p.Q * p.W * (1 + p.z0))
    * (p.a * (p.l0 + p.l2) + p.c * p.l1 + p.a * p.eps * p.l0 * p.l2
      + p.T0 * p.eps * p.l1 * p.l2 * (2 + p.eps * p.l1))

/-- `shift = eps·phi/D1` (line 96). -/
noncomputable def shift (p : Point) : ℝ := p.eps * p.phi / p.D1

/-- `rr = a·T0/K` (line 97). -/
noncomputable def rr (p : Point) : ℝ := p.a * p.T0 / p.K

/-- `tt = a/T0` (line 97). -/
noncomputable def tt (p : Point) : ℝ := p.a / p.T0

/-- `rho = a²/K` (line 97). -/
noncomputable def rho (p : Point) : ℝ := p.a ^ 2 / p.K

/-- `xc = c/T0` (line 97). -/
noncomputable def xc (p : Point) : ℝ := p.c / p.T0

/-- `u0 = 1 - rr + rr²` (line 98). -/
noncomputable def u0 (p : Point) : ℝ := 1 - p.rr + p.rr ^ 2

/-- `v0 = 1 - tt + tt²` (line 98). -/
noncomputable def v0 (p : Point) : ℝ := 1 - p.tt + p.tt ^ 2

/-- `h0 = K(-1 + 2(rr + tt) - rho)/16` (line 98). -/
noncomputable def h0 (p : Point) : ℝ := p.K * (-1 + 2 * (p.rr + p.tt) - p.rho) / 16

/-- `du = (2rr² - rr)z0 + rr²z0² + shift` (line 99). -/
noncomputable def du (p : Point) : ℝ :=
  (2 * p.rr ^ 2 - p.rr) * p.z0 + p.rr ^ 2 * p.z0 ^ 2 + p.shift

/-- `dv = z1(xc/2 - xc²) + z1²(xc²/(1 + z1) - xc·H1)` (line 100). -/
noncomputable def dv (p : Point) : ℝ :=
  p.z1 * (p.xc / 2 - p.xc ^ 2) + p.z1 ^ 2 * (p.xc ^ 2 / (1 + p.z1) - p.xc * p.H1)

/-- `dh = K(2rr·z0 - log(1 + z0) + dv/tt + (S/a)shift)/16` (line 101). -/
noncomputable def dh (p : Point) : ℝ :=
  p.K * (2 * p.rr * p.z0 - Real.log (1 + p.z0) + p.dv / p.tt + p.S / p.a * p.shift) / 16

/-- `u = u0 + du` (line 102). -/
noncomputable def u (p : Point) : ℝ := p.u0 + p.du

/-- `v = v0 + dv` (line 102). -/
noncomputable def v (p : Point) : ℝ := p.v0 + p.dv

/-- `h = h0 + dh` (line 102). -/
noncomputable def h (p : Point) : ℝ := p.h0 + p.dh

/-- The Casimir excess `7/2000 + K²(v0·du + u0·dv + du·dv)/64 - 2h0·dh - dh²` (line 103). -/
noncomputable def excess (p : Point) : ℝ :=
  7 / 2000 + p.K ^ 2 * (p.v0 * p.du + p.u0 * p.dv + p.du * p.dv) / 64 - 2 * p.h0 * p.dh
    - p.dh ^ 2

/-- `hd = h + vY/8` (line 104). -/
noncomputable def hd (p : Point) : ℝ := p.h + p.v * p.Y / 8

/-- `w = (uK² + 16hY + vY²)/Q²` (line 104), the boundary value `w*`. -/
noncomputable def w (p : Point) : ℝ := (p.u * p.K ^ 2 + 16 * p.h * p.Y + p.v * p.Y ^ 2) / p.Q ^ 2

/-- `Kr = r² + 4` (line 104). -/
noncomputable def Kr (p : Point) : ℝ := p.r ^ 2 + 4

/-- `tn = (Q²v - 16hd·Z² + w(Z²)²)/Kr²` (line 105), the next norm `t*`. -/
noncomputable def tn (p : Point) : ℝ :=
  (p.Q ^ 2 * p.v - 16 * p.hd * p.Z ^ 2 + p.w * (p.Z ^ 2) ^ 2) / p.Kr ^ 2

/-- `L2 = 1 - z2/2 + z2²·H2` (line 106). -/
noncomputable def L2 (p : Point) : ℝ := 1 - p.z2 / 2 + p.z2 ^ 2 * p.H2

/-- `Fend = 1 + (d/W)²q - (d/W)q·L2` (line 107). -/
noncomputable def Fend (p : Point) : ℝ := 1 + (p.d / p.W) ^ 2 * p.q - p.d / p.W * p.q * p.L2

/-- `turn = 1/2 - (1 - xc + z1)/(1 + z1)² - z1·H1` (line 108). -/
noncomputable def turn (p : Point) : ℝ := 1 / 2 - (1 - p.xc + p.z1) / (1 + p.z1) ^ 2 - p.z1 * p.H1

/-- `upper_turn = xc - 1/2 - z1(xc/(1 + z1) - H1)` (line 109). -/
noncomputable def upperTurn (p : Point) : ℝ := p.xc - 1 / 2 - p.z1 * (p.xc / (1 + p.z1) - p.H1)

/-- `g₀ = c - a` (line 113, reason 10). -/
noncomputable def g0 (p : Point) : ℝ := p.c - p.a

/-- `g₁ = K - T0²(1 + z0)` (line 113, reason 11). -/
noncomputable def g1 (p : Point) : ℝ := p.K - p.T0 ^ 2 * (1 + p.z0)

/-- `g₂ = 12 - 17a²` (line 113, reason 12). -/
noncomputable def g2 (p : Point) : ℝ := 12 - 17 * p.a ^ 2

/-- `g₃ = 4 - cd - (2/15)W` (line 114, reason 13). -/
noncomputable def g3 (p : Point) : ℝ := 4 - p.c * p.d - 2 / 15 * p.W

/-- `g₄ = c - 2/15 - (d + 2/15)z2` (line 114, reason 14). -/
noncomputable def g4 (p : Point) : ℝ := p.c - 2 / 15 - (p.d + 2 / 15) * p.z2

/-- `g₅ = 4 - a² - 2ac - T0²z1 + Q·z2` (line 115, reason 15), equal to `W(r - a)`. -/
noncomputable def g5 (p : Point) : ℝ := 4 - p.a ^ 2 - 2 * p.a * p.c - p.T0 ^ 2 * p.z1 + p.Q * p.z2

/-- `g₆ = c - a(1 + z1)` (line 115, reason 16). -/
noncomputable def g6 (p : Point) : ℝ := p.c - p.a * (1 + p.z1)

/-- `g₇ = -phi` (line 116, reason 17). -/
noncomputable def g7 (p : Point) : ℝ := -p.phi

/-- `g₈ = upper_turn` (line 116, reason 18). -/
noncomputable def g8 (p : Point) : ℝ := p.upperTurn

/-- `g₉ = turn` (line 116, reason 19). -/
noncomputable def g9 (p : Point) : ℝ := p.turn

/-- `g₁₀ = v - Fend` (line 116, reason 20). -/
noncomputable def g10 (p : Point) : ℝ := p.v - p.Fend

/-- `g₁₁ = 8 - d` (line 117, reason 21). -/
noncomputable def g11 (p : Point) : ℝ := 8 - p.d

/-- `g₁₂ = 8 - r` (line 117, reason 22). -/
noncomputable def g12 (p : Point) : ℝ := 8 - p.r

/-- `g₁₃ = T0 - 1/2` (line 117, reason 23). -/
noncomputable def g13 (p : Point) : ℝ := p.T0 - 1 / 2

/-- `g₁₄ = W - 1/2` (line 117, reason 24). -/
noncomputable def g14 (p : Point) : ℝ := p.W - 1 / 2

/-- `g₁₅ = Z - 1/2` (line 117, reason 25). -/
noncomputable def g15 (p : Point) : ℝ := p.Z - 1 / 2

/-- `g₁₆ = c - a - T0·z1` (line 118, chart 2 only, reason 26). -/
noncomputable def g16 (p : Point) : ℝ := p.c - p.a - p.T0 * p.z1

/-- The sixteen common residuals `g₀, …, g₁₅` are nonnegative (lines 113-117). -/
def Retained (p : Point) : Prop :=
  0 ≤ p.g0 ∧ 0 ≤ p.g1 ∧ 0 ≤ p.g2 ∧ 0 ≤ p.g3 ∧ 0 ≤ p.g4 ∧ 0 ≤ p.g5 ∧ 0 ≤ p.g6 ∧ 0 ≤ p.g7 ∧
    0 ≤ p.g8 ∧ 0 ≤ p.g9 ∧ 0 ≤ p.g10 ∧ 0 ≤ p.g11 ∧ 0 ≤ p.g12 ∧ 0 ≤ p.g13 ∧ 0 ≤ p.g14 ∧
    0 ≤ p.g15

/-- `ar = a + r` (reverse caller, line 121). -/
noncomputable def ar (p : Point) : ℝ := p.a + p.r

/-- `zz = T0·z1/ar` (reverse caller, line 121). -/
noncomputable def zz (p : Point) : ℝ := p.T0 * p.z1 / p.ar

/-- `LL = 1 - zz/2 + zz²·H(zz)` (reverse caller, line 122). -/
noncomputable def LL (p : Point) : ℝ := 1 - p.zz / 2 + p.zz ^ 2 * Hlog p.zz

/-- `ceiling = 1 + r²/(ar·Z) - (r/ar)LL` (reverse caller, line 123), the secant `Sec(a, r, d)`. -/
noncomputable def ceiling (p : Point) : ℝ := 1 + p.r ^ 2 / (p.ar * p.Z) - p.r / p.ar * p.LL

/-- The extra residuals of the reverse caller (line 124): `r² - ad ≥ 0` and `ceiling - w ≥ 0`. -/
def ReverseExtra (p : Point) : Prop := 0 ≤ p.r ^ 2 - p.a * p.d ∧ 0 ≤ p.ceiling - p.w

/-- `tau = tn - 3/4` (forward caller, line 119). -/
noncomputable def tau (p : Point) : ℝ := p.tn - 3 / 4

/-- `B = Z³(4 - dr)/(d·Kr²)` (forward caller, line 125). -/
noncomputable def B (p : Point) : ℝ := p.Z ^ 3 * (4 - p.d * p.r) / (p.d * p.Kr ^ 2)

/-- `Gprime = Q²v/64 - hd·QZ/(8d)` (forward caller, line 126). -/
noncomputable def Gprime (p : Point) : ℝ := p.Q ^ 2 * p.v / 64 - p.hd * p.Q * p.Z / (8 * p.d)

/-- `C = Q²Z²/(256d²)` (forward caller, line 127). -/
noncomputable def C (p : Point) : ℝ := p.Q ^ 2 * p.Z ^ 2 / (256 * p.d ^ 2)

/-- `endpoint_excess = B²·excess + B·Gprime·tau - C·tau²` (forward caller, line 128). -/
noncomputable def endpointExcess (p : Point) : ℝ :=
  p.B ^ 2 * p.excess + p.B * p.Gprime * p.tau - p.C * p.tau ^ 2

/-- The extra residuals of the forward caller, branch 0 (lines 119-121): `tau ≥ 0` and
`-excess ≥ 0`. -/
def ForwardLowerExtra (p : Point) : Prop := 0 ≤ p.tau ∧ 0 ≤ -p.excess

/-- The extra residuals of the forward caller, branch 1 (lines 119-129): `tau ≥ 0` and
`-endpoint_excess ≥ 0`. -/
def ForwardUpperExtra (p : Point) : Prop := 0 ≤ p.tau ∧ 0 ≤ -p.endpointExcess

end Point

/-- The common shape of the four covers: for both charts and every `(a, c, eps, ℓ)` in the root
box `[aLo, aHi] × [2/15, 2] × [1/32, 15] × [0, 1]` (with `l0 = 0`), the common residuals, the
chart-2 residual `g₁₆` and the caller's extra residuals are not all nonnegative. -/
def BoundaryExcluded (aLo aHi : ℝ) (extra : Point → Prop) : Prop :=
  ∀ a c eps ell : ℝ, a ∈ Set.Icc aLo aHi → c ∈ Set.Icc (2 / 15 : ℝ) 2 →
    eps ∈ Set.Icc (1 / 32 : ℝ) 15 → ell ∈ Set.Icc (0 : ℝ) 1 →
    ¬ ((chart1 a c eps ell).Retained ∧ extra (chart1 a c eps ell)) ∧
    ¬ ((chart2 a c eps ell).Retained ∧ 0 ≤ (chart2 a c eps ell).g16 ∧ extra (chart2 a c eps ell))

end Nonshort

/-- **Cert-REV** (`mixed_nonshort_reverse_boundary_interval_certificate.cpp`, branch 1, roots at
lines 283-287): `a ∈ [2/15, 17/20]`, extra residuals `r² - ad` and `Sec(a, r, d) - w*`. -/
def CertNonshortReverse : Prop :=
  Nonshort.BoundaryExcluded (2 / 15) (17 / 20) Nonshort.Point.ReverseExtra

/-- **Cert-LOWA** (`mixed_nonshort_low_a_boundary_interval_certificate.cpp`, branch 2, roots at
lines 283-287): `a ∈ [2/15, 1/2]`, no extra residual. -/
def CertNonshortLowA : Prop :=
  Nonshort.BoundaryExcluded (2 / 15) (1 / 2) fun _ => True

/-- **Cert-FWD0** (`mixed_nonshort_forward_boundary_interval_certificate.cpp`, branch 0, the lower
endpoint `w*`, roots at lines 289-293): `a ∈ [1/2, 17/20]`, extra residuals `tau = t* - 3/4` and
`-excess`. -/
def CertNonshortForwardLower : Prop :=
  Nonshort.BoundaryExcluded (1 / 2) (17 / 20) Nonshort.Point.ForwardLowerExtra

/-- **Cert-FWD1** (`mixed_nonshort_forward_boundary_interval_certificate.cpp`, branch 1, the upper
endpoint `w_cap`, roots at lines 289-293): `a ∈ [1/2, 17/20]`, extra residuals `tau` and
`-(B²·excess + B·G'·tau - C·tau²)`. -/
def CertNonshortForwardUpper : Prop :=
  Nonshort.BoundaryExcluded (1 / 2) (17 / 20) Nonshort.Point.ForwardUpperExtra

end SmoothedOctagon.Certificates
