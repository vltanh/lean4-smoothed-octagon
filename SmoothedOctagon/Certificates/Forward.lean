module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Case F: the neighbour cover and the complementary Casimir cover

The two computer-assisted interval covers of case F (every switch forward, `N ≥ 6`), stated as the
propositions their C++ runs certify. Both are named hypotheses of the main theorem pending a hand
proof: gate H-F of `docs/HAND_PROOF_STATUS.md` (PR branch).

* `CertForwardNeighbor` (CERT-N), `explorations/global_forward_completion_neighbor_certificate.cpp`.
  Consumed by `GLOBAL_FORWARD_NEIGHBOR_CONTRACTION` §3: if a neighbour ratio is `≥ 5/4`, the
  necessary scalar residual `Ē ≥ 0` holds on the closed comparison domain (7), which the cover
  excludes. Record (`GLOBAL_FORWARD_NEIGHBOR_CONTRACTION` §3; no result file): 1 root,
  8183 nodes, 4092 leaves (6 emptied by contraction, 4086 with a negative direct or Taylor upper
  bound), maximum depth 20.
* `CertForwardCasimir` (CERT-C), `explorations/global_forward_completion_casimir_certificate.cpp`.
  Consumed by `GLOBAL_FORWARD_PERIOD_EXCLUSION` §5 on the complement of the central cube (11),
  which §4 excludes by hand. Record
  (`explorations/global_forward_completion_casimir_certificate_result.txt`): 3 roots,
  20999 nodes, 10501 leaves (reason 10: 5436, 11: 995, 13: 65, 20: 4005), maximum depth 23.

## What a run certifies

Both programs use exact GMP rationals, rounded outward to `2⁻⁸⁰ ℤ` after every operation, and
second-order jets. Each node is first contracted by necessary inequalities (three sweeps). It is a
leaf if the contracted box is empty, or if the direct interval enclosure or the second-order
Taylor enclosure (about the exact midpoint, with the full-box Hessian) of one retained quantity
has the excluding sign on the whole contracted box. A box on which an evaluation meets a
denominator interval containing `0` (CERT-C also: an argument of `f` below `1`, or a determinant
enclosure that is not positive) is bisected, never a leaf; a nonempty final stack or a depth-limit
box is a failure. Neither cover uses an LP combination.

So a successful run proves: no point of a root box satisfies all the contraction constraints and
all the retained inequalities. For CERT-N this is stated as one negated conjunction. For CERT-C,
whose hand step also uses the checks made during evaluation, it is stated as: at every point
satisfying the constraints, the denominators are nonzero, the arguments of `f` are at least `1`,
`D > 0`, and one exclusion test holds. Lean's `x / 0 = 0` does not change the meaning: every leaf
enclosed every denominator away from `0`, so at every point of the certified domain the Lean
values are the true values.
-/

@[expose] public section

namespace SmoothedOctagon.Certificates

/-! ### CERT-N: the neighbour cover -/

namespace ForwardNeighbor

/-- `t = (v - 1)/(v + 1)`, the variable of the logarithm series in `lop`, `lom`, `ff`
(`global_forward_completion_neighbor_certificate.cpp`, lines 40-42). -/
noncomputable def tau (v : ℝ) : ℝ := (v - 1) / (v + 1)

/-- `lop(v) = 2t(1 + t²/3 + t⁴/(5(1 - t²)))` (line 40), an upper bound for `log v` when `v ≥ 1`. -/
noncomputable def logUpper (v : ℝ) : ℝ :=
  2 * tau v * (1 + tau v ^ 2 / 3 + tau v ^ 2 * tau v ^ 2 / (5 * (1 - tau v ^ 2)))

/-- `lom(v) = 2t(1 + t²/3 + t⁴/5)` (line 41), a lower bound for `log v` when `v ≥ 1`. -/
noncomputable def logLower (v : ℝ) : ℝ :=
  2 * tau v * (1 + tau v ^ 2 / 3 + tau v ^ 2 * tau v ^ 2 / 5)

/-- `ff(x, v) = 1 + x²v - x(1 + t)(1 + t²/3 + t⁴/(5(1 - t²)))` (line 42), a lower bound for the
exterior floor `F_x(v) = 1 + x²v - x v log v/(v - 1)` when `v ≥ 1`. -/
noncomputable def floorLower (x v : ℝ) : ℝ :=
  1 + x ^ 2 * v
    - x * (1 + tau v) * (1 + tau v ^ 2 / 3 + tau v ^ 2 * tau v ^ 2 / (5 * (1 - tau v ^ 2)))

/-- The four coordinates `(U, z, w, h)` of the neighbour cover (`jet`, line 45). -/
structure Point where
  /-- `U = 4/a²`. -/
  U : ℝ
  /-- `z = b/a`, the smaller neighbour ratio. -/
  z : ℝ
  /-- `w = c/a`, the larger neighbour ratio. -/
  w : ℝ
  /-- `h`, the left exterior factor. -/
  h : ℝ

namespace Point

/-- `S = 1 + z` (line 45). -/
noncomputable def S (p : Point) : ℝ := 1 + p.z

/-- `T = 1 + w` (line 45). -/
noncomputable def T (p : Point) : ℝ := 1 + p.w

/-- `L = 1 + U` (line 45). -/
noncomputable def L (p : Point) : ℝ := 1 + p.U

/-- `Z = z² + U` (line 45). -/
noncomputable def Z (p : Point) : ℝ := p.z ^ 2 + p.U

/-- `W = w² + U` (line 45). -/
noncomputable def W (p : Point) : ℝ := p.w ^ 2 + p.U

/-- `q = ST/L` (line 45). -/
noncomputable def q (p : Point) : ℝ := p.S * p.T / p.L

/-- `ii = T²/W` (line 45), the floor of the right exterior factor. -/
noncomputable def ii (p : Point) : ℝ := p.T ^ 2 / p.W

/-- `A = 1 + z + w - 1/S - 1/T + 1/L - lom(q)` (line 46). -/
noncomputable def A (p : Point) : ℝ :=
  1 + p.z + p.w - 1 / p.S - 1 / p.T + 1 / p.L - logLower p.q

/-- `B = Zh/S + 1 - z²S/(Zh) - z²/S + z³/Z - z lop(h)` (line 47). -/
noncomputable def B (p : Point) : ℝ :=
  p.Z * p.h / p.S + 1 - p.z ^ 2 * p.S / (p.Z * p.h) - p.z ^ 2 / p.S + p.z ^ 2 * p.z / p.Z
    - p.z * logUpper p.h

/-- `n = S²(U - z)(h - 1)/Z` (line 48). -/
noncomputable def n (p : Point) : ℝ := p.S ^ 2 * (p.U - p.z) * (p.h - 1) / p.Z

/-- `m = L²(q - 1 + (h - 1)(Sq - 1))/(SZ)` (line 48). -/
noncomputable def m (p : Point) : ℝ :=
  p.L ^ 2 * (p.q - 1 + (p.h - 1) * (p.S * p.q - 1)) / (p.S * p.Z)

/-- `al = L(hS - z)/Z` (line 48). -/
noncomputable def al (p : Point) : ℝ := p.L * (p.h * p.S - p.z) / p.Z

/-- The excluded residual `Ē = al·A - B - n·ff(z/S, h) - m·ff(w/T, ii)` (line 49), an upper bound
for the necessary quantity `𝓔 ≥ 0`. -/
noncomputable def Ebar (p : Point) : ℝ :=
  p.al * p.A - p.B - p.n * floorLower (p.z / p.S) p.h - p.m * floorLower (p.w / p.T) p.ii

end Point

end ForwardNeighbor

/-- **CERT-N** (`global_forward_completion_neighbor_certificate.cpp`). On the root box
`[11/5, 3] × [1, 7/3] × [5/4, 7/3] × [1, 2]` (line 70), no point satisfies the contraction
constraints of `judge` (lines 59-63: `z ≤ w`, `z + w ≤ 5(U - 1)/3`,
`(1 + z)²/(z² + U) ≤ h ≤ (1 + z)/z`) together with `Ē ≥ 0`. A leaf is an emptied box
(reason 1) or a box with `sup Ē < 0` from the direct enclosure (reason 2) or, at depth `> 8`, the
Taylor enclosure (reason 3); lines 64-65. -/
def CertForwardNeighbor : Prop :=
  ∀ U z w h : ℝ, U ∈ Set.Icc (11 / 5 : ℝ) 3 → z ∈ Set.Icc (1 : ℝ) (7 / 3) →
    w ∈ Set.Icc (5 / 4 : ℝ) (7 / 3) → h ∈ Set.Icc (1 : ℝ) 2 →
    ¬ (z ≤ w ∧ z + w ≤ 5 * (U - 1) / 3 ∧ (1 + z) ^ 2 / (z ^ 2 + U) ≤ h ∧ h ≤ (1 + z) / z ∧
      0 ≤ (⟨U, z, w, h⟩ : ForwardNeighbor.Point).Ebar)

/-! ### CERT-C: the complementary Casimir cover -/

namespace ForwardCasimir

/-- The centred logarithmic remainder `f(r) = (r - 1/r)/2 - log r`
(`global_forward_completion_casimir_certificate.cpp`, `f_at` and `ffun`, lines 41-51). The program
encloses this actual function for `r ≥ 1` by fourteen terms of its positive series in
`t = (r - 1)/(r + 1)` plus the tail bound `2t³¹/(1 - t²)`, with the exact derivatives
`f' = (r - 1)²/(2r²)` and `f'' = (r - 1)/r³`. -/
noncomputable def f (r : ℝ) : ℝ := (r - 1 / r) / 2 - Real.log r

/-- `floordelta(r, h)` (lines 53-57): with `t = (h - 1)/(h + 1)`,
`(r - 1/2)² + (h - 1)r(r - 1/2) + rh/(h + 1) · ∑_{n=1}^{10} (4n/(2n + 1)) t^{2n}`, a rational lower
bound for `F_r(h) - 3/4`. -/
noncomputable def floorDelta (r h : ℝ) : ℝ :=
  (r - 1 / 2) ^ 2 + (h - 1) * r * (r - 1 / 2) +
    r * h * (∑ n ∈ Finset.Icc (1 : ℕ) 10,
      (4 * n / (2 * n + 1) : ℝ) * ((h - 1) / (h + 1)) ^ (2 * n)) / (h + 1)

/-- The five coordinates `(U, z, w, h, k)` of the Casimir cover (`jets`, line 60). -/
structure Point where
  /-- `U = 4/a²`. -/
  U : ℝ
  /-- `z`, the smaller neighbour ratio. -/
  z : ℝ
  /-- `w`, the larger neighbour ratio. -/
  w : ℝ
  /-- `h`, the left exterior factor. -/
  h : ℝ
  /-- `k`, the right exterior factor. -/
  k : ℝ

namespace Point

/-- `S = 1 + z` (line 61). -/
noncomputable def S (p : Point) : ℝ := 1 + p.z

/-- `T = 1 + w` (line 61). -/
noncomputable def T (p : Point) : ℝ := 1 + p.w

/-- `K = 1 + U` (line 61). -/
noncomputable def K (p : Point) : ℝ := 1 + p.U

/-- `Z = z² + U` (line 61). -/
noncomputable def Z (p : Point) : ℝ := p.z ^ 2 + p.U

/-- `W = w² + U` (line 61). -/
noncomputable def W (p : Point) : ℝ := p.w ^ 2 + p.U

/-- `d = 3 - U` (line 62). -/
noncomputable def d (p : Point) : ℝ := 3 - p.U

/-- `X = z - 1` (line 62). -/
noncomputable def X (p : Point) : ℝ := p.z - 1

/-- `Y = w - 1` (line 62). -/
noncomputable def Y (p : Point) : ℝ := p.w - 1

/-- `H = h - 1` (line 62). -/
noncomputable def H (p : Point) : ℝ := p.h - 1

/-- `L = k - 1` (line 62). -/
noncomputable def L (p : Point) : ℝ := p.k - 1

/-- `qgap = (d + 2X + 2Y + XY)/K` (line 63), equal to `ST/K - 1`. -/
noncomputable def qgap (p : Point) : ℝ := (p.d + 2 * p.X + 2 * p.Y + p.X * p.Y) / p.K

/-- `q = 1 + qgap` (line 63). -/
noncomputable def q (p : Point) : ℝ := 1 + p.qgap

/-- `nL = S²(U - z)H/Z` (line 64). -/
noncomputable def nL (p : Point) : ℝ := p.S ^ 2 * (p.U - p.z) * p.H / p.Z

/-- `nR = T²(U - w)L/W` (line 64). -/
noncomputable def nR (p : Point) : ℝ := p.T ^ 2 * (p.U - p.w) * p.L / p.W

/-- `mL = K²(qgap + H(1 + X + S·qgap))/(SZ)` (line 65). -/
noncomputable def mL (p : Point) : ℝ :=
  p.K ^ 2 * (p.qgap + p.H * (1 + p.X + p.S * p.qgap)) / (p.S * p.Z)

/-- `mR = K²(qgap + L(1 + Y + T·qgap))/(TW)` (line 66). -/
noncomputable def mR (p : Point) : ℝ :=
  p.K ^ 2 * (p.qgap + p.L * (1 + p.Y + p.T * p.qgap)) / (p.T * p.W)

/-- `phi = f(S/2) + f(T/2) + f(4/K)` (line 67). -/
noncomputable def phi (p : Point) : ℝ := f (p.S / 2) + f (p.T / 2) + f (4 / p.K)

/-- `e0 = 3/4 + d(K + 2)/(8K)` (line 68). -/
noncomputable def e0 (p : Point) : ℝ := 3 / 4 + p.d * (p.K + 2) / (8 * p.K)

/-- `E0 = e0 - phi` (line 68). -/
noncomputable def E0 (p : Point) : ℝ := p.e0 - p.phi

/-- The polynomial `d²(v² + 4v + 2) + 8dv(v + 1) + 2v²(8 + 4v - v²)` of `resid` (line 70). -/
noncomputable def residPoly (p : Point) (v : ℝ) : ℝ :=
  p.d ^ 2 * (v ^ 2 + 4 * v + 2) + 8 * p.d * v * (v + 1) + 2 * v ^ 2 * (8 + 4 * v - v ^ 2)

/-- `resid(v, t, A, B, F)` (lines 69-74):
`(dv(d + 2v) + F·P)/(8AB) + F²t(d + 4v + v²)/(2(1 + F)B) + K(1 + AF)/B·phi - t f(1 + F)`. -/
noncomputable def resid (p : Point) (v t A B F : ℝ) : ℝ :=
  (p.d * v * (p.d + 2 * v) + F * p.residPoly v) / (8 * A * B)
    + F ^ 2 * t * (p.d + 4 * v + v ^ 2) / (2 * (1 + F) * B)
    + p.K * (1 + A * F) / B * p.phi - t * f (1 + F)

/-- `rL = resid(X, z, S, Z, H)` (line 75). -/
noncomputable def rL (p : Point) : ℝ := p.resid p.X p.z p.S p.Z p.H

/-- `rR = resid(Y, w, T, W, L)` (line 75). -/
noncomputable def rR (p : Point) : ℝ := p.resid p.Y p.w p.T p.W p.L

/-- `dl = floordelta(z/S, h)` (line 76). -/
noncomputable def dl (p : Point) : ℝ := floorDelta (p.z / p.S) p.h

/-- `dr = floordelta(w/T, k)` (line 76). -/
noncomputable def dr (p : Point) : ℝ := floorDelta (p.w / p.T) p.k

/-- The determinant `D = mL·mR - nL·nR` in its factored form (lines 77-79):
`K⁴·qgap/(STZW)·(qgap + H(1 + X + S·qgap) + L(1 + Y + T·qgap) + HL(q + 1)(q(S + T) - q² - 1))`.
Every leaf enclosed it in `(0, ∞)` (line 80). -/
noncomputable def D (p : Point) : ℝ :=
  p.K ^ 2 * p.K ^ 2 * p.qgap / (p.S * p.T * p.Z * p.W)
    * (p.qgap + p.H * (1 + p.X + p.S * p.qgap) + p.L * (1 + p.Y + p.T * p.qgap)
      + p.H * p.L * (p.q + 1) * (p.q * (p.S + p.T) - p.q ^ 2 - 1))

/-- `du = (mL·rR - nR·rL)/D` (line 81). -/
noncomputable def du (p : Point) : ℝ := (p.mL * p.rR - p.nR * p.rL) / p.D

/-- `dv = (mR·rL - nL·rR)/D` (line 81). -/
noncomputable def dv (p : Point) : ℝ := (p.mR * p.rL - p.nL * p.rR) / p.D

/-- `ell = S·du + T·dv` (line 82). -/
noncomputable def ell (p : Point) : ℝ := p.S * p.du + p.T * p.dv

/-- `E = E0 + ell` (line 82). -/
noncomputable def E (p : Point) : ℝ := p.E0 + p.ell

/-- `cx = -(3/2)X - dS(K + 2)/(4K)` (line 83). -/
noncomputable def cx (p : Point) : ℝ := -3 / 2 * p.X - p.d * p.S * (p.K + 2) / (4 * p.K)

/-- `cy = -(3/2)Y - dT(K + 2)/(4K)` (line 84). -/
noncomputable def cy (p : Point) : ℝ := -3 / 2 * p.Y - p.d * p.T * (p.K + 2) / (4 * p.K)

/-- The Casimir excess (lines 85-87): `7/2000 + (-(1/64)d⁴ + K²(2·e0·phi - phi² + cx·du + cy·dv
+ 2·phi·ell + 4·du·dv - ell²))/(16U²)`. -/
noncomputable def excess (p : Point) : ℝ :=
  7 / 2000 + (-1 / 64 * (p.d ^ 2) ^ 2
    + p.K ^ 2 * (2 * p.e0 * p.phi - p.phi ^ 2 + p.cx * p.du + p.cy * p.dv + 2 * p.phi * p.ell
      + 4 * p.du * p.dv - p.ell ^ 2)) / (16 * p.U ^ 2)

/-- `Q0 = rL - nL·dl - mL·dr` (line 88, reason 10). -/
noncomputable def Q0 (p : Point) : ℝ := p.rL - p.nL * p.dl - p.mL * p.dr

/-- `Q1 = rR - mR·dl - nR·dr` (line 88, reason 11). -/
noncomputable def Q1 (p : Point) : ℝ := p.rR - p.mR * p.dl - p.nR * p.dr

/-- `Q2 = du - dl` (line 88, reason 12). -/
noncomputable def Q2 (p : Point) : ℝ := p.du - p.dl

/-- `Q3 = dv - dr` (line 88, reason 13). -/
noncomputable def Q3 (p : Point) : ℝ := p.dv - p.dr

/-- `Q4 = E` (line 88, reason 14). -/
noncomputable def Q4 (p : Point) : ℝ := p.E

/-- `Q5 = excess` (line 88, reason 20 when its lower bound is positive). -/
noncomputable def Q5 (p : Point) : ℝ := p.excess

/-- The contraction constraints of `contract` (lines 102-114). -/
def Domain (p : Point) : Prop :=
  p.z ≤ p.w ∧ p.z + p.w ≤ 5 * (p.U - 1) / 3 ∧
    (1 + p.z) ^ 2 / (p.z ^ 2 + p.U) ≤ p.h ∧ p.h ≤ 1 + 1 / p.z ∧
    (1 + p.w) ^ 2 / (p.w ^ 2 + p.U) ≤ p.k ∧ p.k ≤ 1 + 1 / p.w

/-- The atomic denominators are nonzero. Every division in the functions above is by a product of
`S, T, K, Z, W, U, h + 1, k + 1`, of `1 + H = h` and `1 + L = k`, of an argument of `f`, or of
`D`; the last three are covered by `FArgsGeOne` and `0 < D`. `jets` (lines 58-89) throws when a
denominator interval contains `0` (line 24), so such a box is bisected, never a leaf. -/
def DenominatorsNonzero (p : Point) : Prop :=
  p.S ≠ 0 ∧ p.T ≠ 0 ∧ p.K ≠ 0 ∧ p.Z ≠ 0 ∧ p.W ≠ 0 ∧ p.U ≠ 0 ∧ p.h + 1 ≠ 0 ∧ p.k + 1 ≠ 0

/-- Every argument of `f` is at least `1`: `S/2, T/2, 4/K` (line 67) and `1 + H = h`, `1 + L = k`
(`resid`, line 73). `f_at` throws on an argument enclosure below `1` (line 42). -/
def FArgsGeOne (p : Point) : Prop :=
  1 ≤ p.S / 2 ∧ 1 ≤ p.T / 2 ∧ 1 ≤ 4 / p.K ∧ 1 ≤ 1 + p.H ∧ 1 ≤ 1 + p.L

/-- The exclusion tests of `judge` (lines 116-125): `Qᵢ < 0` for some `i ≤ 4` (reason `10 + i`)
or `Q5 > 0` (reason 20). -/
def Excluded (p : Point) : Prop :=
  p.Q0 < 0 ∨ p.Q1 < 0 ∨ p.Q2 < 0 ∨ p.Q3 < 0 ∨ p.Q4 < 0 ∨ 0 < p.Q5

/-- What the run certifies at a point of the domain: the leaf containing it evaluated `jets` on
the whole contracted box without an exception, so the denominators are nonzero, the arguments of
`f` are at least `1` and `D > 0` (line 80) there, and one exclusion test succeeded. -/
def Certified (p : Point) : Prop :=
  p.DenominatorsNonzero ∧ p.FArgsGeOne ∧ 0 < p.D ∧ p.Excluded

end Point

/-- One root of CERT-C: at every point of the box `[U₀, U₁] × [z₀, z₁] × [w₀, w₁] × [1, 2] × [1, 2]`
satisfying the contraction constraints, the run's checks hold. A point satisfying the constraints
is never removed by contraction, so it lies in a leaf whose contracted box was evaluated. -/
def RootCertified (U₀ U₁ z₀ z₁ w₀ w₁ : ℝ) : Prop :=
  ∀ U z w h k : ℝ, U ∈ Set.Icc U₀ U₁ → z ∈ Set.Icc z₀ z₁ → w ∈ Set.Icc w₀ w₁ →
    h ∈ Set.Icc (1 : ℝ) 2 → k ∈ Set.Icc (1 : ℝ) 2 →
    (⟨U, z, w, h, k⟩ : Point).Domain → (⟨U, z, w, h, k⟩ : Point).Certified

end ForwardCasimir

/-- **CERT-C** (`global_forward_completion_casimir_certificate.cpp`), one conjunct per root
(lines 130-133). The roots cover `[11/5, 3] × [1, 5/4]² × [1, 2]²` minus the central cube
`U > 95/32, z < 33/32, w < 33/32`. `GLOBAL_FORWARD_PERIOD_EXCLUSION` §5 (R49 of the F inventory)
uses `D > 0` to identify `(du, dv)` with the true `(u - 3/4, v - 3/4)` by Cramer's rule, then
`Q0, …, Q4 ≥ 0` and `Q5 < 0` at an actual window, contradicting `Excluded`.

The exclusion is the code's six-way disjunction. By its recorded leaf reasons (10, 11, 13, 20
only) this run also certified the stronger `Q0 < 0 ∨ Q1 < 0 ∨ Q3 < 0 ∨ Q5 > 0`, which is not part
of this proposition. -/
def CertForwardCasimir : Prop :=
  ForwardCasimir.RootCertified (11 / 5) (95 / 32) 1 (5 / 4) 1 (5 / 4) ∧
    ForwardCasimir.RootCertified (95 / 32) 3 (33 / 32) (5 / 4) 1 (5 / 4) ∧
    ForwardCasimir.RootCertified (95 / 32) 3 1 (33 / 32) (33 / 32) (5 / 4)

/-- The two case-F covers, hypotheses pending the hand proof of gate H-F. -/
structure ForwardCovers : Prop where
  /-- CERT-N, the neighbour cover. -/
  neighbor : CertForwardNeighbor
  /-- CERT-C, the complementary Casimir cover. -/
  casimir : CertForwardCasimir

end SmoothedOctagon.Certificates
