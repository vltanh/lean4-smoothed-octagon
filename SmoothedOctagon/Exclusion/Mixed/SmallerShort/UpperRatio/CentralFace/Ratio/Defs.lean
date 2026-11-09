module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.CentralFace.Defs

/-!
# Smaller-short window, upper ratio: the central x comparison, definitions

Along the curve `b = b_+(x, a)`, `u = u_C(x, b)` (`a` fixed), the total x-derivatives of the two
duration-tangent tests are bounded by the upper derivatives `R₀`, `R₁`, obtained by the
substitutions `u → U`, `u_x → V` of the incoming norm and speed by their majorants. Everything
is written in the atoms `S = 1 + x`, `K`, `B = a + b`, `D`, `D_x`,
`ℓ = B_x`, the norm `u` and the speed `v` (`= u_x`, or `V`).

## Main API

* `urcxl` (`ℓ`), `urcxDx` (`D_x`), `urcxU`, `urcxV` (the majorants).
* The primitives `urcxE0`, `urcxE1`, `urcxH0`, `urcxH1`, `urcxPa`, `urcxP1`, `urcxP2`,
  `urcxG0`, `urcxC0`, `urcxG1`, `urcxC1`; `urcxQ` (the common part of `R₀`, `R₁`),
  `urcxR0`, `urcxR1`; `urcxN0`, `urcxN1` (their cleared numerators).
* `urcx_R0_aff`, `urcx_R1_aff`: both upper derivatives are affine in `(u, v)` with the
  coefficients `urcxMv0`, `urcxMu0`, `urcxMv1`, `urcxMu1`.
* `urcx_R0_eq`, `urcx_R1_eq`: `aB²K⁴R₀ = N₀`, `aB²K³R₁ = N₁`.
* `urcx_box`: the monomial facts of the termwise bound on `0 ≤ X ≤ 7/30`, `0 ≤ A ≤ 1/3`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- `ℓ = B_x = (3a + 13)/16`. -/
noncomputable def urcxl (a : ℝ) : ℝ := (3 * a + 13) / 16

/-- `D_x = 2 + 2ℓ(a - x) - 2b` along `b = b_+(x, a)`. -/
noncomputable def urcxDx (x a : ℝ) : ℝ := 2 + 2 * urcxl a * (a - x) - 2 * urcbp x a

/-- The incoming-norm majorant `U = 3/4 + (x - 1)/96 - 1/400 - (a - 1)/200`. -/
noncomputable def urcxU (x a : ℝ) : ℝ := 3 / 4 + (x - 1) / 96 - 1 / 400 - (a - 1) / 200

/-- The incoming-speed majorant `V = 1/96 - (a - 1)/400`. -/
noncomputable def urcxV (a : ℝ) : ℝ := 1 / 96 - (a - 1) / 400

/-- `E₀ = S³(u - 1) + 3S - 1`. -/
noncomputable def urcxE0 (S u : ℝ) : ℝ := S ^ 3 * (u - 1) + 3 * S - 1

/-- `E₁ = 3S²(u - 1) + S³v + 3`. -/
noncomputable def urcxE1 (S u v : ℝ) : ℝ := 3 * S ^ 2 * (u - 1) + S ^ 3 * v + 3

/-- `H₀ = M + D²u - DE₀ - 3K²/4`, `M = S²(S² - S + 1)`. -/
noncomputable def urcxH0 (S K D u : ℝ) : ℝ :=
  S ^ 2 * (S ^ 2 - S + 1) + D ^ 2 * u - D * urcxE0 S u - 3 / 4 * K ^ 2

/-- `H₁ = 4S³ - 3S² + 2S + 2DD_x u + D²v - D_x E₀ - DE₁ - 3SK`. -/
noncomputable def urcxH1 (S K D Dx u v : ℝ) : ℝ :=
  4 * S ^ 3 - 3 * S ^ 2 + 2 * S + 2 * D * Dx * u + D ^ 2 * v - Dx * urcxE0 S u -
    D * urcxE1 S u v - 3 * S * K

/-- `P_a = vB + (u - 1)ℓ`. -/
noncomputable def urcxPa (l B u v : ℝ) : ℝ := v * B + (u - 1) * l

/-- `P₁ = J₁ + 2S`, `J₁ = 2D_x u + 2Dv - E₁`. -/
noncomputable def urcxP1 (S D Dx u v : ℝ) : ℝ := 2 * Dx * u + 2 * D * v - urcxE1 S u v + 2 * S

/-- `P₂ = 2S(a² + J₀)`, `J₀ = 2Du - E₀`. -/
noncomputable def urcxP2 (a S D u : ℝ) : ℝ := 2 * S * (a ^ 2 + (2 * D * u - urcxE0 S u))

/-- `G₀ = 4K - 7aB/2`. -/
noncomputable def urcxG0 (a K B : ℝ) : ℝ := 4 * K - 7 * a * B / 2

/-- `C₀ = 21aSB - (7aℓ/2 + 16S)K`. -/
noncomputable def urcxC0 (a l S K B : ℝ) : ℝ := 21 * a * S * B - (7 * a * l / 2 + 16 * S) * K

/-- `G₁ = K + aB/4`. -/
noncomputable def urcxG1 (a K B : ℝ) : ℝ := K + a * B / 4

/-- `C₁ = -2SBK - ℓK² - SaB²`. -/
noncomputable def urcxC1 (a l S K B : ℝ) : ℝ := -2 * S * B * K - l * K ^ 2 - S * a * B ^ 2

/-- The common part `P_a/a + P_b/B² - P₁/K + P₂/K²` of `R₀` and `R₁`, `P_b = ℓb = ℓ(B - a)`. -/
noncomputable def urcxQ (a l S K B D Dx u v : ℝ) : ℝ :=
  urcxPa l B u v / a + l * (B - a) / B ^ 2 - urcxP1 S D Dx u v / K +
    urcxP2 a S D u / K ^ 2

/-- The upper derivative `R₀ = Q + G₀H₁/K³ + C₀H₀/K⁴` of the first test. -/
noncomputable def urcxR0 (a l S K B D Dx u v : ℝ) : ℝ :=
  urcxQ a l S K B D Dx u v + urcxG0 a K B * urcxH1 S K D Dx u v / K ^ 3 +
    urcxC0 a l S K B * urcxH0 S K D u / K ^ 4

/-- The upper derivative `R₁ = Q + G₁H₁/(aBK²) + C₁H₀/(aB²K³)` of the second test. -/
noncomputable def urcxR1 (a l S K B D Dx u v : ℝ) : ℝ :=
  urcxQ a l S K B D Dx u v + urcxG1 a K B * urcxH1 S K D Dx u v / (a * B * K ^ 2) +
    urcxC1 a l S K B * urcxH0 S K D u / (a * B ^ 2 * K ^ 3)

/-- The cleared numerator `N₀ = aB²K⁴R₀`. -/
noncomputable def urcxN0 (a l S K B D Dx u v : ℝ) : ℝ :=
  urcxPa l B u v * B ^ 2 * K ^ 4 + l * (B - a) * a * K ^ 4 -
    urcxP1 S D Dx u v * a * B ^ 2 * K ^ 3 + urcxP2 a S D u * a * B ^ 2 * K ^ 2 +
    urcxG0 a K B * urcxH1 S K D Dx u v * a * B ^ 2 * K +
    urcxC0 a l S K B * urcxH0 S K D u * a * B ^ 2

/-- The cleared numerator `N₁ = aB²K³R₁`. -/
noncomputable def urcxN1 (a l S K B D Dx u v : ℝ) : ℝ :=
  urcxPa l B u v * B ^ 2 * K ^ 3 + l * (B - a) * a * K ^ 3 -
    urcxP1 S D Dx u v * a * B ^ 2 * K ^ 2 + urcxP2 a S D u * a * B ^ 2 * K +
    urcxG1 a K B * urcxH1 S K D Dx u v * B * K +
    urcxC1 a l S K B * urcxH0 S K D u

theorem urcx_R0_eq {a l S K B D Dx u v : ℝ} (ha : a ≠ 0) (hB : B ≠ 0) (hK : K ≠ 0) :
    a * B ^ 2 * K ^ 4 * urcxR0 a l S K B D Dx u v = urcxN0 a l S K B D Dx u v := by
  unfold urcxR0 urcxN0 urcxQ
  generalize urcxPa l B u v = p1
  generalize urcxP1 S D Dx u v = p2
  generalize urcxP2 a S D u = p3
  generalize urcxH1 S K D Dx u v = p4
  generalize urcxH0 S K D u = p5
  field_simp

theorem urcx_R1_eq {a l S K B D Dx u v : ℝ} (ha : a ≠ 0) (hB : B ≠ 0) (hK : K ≠ 0) :
    a * B ^ 2 * K ^ 3 * urcxR1 a l S K B D Dx u v = urcxN1 a l S K B D Dx u v := by
  unfold urcxR1 urcxN1 urcxQ
  generalize urcxPa l B u v = p1
  generalize urcxP1 S D Dx u v = p2
  generalize urcxP2 a S D u = p3
  generalize urcxH1 S K D Dx u v = p4
  generalize urcxH0 S K D u = p5
  field_simp

/-- `Z = 2SB - ℓK`, so that `(1/k)_x = Z/(aB²)`. -/
noncomputable def urcxZ (l S K B : ℝ) : ℝ := 2 * S * B - l * K

/-- `aK³` times the `v`-coefficient `C = B/a - (2D - S³)/K + G₀(D² - DS³)/K³` of `R₀`. -/
noncomputable def urcxMv0 (a S K B D : ℝ) : ℝ :=
  B * K ^ 3 - a * (2 * D - S ^ 3) * K ^ 2 + a * urcxG0 a K B * (D ^ 2 - D * S ^ 3)

/-- `aK⁴` times the `u`-coefficient `C_x` of `R₀`. -/
noncomputable def urcxMu0 (a l S K B D Dx : ℝ) : ℝ :=
  l * K ^ 4 - a * (2 * Dx - 3 * S ^ 2) * K ^ 3 + 2 * a * S * (2 * D - S ^ 3) * K ^ 2 +
    a * urcxG0 a K B * (2 * D * Dx - Dx * S ^ 3 - 3 * D * S ^ 2) * K +
    a * urcxC0 a l S K B * (D ^ 2 - D * S ^ 3)

/-- `aBK²` times the `v`-coefficient `C = B/a - (2D - S³)/K + G₁(D² - DS³)/(aBK²)` of `R₁`. -/
noncomputable def urcxMv1 (a S K B D : ℝ) : ℝ :=
  B ^ 2 * K ^ 2 - a * B * (2 * D - S ^ 3) * K + urcxG1 a K B * (D ^ 2 - D * S ^ 3)

/-- `aB²K³` times the `u`-coefficient `C_x` of `R₁`. -/
noncomputable def urcxMu1 (a l S K B D Dx : ℝ) : ℝ :=
  l * B ^ 2 * K ^ 3 - a * B ^ 2 * (2 * Dx - 3 * S ^ 2) * K ^ 2 +
    2 * a * S * B ^ 2 * (2 * D - S ^ 3) * K +
    urcxG1 a K B * (2 * D * Dx - Dx * S ^ 3 - 3 * D * S ^ 2) * B * K +
    urcxC1 a l S K B * (D ^ 2 - D * S ^ 3)

/-- The primitives are affine in `(u, v)`. -/
theorem urcx_prim_aff (a l S K B D Dx u v U V : ℝ) :
    urcxPa l B U V = urcxPa l B u v + ((V - v) * B + (U - u) * l) ∧
      urcxP1 S D Dx U V = urcxP1 S D Dx u v +
        ((U - u) * (2 * Dx - 3 * S ^ 2) + (V - v) * (2 * D - S ^ 3)) ∧
      urcxP2 a S D U = urcxP2 a S D u + 2 * S * (U - u) * (2 * D - S ^ 3) ∧
      urcxH1 S K D Dx U V = urcxH1 S K D Dx u v +
        ((U - u) * (2 * D * Dx - Dx * S ^ 3 - 3 * D * S ^ 2) + (V - v) * (D ^ 2 - D * S ^ 3)) ∧
      urcxH0 S K D U = urcxH0 S K D u + (U - u) * (D ^ 2 - D * S ^ 3) := by
  unfold urcxPa urcxP1 urcxP2 urcxH1 urcxH0 urcxE0 urcxE1
  refine ⟨by ring, by ring, by ring, by ring, by ring⟩

/-- **`R₀` is affine in `(u, v)`**: its `v`- and `u`-coefficients are
`C = M_v/(aK³)`, `C_x = M_u/(aK⁴)`. -/
theorem urcx_R0_aff {a l S K B D Dx u v U V : ℝ} (ha : a ≠ 0) (hK : K ≠ 0) :
    urcxR0 a l S K B D Dx U V = urcxR0 a l S K B D Dx u v +
      (V - v) * (urcxMv0 a S K B D / (a * K ^ 3)) +
      (U - u) * (urcxMu0 a l S K B D Dx / (a * K ^ 4)) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := urcx_prim_aff a l S K B D Dx u v U V
  unfold urcxR0 urcxQ urcxMv0 urcxMu0
  rw [e1, e2, e3, e4, e5]
  field_simp
  ring

/-- **`R₁` is affine in `(u, v)`**: its `v`- and `u`-coefficients are
`C = M_v/(aBK²)`, `C_x = M_u/(aB²K³)`. -/
theorem urcx_R1_aff {a l S K B D Dx u v U V : ℝ} (ha : a ≠ 0) (hB : B ≠ 0) (hK : K ≠ 0) :
    urcxR1 a l S K B D Dx U V = urcxR1 a l S K B D Dx u v +
      (V - v) * (urcxMv1 a S K B D / (a * B * K ^ 2)) +
      (U - u) * (urcxMu1 a l S K B D Dx / (a * B ^ 2 * K ^ 3)) := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := urcx_prim_aff a l S K B D Dx u v U V
  unfold urcxR1 urcxQ urcxMv1 urcxMu1
  rw [e1, e2, e3, e4, e5]
  field_simp
  ring

/-- The monomial facts of the termwise bound on `0 ≤ X ≤ 7/30`, `0 ≤ A ≤ 1/3`: every monomial
is nonnegative, and one with `A`-degree `k ≥ 2` (resp. `X`-degree `j ≥ 2`) is at most its value at
the upper corner times `A²/(1/3)²` (resp. `X²/(7/30)²`). -/
theorem urcx_box {X A : ℝ} (hX : 0 ≤ X) (hX' : X ≤ 7 / 30) (hA : 0 ≤ A) (hA' : A ≤ 1 / 3) :
    (∀ j k : ℕ, 0 ≤ X ^ j * A ^ k) ∧
      (∀ j k : ℕ, 2 ≤ k → X ^ j * A ^ k ≤ (7 / 30) ^ j * (1 / 3) ^ k * 9 * A ^ 2) ∧
      (∀ j k : ℕ, 2 ≤ j → X ^ j * A ^ k ≤ (7 / 30) ^ j * (1 / 3) ^ k * (900 / 49) * X ^ 2) := by
  refine ⟨fun j k => by positivity, fun j k hk => ?_, fun j k hj => ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    have h1 : X ^ j ≤ (7 / 30) ^ j := pow_le_pow_left₀ hX hX' j
    have h2 : A ^ m ≤ (1 / 3) ^ m := pow_le_pow_left₀ hA hA' m
    have h3 : X ^ j * A ^ m ≤ (7 / 30) ^ j * (1 / 3) ^ m :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg A)
    calc X ^ j * A ^ (2 + m) = X ^ j * A ^ m * A ^ 2 := by ring
      _ ≤ (7 / 30) ^ j * (1 / 3) ^ m * A ^ 2 := h4
      _ = (7 / 30) ^ j * (1 / 3) ^ (2 + m) * 9 * A ^ 2 := by ring
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    have h1 : X ^ m ≤ (7 / 30) ^ m := pow_le_pow_left₀ hX hX' m
    have h2 : A ^ k ≤ (1 / 3) ^ k := pow_le_pow_left₀ hA hA' k
    have h3 : X ^ m * A ^ k ≤ (7 / 30) ^ m * (1 / 3) ^ k :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 := mul_le_mul_of_nonneg_right h3 (sq_nonneg X)
    calc X ^ (2 + m) * A ^ k = X ^ m * A ^ k * X ^ 2 := by ring
      _ ≤ (7 / 30) ^ m * (1 / 3) ^ k * X ^ 2 := h4
      _ = (7 / 30) ^ (2 + m) * (1 / 3) ^ k * (900 / 49) * X ^ 2 := by ring

end SmoothedOctagon
