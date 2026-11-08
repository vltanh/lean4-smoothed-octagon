module

public import SmoothedOctagon.Reduction.CompactDomain
public import SmoothedOctagon.Exclusion.Mixed.Frames

/-!
# Case M2: the compact domain on the costate cycle

`MIXED_NONSHORT_BLOWUP_REDUCTION` §1, (2), (2a) (inventory E2, entries 10-11). On `𝔥**`
(Hales–Vajjha, Definition 5.0.1) every margin is at least `2/15`; the height bound `y ≤ 9/2` and the
two cusp disks give every pair sum of margins at least `8/(9√3) > 1/2`, and then the quadric
`p₀p₁ + p₁p₂ + p₂p₀ = 4` gives every margin at most `8`. On the costate cycle of a normal period in
`𝔥**` these bounds hold for the switch margins `m k j` at every switch, across the twisted seam.

## Main API

* `wx_half_le_margin_add`: on `𝔥**`, `1/2 ≤ p_i + p_j` for `i ≠ j`.
* `NormalPeriod.wx_m_ge`: `2/15 ≤ m k j`.
* `NormalPeriod.wx_half_le_m_add`: `1/2 ≤ m k j + m k j'` for `j ≠ j'`.
* `NormalPeriod.wx_m_le`: `m k j ≤ 8`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set

/-- **Pair sums on `𝔥**`** (`MIXED_NONSHORT_BLOWUP_REDUCTION` §1): every pair sum of the margins
of a state in `𝔥**` is at least `1/2` (in fact at least `8/(9√3)`). -/
theorem wx_half_le_margin_add {X : Mat2} (hX : Cited.HalesVajjha.InCompactDomain X) {i j : Fin 3}
    (hij : i ≠ j) : 1 / 2 ≤ margin i X + margin j X := by
  obtain ⟨x, y, rfl, hmem⟩ := hX
  obtain ⟨⟨hy, -, -, -⟩, hy9, hd1, hd2, -, -, -⟩ := hmem
  simp only at hy hy9 hd1 hd2
  have htr : (Φ x y).trace = 0 := by
    rw [Matrix.trace_fin_two]; simp only [Φ, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  obtain ⟨e0, e1, e2⟩ := margin_eq_two_mul_rho _ htr
  have s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have s3p : 0 < √3 := by positivity
  have s3le : √3 ≤ 16 / 9 := by nlinarith
  have r0 : ρ₀ (Φ x y) = (1 + √3 * x) / (√3 * y) := by simp [ρ₀, Φ]; field_simp
  have r1 : ρ₁ (Φ x y) = (1 - √3 * x) / (√3 * y) := by simp [ρ₁, Φ]; field_simp
  have r2 : ρ₂ (Φ x y) = (3 * (x ^ 2 + y ^ 2) - 1) / (2 * √3 * y) := by
    simp [ρ₂, Φ]; field_simp; ring
  have hsy : 0 < √3 * y := by positivity
  have hinv : 1 / √3 = √3 / 3 := by field_simp; rw [s3]
  rw [hinv] at hd1 hd2
  -- the three pair sums
  have p12 : 1 / 2 ≤ margin 1 (Φ x y) + margin 2 (Φ x y) := by
    rw [e1, e2, r0, r1, show 2 * ((1 - √3 * x) / (√3 * y)) + 2 * ((1 + √3 * x) / (√3 * y)) =
      4 / (√3 * y) by field_simp; ring, le_div_iff₀ hsy]
    nlinarith
  have p01 : 1 / 2 ≤ margin 0 (Φ x y) + margin 1 (Φ x y) := by
    rw [e0, e1, r1, r2, show 2 * ((3 * (x ^ 2 + y ^ 2) - 1) / (2 * √3 * y)) +
      2 * ((1 - √3 * x) / (√3 * y)) = (3 * x ^ 2 + 3 * y ^ 2 + 1 - 2 * √3 * x) / (√3 * y) by
        field_simp; ring, le_div_iff₀ hsy]
    have : 3 * ((x - √3 / 3) ^ 2 + y ^ 2) = 3 * x ^ 2 + 3 * y ^ 2 + 1 - 2 * √3 * x := by
      ring_nf; rw [s3]; ring
    nlinarith
  have p02 : 1 / 2 ≤ margin 0 (Φ x y) + margin 2 (Φ x y) := by
    rw [e0, e2, r0, r2, show 2 * ((3 * (x ^ 2 + y ^ 2) - 1) / (2 * √3 * y)) +
      2 * ((1 + √3 * x) / (√3 * y)) = (3 * x ^ 2 + 3 * y ^ 2 + 1 + 2 * √3 * x) / (√3 * y) by
        field_simp; ring, le_div_iff₀ hsy]
    have : 3 * ((x + √3 / 3) ^ 2 + y ^ 2) = 3 * x ^ 2 + 3 * y ^ 2 + 1 + 2 * √3 * x := by
      ring_nf; rw [s3]; ring
    nlinarith
  fin_cases i <;> fin_cases j <;> simp at hij <;> simp only [Fin.zero_eta, Fin.mk_one,
    Fin.reduceFinMk, Fin.isValue] <;> linarith

namespace NormalPeriod

variable (P : NormalPeriod)

/-- The switching time read by the cycle at the switch `k`. -/
theorem wx_τ_mem (k : ℤ) : P.rep.τ (k % P.N) ∈ Icc 0 P.T :=
  ⟨P.rep.τ_nonneg (term_emod_nonneg P k), P.rep.τ_le_T (term_emod_lt P k).le⟩

/-- **Compact lower margin** (`MIXED_NONSHORT_BLOWUP_REDUCTION` (2a)): every switch margin of a
period in `𝔥**` is at least `2/15`. -/
theorem wx_m_ge (hK : P.InCompactDomain) (k : ℤ) (j : Fin 3) : 2 / 15 ≤ P.costateCycle.m k j := by
  rw [costateCycle_m, termMargin_eq_cut]
  exact Reduction.two_div_fifteen_le_margin (hK _ (P.wx_τ_mem k)) _

/-- **Compact pair sums** (`MIXED_NONSHORT_BLOWUP_REDUCTION` §1): two distinct switch margins of a
period in `𝔥**` sum to at least `1/2`. -/
theorem wx_half_le_m_add (hK : P.InCompactDomain) (k : ℤ) {j j' : Fin 3} (h : j ≠ j') :
    1 / 2 ≤ P.costateCycle.m k j + P.costateCycle.m k j' := by
  rw [costateCycle_m, costateCycle_m, termMargin_eq_cut, termMargin_eq_cut]
  exact wx_half_le_margin_add (hK _ (P.wx_τ_mem k)) (fun e => h (sub_left_injective e))

/-- **Compact upper margin** (`MIXED_NONSHORT_BLOWUP_REDUCTION` §1): every switch margin of a period
in `𝔥**` is at most `8`. -/
theorem wx_m_le (hK : P.InCompactDomain) (k : ℤ) (j : Fin 3) : P.costateCycle.m k j ≤ 8 := by
  have hq := P.costateCycle.m2_quad_rot k j
  have hs := P.wx_half_le_m_add hK k (j := j + 1) (j' := j - 1)
    ((by decide : ∀ x : Fin 3, x + 1 ≠ x - 1) j)
  have h0 := P.costateCycle.m_pos k j
  have h1 := P.costateCycle.m_pos k (j + 1)
  have h2 := P.costateCycle.m_pos k (j - 1)
  nlinarith [mul_pos h1 h2]

end NormalPeriod

end SmoothedOctagon
