module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Analysis
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Boundary

/-!
# The high-ratio terminal face

At `t = 3/8`, the residual is concave in the duration increment `y`.
Its sign therefore reduces to zero duration and the actual duration boundary
`b(x) = (1 - 2x)/(1 + 4x)`. The zero-duration value is concave in `x`.
After clearing the boundary denominator and removing the positive factor
`(1 + x)²`, the boundary numerator has a concave derivative that starts
positive. Both signs follow from endpoint values.
-/

@[expose] public section
namespace SmoothedOctagon

/-! ### The face coefficients -/

/-- The coefficient `C_0(x)` of the face residual (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF0 (x : ℝ) : ℝ :=
  -(74732415 / 65536) * x + (1238140495 / 262144) * x ^ (2 : ℕ) + (635549755 / 262144) * x ^ (3 : ℕ) - (2542125 / 256) * x ^ (4 : ℕ) - (4381125 / 512) * x ^ (5 : ℕ) - (3825 / 2) * x ^ (6 : ℕ)

/-- The coefficient `C_1(x)` of the face residual (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF1 (x : ℝ) : ℝ :=
  -(44839449 / 65536) + (591967515 / 262144) * x + (16856367297 / 524288) * x ^ (2 : ℕ) - (2481472989 / 524288) * x ^ (3 : ℕ) - (3434657649 / 32768) * x ^ (4 : ℕ) - (105946215 / 1024) * x ^ (5 : ℕ) - (2167215 / 64) * x ^ (6 : ℕ) - 1965 * x ^ (7 : ℕ)

/-- The coefficient `C_2(x)` of the face residual (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF2 (x : ℝ) : ℝ :=
  (145359519 / 131072) + (6313406737 / 524288) * x + (10322714837 / 524288) * x ^ (2 : ℕ) - (11554797201 / 65536) * x ^ (3 : ℕ) - (31332968633 / 65536) * x ^ (4 : ℕ) - (116601189 / 256) * x ^ (5 : ℕ) - (24615003 / 128) * x ^ (6 : ℕ) - 33540 * x ^ (7 : ℕ) - 2448 * x ^ (8 : ℕ)

/-- The coefficient `C_3(x)` of the face residual (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF3 (x : ℝ) : ℝ :=
  (10753107 / 8192) - (264165151 / 65536) * x - (19730788975 / 262144) * x ^ (2 : ℕ) - (100902544067 / 262144) * x ^ (3 : ℕ) - (3063148985 / 4096) * x ^ (4 : ℕ) - (1418453067 / 2048) * x ^ (5 : ℕ) - (20825019 / 64) * x ^ (6 : ℕ) - (146475 / 2) * x ^ (7 : ℕ) - 6528 * x ^ (8 : ℕ)

/-- The coefficient `C_4(x)` of the face residual (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF4 (x : ℝ) : ℝ :=
  -(144402831 / 65536) - (7396491861 / 262144) * x - (3879209205 / 32768) * x ^ (2 : ℕ) - (84147940983 / 262144) * x ^ (3 : ℕ) - (16553778615 / 32768) * x ^ (4 : ℕ) - (460321809 / 1024) * x ^ (5 : ℕ) - (14389761 / 64) * x ^ (6 : ℕ) - (464265 / 8) * x ^ (7 : ℕ) - 5712 * x ^ (8 : ℕ)

/-- The coefficient `C_5(x)` of the face residual (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF5 (x : ℝ) : ℝ :=
  -(127147563 / 65536) - (4463664003 / 262144) * x - (28149980355 / 524288) * x ^ (2 : ℕ) - (56966436693 / 524288) * x ^ (3 : ℕ) - (4717837395 / 32768) * x ^ (4 : ℕ) - (246960519 / 2048) * x ^ (5 : ℕ) - (7970421 / 128) * x ^ (6 : ℕ) - (140175 / 8) * x ^ (7 : ℕ) - 1836 * x ^ (8 : ℕ)

/-- The coefficient `C_6(x)` of the face residual (`t = 3/8`, `k₀ = 261/256`). -/
noncomputable def hrlCF6 (x : ℝ) : ℝ :=
  -(26376921 / 131072) - (746579511 / 524288) * x - (1484996355 / 524288) * x ^ (2 : ℕ) - (233133111 / 65536) * x ^ (3 : ℕ) - (208980465 / 65536) * x ^ (4 : ℕ) - (1996137 / 1024) * x ^ (5 : ℕ) - (67263 / 64) * x ^ (6 : ℕ) - (1575 / 4) * x ^ (7 : ℕ) - 51 * x ^ (8 : ℕ)

/-- `P(x, y) = ∑ Cᵢ(x) yⁱ`, the normalized face residual. -/
noncomputable def hrlP (x y : ℝ) : ℝ :=
  hrlCF0 x * y ^ (0 : ℕ) + hrlCF1 x * y ^ (1 : ℕ) + hrlCF2 x * y ^ (2 : ℕ) + hrlCF3 x * y ^ (3 : ℕ) + hrlCF4 x * y ^ (4 : ℕ) + hrlCF5 x * y ^ (5 : ℕ) + hrlCF6 x * y ^ (6 : ℕ)

/-- The actual maximum-duration numerator after removing `(1 + x)²`. -/
private def boundaryNumerator {R : Type*} [CommRing R] (x : R) : R :=
  -12941524992 * x ^ 12 - 180366606336 * x ^ 11 - 489113321472 * x ^ 10
    - 440043171840 * x ^ 9 - 29057536928 * x ^ 8 + 147719438312 * x ^ 7
    + 49308274890 * x ^ 6 - 27314362585 * x ^ 5 - 10163112212 * x ^ 4
    + 6240727818 * x ^ 3 + 2081433886 * x ^ 2 - 308000401 * x - 85436844

private noncomputable def boundaryPolynomial : Polynomial ℝ :=
  boundaryNumerator Polynomial.X

private theorem boundary_eval (x : ℝ) : boundaryPolynomial.eval x = boundaryNumerator x := by
  simp [boundaryPolynomial, boundaryNumerator]

private theorem boundary_link {x : ℝ} (hx : 17 / 60 ≤ x) :
    32768 * (1 + 4 * x) ^ 6 * hrlP x ((1 - 2 * x) / (1 + 4 * x)) =
      (1 + x) ^ 2 * boundaryNumerator x := by
  have hd : 1 + 4 * x ≠ 0 := ne_of_gt (by linarith only [hx])
  unfold hrlP hrlCF0 hrlCF1 hrlCF2 hrlCF3 hrlCF4 hrlCF5 hrlCF6 boundaryNumerator
  field_simp
  ring

private theorem boundary_third_nonpos {x : ℝ} (hx : 17 / 60 ≤ x) :
    boundaryPolynomial.derivative.derivative.derivative.eval x ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = 17 / 60 + u := ⟨x - 17 / 60, by ring⟩
  have hu : 0 ≤ u := by linarith only [hx]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  norm_num [boundaryPolynomial, boundaryNumerator, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 9, lo 8, lo 7, lo 6, lo 5, lo 4, lo 3, lo 2, lo 1]

private theorem boundary_floor {x : ℝ} (hx : 17 / 60 ≤ x) (hx1 : x ≤ 3 / 7) :
    32768 * 1000 ≤ boundaryNumerator x := by
  have hf := LowT.polynomial_floor_of_concave_derivative
    (p := boundaryPolynomial) (m := 32768 * 1000) hx hx1
    (fun _ hs _ => boundary_third_nonpos hs)
    (by norm_num [boundaryPolynomial, boundaryNumerator, Polynomial.derivative_mul,
      Polynomial.derivative_pow])
    (by norm_num [boundary_eval, boundaryNumerator])
    (by norm_num [boundary_eval, boundaryNumerator])
  simpa only [boundary_eval] using hf

private noncomputable def initialPolynomial : Polynomial ℝ :=
  -Polynomial.C (74732415 / 65536) * Polynomial.X
    + Polynomial.C (1238140495 / 262144) * Polynomial.X ^ 2
    + Polynomial.C (635549755 / 262144) * Polynomial.X ^ 3
    - Polynomial.C (2542125 / 256) * Polynomial.X ^ 4
    - Polynomial.C (4381125 / 512) * Polynomial.X ^ 5
    - Polynomial.C (3825 / 2) * Polynomial.X ^ 6

private theorem initial_eval (x : ℝ) : initialPolynomial.eval x = hrlCF0 x := by
  norm_num [initialPolynomial, hrlCF0]

private theorem initial_concave {x : ℝ} (hx : 17 / 60 ≤ x) :
    initialPolynomial.derivative.derivative.eval x ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = 17 / 60 + u := ⟨x - 17 / 60, by ring⟩
  have hu : 0 ≤ u := by linarith only [hx]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  norm_num [initialPolynomial, Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring_nf
  linarith only [lo 4, lo 3, lo 2, lo 1]

private theorem initial_floor {x : ℝ} (hx : 17 / 60 ≤ x) (hx1 : x ≤ 3 / 7) :
    1 ≤ hrlCF0 x := by
  have hf := UnitShape.polynomial_floor (p := initialPolynomial) (m := 1) hx hx1
    (fun _ hs _ => initial_concave hs)
    (by norm_num [initial_eval, hrlCF0]) (by norm_num [initial_eval, hrlCF0])
  simpa only [initial_eval] using hf

private theorem coefficient2_nonpos {x : ℝ} (hx : 17 / 60 ≤ x) : hrlCF2 x ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = 17 / 60 + u := ⟨x - 17 / 60, by ring⟩
  have hu : 0 ≤ u := by linarith only [hx]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  unfold hrlCF2
  ring_nf
  linarith only [lo 8, lo 7, lo 6, lo 5, lo 4, lo 3, lo 2, lo 1]

private theorem coefficient3_nonpos {x : ℝ} (hx : 17 / 60 ≤ x) : hrlCF3 x ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = 17 / 60 + u := ⟨x - 17 / 60, by ring⟩
  have hu : 0 ≤ u := by linarith only [hx]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  unfold hrlCF3
  ring_nf
  linarith only [lo 8, lo 7, lo 6, lo 5, lo 4, lo 3, lo 2, lo 1]

private theorem coefficient4_nonpos {x : ℝ} (hx : 17 / 60 ≤ x) : hrlCF4 x ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = 17 / 60 + u := ⟨x - 17 / 60, by ring⟩
  have hu : 0 ≤ u := by linarith only [hx]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  unfold hrlCF4
  ring_nf
  linarith only [lo 8, lo 7, lo 6, lo 5, lo 4, lo 3, lo 2, lo 1]

private theorem coefficient5_nonpos {x : ℝ} (hx : 17 / 60 ≤ x) : hrlCF5 x ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = 17 / 60 + u := ⟨x - 17 / 60, by ring⟩
  have hu : 0 ≤ u := by linarith only [hx]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  unfold hrlCF5
  ring_nf
  linarith only [lo 8, lo 7, lo 6, lo 5, lo 4, lo 3, lo 2, lo 1]

private theorem coefficient6_nonpos {x : ℝ} (hx : 17 / 60 ≤ x) : hrlCF6 x ≤ 0 := by
  obtain ⟨u, rfl⟩ : ∃ u, x = 17 / 60 + u := ⟨x - 17 / 60, by ring⟩
  have hu : 0 ≤ u := by linarith only [hx]
  have lo (n : ℕ) : 0 ≤ u ^ n := pow_nonneg hu n
  unfold hrlCF6
  ring_nf
  linarith only [lo 8, lo 7, lo 6, lo 5, lo 4, lo 3, lo 2, lo 1]

/-- The residual on the actual duration boundary is at least one. -/
private theorem terminal_floor {x : ℝ} (hx : 17 / 60 ≤ x) (hx1 : x ≤ 3 / 7) :
    1 ≤ hrlP x ((1 - 2 * x) / (1 + 4 * x)) := by
  have hd0 : 0 < 1 + 4 * x := by linarith only [hx]
  have hd1 : 1 + 4 * x ≤ 3 := by linarith only [hx1]
  have hd6 : (1 + 4 * x) ^ 6 ≤ (3 : ℝ) ^ 6 := pow_le_pow_left₀ hd0.le hd1 6
  have hw : 1 ≤ (1 + x) ^ 2 := by nlinarith only [hx, sq_nonneg x]
  have hn := boundary_floor hx hx1
  have hm := mul_le_mul_of_nonneg_left hn (sq_nonneg (1 + x))
  have he := boundary_link hx
  have hp : 0 < 32768 * (1 + 4 * x) ^ 6 := by positivity
  nlinarith only [hd6, hw, hm, he, hp]

/-- Concavity in duration reduces the terminal face to its two actual boundaries. -/
theorem hrl_face {x y : ℝ} (hx : 17 / 60 ≤ x) (hx1 : x ≤ 3 / 7) (hy0 : 0 ≤ y)
    (hy : y * (1 + 4 * x) ≤ 1 - 2 * x) : 1 ≤ hrlP x y := by
  let b := (1 - 2 * x) / (1 + 4 * x)
  have hd : 0 < 1 + 4 * x := by linarith only [hx]
  have hb : 0 < b := div_pos (by linarith only [hx1]) hd
  have hyb : y ≤ b := (le_div_iff₀ hd).mpr hy
  have h0 := initial_floor hx hx1
  have h1 := terminal_floor hx hx1
  have c2 := coefficient2_nonpos hx
  have c3 := coefficient3_nonpos hx
  have c4 := coefficient4_nonpos hx
  have c5 := coefficient5_nonpos hx
  have c6 := coefficient6_nonpos hx
  have hp (n : ℕ) : y ^ n ≤ b ^ n := pow_le_pow_left₀ hy0 hyb n
  have chord (n : ℕ) {c : ℝ} (hc : c ≤ 0) :
      c * (y * b ^ (n + 1)) ≤ c * (y ^ (n + 1) * b) := by
    apply mul_le_mul_of_nonpos_left _ hc
    have hm := mul_le_mul_of_nonneg_left (hp n) (mul_nonneg hy0 hb.le)
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hm
  have f2 := chord 1 c2
  have f3 := chord 2 c3
  have f4 := chord 3 c4
  have f5 := chord 4 c5
  have f6 := chord 5 c6
  norm_num only at f2 f3 f4 f5 f6
  have g1 := mul_le_mul_of_nonneg_left h1 hy0
  have g0 := mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr hyb)
  change y * 1 ≤ y * hrlP x b at g1
  have hchord : b ≤ hrlP x y * b := by
    unfold hrlP at g1 ⊢
    norm_num only [pow_zero, pow_one, mul_one] at g1 ⊢
    linarith only [g1, g0, f2, f3, f4, f5, f6]
  exact (le_mul_iff_one_le_left hb).mp hchord

end SmoothedOctagon
