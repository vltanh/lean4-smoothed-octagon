module

public import SmoothedOctagon.Exclusion.Forward.Log

/-!
# Case F: the conditional Casimir theorem

Two small norm increments force `γ² > 23/125`.

The exact central offset `E₀ = e₀ - Φ` is replaced by `e₀` (`0 < E₀ ≤ e₀`), the bracket decreases in
both increments and is concave along the edge `δu + δv = 1/35`, so it suffices to treat the vertices
`A = (1/35, 0)` and `B = (29/2240, 1/64)`. At `B` the estimate
`(c - b)S + bT ≤ (c - b)(S + T) + (2b - c)T` (resp. `≤ (7/3)c`) is used. The four resulting
one-variable inequalities are quartic polynomial signs on `[11/5, 13/5]` and `[13/5, 3]`, proved
from their positive Bernstein coefficients.

## Main API

* `ff_e0_ge`: `e₀ ≥ 3/4` for `U ≤ 3`.
* `ff_Phi_nonneg`, `ff_Phi_le`: `0 ≤ Φ ≤ 1/100` on the forward domain.
* `ff_casimir_lower`: the conditional Casimir theorem.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

theorem ff_e0_ge {U : ℝ} (hU : 0 < U) (hU3 : U ≤ 3) : 3 / 4 ≤ ff_e0 U := by
  unfold ff_e0
  have hK : 0 < 1 + U := by linarith
  have : 1 / 4 ≤ 1 / (1 + U) := by rw [div_le_div_iff₀ (by norm_num) hK]; linarith
  linarith

theorem ff_e0_le {U : ℝ} (hU : 11 / 5 ≤ U) : ff_e0 U ≤ 73 / 80 := by
  unfold ff_e0
  have hK : 0 < 1 + U := by linarith
  have : 1 / (1 + U) ≤ 5 / 16 := by rw [div_le_div_iff₀ hK (by norm_num)]; linarith
  linarith

theorem ff_Phi_nonneg {U z w : ℝ} (hU : 0 < U) (hU3 : U ≤ 3) (hz : 1 ≤ z) (hw : 1 ≤ w) :
    0 ≤ ff_Phi U z w := by
  unfold ff_Phi
  have h1 := ff_f_nonneg (r := (1 + z) / 2) (by linarith)
  have h2 := ff_f_nonneg (r := (1 + w) / 2) (by linarith)
  have h3 := ff_f_nonneg (r := 4 / (1 + U)) (by rw [le_div_iff₀ (by linarith)]; linarith)
  linarith

theorem ff_Phi_le {U z w : ℝ} (hU : 11 / 5 ≤ U) (hU3 : U ≤ 3) (hz : 1 ≤ z) (hz' : z ≤ 4 / 3)
    (hw : 1 ≤ w) (hw' : w ≤ 4 / 3) : ff_Phi U z w ≤ 1 / 100 := by
  unfold ff_Phi
  have hK : 0 < 1 + U := by linarith
  have h1 := ff_f_le_cube (t := (z - 1) / 2) (by linarith)
  have h2 := ff_f_le_cube (t := (w - 1) / 2) (by linarith)
  have h3 := ff_f_le_cube (t := (3 - U) / (1 + U)) (div_nonneg (by linarith) hK.le)
  rw [show 1 + (z - 1) / 2 = (1 + z) / 2 by ring] at h1
  rw [show 1 + (w - 1) / 2 = (1 + w) / 2 by ring] at h2
  rw [show 1 + (3 - U) / (1 + U) = 4 / (1 + U) by field_simp; ring] at h3
  have b1 : ((z - 1) / 2) ^ 3 ≤ (1 / 6) ^ 3 := by
    apply pow_le_pow_left₀ (by linarith); linarith
  have b2 : ((w - 1) / 2) ^ 3 ≤ (1 / 6) ^ 3 := by
    apply pow_le_pow_left₀ (by linarith); linarith
  have b3 : ((3 - U) / (1 + U)) ^ 3 ≤ (1 / 4) ^ 3 := by
    apply pow_le_pow_left₀ (div_nonneg (by linarith) hK.le)
    rw [div_le_div_iff₀ hK (by norm_num)]; linarith
  linarith

/-! ### The four vertex inequalities -/

private lemma ff_vA1 {U : ℝ} (h1 : 11 / 5 ≤ U) (h2 : U ≤ 13 / 5) :
    23 / 125 * (16 * U ^ 2) < 327 / 140 * (1 + U) ^ 2 -
      ((1 + U) - (1 + U) ^ 2 / 8 + 1 + (1 + U) * (1 / 35) * ((5 * U + 1) / 6)) ^ 2 := by
  have hx : 0 ≤ U - 11 / 5 := by linarith
  have hy : 0 ≤ 13 / 5 - U := by linarith
  nlinarith [mul_nonneg (mul_nonneg hx hx) (mul_nonneg hx hx),
    mul_nonneg (mul_nonneg hx hx) (mul_nonneg hx hy), mul_nonneg (mul_nonneg hx hx) (mul_nonneg hy hy),
    mul_nonneg (mul_nonneg hx hy) (mul_nonneg hy hy), mul_nonneg (mul_nonneg hy hy) (mul_nonneg hy hy)]

private lemma ff_vA2 {U : ℝ} (h1 : 13 / 5 ≤ U) (h2 : U ≤ 3) :
    23 / 125 * (16 * U ^ 2) < 327 / 140 * (1 + U) ^ 2 -
      ((1 + U) - (1 + U) ^ 2 / 8 + 1 + (1 + U) * (1 / 35) * (7 / 3)) ^ 2 := by
  have hx : 0 ≤ U - 13 / 5 := by linarith
  have hy : 0 ≤ 3 - U := by linarith
  nlinarith [mul_nonneg (mul_nonneg hx hx) (mul_nonneg hx hx),
    mul_nonneg (mul_nonneg hx hx) (mul_nonneg hx hy), mul_nonneg (mul_nonneg hx hx) (mul_nonneg hy hy),
    mul_nonneg (mul_nonneg hx hy) (mul_nonneg hy hy), mul_nonneg (mul_nonneg hy hy) (mul_nonneg hy hy)]

private lemma ff_vB1 {U : ℝ} (h1 : 11 / 5 ≤ U) (h2 : U ≤ 13 / 5) :
    23 / 125 * (16 * U ^ 2) < 4 * (3 / 4 + (1 / 35 - 1 / 64)) * (3 / 4 + 1 / 64) * (1 + U) ^ 2 -
      ((1 + U) - (1 + U) ^ 2 / 8 + 1 + (1 + U) * ((1 / 35 - 1 / 64) * (2 + 5 * (U - 1) / 3) +
        (2 * (1 / 64) - 1 / 35) * (7 / 3))) ^ 2 := by
  have hx : 0 ≤ U - 11 / 5 := by linarith
  have hy : 0 ≤ 13 / 5 - U := by linarith
  nlinarith [mul_nonneg (mul_nonneg hx hx) (mul_nonneg hx hx),
    mul_nonneg (mul_nonneg hx hx) (mul_nonneg hx hy), mul_nonneg (mul_nonneg hx hx) (mul_nonneg hy hy),
    mul_nonneg (mul_nonneg hx hy) (mul_nonneg hy hy), mul_nonneg (mul_nonneg hy hy) (mul_nonneg hy hy)]

private lemma ff_vB2 {U : ℝ} (h1 : 13 / 5 ≤ U) (h2 : U ≤ 3) :
    23 / 125 * (16 * U ^ 2) < 4 * (3 / 4 + (1 / 35 - 1 / 64)) * (3 / 4 + 1 / 64) * (1 + U) ^ 2 -
      ((1 + U) - (1 + U) ^ 2 / 8 + 1 + (1 + U) * (1 / 35) * (7 / 3)) ^ 2 := by
  have hx : 0 ≤ U - 13 / 5 := by linarith
  have hy : 0 ≤ 3 - U := by linarith
  nlinarith [mul_nonneg (mul_nonneg hx hx) (mul_nonneg hx hx),
    mul_nonneg (mul_nonneg hx hx) (mul_nonneg hx hy), mul_nonneg (mul_nonneg hx hx) (mul_nonneg hy hy),
    mul_nonneg (mul_nonneg hx hy) (mul_nonneg hy hy), mul_nonneg (mul_nonneg hy hy) (mul_nonneg hy hy)]

/-- The Gram bracket `Q(x, y) = 4(3/4 + x)(3/4 + y) - (e + Sx + Ty)²`, with `E` replaced by its
upper bound `e + Sx + Ty`. -/
private noncomputable def ffQ (e S T x y : ℝ) : ℝ := 4 * (3 / 4 + x) * (3 / 4 + y) - (e + S * x + T * y) ^ 2

/-- The core of the conditional Casimir theorem, with `e = e₀`, `S`, `T` as free variables. -/
private lemma ff_cas_core {U e S T du dv E : ℝ} (hU : 11 / 5 ≤ U) (hU3 : U < 3)
    (he0 : 3 / 4 ≤ e) (hKe : (1 + U) * e = (1 + U) - (1 + U) ^ 2 / 8 + 1)
    (hS : 2 ≤ S) (hST : S ≤ T) (hT : T ≤ 7 / 3) (hsig : S + T ≤ 2 + 5 * (U - 1) / 3)
    (hdu : 0 ≤ du) (hdv : 0 ≤ dv) (hsum : du + dv ≤ 1 / 35) (hdv' : dv ≤ 1 / 64)
    (hE0 : 0 ≤ E) (hE1 : E ≤ e + S * du + T * dv) :
    23 / 125 * (16 * U ^ 2) < (1 + U) ^ 2 * (4 * (3 / 4 + du) * (3 / 4 + dv) - E ^ 2) := by
  have hU0 : 0 < U := by linarith
  have hK : 0 < 1 + U := by linarith
  let Q := ffQ e S T
  have hq : Q du dv ≤ 4 * (3 / 4 + du) * (3 / 4 + dv) - E ^ 2 := by
    unfold Q ffQ
    nlinarith
  -- `Q` decreases in the first variable: `Q(δu, δv) ≥ Q(c - δv, δv)`, `c = 1/35`
  have hmono : Q (1 / 35 - dv) dv ≤ Q du dv := by
    have hd : 0 ≤ 1 / 35 - dv - du := by linarith
    have h1 : 3 ≤ 2 * S * e := by nlinarith
    have h2 : 0 ≤ S * (S * (du + (1 / 35 - dv))) := by
      have : 0 ≤ du + (1 / 35 - dv) := by linarith
      positivity
    have h3 : 8 * dv ≤ 2 * S * T * dv := by
      have : 4 ≤ S * T := by nlinarith
      nlinarith
    have hbr : 3 + 4 * dv - S * (2 * e + S * (du + (1 / 35 - dv)) + 2 * T * dv) ≤ 0 := by
      have : S * (2 * e + S * (du + (1 / 35 - dv)) + 2 * T * dv) =
          2 * S * e + S * (S * (du + (1 / 35 - dv))) + 2 * S * T * dv := by ring
      linarith
    have e1 : Q (1 / 35 - dv) dv - Q du dv =
        (1 / 35 - dv - du) * (3 + 4 * dv - S * (2 * e + S * (du + (1 / 35 - dv)) + 2 * T * dv)) := by
      unfold Q ffQ
      ring
    have := mul_le_mul_of_nonneg_left hbr hd
    linarith
  -- concavity along the edge
  have hconc : (1 - 64 * dv) * Q (1 / 35) 0 + 64 * dv * Q (1 / 35 - 1 / 64) (1 / 64) ≤
      Q (1 / 35 - dv) dv := by
    have e1 : Q (1 / 35 - dv) dv - ((1 - 64 * dv) * Q (1 / 35) 0 +
        64 * dv * Q (1 / 35 - 1 / 64) (1 / 64)) = (4 + (T - S) ^ 2) * dv * (1 / 64 - dv) := by
      unfold Q ffQ
      ring
    have : 0 ≤ (4 + (T - S) ^ 2) * dv * (1 / 64 - dv) := by
      apply mul_nonneg (mul_nonneg (by positivity) hdv); linarith
    linarith
  -- the two vertices, after multiplying by `K²`
  have hvert : ∀ (P0 s : ℝ), 0 ≤ s → (23 / 125 * (16 * U ^ 2) < P0 * (1 + U) ^ 2 -
      ((1 + U) - (1 + U) ^ 2 / 8 + 1 + (1 + U) * s) ^ 2) →
      23 / 125 * (16 * U ^ 2) < (1 + U) ^ 2 * (P0 - (e + s) ^ 2) := by
    intro P0 s hs h
    have : ((1 + U) - (1 + U) ^ 2 / 8 + 1 + (1 + U) * s) = (1 + U) * (e + s) := by
      rw [mul_add, hKe]
    rw [this] at h
    nlinarith
  have hS2 : S ≤ (5 * U + 1) / 6 := by linarith
  have hS3 : S ≤ 7 / 3 := by linarith
  have hK2 : 0 < (1 + U) ^ 2 := by positivity
  have fin : ∀ P0 s x : ℝ, 0 ≤ x → x ≤ s →
      23 / 125 * (16 * U ^ 2) < (1 + U) ^ 2 * (P0 - (e + s) ^ 2) →
      23 / 125 * (16 * U ^ 2) < (1 + U) ^ 2 * (P0 - (e + x) ^ 2) := by
    intro P0 s x hx hxs h
    have hle : (e + x) ^ 2 ≤ (e + s) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    have := mul_le_mul_of_nonneg_left (sub_le_sub_left hle P0) hK2.le
    linarith
  have hA : 23 / 125 * (16 * U ^ 2) < (1 + U) ^ 2 * Q (1 / 35) 0 := by
    unfold Q ffQ
    rw [show e + S * (1 / 35) + T * 0 = e + S * (1 / 35) by ring]
    rcases le_total U (13 / 5) with hU' | hU'
    · refine fin _ ((1 / 35) * ((5 * U + 1) / 6)) _ (by linarith) (by linarith) ?_
      refine hvert _ _ (by positivity) ?_
      have h := ff_vA1 hU hU'; ring_nf at h ⊢; linarith
    · refine fin _ ((1 / 35) * (7 / 3)) _ (by linarith) (by linarith) ?_
      refine hvert _ _ (by positivity) ?_
      have h := ff_vA2 hU' hU3.le; ring_nf at h ⊢; linarith
  have hB : 23 / 125 * (16 * U ^ 2) < (1 + U) ^ 2 * Q (1 / 35 - 1 / 64) (1 / 64) := by
    unfold Q ffQ
    rw [show e + S * (1 / 35 - 1 / 64) + T * (1 / 64) = e + (S * (1 / 35 - 1 / 64) + T * (1 / 64)) by
      ring]
    rcases le_total U (13 / 5) with hU' | hU'
    · refine fin _ ((1 / 35 - 1 / 64) * (2 + 5 * (U - 1) / 3) + (2 * (1 / 64) - 1 / 35) * (7 / 3))
        _ (by linarith) (by linarith) ?_
      refine hvert _ _ (by linarith) ?_
      have h := ff_vB1 hU hU'; ring_nf at h ⊢; linarith
    · refine fin _ ((1 / 35) * (7 / 3)) _ (by linarith) (by linarith) ?_
      refine hvert _ _ (by positivity) ?_
      have h := ff_vB2 hU' hU3.le; ring_nf at h ⊢; linarith
  -- assemble
  have h64 : 0 ≤ 64 * dv := by linarith
  have h64' : 0 ≤ 1 - 64 * dv := by linarith
  clear_value Q
  have hfin : 23 / 125 * (16 * U ^ 2) < (1 + U) ^ 2 * Q du dv := by
    have c1 := mul_le_mul_of_nonneg_left (hconc.trans hmono) hK2.le
    have e1 : (1 + U) ^ 2 * ((1 - 64 * dv) * Q (1 / 35) 0 + 64 * dv * Q (1 / 35 - 1 / 64) (1 / 64)) =
        (1 - 64 * dv) * ((1 + U) ^ 2 * Q (1 / 35) 0) +
          64 * dv * ((1 + U) ^ 2 * Q (1 / 35 - 1 / 64) (1 / 64)) := by ring
    rw [e1] at c1
    have h1 := mul_le_mul_of_nonneg_left hA.le h64'
    have hX : 23 / 125 * (16 * U ^ 2) = (1 - 64 * dv) * (23 / 125 * (16 * U ^ 2)) +
        64 * dv * (23 / 125 * (16 * U ^ 2)) := by ring
    rcases eq_or_lt_of_le h64 with h0 | h0
    · rw [← h0] at c1 h1 hX
      linarith
    · have h2 := mul_lt_mul_of_pos_left hB h0
      linarith
  have := mul_le_mul_of_nonneg_left hq hK2.le
  linarith

/-- **The conditional Casimir theorem**: on `11/5 ≤ U < 3`, `1 ≤ z ≤ w ≤ 4/3`, `z + w ≤ 5(U - 1)/3`,
nonnegative norm increments with `δu + δv ≤ 1/35` and `δv ≤ 1/64`, and `E = e₀ - Φ + Sδu + Tδv`, the
Casimir exceeds `23/125`. -/
theorem ff_casimir_lower {U z w du dv E : ℝ} (hU : 11 / 5 ≤ U) (hU3 : U < 3) (hz : 1 ≤ z)
    (hzw : z ≤ w) (hw : w ≤ 4 / 3) (hzw' : z + w ≤ 5 * (U - 1) / 3) (hdu : 0 ≤ du) (hdv : 0 ≤ dv)
    (hsum : du + dv ≤ 1 / 35) (hdv' : dv ≤ 1 / 64)
    (hE : E = ff_e0 U - ff_Phi U z w + (1 + z) * du + (1 + w) * dv) :
    23 / 125 < ff_cas U (3 / 4 + du) (3 / 4 + dv) E := by
  have hU0 : 0 < U := by linarith
  have hK : 0 < 1 + U := by linarith
  have he0 := ff_e0_ge hU0 hU3.le
  have hP0 := ff_Phi_nonneg (z := z) (w := w) hU0 hU3.le hz (by linarith)
  have hP1 := ff_Phi_le (z := z) (w := w) hU hU3.le hz (by linarith) (by linarith) hw
  have hKe : (1 + U) * ff_e0 U = (1 + U) - (1 + U) ^ 2 / 8 + 1 := by
    unfold ff_e0; field_simp
  have hE0 : 0 ≤ E := by rw [hE]; nlinarith
  have hE1 : E ≤ ff_e0 U + (1 + z) * du + (1 + w) * dv := by rw [hE]; linarith
  have key := ff_cas_core hU hU3 he0 hKe (by linarith : (2 : ℝ) ≤ 1 + z) (by linarith)
    (by linarith : 1 + w ≤ 7 / 3) (by linarith) hdu hdv hsum hdv' hE0 hE1
  unfold ff_cas
  rw [lt_div_iff₀ (by positivity)]
  linarith

end SmoothedOctagon
