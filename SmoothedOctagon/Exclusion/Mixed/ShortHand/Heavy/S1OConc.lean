module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1ORep
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1CDeriv

/-!
# Gate S1, outer face: concavity in the reciprocal shape

At fixed `x`, slope `C` and norm `u`, `F₁(x, 1/r, x + C(1/r - 1), u) = g(r)` with
`g(r) = P₀ + P₁r + P₂r² + P₃r³ + P₄r⁴ + Q/Z - (7/96)ℓ(2Z/7)`, `Z = (1 + C) + (x - C)r`
(`hh1o_F1_rep`). With `ℓ'(y) = 8(y² + 1)/(y + 1)⁴`, `ℓ''(y) = -16(y² - y + 2)/(y + 1)⁵ ≥ -1/y²`
for `0 < y ≤ 1` (`(y + 1)⁵ - 16y²(y² - y + 2) = (1 - y)³(1 + 8y - y²)`), the curvature satisfies
`g'' ≤ 2P₂ + 6P₃/x + 12P₄/x² + c(ex/(dx + e))²` on `r ≥ 1/x` when `P₄ ≤ 0`, `4P₄/x + P₃ ≤ 0`,
`Q ≤ 0` (`SHORT_OUTER_RECIPROCAL_LOW_SHAPE` §3). Then `g` is concave and `g(r) ≥ min(g(r₀), g(r₁))`.

## Main API

* `hh1og`, `hh1og1`, `hh1og2`: `g`, `g'`, `g''`; `hh1og_hasDerivAt`, `hh1og1_hasDerivAt`;
* `hh1oP4_nonpos`, `hh1og2_nonpos`, `hh1og_min`, `hh1o_F1_eq_g`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- `ℓ'(y) = 8(y² + 1)/(y + 1)⁴`. -/
noncomputable def hh1ell1 (y : ℝ) : ℝ := 8 * (y ^ 2 + 1) / (y + 1) ^ 4

/-- `ℓ''(y) = -16(y² - y + 2)/(y + 1)⁵`. -/
noncomputable def hh1ell2 (y : ℝ) : ℝ := -16 * (y ^ 2 - y + 2) / (y + 1) ^ 5

theorem hh1_ell_hasDerivAt' {y : ℝ} (hy : 0 < y) : HasDerivAt hh1ell (hh1ell1 y) y := by
  have h := hh1_ell_hasDerivAt hy
  convert h using 1
  unfold hh1ell1 hh1eps
  have h1 : y + 1 ≠ 0 := by linarith
  have hy0 : y ≠ 0 := hy.ne'
  field_simp
  ring

theorem hh1_ell1_hasDerivAt {y : ℝ} (hy : 0 < y) : HasDerivAt hh1ell1 (hh1ell2 y) y := by
  have h1 : y + 1 ≠ 0 := by linarith
  have h := ((((hasDerivAt_id' y).fun_pow 2).add_const 1).const_mul 8).fun_div
    (((hasDerivAt_id' y).add_const 1).fun_pow 4) (pow_ne_zero 4 h1)
  have hf : hh1ell1 = fun s => 8 * (s ^ 2 + 1) / (s + 1) ^ 4 := rfl
  rw [hf]
  convert h using 1
  unfold hh1ell2
  norm_num
  field_simp
  ring

theorem hh1_ell2_ge {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) : -(1 / y ^ 2) ≤ hh1ell2 y := by
  have h1 : 0 < y + 1 := by linarith
  have key : hh1ell2 y + 1 / y ^ 2 = (1 - y) ^ 3 * (1 + 8 * y - y ^ 2) / (y ^ 2 * (y + 1) ^ 5) := by
    unfold hh1ell2
    have h2 : y + 1 ≠ 0 := h1.ne'
    have hy0 : y ≠ 0 := hy.ne'
    field_simp
    ring
  have : 0 ≤ (1 - y) ^ 3 * (1 + 8 * y - y ^ 2) / (y ^ 2 * (y + 1) ^ 5) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (pow_nonneg (by linarith) 3) (by nlinarith)
  linarith

/-- `Z = (1 + C) + (x - C)r = (α + β)/α`. -/
noncomputable def hh1oZ (x C r : ℝ) : ℝ := 1 + C + (x - C) * r

/-- The reciprocal-shape form `g(r)` of `F₁`. -/
noncomputable def hh1og (x C u r : ℝ) : ℝ :=
  hh1oP0 x C u + hh1oP1 x C u * r + hh1oP2 x C u * r ^ 2 + hh1oP3 x C u * r ^ 3 +
    hh1oP4 x C u * r ^ 4 + hh1oQ x C u / hh1oZ x C r - 7 / 96 * hh1ell (2 * hh1oZ x C r / 7)

/-- `g'(r)`. -/
noncomputable def hh1og1 (x C u r : ℝ) : ℝ :=
  hh1oP1 x C u + 2 * hh1oP2 x C u * r + 3 * hh1oP3 x C u * r ^ 2 + 4 * hh1oP4 x C u * r ^ 3 -
    hh1oQ x C u * (x - C) / hh1oZ x C r ^ 2 -
      7 / 96 * hh1ell1 (2 * hh1oZ x C r / 7) * (2 * (x - C) / 7)

/-- `g''(r)`. -/
noncomputable def hh1og2 (x C u r : ℝ) : ℝ :=
  2 * hh1oP2 x C u + 6 * hh1oP3 x C u * r + 12 * hh1oP4 x C u * r ^ 2 +
    2 * hh1oQ x C u * (x - C) ^ 2 / hh1oZ x C r ^ 3 -
      7 / 96 * hh1ell2 (2 * hh1oZ x C r / 7) * (2 * (x - C) / 7) ^ 2

theorem hh1oZ_hasDerivAt (x C r : ℝ) : HasDerivAt (fun s => hh1oZ x C s) (x - C) r := by
  have h := ((hasDerivAt_id' r).const_mul (x - C)).const_add (1 + C)
  simpa [hh1oZ] using h

theorem hh1og_hasDerivAt {x C u r : ℝ} (hZ : 0 < hh1oZ x C r) :
    HasDerivAt (hh1og x C u) (hh1og1 x C u r) r := by
  have hZd := hh1oZ_hasDerivAt x C r
  have hyd : HasDerivAt (fun s => 2 * hh1oZ x C s / 7) (2 * (x - C) / 7) r := by
    simpa using (hZd.const_mul 2).div_const 7
  have hy : 0 < 2 * hh1oZ x C r / 7 := by positivity
  have hl := (hh1_ell_hasDerivAt' hy).comp r hyd
  have hid := hasDerivAt_id' r
  have hp := (((((hid.const_mul (hh1oP1 x C u)).const_add (hh1oP0 x C u)).add
    ((hid.fun_pow 2).const_mul (hh1oP2 x C u))).add ((hid.fun_pow 3).const_mul (hh1oP3 x C u))).add
    ((hid.fun_pow 4).const_mul (hh1oP4 x C u))).add ((hasDerivAt_const r
        (hh1oQ x C u)).fun_div hZd hZ.ne')
  have h := hp.sub (hl.const_mul (7 / 96))
  have hf : hh1og x C u = fun s => hh1oP0 x C u + hh1oP1 x C u * s + hh1oP2 x C u * s ^ 2 +
      hh1oP3 x C u * s ^ 3 + hh1oP4 x C u * s ^ 4 + hh1oQ x C u / hh1oZ x C s -
        7 / 96 * hh1ell (2 * hh1oZ x C s / 7) := rfl
  rw [hf]
  convert h using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]
  unfold hh1og1
  norm_num
  field_simp
  ring

theorem hh1og1_hasDerivAt {x C u r : ℝ} (hZ : 0 < hh1oZ x C r) :
    HasDerivAt (hh1og1 x C u) (hh1og2 x C u r) r := by
  have hZd := hh1oZ_hasDerivAt x C r
  have hyd : HasDerivAt (fun s => 2 * hh1oZ x C s / 7) (2 * (x - C) / 7) r := by
    simpa using (hZd.const_mul 2).div_const 7
  have hy : 0 < 2 * hh1oZ x C r / 7 := by positivity
  have hl := (hh1_ell1_hasDerivAt hy).comp r hyd
  have hid := hasDerivAt_id' r
  have hp := (((((hid.const_mul (2 * hh1oP2 x C u)).const_add (hh1oP1 x C u)).add
    ((hid.fun_pow 2).const_mul (3 * hh1oP3 x C u))).add ((hid.fun_pow 3).const_mul
        (4 * hh1oP4 x C u))).sub
    ((hasDerivAt_const r (hh1oQ x C u * (x - C))).fun_div (hZd.fun_pow 2) (pow_ne_zero 2 hZ.ne')))
  have h := hp.sub ((hl.mul_const (2 * (x - C) / 7)).const_mul (7 / 96))
  have hf : hh1og1 x C u = fun s => hh1oP1 x C u + 2 * hh1oP2 x C u * s + 3 * hh1oP3 x C u * s ^ 2 +
      4 * hh1oP4 x C u * s ^ 3 - hh1oQ x C u * (x - C) / hh1oZ x C s ^ 2 -
        7 / 96 * hh1ell1 (2 * hh1oZ x C s / 7) * (2 * (x - C) / 7) := rfl
  rw [hf]
  convert h using 1
  · funext s; simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply]; ring
  unfold hh1og2
  norm_num
  field_simp
  ring

/-- `P₄ = -(u(x + 1)² - (x² + x + 1))²/(576(x + 1)²) ≤ 0`. -/
theorem hh1oP4_nonpos {x C u : ℝ} (hx : 0 < x) : hh1oP4 x C u ≤ 0 := by
  have key : hh1oP4 x C u = -(u * (x + 1) ^ 2 - (x ^ 2 + x + 1)) ^ 2 / (576 * (x + 1) ^ 2) := by
    unfold hh1oP4
    ring
  rw [key]
  apply div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (u * (x + 1) ^ 2 -
      (x ^ 2 + x + 1))])
  positivity

theorem hh1og2_nonpos {x C u r : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hC0 : 0 ≤ C) (hCx : C < x)
    (hr0 : 1 / x ≤ r) (hr1 : r ≤ 1) (h2 : 0 ≤ -(4 * hh1oP4 x C u / x + hh1oP3 x C u))
    (h3 : 0 ≤ -hh1oQ x C u)
    (h4 : 0 ≤ -(12 * hh1oP4 x C u / x ^ 2 + 6 * hh1oP3 x C u / x + 2 * hh1oP2 x C u +
      7 / 96 * ((x - C) * x / ((1 + C) * x + (x - C))) ^ 2)) :
    hh1og2 x C u r ≤ 0 := by
  have hx0 : 0 < x := by linarith
  have hP4 := hh1oP4_nonpos (C := C) (u := u) hx0
  unfold hh1og2
  generalize hh1oP2 x C u = P2 at h4 ⊢
  generalize hh1oP3 x C u = P3 at h2 h4 ⊢
  generalize hh1oP4 x C u = P4 at hP4 h2 h4 ⊢
  generalize hh1oQ x C u = Q at h3 ⊢
  have hZ : hh1oZ x C r = 1 + C + (x - C) * r := rfl
  rw [hZ]
  obtain ⟨s, hs⟩ : ∃ s, s = 1 / x := ⟨_, rfl⟩
  rw [← hs] at hr0
  have hs0 : 0 < s := by rw [hs]; positivity
  have hxs : x * s = 1 := by rw [hs]; field_simp
  have hxr : 1 ≤ x * r := by nlinarith
  have he : 0 < x - C := by linarith
  obtain ⟨e, he_def⟩ : ∃ e, e = x - C := ⟨_, rfl⟩
  rw [← he_def] at he h4 ⊢
  have hr : 0 < r := lt_of_lt_of_le hs0 hr0
  have hZ0 : 0 < 1 + C + e * r := by positivity
  have hZ3 : 1 + C + e * r ≤ 1 + x := by
    have : e * r ≤ e * 1 := mul_le_mul_of_nonneg_left hr1 he.le
    linarith
  -- the polynomial part
  have h2' : 4 * P4 * s + P3 ≤ 0 := by
    have : 4 * P4 / x = 4 * P4 * s := by rw [hs]; ring
    linarith
  have hA : 12 * P4 * (r + s) + 6 * P3 ≤ 0 := by nlinarith [mul_le_mul_of_nonpos_left hr0 hP4]
  have hpoly : 6 * P3 * r + 12 * P4 * r ^ 2 ≤ 6 * P3 * s + 12 * P4 * s ^ 2 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hr0) hA]
  -- the residue part
  have hQ : 2 * Q * e ^ 2 / (1 + C + e * r) ^ 3 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg e]) (by positivity)
  -- the logarithm part
  have hy : 0 < 2 * (1 + C + e * r) / 7 := by positivity
  have hy1 : 2 * (1 + C + e * r) / 7 ≤ 1 := by linarith
  have hl := hh1_ell2_ge hy hy1
  have hk : 0 ≤ (2 * e / 7) ^ 2 := sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_right hl hk
  have h1' : 1 / (2 * (1 + C + e * r) / 7) ^ 2 * (2 * e / 7) ^ 2 = (e / (1 + C + e * r)) ^ 2 := by
    field_simp
  have hD0 : 0 < (1 + C) * x + e := by positivity
  have hq : e / (1 + C + e * r) ≤ e * x / ((1 + C) * x + e) := by
    rw [div_le_div_iff₀ hZ0 hD0]
    nlinarith [mul_le_mul_of_nonneg_left hxr (le_of_lt (mul_pos he he))]
  have hq0 : 0 ≤ e / (1 + C + e * r) := by positivity
  have hq2 : (e / (1 + C + e * r)) ^ 2 ≤ (e * x / ((1 + C) * x + e)) ^ 2 := by
    nlinarith [mul_le_mul hq hq hq0 (hq0.trans hq)]
  have h4' : 12 * P4 * s ^ 2 + 6 * P3 * s + 2 * P2 + 7 / 96 * (e * x /
      ((1 + C) * x + e)) ^ 2 ≤ 0 := by
    have : 12 * P4 / x ^ 2 + 6 * P3 / x = 12 * P4 * s ^ 2 + 6 * P3 * s := by rw [hs]; ring
    linarith
  linarith

theorem hh1og_min {x C u r0 r r1 : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hC0 : 0 ≤ C) (hCx : C < x)
    (h0 : 1 / x ≤ r0) (h01 : r0 ≤ r) (h12 : r ≤ r1) (h1 : r1 ≤ 1)
    (h2 : 0 ≤ -(4 * hh1oP4 x C u / x + hh1oP3 x C u))
    (h3 : 0 ≤ -hh1oQ x C u)
    (h4 : 0 ≤ -(12 * hh1oP4 x C u / x ^ 2 + 6 * hh1oP3 x C u / x + 2 * hh1oP2 x C u +
      7 / 96 * ((x - C) * x / ((1 + C) * x + (x - C))) ^ 2)) :
    min (hh1og x C u r0) (hh1og x C u r1) ≤ hh1og x C u r := by
  have hx0 : 0 < x := by linarith
  have hZ : ∀ s, 1 / x ≤ s → 0 < hh1oZ x C s := fun s hs => by
    have : 0 < s := lt_of_lt_of_le (by positivity) hs
    unfold hh1oZ
    have : 0 < (x - C) * s := mul_pos (by linarith) this
    linarith
  have hg2 : ∀ s ∈ Icc r0 r1, hh1og2 x C u s ≤ 0 := fun s hs =>
    hh1og2_nonpos hx hx2 hC0 hCx (h0.trans hs.1) (hs.2.trans h1) h2 h3 h4
  have hanti : ∀ s t, r0 ≤ s → s ≤ t → t ≤ r1 → hh1og1 x C u t ≤ hh1og1 x C u s := by
    intro s t hs hst ht
    have key := ss_le_of_deriv (f := fun z => -hh1og1 x C u z) (f' := fun z => -hh1og2 x C u z) hst
      (fun z hz => (hh1og1_hasDerivAt (hZ z (by linarith [hz.1]))).neg)
      (fun z hz => by
        have := hg2 z ⟨by linarith [hz.1], by linarith [hz.2]⟩
        linarith)
    linarith
  rcases le_total 0 (hh1og1 x C u r) with hp | hn
  · have key := ss_le_of_deriv (f := hh1og x C u) (f' := hh1og1 x C u) h01
      (fun z hz => hh1og_hasDerivAt (hZ z (by linarith [hz.1])))
      (fun z hz => le_trans hp (hanti z r (by linarith [hz.1]) (by linarith [hz.2]) h12))
    exact (min_le_left _ _).trans key
  · have key := ss_le_of_deriv (f := fun z => -hh1og x C u z) (f' := fun z => -hh1og1 x C u z) h12
      (fun z hz => (hh1og_hasDerivAt (hZ z (by linarith [hz.1]))).neg)
      (fun z hz => by
        have := hanti r z h01 (by linarith [hz.1]) (by linarith [hz.2])
        linarith)
    exact (min_le_right _ _).trans (by linarith)

/-- `F₁` in the reciprocal-shape form: `F₁(x, α, x + C(α - 1), u) = g(1/α)`. -/
theorem hh1o_F1_eq_g {x C u a b : ℝ} (hx : 1 < x) (ha : 0 < a) (hC : 0 ≤ C) (hCx : C < x)
    (hb : b = x + C * (a - 1)) : hh1oF1 x a b u = hh1og x C u (1 / a) := by
  rw [hh1o_F1_rep hx ha hC hCx hb]
  have ha0 : a ≠ 0 := ha.ne'
  have hZ : hh1oZ x C (1 / a) = (a + b) / a := by
    unfold hh1oZ; rw [hb]; field_simp; ring
  have hy : hh1oy a b = 2 * hh1oZ x C (1 / a) / 7 := by
    rw [hZ]; unfold hh1oy; ring
  unfold hh1og
  rw [hy, hZ, div_div_eq_mul_div]
  ring

end SmoothedOctagon
