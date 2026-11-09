module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Reverse.Residual
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Reverse.UnitShape.Signs

/-!
# Case M2, reverse successor: the unit-shape exclusion

On the face `k = 1`, for
`0 < t ≤ 13/35`, `0 < x ≤ 1 - 2t`, `1 < 2t + 2x + x²`, `q > 1`, the exact incoming secant
`v = Sec(t, 1 - t, t + x)` with its missing-control floor `v ≥ F_{p/W}(q)` gives `N > 0`.
After the relaxations `v ↦ v̄`, `log q ↦ L₊` and the subtraction of `(q - 1)(v̄ - F_ℓ)`, the
cleared residual is the cubic `P = C₀ + C₁y + C₂y² + C₃y³` in `y = q - 1` (`nsrU_P_eq`),
positive by six coefficient signs (`nsr_cubic_pos`), which are proved by the generated
certificates of `Nonshort/Reverse/UnitShape/Signs`.

## Main API

* `nsrUC0`, …, `nsrUC3`; `nsrU_P_eq`.
* `nsr_cubic_pos`: the univariate reduction (six coefficient signs give a positive cubic).
* `nsrU_signs`: the six signs on the unit-shape domain.
* `nsrU_poly_pos`: `P(t, x, y) > 0` on the domain, for every `y ≥ 0` (only the shape inequalities
  are used: no norm floor).
* `nsr_unit_shape`: **the unit-shape theorem**, `N(t, x, 1, q, v, log q) > 0`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The coefficient of `y^0` in the unit-shape cubic `P`. -/
noncomputable def nsrUC0 (t x : ℝ) : ℝ :=
  48 * x ^ 2 + 104 * x ^ 3 + 76 * x ^ 4 + 20 * x ^ 5 - 192 * t * x ^ 2 - 480 * t * x ^ 3 - 464 * t * x ^ 4 - 232 * t * x ^ 5 - 68 * t * x ^ 6 - 12 * t * x ^ 7 + 240 * t ^ 2 * x ^ 2 + 648 * t ^ 2 * x ^ 3 + 700 * t ^ 2 * x ^ 4 + 404 * t ^ 2 * x ^ 5 + 136 * t ^ 2 * x ^ 6 + 24 * t ^ 2 * x ^ 7 - 96 * t ^ 3 * x ^ 2 - 272 * t ^ 3 * x ^ 3 - 312 * t ^ 3 * x ^ 4 - 192 * t ^ 3 * x ^ 5 - 68 * t ^ 3 * x ^ 6 - 12 * t ^ 3 * x ^ 7

/-- The coefficient of `y^1` in the unit-shape cubic `P`. -/
noncomputable def nsrUC1 (t x : ℝ) : ℝ :=
  -48 * x + 128 * x ^ 2 + 416 * x ^ 3 + 378 * x ^ 4 + 146 * x ^ 5 + 20 * x ^ 6 + 240 * t * x - 152 * t * x ^ 2 - 1460 * t * x ^ 3 - 2176 * t * x ^ 4 - 1652 * t * x ^ 5 - 726 * t * x ^ 6 - 174 * t * x ^ 7 - 16 * t * x ^ 8 - 384 * t ^ 2 * x - 504 * t ^ 2 * x ^ 2 + 540 * t ^ 2 * x ^ 3 + 1762 * t ^ 2 * x ^ 4 + 1842 * t ^ 2 * x ^ 5 + 1000 * t ^ 2 * x ^ 6 + 276 * t ^ 2 * x ^ 7 + 28 * t ^ 2 * x ^ 8 + 192 * t ^ 3 * x + 528 * t ^ 3 * x ^ 2 + 504 * t ^ 3 * x ^ 3 + 36 * t ^ 3 * x ^ 4 - 336 * t ^ 3 * x ^ 5 - 294 * t ^ 3 * x ^ 6 - 102 * t ^ 3 * x ^ 7 - 12 * t ^ 3 * x ^ 8

/-- The coefficient of `y^2` in the unit-shape cubic `P`. -/
noncomputable def nsrUC2 (t x : ℝ) : ℝ :=
  -72 * x + 124 * x ^ 2 + 474 * x ^ 3 + 456 * x ^ 4 + 190 * x ^ 5 + 30 * x ^ 6 - 48 * t + 336 * t * x + 224 * t * x ^ 2 - 1400 * t * x ^ 3 - 3068 * t * x ^ 4 - 3026 * t * x ^ 5 - 1690 * t * x ^ 6 - 540 * t * x ^ 7 - 90 * t * x ^ 8 - 6 * t * x ^ 9 + 144 * t ^ 2 - 312 * t ^ 2 * x - 1476 * t ^ 2 * x ^ 2 - 1662 * t ^ 2 * x ^ 3 - 280 * t ^ 2 * x ^ 4 + 940 * t ^ 2 * x ^ 5 + 854 * t ^ 2 * x ^ 6 + 294 * t ^ 2 * x ^ 7 + 36 * t ^ 2 * x ^ 8 - 96 * t ^ 3 - 144 * t ^ 3 * x + 168 * t ^ 3 * x ^ 2 + 476 * t ^ 3 * x ^ 3 + 204 * t ^ 3 * x ^ 4 - 276 * t ^ 3 * x ^ 5 - 334 * t ^ 3 * x ^ 6 - 132 * t ^ 3 * x ^ 7 - 18 * t ^ 3 * x ^ 8

/-- The coefficient of `y^3` in the unit-shape cubic `P`. -/
noncomputable def nsrUC3 (t x : ℝ) : ℝ :=
  -8 * x + 76 * x ^ 2 + 182 * x ^ 3 + 157 * x ^ 4 + 63 * x ^ 5 + 10 * x ^ 6 - 8 * t + 164 * t * x + 234 * t * x ^ 2 - 233 * t * x ^ 3 - 848 * t * x ^ 4 - 931 * t * x ^ 5 - 528 * t * x ^ 6 - 160 * t * x ^ 7 - 23 * t * x ^ 8 - t * x ^ 9 + 88 * t ^ 2 + 12 * t ^ 2 * x - 402 * t ^ 2 * x ^ 2 - 543 * t ^ 2 * x ^ 3 - 31 * t ^ 2 * x ^ 4 + 456 * t ^ 2 * x ^ 5 + 394 * t ^ 2 * x ^ 6 + 135 * t ^ 2 * x ^ 7 + 17 * t ^ 2 * x ^ 8 - 48 * t ^ 3 - 88 * t ^ 3 * x + 84 * t ^ 3 * x ^ 2 + 342 * t ^ 3 * x ^ 3 + 306 * t ^ 3 * x ^ 4 + 54 * t ^ 3 * x ^ 5 - 66 * t ^ 3 * x ^ 6 - 38 * t ^ 3 * x ^ 7 - 6 * t ^ 3 * x ^ 8

/-- **The cleared unit-shape cubic**: at `k = 1`,
`6(q + 1)W²X³(N(v̄, L₊(q)) - (q - 1)(v̄ - F_ℓ)) = C₀ + C₁y + C₂y² + C₃y³` with `y = q - 1`. -/
theorem nsrU_P_eq {t x q : ℝ} (hx : 0 < x) (hq : 0 < q) :
    6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 *
      (nsrN t x 1 q (nsrVbar t x) (nsrLp q) - (q - 1) * (nsrVbar t x - nsrFl t x q)) =
      nsrUC0 t x + nsrUC1 t x * (q - 1) + nsrUC2 t x * (q - 1) ^ 2 + nsrUC3 t x * (q - 1) ^ 3 := by
  have h1 : (1 + x) ≠ 0 := by positivity
  have h2 : (x + 2) ≠ 0 := by positivity
  have h3 : (q + 1) ≠ 0 := by positivity
  unfold nsrN nsrVbar nsrLp nsrFl nsrUC0 nsrUC1 nsrUC2 nsrUC3
  field_simp
  ring

theorem nsrU_J0 (t x : ℝ) : nsrUC0 t x = x ^ 2 * nsrUJr0 x (1 - 2 * t - x) := by
  unfold nsrUC0 nsrUJr0; ring

theorem nsrU_J1 (t x : ℝ) :
    20 * x * nsrUC1 t x + 3 * nsrUC0 t x = x ^ 2 * nsrUJr1 x (1 - 2 * t - x) := by
  unfold nsrUC0 nsrUC1 nsrUJr1; ring

theorem nsrU_J2 (t x : ℝ) :
    53 * nsrUC0 t x + 20 * x ^ 2 * nsrUC2 t x = x ^ 2 * nsrUJr2 x (1 - 2 * t - x) := by
  unfold nsrUC0 nsrUC2 nsrUJr2; ring

theorem nsrU_J3 (t x : ℝ) :
    24 * x ^ 3 * nsrUC3 t x + 12 * x ^ 2 * nsrUC2 t x - nsrUC0 t x =
      x ^ 2 * nsrUJr3 x (1 - 2 * t - x) := by
  unfold nsrUC0 nsrUC2 nsrUC3 nsrUJr3; ring

theorem nsrU_J4 (t x : ℝ) :
    40 * x ^ 3 * nsrUC3 t x + 30 * x ^ 2 * nsrUC2 t x + 7 * nsrUC0 t x =
      x ^ 2 * nsrUJr4 x (1 - 2 * t - x) := by
  unfold nsrUC0 nsrUC2 nsrUC3 nsrUJr4; ring

theorem nsrU_J5 (t x : ℝ) :
    24 * x ^ 3 * nsrUC3 t x - nsrUC0 t x = x ^ 2 * nsrUJr5 x (1 - 2 * t - x) := by
  unfold nsrUC0 nsrUC3 nsrUJr5; ring

/-- The unit-shape domain, in the coordinates `(x, s)`, `s = 1 - 2t - x`, is covered by the three
pieces of `Nonshort/Reverse/UnitShape/Signs`. -/
theorem nsrU_dom {f : ℝ → ℝ → ℝ} {t x : ℝ} (ht : 0 < t) (ht' : t ≤ 13 / 35) (hx : 0 < x)
    (hxt : x ≤ 1 - 2 * t) (hgap : 1 < 2 * t + 2 * x + x ^ 2)
    (ha : ∀ x s : ℝ, (3 / 25) ≤ x → x ≤ (9 / 35) → (9 / 35) - x ≤ s → s ≤ x + x ^ 2 →
      0 < (x + x ^ 2) - ((9 / 35) - x) → 0 < f x s)
    (hb : ∀ x s : ℝ, (9 / 35) ≤ x → x ≤ (2 / 5) → 0 ≤ s → s ≤ x + x ^ 2 →
      0 < (x + x ^ 2) - (0) → 0 < f x s)
    (hc : ∀ x s : ℝ, (2 / 5) ≤ x → x ≤ 1 → 0 ≤ s → s ≤ 1 - x → 0 < (1 - x) - (0) → 0 < f x s) :
    0 < f x (1 - 2 * t - x) := by
  have hx3 : 3 / 25 ≤ x := by nlinarith
  rcases le_total x (9 / 35) with h1 | h1
  · exact ha x _ hx3 h1 (by linarith) (by linarith) (by linarith)
  rcases le_total x (2 / 5) with h2 | h2
  · exact hb x _ h1 h2 (by linarith) (by linarith) (by nlinarith)
  · exact hc x _ h2 (by linarith) (by linarith) (by linarith) (by linarith)

/-- **The six signs** on the unit-shape domain. -/
theorem nsrU_signs {t x : ℝ} (ht : 0 < t) (ht' : t ≤ 13 / 35) (hx : 0 < x) (hxt : x ≤ 1 - 2 * t)
    (hgap : 1 < 2 * t + 2 * x + x ^ 2) :
    0 < nsrUC0 t x ∧ 0 < 20 * x * nsrUC1 t x + 3 * nsrUC0 t x ∧
      0 < 53 * nsrUC0 t x + 20 * x ^ 2 * nsrUC2 t x ∧
      0 < 24 * x ^ 3 * nsrUC3 t x + 12 * x ^ 2 * nsrUC2 t x - nsrUC0 t x ∧
      0 < 40 * x ^ 3 * nsrUC3 t x + 30 * x ^ 2 * nsrUC2 t x + 7 * nsrUC0 t x ∧
      0 < 24 * x ^ 3 * nsrUC3 t x - nsrUC0 t x := by
  have hx2 : 0 < x ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [nsrU_J0]; exact mul_pos hx2 (nsrU_dom ht ht' hx hxt hgap nsrUJr0_pos_a nsrUJr0_pos_b nsrUJr0_pos_c)
  · rw [nsrU_J1]; exact mul_pos hx2 (nsrU_dom ht ht' hx hxt hgap nsrUJr1_pos_a nsrUJr1_pos_b nsrUJr1_pos_c)
  · rw [nsrU_J2]; exact mul_pos hx2 (nsrU_dom ht ht' hx hxt hgap nsrUJr2_pos_a nsrUJr2_pos_b nsrUJr2_pos_c)
  · rw [nsrU_J3]; exact mul_pos hx2 (nsrU_dom ht ht' hx hxt hgap nsrUJr3_pos_a nsrUJr3_pos_b nsrUJr3_pos_c)
  · rw [nsrU_J4]; exact mul_pos hx2 (nsrU_dom ht ht' hx hxt hgap nsrUJr4_pos_a nsrUJr4_pos_b nsrUJr4_pos_c)
  · rw [nsrU_J5]; exact mul_pos hx2 (nsrU_dom ht ht' hx hxt hgap nsrUJr5_pos_a nsrUJr5_pos_b nsrUJr5_pos_c)

/-- **The univariate reduction**: the six signs force the cubic `C₀ + C₁y + C₂y² + C₃y³` to be
positive for every `y ≥ 0`. -/
theorem nsr_cubic_pos {c0 c1 c2 c3 x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) (h0 : 0 < c0)
    (h1 : 0 < 20 * x * c1 + 3 * c0) (h2 : 0 < 53 * c0 + 20 * x ^ 2 * c2)
    (h3 : 0 < 24 * x ^ 3 * c3 + 12 * x ^ 2 * c2 - c0)
    (h4 : 0 < 40 * x ^ 3 * c3 + 30 * x ^ 2 * c2 + 7 * c0) (h5 : 0 < 24 * x ^ 3 * c3 - c0) :
    0 < c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 := by
  obtain ⟨z, hz, rfl⟩ : ∃ z, 0 ≤ z ∧ y = x * z := ⟨y / x, div_nonneg hy hx.le, by field_simp⟩
  have f0 : 1 / 3 ≤ 1 - 3 / 20 * z + 1 / 24 * z ^ 3 := by
    nlinarith [mul_nonneg hz (sq_nonneg (z - 1)), sq_nonneg (z - 23 / 20)]
  have f1 : 1 / 3 ≤ 1 - 3 / 20 * z - 13 / 15 * z ^ 2 + 19 / 40 * z ^ 3 := by
    nlinarith [mul_nonneg hz (sq_nonneg (z - 4 / 3)), sq_nonneg (z - 4 / 3 + 13 / 144)]
  have f2 : 1 / 100 ≤ 1 - 3 / 20 * z - 53 / 20 * z ^ 2 + 29 / 16 * z ^ 3 := by
    nlinarith [mul_nonneg hz (sq_nonneg (z - 1)), sq_nonneg (z - 1 - 1 / 156)]
  have e : c0 + c1 * (x * z) + c2 * (x * z) ^ 2 + c3 * (x * z) ^ 3 =
      c0 + (x * c1) * z + (x ^ 2 * c2) * z ^ 2 + (x ^ 3 * c3) * z ^ 3 := by ring
  rw [e]
  have h1' : 0 < 20 * (x * c1) + 3 * c0 := by linarith
  have h2' : 0 < 53 * c0 + 20 * (x ^ 2 * c2) := by linarith
  have h3' : 0 < 24 * (x ^ 3 * c3) + 12 * (x ^ 2 * c2) - c0 := by linarith
  have h4' : 0 < 40 * (x ^ 3 * c3) + 30 * (x ^ 2 * c2) + 7 * c0 := by linarith
  have h5' : 0 < 24 * (x ^ 3 * c3) - c0 := by linarith
  clear h1 h2 h3 h4 h5 e
  generalize x * c1 = A at h1' ⊢
  generalize x ^ 2 * c2 = B at h2' h3' h4' ⊢
  generalize x ^ 3 * c3 = G at h3' h4' h5' ⊢
  have hA : 0 ≤ (A + 3 / 20 * c0) * z := mul_nonneg (by linarith) hz
  have hz2 : 0 ≤ z ^ 2 := by positivity
  have hz3 : 0 ≤ z ^ 3 := by positivity
  rcases le_or_gt 0 B with hB | hB
  · have hB' : 0 ≤ B * z ^ 2 := mul_nonneg hB hz2
    have hG : 0 ≤ (G - c0 / 24) * z ^ 3 := mul_nonneg (by linarith) hz3
    have w : 0 ≤ c0 * ((1 - 3 / 20 * z + 1 / 24 * z ^ 3) - 1 / 3) := mul_nonneg h0.le (by linarith)
    linear_combination hA + hB' + hG + w + (1 / 3 : ℝ) * h0
  rcases le_or_gt (-13 / 15 * c0) B with hB2 | hB2
  · have hG : 0 ≤ (G - (c0 - 12 * B) / 24) * z ^ 3 := mul_nonneg (by linarith) hz3
    have w0 : 0 ≤ (c0 + 15 / 13 * B) * ((1 - 3 / 20 * z + 1 / 24 * z ^ 3) - 1 / 3) :=
      mul_nonneg (by linarith) (by linarith)
    have w1 : 0 ≤ (-15 / 13 * B) * ((1 - 3 / 20 * z - 13 / 15 * z ^ 2 + 19 / 40 * z ^ 3) - 1 / 3) :=
      mul_nonneg (by linarith) (by linarith)
    linear_combination hA + hG + w0 + w1 + (1 / 3 : ℝ) * h0
  · have hG : 0 ≤ (G + (30 * B + 7 * c0) / 40) * z ^ 3 := mul_nonneg (by linarith) hz3
    have w1 : 0 ≤ (c0 + 60 / 107 * (B + 13 / 15 * c0)) *
        ((1 - 3 / 20 * z - 13 / 15 * z ^ 2 + 19 / 40 * z ^ 3) - 1 / 100) :=
      mul_nonneg (by linarith) (by linarith)
    have w2 : 0 ≤ (-(60 / 107) * (B + 13 / 15 * c0)) *
        ((1 - 3 / 20 * z - 53 / 20 * z ^ 2 + 29 / 16 * z ^ 3) - 1 / 100) :=
      mul_nonneg (by nlinarith) (by linarith)
    linear_combination hA + hG + w1 + w2 + (1 / 100 : ℝ) * h0

/-- **The polynomial part of the unit-shape theorem**: on the shape domain, the cleared cubic is
positive for every `q ≥ 1`. Only the shape inequalities are used. -/
theorem nsrU_poly_pos {t x q : ℝ} (ht : 0 < t) (ht' : t ≤ 13 / 35) (hx : 0 < x)
    (hxt : x ≤ 1 - 2 * t) (hgap : 1 < 2 * t + 2 * x + x ^ 2) (hq : 1 ≤ q) :
    0 < nsrN t x 1 q (nsrVbar t x) (nsrLp q) - (q - 1) * (nsrVbar t x - nsrFl t x q) := by
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := nsrU_signs ht ht' hx hxt hgap
  have hc := nsr_cubic_pos hx (by linarith : (0 : ℝ) ≤ q - 1) s0 s1 s2 s3 s4 s5
  rw [← nsrU_P_eq hx (by linarith)] at hc
  have hpos : 0 < 6 * (q + 1) * (1 + x) ^ 2 * (x + 2) ^ 3 := by
    have : 0 < q + 1 := by linarith
    positivity
  exact pos_of_mul_pos_right hc hpos.le

/-- **The unit-shape theorem**: on the face
`k = 1`, with the exact incoming secant and its missing-control floor, `N > 0`. -/
theorem nsr_unit_shape {t x q v : ℝ} (ht : 0 < t) (ht' : t ≤ 13 / 35) (hx : 0 < x)
    (hxt : x ≤ 1 - 2 * t) (hgap : 1 < 2 * t + 2 * x + x ^ 2) (hq : 1 < q) (hv : v = nsrSecN t x)
    (hF : m2F ((t + x) / (1 + x)) q ≤ v) : 0 < nsrN t x 1 q v (Real.log q) := by
  refine nsr_N_pos_of_relax (vb := nsrVbar t x) (Lb := nsrLp q) (Fl := nsrFl t x q) (m := q - 1)
    ?_ (nsr_log_lt_Lp hq).le (nsrNv_nonpos ht.le hx.le hq.le (by linarith))
    (nsrNL_nonpos ht.le hx.le (by linarith) (by norm_num))
    ((nsr_m2F_gt_Fl hq (by linarith) (by linarith)).le.trans hF) (by linarith)
    (nsrU_poly_pos ht ht' hx hxt hgap hq.le)
  rw [hv]; exact (nsr_secN_lt_vbar hx (by linarith)).le

end SmoothedOctagon
