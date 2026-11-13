module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Window
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Clearing

/-!
# Norm bounds in the forward low-ratio region

The event-factor ceiling bounds `Je²` and the incoming displacement.
These bounds make the norm coefficient of the combined residual negative.
The effective norm remains below the endpoint norm ceiling by a positive
sum of the time, order, and endpoint gaps.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The low-ratio effective norm `v̂ = v_G + ρ(v_G - F_ℓ)`, `ρ = (3/4)(q + 2t + x - 1)`. -/
noncomputable def nsfVhat (t x q : ℝ) : ℝ :=
  nsfVG t x + 3 / 4 * (q + 2 * t + x - 1) * (nsfVG t x - nsrFl t x q)

/-- `Je² ≤ 10/3` on the low-ratio domain. -/
theorem nsf_LR_J {t x q : ℝ} (ht1 : t ≤ 1 / 3) (hx1 : x ≤ 1) (hx : 0 < x) (ho : 1 ≤ 2 * t + x)
    (hq : 0 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
    (t + x * (x + 2)) * q ^ 2 ≤ 10 / 3 * (1 + x) ^ 2 := by
  have h1 : (q * (2 * t + x)) ^ 2 ≤ (1 + x) ^ 2 := pow_le_pow_left₀ (by positivity) hqo 2
  have h2 : t + x * (x + 2) ≤ 10 / 3 * (2 * t + x) ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg q)
  nlinarith

/-- `WD/x ≤ 9/4` on the low-ratio domain. -/
theorem nsf_LR_WD {t x q : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3) (hx0 : 1 - 2 * t ≤ x)
    (hx : 0 < x) (_hq : 0 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
    q * (t + x * (x + 2)) - (t + x) * (1 + x) ≤ 9 / 4 * x := by
  have hW : 0 < 1 + x := by linarith
  have hJ0 : 0 ≤ t + x * (x + 2) := by positivity
  have ho0 : 0 < 2 * t + x := by linarith
  have h1 : (2 * t + x) * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) ≤
      (1 + x) * (t + x * (x + 2)) - (t + x) * (1 + x) * (2 * t + x) := by
    have := mul_le_mul_of_nonneg_right hqo hJ0
    linarith
  have h2b : 2 * (1 - t) * (1 + x) ≤ 9 / 4 * (2 * t + x) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1 / 4) (by linarith : (0 : ℝ) ≤ 7 / 4 - t),
      mul_nonneg (by linarith : (0 : ℝ) ≤ x - (1 - 2 * t)) (by linarith : (0 : ℝ) ≤ 1 / 4 + 2 * t)]
  have e : (1 + x) * (t + x * (x + 2)) - (t + x) * (1 + x) * (2 * t + x) =
      (1 + x) * (t * (1 - 2 * t) + x * (2 - 3 * t)) := by ring
  have h3 : t * (1 - 2 * t) + x * (2 - 3 * t) ≤ x * (2 * (1 - t)) := by
    have := mul_le_mul_of_nonneg_left hx0 (by linarith : (0 : ℝ) ≤ t)
    linarith
  have h4 : (1 + x) * (t * (1 - 2 * t) + x * (2 - 3 * t)) ≤ 9 / 4 * x * (2 * t + x) := by
    have h5 := mul_le_mul_of_nonneg_left h3 hW.le
    have h6 := mul_le_mul_of_nonneg_left h2b hx.le
    nlinarith
  rw [e] at h1
  have h7 : (2 * t + x) * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) ≤ (2 * t + x) * (9 / 4 * x) := by
    linarith
  exact le_of_mul_le_mul_left h7 ho0

/-- **The `v`-coefficient is negative** on the low-ratio domain, by `Je² ≤ 10/3` and
`WD/x ≤ 9/4`. -/
theorem nsf_LR_Cv {t x k q : ℝ} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3) (hx0 : 1 - 2 * t ≤ x)
    (hx1 : x ≤ 1) (hk : 1 ≤ k) (hq : 1 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
    nsfCv 6 0 t x k q < 0 := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have ho : 1 ≤ 2 * t + x := by linarith
  have hJ0 : 0 < t + x * (x + 2) := by positivity
  have hq0 : 0 < q := by linarith
  have hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2)) := by
    have : (t + x) * (1 + x) ≤ t + x * (x + 2) := by nlinarith
    have := mul_le_mul_of_nonneg_right hq hJ0.le
    linarith
  have hle := nsf_Cv_le (α := 6) (M := 0) (t := t) (x := x) (k := k) (q := q) (by linarith)
    (by linarith) hD (by positivity)
  have hNv := nsf_Nv_le (t := t) (x := x) (k := k) (q := q) (by linarith) hx.le hq (by linarith)
  have hJ := nsf_LR_J ht1 hx1 hx ho hq0.le hqo
  have hWD := nsf_LR_WD ht0 ht1 hx0 hx hq0.le hqo
  have hA : 0 < x * q * k := by positivity
  have hNv0 : nsrNv t x k q < 0 := by linarith
  have e1 : 4 * q * ((6 + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) * nsrNv t x k q ≤
      4 * q * (11 / 3 * (1 + x) ^ 2) * nsrNv t x k q := by
    apply mul_le_mul_of_nonpos_right _ hNv0.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have e2 : 4 * q ^ 2 * (1 + x) ^ 2 * k * (q * (t + x * (x + 2)) - (t + x) * (1 + x)) ≤
      4 * q * (1 + x) ^ 2 * (9 / 4) * (x * q * k) := by
    have h0 : 0 ≤ 4 * q ^ 2 * (1 + x) ^ 2 * k := by positivity
    have := mul_le_mul_of_nonneg_left hWD h0
    have e : 4 * q ^ 2 * (1 + x) ^ 2 * k * (9 / 4 * x) = 4 * q * (1 + x) ^ 2 * (9 / 4) * (x * q * k) := by
      ring
    linarith
  have e3 : 4 * q * (1 + x) ^ 2 * (9 / 4) * (x * q * k) ≤
      4 * q * (1 + x) ^ 2 * (9 / 4) * (-nsrNv t x k q) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hneg : 4 * q * (1 + x) ^ 2 * nsrNv t x k q < 0 := mul_neg_of_pos_of_neg (by positivity) hNv0
  have e4 : 4 * q * (11 / 3 * (1 + x) ^ 2) * nsrNv t x k q + 4 * q * (1 + x) ^ 2 * (9 / 4) * (-nsrNv t x k q)
      = 17 / 12 * (4 * q * (1 + x) ^ 2 * nsrNv t x k q) := by ring
  linarith

/-- The quadratic secant ceiling lies above the positive-integral ceiling. -/
theorem nsf_VG_le_V2 {t x : ℝ} (ht : t ≤ 1) (hx : 0 < x) : nsfVG t x ≤ nsfV2 t x := by
  have hW : (1 + x) ≠ 0 := by positivity
  have hR : (x ^ 2 + 10 * x + 15) ≠ 0 := by positivity
  have he : nsfV2 t x - nsfVG t x =
      (1 - t) * x ^ 4 * (x + 6) / (12 * (1 + x) ^ 2 * (x ^ 2 + 10 * x + 15)) := by
    unfold nsfV2 nsfVG
    field_simp
    ring
  have hc : 0 ≤ 1 - t := sub_nonneg.mpr ht
  have hp : 0 ≤ nsfV2 t x - nsfVG t x := by rw [he]; positivity
  linarith only [hp]

/-- The effective norm stays strictly below the endpoint norm ceiling. -/
theorem nsf_LR_norm_ceiling {t x q : ℝ} (ht1 : t ≤ 1 / 3)
    (hx0 : 1 - 2 * t ≤ x) (hx1 : x ≤ 1) (hq : 1 < q)
    (hqo : q * (2 * t + x) ≤ 1 + x) (hF : nsrFl t x q ≤ nsfVG t x) :
    nsfVhat t x q < 1 - t + t ^ 2 := by
  have hx : 0 < x := by linarith only [ht1, hx0]
  have hW : (1 + x) ≠ 0 := by positivity
  have hy : 0 ≤ q - 1 := by linarith only [hq]
  have ho : 0 ≤ 2 * t + x - 1 := by linarith only [hx0]
  have hqh : q ≤ 2 - 2 * t := by
    have hp := mul_nonneg hy ho
    nlinarith only [hqo, hp]
  have hρ : 3 / 4 * (q + 2 * t + x - 1) ≤ 3 / 2 := by linarith only [hqh, hx1]
  have hgap := mul_le_mul_of_nonneg_right hρ (sub_nonneg.mpr hF)
  have hG := nsf_VG_le_V2 (by linarith only [ht1]) hx
  have hfloor := nsr_Fl_gt_g (t := t) hx (by linarith only [hx0]) hq
  have hbound : nsfVhat t x q ≤ 5 / 2 * nsfV2 t x
      - 3 / 2 * (1 - (1 - t) * (t + x) / (1 + x) ^ 2) := by
    unfold nsfVhat
    linarith only [hgap, hG, hfloor]
  have htime : 0 ≤ (1 / 3 - t) * (13 / 12 - 2 * t) := by
    have : 0 ≤ 1 / 3 - t := sub_nonneg.mpr ht1
    have : 0 ≤ 13 / 12 - 2 * t := by linarith only [ht1]
    positivity
  have horder : 0 ≤ (5 / 8 - t) * (2 * t + x - 1) := by
    have : 0 ≤ 5 / 8 - t := by linarith only [ht1]
    positivity
  have hend : 0 ≤ x * (1 - x) := mul_nonneg hx.le (sub_nonneg.mpr hx1)
  have he : 1 - t + t ^ 2 - (5 / 2 * nsfV2 t x
      - 3 / 2 * (1 - (1 - t) * (t + x) / (1 + x) ^ 2)) =
      (1 - t) * x / (1 + x) ^ 2 *
        (1 / 72 + (1 / 3 - t) * (13 / 12 - 2 * t)
          + (5 / 8 - t) * (2 * t + x - 1) + 5 / 24 * x * (1 - x)) := by
    unfold nsfV2
    field_simp
    ring
  have hp : 0 < 1 - t + t ^ 2 - (5 / 2 * nsfV2 t x
      - 3 / 2 * (1 - (1 - t) * (t + x) / (1 + x) ^ 2)) := by
    rw [he]
    have : 0 < 1 - t := by linarith only [ht1]
    positivity
  linarith only [hp, hbound]

end SmoothedOctagon
