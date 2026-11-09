from links import link, link3, yform_tx
LEAN=__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '../../../SmoothedOctagon/Exclusion/Mixed/FwdHand/')
lhsA = "48 * (q + 1) * (1 + x) * (x ^ 2 + 10 * x + 15) * fhComb 6 0 t x 1 q (fhVhat t x q) (nhLp q) 0"
lhsB = "48 * (q + 1) * (1 + x) * (x ^ 2 + 10 * x + 15) * fhComb 6 0 t x (2 * t + x) q (fhVhat t x q) (nhLp q) 0"
linkA = link3('fhCLRa', 'fh_LRa_link', 'LR', '6', '0', '1', 'The cleared low-ratio residual at `k = 1` is the certificate polynomial `fhCLRa`.')
linkB = link3('fhCLRb', 'fh_LRb_link', 'LR', '6', '0', '(2 * t + x)', 'The cleared low-ratio residual at `k = 2t + x` is the certificate polynomial `fhCLRb`.')
s = f'''module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Window
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.Clear
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLRa
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.CertLRb

/-!
# Case M2, forward successor by hand: the duration ratio exceeds one third

`MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION` with `MIXED_NONSHORT_FORWARD_RATIO_REDUCTION` §§2-3: an
actual forward window has `t > 1/3`. Suppose `1/4 < t ≤ 1/3`. The combined residual
`F = (7 - Je²)N + C_*(3/4 - 𝒯_U)` (`fhComb 6 0`) is negative (`fh_window_comb`); its
`v`-coefficient is negative (`fh_LR_Cv`, from `Je² ≤ 10/3`, `WD/x ≤ 9/4`) and its `log q`
coefficient is nonpositive, so raising `v` to `v̂ = v_G + ρ(v_G - F_ℓ)` (`ρ = (3/4)(q + 2t + x - 1)`)
and `log q` to `L₊` keeps it negative. It is a concave quadratic in `k` (`fh_comb_pos_of_ends`), and
both shape endpoints `k = 1`, `k = 2t + x` have positive residual (certificates `CertLRa`,
`CertLRb`), a contradiction.

Route: the shape monotonicity `Ĝ_k > 0` of the notes (§5 of the ratio reduction) is replaced by
concavity in `k` and a second endpoint certificate at `k = 2t + x`; the polynomial sign of §§2-5 of
the low-ratio note is a generated Bernstein certificate.

## Main API

* `fhVhat`; `fh_LRa_link`, `fh_LRb_link`; `fh_LR_Cv`.
* `fh_lowRatio_core`: the scalar exclusion; `fh_low_ratio`: **`t > 1/3`** for an actual forward
  window.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The low-ratio effective norm `v̂ = v_G + ρ(v_G - F_ℓ)`, `ρ = (3/4)(q + 2t + x - 1)`
(`MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION` (4)). -/
noncomputable def fhVhat (t x q : ℝ) : ℝ :=
  fhVG t x + 3 / 4 * (q + 2 * t + x - 1) * (fhVG t x - nhFl t x q)

{linkA}
{linkB}
/-- `Je² ≤ 10/3` on the low-ratio domain (`MIXED_NONSHORT_FORWARD_RATIO_REDUCTION` (8)). -/
theorem fh_LR_J {{t x q : ℝ}} (ht1 : t ≤ 1 / 3) (hx1 : x ≤ 1) (hx : 0 < x) (ho : 1 ≤ 2 * t + x)
    (hq : 0 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
    (t + x * (x + 2)) * q ^ 2 ≤ 10 / 3 * (1 + x) ^ 2 := by
  have h1 : (q * (2 * t + x)) ^ 2 ≤ (1 + x) ^ 2 := pow_le_pow_left₀ (by positivity) hqo 2
  have h2 : t + x * (x + 2) ≤ 10 / 3 * (2 * t + x) ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg q)
  nlinarith

/-- `WD/x ≤ 9/4` on the low-ratio domain (`MIXED_NONSHORT_FORWARD_RATIO_REDUCTION` (8)). -/
theorem fh_LR_WD {{t x q : ℝ}} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3) (hx0 : 1 - 2 * t ≤ x)
    (hx : 0 < x) (hq : 0 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
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

/-- **The `v`-coefficient is negative** on the low-ratio domain
(`MIXED_NONSHORT_FORWARD_RATIO_REDUCTION` (8)-(9)). -/
theorem fh_LR_Cv {{t x k q : ℝ}} (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 1 / 3) (hx0 : 1 - 2 * t ≤ x)
    (hx1 : x ≤ 1) (hk : 1 ≤ k) (hq : 1 ≤ q) (hqo : q * (2 * t + x) ≤ 1 + x) :
    fhCv 6 0 t x k q < 0 := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have ho : 1 ≤ 2 * t + x := by linarith
  have hJ0 : 0 < t + x * (x + 2) := by positivity
  have hq0 : 0 < q := by linarith
  have hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2)) := by
    have : (t + x) * (1 + x) ≤ t + x * (x + 2) := by nlinarith
    have := mul_le_mul_of_nonneg_right hq hJ0.le
    linarith
  have hle := fh_Cv_le (α := 6) (M := 0) (t := t) (x := x) (k := k) (q := q) (by linarith)
    (by linarith) hD (by positivity)
  have hNv := fh_Nv_le (t := t) (x := x) (k := k) (q := q) (by linarith) hx.le hq (by linarith)
  have hJ := fh_LR_J ht1 hx1 hx ho hq0.le hqo
  have hWD := fh_LR_WD ht0 ht1 hx0 hx hq0.le hqo
  have hA : 0 < x * q * k := by positivity
  have hNv0 : nhNv t x k q < 0 := by linarith
  have e1 : 4 * q * ((6 + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) * nhNv t x k q ≤
      4 * q * (11 / 3 * (1 + x) ^ 2) * nhNv t x k q := by
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
      4 * q * (1 + x) ^ 2 * (9 / 4) * (-nhNv t x k q) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hneg : 4 * q * (1 + x) ^ 2 * nhNv t x k q < 0 := mul_neg_of_pos_of_neg (by positivity) hNv0
  have e4 : 4 * q * (11 / 3 * (1 + x) ^ 2) * nhNv t x k q + 4 * q * (1 + x) ^ 2 * (9 / 4) * (-nhNv t x k q)
      = 17 / 12 * (4 * q * (1 + x) ^ 2 * nhNv t x k q) := by ring
  linarith

/-- **The low-ratio scalar exclusion** (`MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION`). -/
theorem fh_lowRatio_core {{t x k q v F : ℝ}} (ht0 : 1 / 4 < t) (ht1 : t ≤ 1 / 3) (hk1 : 1 ≤ k)
    (hko : k < 2 * t + x) (h4 : 4 * t + x < 2) (hx1 : x < 1) (hq : 1 < q)
    (hqs : q * (4 * t + 2 * x - 1) < 1 + x) (hv : v = nhSecN t x)
    (hF : m2F ((t + x) / (1 + x)) q ≤ v) (hcomb : fhComb 6 0 t x k q v (Real.log q) F < 0) :
    False := by
  have hx : 0 < x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hj : 1 < 2 * t + x := by linarith
  have hq0 : 0 < q := by linarith
  have hqo : q * (2 * t + x) ≤ 1 + x := by nlinarith
  have hCv := fh_LR_Cv ht0.le ht1 (by linarith) hx1.le hk1 hq.le hqo
  have hCL : fhCL 6 t x k q ≤ 0 := by
    unfold fhCL
    have hJ : (t + x * (x + 2)) * q ^ 2 ≤ 7 * (1 + x) ^ 2 := by
      have h1 : q * (2 * t + x) ≤ 1 + x := hqo
      have h2 : q ^ 2 * (2 * t + x) ^ 2 ≤ (1 + x) ^ 2 := by nlinarith [mul_le_mul h1 h1 (by positivity) (by linarith)]
      have h3 : t + x * (x + 2) ≤ 7 * (2 * t + x) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg q)]
    have := nhNL_nonpos (t := t) (x := x) (k := k) (q := q) (by linarith) hx.le hq0.le (by linarith)
    have h7 : 0 ≤ 4 * q * ((6 + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) := by
      apply mul_nonneg (by positivity); linarith
    exact mul_nonpos_of_nonneg_of_nonpos h7 this
  -- the rational substitutions
  have hVG := fh_secN_lt_VG hx (by linarith : t < 1)
  rw [← hv] at hVG
  have hFl := nh_m2F_gt_Fl hq (by linarith : 0 < t + x) hW
  have hLp := nh_log_lt_Lp hq
  have hvh : v < fhVhat t x q := by
    unfold fhVhat
    have : 0 ≤ 3 / 4 * (q + 2 * t + x - 1) * (fhVG t x - nhFl t x q) := by
      apply mul_nonneg (by linarith); linarith
    linarith
  have e1 := fh_comb_sub_v 6 0 t x k q (fhVhat t x q) v (nhLp q) 0
  have e2 := fh_comb_sub_L 6 0 t x k q v (nhLp q) (Real.log q) 0
  have e3 := fh_comb_sub_F 6 0 t x k q v (Real.log q) 0 F
  have m1 : (fhVhat t x q - v) * fhCv 6 0 t x k q < 0 := mul_neg_of_pos_of_neg (by linarith) hCv
  have m2 : (nhLp q - Real.log q) * fhCL 6 t x k q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hCL
  have hG : fhComb 6 0 t x k q (fhVhat t x q) (nhLp q) 0 < 0 := by
    have : (0 - F) * (4 * q * (1 + x) ^ 2 * 0) = 0 := by ring
    linarith
  -- the two shape endpoints
  have hy1 : (q - 1) * (1 + 2 * (2 * t + x - 1)) ≤ (1 - 2 * t) - (2 * t + x - 1) := by nlinarith
  have hA : 0 < fhComb 6 0 t x 1 q (fhVhat t x q) (nhLp q) 0 := by
    have h := fhCLRa_pos_y (1 - 2 * t) (2 * t + x - 1) (q - 1) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith) hy1
    rw [← fh_LRa_link t x q hq0 hx] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hB : 0 < fhComb 6 0 t x (2 * t + x) q (fhVhat t x q) (nhLp q) 0 := by
    have hy2 : q - 1 ≤ 1 - 2 * t := by nlinarith
    have h := fhCLRb_pos_y (1 - 2 * t) (2 * t + x - 1) (q - 1) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) hy2
    rw [← fh_LRb_link t x q hq0 hx] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hD : (t + x) * (1 + x) ≤ q * (t + x * (x + 2)) := by nlinarith
  have := fh_comb_pos_of_ends (by linarith) hq0.le hD hk1 hko.le hA hB
  linarith

/-- **The duration ratio exceeds one third** (`MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION` (1)). -/
theorem fh_low_ratio (W : M2Window) (hF : W.ForwardNext) : 1 / 3 < W.nt := by
  by_contra h
  push Not at h
  obtain ⟨-, -, hx, hk1, hq, -, hv, -, -, hFl, -⟩ := nh_window_basic W
  exact fh_lowRatio_core (fh_window_quarter W) h hk1.le (fh_window_order W) (fh_window_four W)
    (fh_window_x_lt_one W) hq (by
      have := fh_window_swap W
      have hden : 0 < 4 * W.nt + 2 * W.nx - 1 := by
        have := fh_window_order W; have := fh_window_quarter W; linarith
      rwa [lt_div_iff₀ hden] at this) hv hFl
    (fh_window_comb W hF (α := 6) (M := 0) (by norm_num) le_rfl)

end SmoothedOctagon
'''
open(LEAN + 'LowRatio.lean', 'w').write(s)
print(len(s))
