module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOB3

/-!
# Gate S1 by hand, outer face, branch B: the test `F₀`

`SHORT_OUTER_BETA_LOW_SHAPE`, `SHORT_OUTER_ALPHA_LOW_SHAPE`, `SHORT_OUTER_LOW_SHAPE_TERMINAL`.
On `3/2 ≤ x ≤ 2`, `1 ≤ α ≤ 6/5`, `6α² ≥ x(x + 2)`, `x ≤ β ≤ x + (10/13)(α - 1)`,
`u_f ≤ u ≤ u_ℓ(x, β)`:

* norm concavity at the actual point reduces `u` to the two curves `u_f(x)`, `u_ℓ(x, β)`;
* `β ↦ F₀` decreases with slope `≤ -7/5120` at a fixed norm (`hl1o_F0_bmono`), and along the ceiling
  `u_ℓ(x, β)` as well: `(F₀)_u ≥ -1/6` on the capped strip (`(8)-(15)`; `(F₀)_u` is affine
  decreasing in `u` and concave in `β`) and `0 ≤ -(u_ℓ)_β ≤ 15/1992` (`(16)-(17)`); so `C = 10/13`;
* at `C = 10/13`, `α ↦ F₀` increases at a fixed norm: in the reciprocal shape
  `g′(r) ≤ P′(r) + ce/Z² - (399/400)ce/Z ≤ -1/400` (`ℓ′(y) ≥ (1 - (5/23)⁴)/y`, and
  `P′ = Σ i pᵢ r^{i-1}` decreases in `u ≥ 3/4`); along the ceiling the norm motion costs at most
  `(1/4)(15/1992)(10/13)` per unit of `α` since `(F₀)_u ≤ Γ_u ≤ 1/4` (`(17)`, `(23)`); so
  `α = α_*(x)`, `1` on `x ≤ 5/3`, `(45x + 22)/97` on `x ≥ 5/3` (`(3)`, `(26)`);
* the four terminal curves are positive.

Route: the shape derivative is bounded through the reciprocal-shape form at the single slope
`C = 10/13` (two-variable signs in `(x, r)`), instead of the `C`-concavity and the quadratic
`H` of `SHORT_OUTER_ALPHA_LOW_SHAPE` §1; the terminal curves are cleared and bounded termwise, instead
of the `x`-monotonicity and the grid evaluation at `x = 2` of `SHORT_OUTER_LOW_SHAPE_TERMINAL`.

## Main API

* `hl1o_F0_uquad`, `hl1o_B_F0u_ge`, `hl1o_B_F0u_le`, `hl1o_F0_bmono_ul`, `hl1o_B_amono`,
  `hl1o_B_amono_ul`, `hl1o_B_F0`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real



/-! ### The shape motion at `C = 10/13` -/

/-- `P′` is a concave quadratic in `u`, decreasing for `u ≥ 3/4`. -/
theorem hl1o_Pd_le {x u r : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (hr0 : 5 / 6 ≤ r) (hr1 : r ≤ 1)
    (hu : 3 / 4 ≤ u) : hl1oPd x (10 / 13) u r ≤ hl1oPd x (10 / 13) (3 / 4) r := by
  have hS : (1 + x) ≠ 0 := by linarith
  have hid : hl1oPd x (10 / 13) u r = hl1oPd x (10 / 13) (3 / 4) r -
      (u - 3 / 4) * hl1PdA (x - 3 / 2) (r - 5 / 6) - (u - 3 / 4) ^ 2 * (r * (r ^ 2 + 6) * (x + 1) ^ 2 / 144) := by
    simp only [hl1oPd, hl1p1, hl1p2, hl1p3, hl1p4, hl1g2, hl1g4, hl1W1, hl1W2, hl1W3, hl1W4, hl1d0,
      hl1d1, hl1d2, hl1J2, hsE0, hl1PdA]
    field_simp
    ring
  have hA := hl1PdA_pos (t := x - 3 / 2) (s := r - 5 / 6) (by linarith) (by linarith) (by linarith)
    (by linarith)
  have h1 : 0 ≤ (u - 3 / 4) * hl1PdA (x - 3 / 2) (r - 5 / 6) := mul_nonneg (by linarith) hA
  have h2 : 0 ≤ (u - 3 / 4) ^ 2 * (r * (r ^ 2 + 6) * (x + 1) ^ 2 / 144) := by
    have : 0 ≤ r := by linarith
    positivity
  linarith

/-- Numerator of `-(P′(x, 3/4, r) - (7/480)(x - 10/13) + 1/400)` at `C = 10/13`, `x = 3/2 + t`, `r = 5/6 + s`. -/
noncomputable def hl1PT2 (t s : ℝ) : ℝ :=
  1 / 28 * t ^ 6 * s ^ 3 + 5 / 56 * t ^ 6 * s ^ 2 + 25 / 336 * t ^ 6 * s + 125 / 6048 * t ^ 6 + 673 / 2184 * t ^ 5 * s ^ 3 + 473 / 624 * t ^ 5 * s ^ 2 + 15817 / 26208 * t ^ 5 * s + 73055 / 471744 * t ^ 5 + 391177 / 389376 * t ^ 4 * s ^ 3 + 1907933 / 778752 * t ^ 4 * s ^ 2 + 59996479 / 32707584 * t ^ 4 * s + 241775291 / 588736512 * t ^ 4 + 2084239 / 1362816 * t ^ 3 * s ^ 3 + 793727 / 209664 * t ^ 3 * s ^ 2 + 43900711 / 16353792 * t ^ 3 * s + 734686447 / 1471841280 * t ^ 3 + 1964903 / 1817088 * t ^ 2 * s ^ 3 + 10530595 / 3634176 * t ^ 2 * s ^ 2 + 46574807 / 21805056 * t ^ 2 * s + 3590123707 / 9812275200 * t ^ 2 + 1641811 / 5451264 * t * s ^ 3 + 11067743 / 10902528 * t * s ^ 2 + 8912173 / 9345024 * t * s + 1042671211 / 5887365120 * t + 1223743 / 43610112 * s ^ 3 + 807575 / 6709248 * s ^ 2 + 80315551 / 523321344 * s + 21535559 / 724598784

theorem hl1PT2_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (1 / 2 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (1 / 6 : ℝ)) :
    (0 : ℝ) ≤ hl1PT2 t s := by
  unfold hl1PT2
  nlinarith [(by positivity : (0 : ℝ) ≤ s),
    (by positivity : (0 : ℝ) ≤ s ^ 2),
    (by positivity : (0 : ℝ) ≤ s ^ 3),
    (by positivity : (0 : ℝ) ≤ t),
    (by positivity : (0 : ℝ) ≤ t * s),
    (by positivity : (0 : ℝ) ≤ t * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 4),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 5),
    (by positivity : (0 : ℝ) ≤ t ^ 5 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 3),
    (by positivity : (0 : ℝ) ≤ t ^ 6),
    (by positivity : (0 : ℝ) ≤ t ^ 6 * s),
    (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 2),
    (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 3)]

/-- **The reciprocal-shape slope of `F₀` at `C = 10/13`**: `g′(r) ≤ -1/400`. -/
theorem hl1o_B_G1 {x u r : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (hr0 : 5 / 6 ≤ r) (hr1 : r ≤ 1)
    (hu : 3 / 4 ≤ u) :
    hl1G1 (hl1p1 x (10 / 13) u) (hl1p2 x (10 / 13) u) (hl1p3 x (10 / 13) u) (hl1p4 x (10 / 13) u)
      (-(7 / 96)) (1 + 10 / 13) (x - 10 / 13) r ≤ -(1 / 400) := by
  have hP := hl1o_Pd_le hx hx2 hr0 hr1 hu
  have hT : hl1oPd x (10 / 13) (3 / 4) r - 7 / 480 * (x - 10 / 13) + 1 / 400 ≤ 0 := by
    have hpos := hl1PT2_pos (t := x - 3 / 2) (s := r - 5 / 6) (by linarith) (by linarith)
      (by linarith) (by linarith)
    have hid : hl1oPd x (10 / 13) (3 / 4) r - 7 / 480 * (x - 10 / 13) + 1 / 400 =
        -hl1PT2 (x - 3 / 2) (r - 5 / 6) / (x + 1) ^ 2 := by
      have hS : 1 + x ≠ 0 := by linarith
      have hS' : x + 1 ≠ 0 := by linarith
      simp only [hl1oPd, hl1p1, hl1p2, hl1p3, hl1p4, hl1g2, hl1g4, hl1W1, hl1W2, hl1W3, hl1W4,
        hl1d0, hl1d1, hl1d2, hl1J2, hsE0, hl1PT2]
      field_simp
      ring
    rw [hid, neg_div]
    have : 0 ≤ hl1PT2 (x - 3 / 2) (r - 5 / 6) / (x + 1) ^ 2 := div_nonneg hpos (by positivity)
    linarith
  set Z := 1 + 10 / 13 + (x - 10 / 13) * r with hZ
  have hZ0 : 9 / 4 ≤ Z := by nlinarith
  have hZ1 : Z ≤ 3 := by nlinarith
  have he : 0 < x - 10 / 13 := by linarith
  have hy0 : 9 / 14 ≤ 2 * Z / 7 := by linarith
  have hy1 : 2 * Z / 7 ≤ 1 := by linarith
  have hyl : 399 / 400 ≤ 2 * Z / 7 * hl1ell1 (2 * Z / 7) := by
    have e : 2 * Z / 7 * hl1ell1 (2 * Z / 7) = 1 - hh1eps (2 * Z / 7) := by
      unfold hl1ell1 hh1eps
      have : 2 * Z / 7 + 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [e]
    have := hl1_eps_le hy0 hy1
    norm_num at this
    linarith
  -- the pole and logarithm terms together are at most `-(1/5)ce`
  have hpl : 7 / 96 * (x - 10 / 13) / Z ^ 2 -
      7 / 96 * hl1ell1 (2 * Z / 7) * (2 * (x - 10 / 13) / 7) ≤ -(7 / 480 * (x - 10 / 13)) := by
    have hZp : 0 < Z := by linarith
    have h1 : 7 / 96 * hl1ell1 (2 * Z / 7) * (2 * (x - 10 / 13) / 7) =
        7 / 96 * (x - 10 / 13) * (2 * Z / 7 * hl1ell1 (2 * Z / 7)) / Z := by
      field_simp
    rw [h1]
    have h2 : 7 / 96 * (x - 10 / 13) * (399 / 400) / Z ≤
        7 / 96 * (x - 10 / 13) * (2 * Z / 7 * hl1ell1 (2 * Z / 7)) / Z := by
      apply div_le_div_of_nonneg_right _ hZp.le
      exact mul_le_mul_of_nonneg_left hyl (by positivity)
    have h3 : 7 / 96 * (x - 10 / 13) / Z ^ 2 - 7 / 96 * (x - 10 / 13) * (399 / 400) / Z ≤
        -(7 / 480 * (x - 10 / 13)) := by
      have e : 7 / 96 * (x - 10 / 13) / Z ^ 2 - 7 / 96 * (x - 10 / 13) * (399 / 400) / Z =
          -(7 / 96 * (x - 10 / 13)) * ((399 / 400) * Z - 1) / Z ^ 2 := by field_simp; ring
      rw [e, div_le_iff₀ (by positivity)]
      have : Z ^ 2 / 5 ≤ (399 / 400) * Z - 1 := by nlinarith
      nlinarith
    linarith
  unfold hl1G1
  rw [← hZ]
  have e : hl1p1 x (10 / 13) u + 2 * hl1p2 x (10 / 13) u * r + 3 * hl1p3 x (10 / 13) u * r ^ 2 +
      4 * hl1p4 x (10 / 13) u * r ^ 3 = hl1oPd x (10 / 13) u r := rfl
  have e2 : -(7 / 96) * (x - 10 / 13) / Z ^ 2 = -(7 / 96 * (x - 10 / 13) / Z ^ 2) := by ring
  rw [e2]
  linarith

end SmoothedOctagon
