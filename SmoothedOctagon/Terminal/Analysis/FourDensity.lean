module

public import SmoothedOctagon.Terminal.Analysis.LogBounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.LinearCombination

/-!
# The four-piece density on the quarter circle

The four-piece density is
`δ(a, b) = [4s(s - 1) + 2(1 + a)(1 - b) log a + 2(1 - a)(1 + b) log b]/((s - 1)(s + 3))`,
`s = a + b`, on the open quarter circle `a, b > 0`, `a² + b² = 1`. Its minimum is
`δ(1/√2, 1/√2) = (8 - 4√2 - log 2)/(2√2 - 1)`, attained only at `a = b`.

* `ra_weight_monotoneOn`: for `c ≥ 2`, `x ↦ (2x + c) log x/(1 - x)` is monotone on `(0, 1)`.
* `ra_weight_le`: hence `(2b + c)(1 - a) log b ≤ (2a + c)(1 - b) log a` for `0 < b ≤ a < 1`.
* `ra_four_density`: the minimum and its equality case.

By symmetry `b ≤ a`, so `b ∈ (0, √2/2]` and `a = √(1 - b²)`. The density `ψ(b) = δ(a, b)` is
strictly decreasing there (`psi_strictAntiOn`). The sign of its derivative is that of
`H = (s - 1)² [(2b + c) log b/(1 - b) - (2a + c) log a/(1 - a)]/(a - b)`, `c = 2 + 2ab`, which is
fixed by the monotonicity of `x ↦ (2x + c) log x/(1 - x)`. That monotonicity follows from
`log x ≥ (x - x⁻¹)/2`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- `√32 = 4√2`. -/
theorem ra_sqrt32 : √32 = 4 * √2 := by
  rw [show (32 : ℝ) = 4 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]

/-- `√8 = 2√2`. -/
theorem ra_sqrt8 : √8 = 2 * √2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- The derivative of `x ↦ (2x + c) log x/(1 - x)`. -/
private lemma ra_w_hasDerivAt (c : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => (2 * x + c) * Real.log x / (1 - x))
      (((2 + c) * Real.log x + (2 * x + c) * (1 - x) / x) / (1 - x) ^ 2) x := by
  have h1 := (((hasDerivAt_id' x).const_mul 2).add_const c).mul (Real.hasDerivAt_log hx0.ne')
  have h2 := (hasDerivAt_id' x).const_sub 1
  have h := h1.div h2 (by linarith : (1 : ℝ) - x ≠ 0)
  convert h using 1
  simp only [Pi.mul_apply]
  field_simp
  ring

/-- For `c ≥ 2`, `x ↦ (2x + c) log x/(1 - x)` is monotone on `(0, 1)`. -/
theorem ra_weight_monotoneOn {c : ℝ} (hc : 2 ≤ c) :
    MonotoneOn (fun x => (2 * x + c) * Real.log x / (1 - x)) (Ioo 0 1) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
    (f' := fun x => ((2 + c) * Real.log x + (2 * x + c) * (1 - x) / x) / (1 - x) ^ 2)
    (fun x hx => (ra_w_hasDerivAt c hx.1 hx.2).continuousAt.continuousWithinAt) ?_ ?_
  · intro x hx
    rw [interior_Ioo] at hx ⊢
    exact (ra_w_hasDerivAt c hx.1 hx.2).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    obtain ⟨hx0, hx1⟩ := hx
    apply div_nonneg _ (sq_nonneg _)
    have hL := ra_half_sub_inv_le_log hx0 hx1.le
    have e : (2 + c) * ((x - x⁻¹) / 2) + (2 * x + c) * (1 - x) / x =
        (c - 2) * (1 - x) ^ 2 / (2 * x) := by
      field_simp
      ring
    have h3 : 0 ≤ (c - 2) * (1 - x) ^ 2 / (2 * x) :=
      div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ 2 + c)]

/-- `(2b + c)(1 - a) log b ≤ (2a + c)(1 - b) log a` for `0 < b ≤ a < 1` and `c ≥ 2`. -/
theorem ra_weight_le {a b c : ℝ} (hc : 2 ≤ c) (hb : 0 < b) (hba : b ≤ a) (ha1 : a < 1) :
    (2 * b + c) * (1 - a) * Real.log b ≤ (2 * a + c) * (1 - b) * Real.log a := by
  have h := ra_weight_monotoneOn hc ⟨hb, by linarith⟩ ⟨by linarith, ha1⟩ hba
  simp only at h
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at h
  linarith

/-- The four-piece density expression. -/
private noncomputable def fd (a b : ℝ) : ℝ :=
  (4 * (a + b) * (a + b - 1) + 2 * (1 + a) * (1 - b) * Real.log a +
    2 * (1 - a) * (1 + b) * Real.log b) / ((a + b - 1) * (a + b + 3))

private lemma fd_symm (a b : ℝ) : fd a b = fd b a := by
  unfold fd
  ring_nf

/-- The derivative of `y ↦ δ(A(y), y)`. -/
private lemma fd_hasDerivAt {A : ℝ → ℝ} {A' x : ℝ} (hA : HasDerivAt A A' x) (ha : 0 < A x)
    (hx : 0 < x) (hd : (A x + x - 1) * (A x + x + 3) ≠ 0) :
    HasDerivAt (fun y => fd (A y) y)
      (((4 * (A' + 1) * (2 * (A x + x) - 1) + 2 * A' * (1 - x) * Real.log (A x)
          - 2 * (1 + A x) * Real.log (A x) + 2 * (1 + A x) * (1 - x) * (A' / A x)
          - 2 * A' * (1 + x) * Real.log x + 2 * (1 - A x) * Real.log x
          + 2 * (1 - A x) * (1 + x) / x) * ((A x + x - 1) * (A x + x + 3))
        - (4 * (A x + x) * (A x + x - 1) + 2 * (1 + A x) * (1 - x) * Real.log (A x) +
            2 * (1 - A x) * (1 + x) * Real.log x) * ((A' + 1) * (2 * (A x + x) + 2)))
        / ((A x + x - 1) * (A x + x + 3)) ^ 2) x := by
  have hs : HasDerivAt (fun y => A y + y) (A' + 1) x := hA.add (hasDerivAt_id' x)
  have e1 := (hs.const_mul 4).mul (hs.sub_const 1)
  have e2 := (((hA.const_add 1).const_mul 2).mul ((hasDerivAt_id' x).const_sub 1)).mul
    (hA.log ha.ne')
  have e3 := (((hA.const_sub 1).const_mul 2).mul ((hasDerivAt_id' x).const_add 1)).mul
    (Real.hasDerivAt_log hx.ne')
  have hn := (e1.add e2).add e3
  have hdn := (hs.sub_const 1).mul (hs.add_const 3)
  have h := hn.div hdn hd
  convert h using 1
  · funext y
    simp only [fd, Pi.mul_apply, Pi.add_apply, Pi.div_apply]
  · simp only [Pi.mul_apply, Pi.add_apply]
    ring

/-- The numerator of the derivative of `y ↦ δ(√(1 - y²), y)`, cleared of `a²b`. -/
private noncomputable def kp (a b : ℝ) : ℝ :=
  (4 * a * b * (a - b) * (2 * (a + b) - 1) - 2 * a * b ^ 2 * (1 - b) * Real.log a
      - 2 * a ^ 2 * b * (1 + a) * Real.log a - 2 * b ^ 2 * (1 + a) * (1 - b)
      + 2 * a * b ^ 2 * (1 + b) * Real.log b + 2 * a ^ 2 * b * (1 - a) * Real.log b
      + 2 * a ^ 2 * (1 - a) * (1 + b)) * ((a + b - 1) * (a + b + 3))
    - (4 * (a + b) * (a + b - 1) + 2 * (1 + a) * (1 - b) * Real.log a +
        2 * (1 - a) * (1 + b) * Real.log b) * ((2 * (a + b) + 2) * (a - b)) * (a * b)

private lemma one_lt_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1) :
    1 < a + b := by
  nlinarith [mul_pos ha hb]

private lemma psi_hasDerivAt {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun y => fd (√(1 - y ^ 2)) y)
      (kp (√(1 - y ^ 2)) y / (√(1 - y ^ 2) ^ 2 * y *
        ((√(1 - y ^ 2) + y - 1) * (√(1 - y ^ 2) + y + 3)) ^ 2)) y := by
  have hpos : 0 < 1 - y ^ 2 := by nlinarith
  have ha : 0 < √(1 - y ^ 2) := Real.sqrt_pos.2 hpos
  have ha2 : √(1 - y ^ 2) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt hpos.le
  have hA : HasDerivAt (fun y => √(1 - y ^ 2)) (-y / √(1 - y ^ 2)) y := by
    have h1 : HasDerivAt (fun y => 1 - y ^ 2) (-(2 * y)) y := by
      simpa using (hasDerivAt_pow 2 y).const_sub 1
    have := h1.sqrt hpos.ne'
    convert this using 1
    field_simp
  have hs1 := one_lt_add ha hy0 (by rw [ha2]; ring)
  have hd : (√(1 - y ^ 2) + y - 1) * (√(1 - y ^ 2) + y + 3) ≠ 0 :=
    (mul_pos (by linarith) (by linarith)).ne'
  have h := fd_hasDerivAt hA ha hy0 hd
  convert h using 1
  generalize √(1 - y ^ 2) = a at ha hd ⊢
  rw [kp]
  field_simp
  ring

/-- The sign of the derivative: `kp a b < 0` for `0 < b < a` on the circle. -/
private lemma kp_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hba : b < a) (hab : a ^ 2 + b ^ 2 = 1) :
    kp a b < 0 := by
  have ha1 : a < 1 := by nlinarith
  have hb1 : b < 1 := by linarith
  have hs1 := one_lt_add ha hb hab
  have hX := ra_weight_le (c := 2 + 2 * a * b) (by nlinarith [mul_pos ha hb]) hb hba.le ha1
  have key : kp a b * ((1 - a) * (1 - b) * (a + b + 1)) =
      a * b * (2 * (a + b - 1) ^ 2 * (a + b + 1) *
          ((2 * b + (2 + 2 * a * b)) * (1 - a) * Real.log b -
            (2 * a + (2 + 2 * a * b)) * (1 - b) * Real.log a) -
        2 * (a - b) * (a + b) * (a + b - 1) ^ 3 * (1 - a) * (1 - b)) := by
    rw [kp]
    linear_combination
      (Real.log a * (-2*a^5*b^2 + 2*a^5*b - 2*a^4*b^3 - 8*a^4*b^2 + 10*a^4*b + 2*a^3*b^4 -
        16*a^3*b^3 + 4*a^3*b^2 + 10*a^3*b + 2*a^2*b^5 - 8*a^2*b^4 + 8*a^2*b^2 - 2*a^2*b -
        2*a*b^5 + 2*a*b^4 + 6*a*b^3 - 2*a*b^2 - 4*a*b) +
      Real.log b * (-2*a^5*b^2 + 2*a^5*b - 2*a^4*b^3 + 8*a^4*b^2 - 2*a^4*b + 2*a^3*b^4 +
        16*a^3*b^3 - 6*a^3*b + 2*a^2*b^5 + 8*a^2*b^4 - 4*a^2*b^3 - 8*a^2*b^2 + 2*a^2*b -
        2*a*b^5 - 10*a*b^4 - 10*a*b^3 + 2*a*b^2 + 4*a*b) - 2*a^5*b + 2*a^5 - 4*a^4*b^2 +
        2*a^4*b + 2*a^4 + 10*a^3*b - 10*a^3 + 4*a^2*b^4 - 10*a^2*b + 6*a^2 + 2*a*b^5 -
        2*a*b^4 - 10*a*b^3 + 10*a*b^2 - 2*b^5 - 2*b^4 + 10*b^3 - 6*b^2) * hab
  have hP : 0 < (1 - a) * (1 - b) * (a + b + 1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have t1 : 2 * (a + b - 1) ^ 2 * (a + b + 1) *
      ((2 * b + (2 + 2 * a * b)) * (1 - a) * Real.log b -
        (2 * a + (2 + 2 * a * b)) * (1 - b) * Real.log a) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have t2 : 0 < 2 * (a - b) * (a + b) * (a + b - 1) ^ 3 * (1 - a) * (1 - b) := by
    have : 0 < a - b := by linarith
    have : 0 < a + b - 1 := by linarith
    have : 0 < 1 - a := by linarith
    have : 0 < 1 - b := by linarith
    positivity
  have hR : a * b * (2 * (a + b - 1) ^ 2 * (a + b + 1) *
          ((2 * b + (2 + 2 * a * b)) * (1 - a) * Real.log b -
            (2 * a + (2 + 2 * a * b)) * (1 - b) * Real.log a) -
        2 * (a - b) * (a + b) * (a + b - 1) ^ 3 * (1 - a) * (1 - b)) < 0 :=
    mul_neg_of_pos_of_neg (mul_pos ha hb) (by linarith)
  by_contra hc
  have := mul_nonneg (not_lt.1 hc) hP.le
  linarith

private lemma sqrt2_half_sq : (√2 / 2) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

private lemma sqrt2_half_pos : 0 < √2 / 2 := by positivity

private lemma sqrt2_half_lt_one : √2 / 2 < 1 := by
  nlinarith [sqrt2_half_sq, sqrt2_half_pos]

/-- `y ↦ δ(√(1 - y²), y)` is strictly decreasing on `(0, √2/2]`. -/
private lemma psi_strictAntiOn :
    StrictAntiOn (fun y => fd (√(1 - y ^ 2)) y) (Ioc 0 (√2 / 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 _)
  · intro y hy
    exact (psi_hasDerivAt hy.1
      (lt_of_le_of_lt hy.2 sqrt2_half_lt_one)).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioc] at hy
    obtain ⟨hy0, hy1⟩ := hy
    have hy1' : y < 1 := hy1.trans sqrt2_half_lt_one
    rw [(psi_hasDerivAt hy0 hy1').deriv]
    have hpos : 0 < 1 - y ^ 2 := by nlinarith
    have ha : 0 < √(1 - y ^ 2) := Real.sqrt_pos.2 hpos
    have ha2 : √(1 - y ^ 2) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt hpos.le
    have hy2 : y ^ 2 < 1 / 2 := by nlinarith [sqrt2_half_sq]
    have hba : y < √(1 - y ^ 2) := by
      rw [Real.lt_sqrt hy0.le]
      linarith
    have hs1 := one_lt_add ha hy0 (by rw [ha2]; ring)
    apply div_neg_of_neg_of_pos (kp_neg ha hy0 hba (by rw [ha2]; ring))
    have : 0 < (√(1 - y ^ 2) + y - 1) * (√(1 - y ^ 2) + y + 3) :=
      mul_pos (by linarith) (by linarith)
    positivity

/-- The value at the symmetric point. -/
private lemma fd_sym_value :
    fd (√(1 - (√2 / 2) ^ 2)) (√2 / 2) = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) := by
  have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : √(1 - (√2 / 2) ^ 2) = √2 / 2 := by
    rw [show 1 - (√2 / 2) ^ 2 = (√2 / 2) ^ 2 by rw [sqrt2_half_sq]; norm_num]
    exact Real.sqrt_sq sqrt2_half_pos.le
  have hlog : Real.log (√2 / 2) = -(Real.log 2 / 2) := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt (by norm_num)]
    ring
  rw [hr, fd, hlog]
  have hnum : 4 * (√2 / 2 + √2 / 2) * (√2 / 2 + √2 / 2 - 1) +
      2 * (1 + √2 / 2) * (1 - √2 / 2) * -(Real.log 2 / 2) +
      2 * (1 - √2 / 2) * (1 + √2 / 2) * -(Real.log 2 / 2) = 8 - 4 * √2 - Real.log 2 := by
    linear_combination (4 + Real.log 2 / 2) * hs2
  have hden : (√2 / 2 + √2 / 2 - 1) * (√2 / 2 + √2 / 2 + 3) = 2 * √2 - 1 := by
    linear_combination hs2
  rw [hnum, hden]

private lemma fd_core {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1)
    (hba : b ≤ a) :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ≤ fd a b ∧
      (fd a b = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) → a = b) := by
  have hb2 : b ≤ √2 / 2 := by
    nlinarith [sqrt2_half_sq, sqrt2_half_pos]
  have ha_eq : a = √(1 - b ^ 2) := by
    rw [show 1 - b ^ 2 = a ^ 2 by linarith, Real.sqrt_sq ha.le]
  rw [ha_eq, ← fd_sym_value]
  rcases hb2.lt_or_eq with hlt | heq
  · have h := psi_strictAntiOn ⟨hb, hb2⟩ ⟨sqrt2_half_pos, le_rfl⟩ hlt
    simp only at h
    exact ⟨h.le, fun he => absurd he h.ne'⟩
  · subst heq
    refine ⟨le_rfl, fun _ => ?_⟩
    rw [show 1 - (√2 / 2) ^ 2 = (√2 / 2) ^ 2 by rw [sqrt2_half_sq]; norm_num]
    exact Real.sqrt_sq sqrt2_half_pos.le

/-- **The four-piece density on the quarter circle**: for `a, b > 0`, `a² + b² = 1`,
`δ(a, b) ≥ (8 - 4√2 - log 2)/(2√2 - 1)`, with equality only at `a = b`. -/
theorem ra_four_density {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1) :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ≤
        (4 * (a + b) * (a + b - 1) + 2 * (1 + a) * (1 - b) * Real.log a +
          2 * (1 - a) * (1 + b) * Real.log b) / ((a + b - 1) * (a + b + 3)) ∧
      ((4 * (a + b) * (a + b - 1) + 2 * (1 + a) * (1 - b) * Real.log a +
          2 * (1 - a) * (1 + b) * Real.log b) / ((a + b - 1) * (a + b + 3)) =
        (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) → a = b) := by
  change _ ≤ fd a b ∧ (fd a b = _ → a = b)
  rcases le_total b a with hba | hab'
  · exact fd_core ha hb hab hba
  · rw [fd_symm]
    obtain ⟨h1, h2⟩ := fd_core hb ha (by linarith) hab'
    exact ⟨h1, fun h => (h2 h).symm⟩

end SmoothedOctagon
