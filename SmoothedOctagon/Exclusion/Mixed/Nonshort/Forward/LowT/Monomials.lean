module

public import SmoothedOctagon.Exclusion.Mixed.PolyDeriv

/-!
# Case M2, forward successor: small tools for the low-`t` large-gap signs

Elementary one-variable tools for the proofs of the low-`t` signs:

* `nlt_pw`: `z^(k+1) ≤ w z^k` on `0 ≤ z ≤ w`, the step of every termwise monomial bound on an
  interval (a negative monomial is absorbed into the next lower power);
* `nlt_lo`, `nlt_hi`: monomial comparisons `aʳ xˢ ≤ tʳ xˢ ≤ bʳ xˢ` on `a ≤ t ≤ b`;
* `nlt_taylor3`: the cubic Taylor lower bound from a lower bound of the third derivative;
* `nlt_unimodal`: if `f'''' ≥ 0` on `[0, Y]`, `f''(0) ≤ 0` and `f'(Y) ≤ 0`, then `f` is at least
  the smaller endpoint value on `[0, Y]`;
* `nlt_poly6_chord`: a sextic with `c₃, c₄, c₅ ≤ 0 ≤ c₆` and `c₂ + 5Y⁴c₆ ≤ 0` lies above its chord
  on `[0, Y]`.

## Main API

* `nlt_pw`, `nlt_lo`, `nlt_hi`, `nlt_taylor3`, `nlt_unimodal`, `nlt_poly6_chord`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `z^(k+1) ≤ w z^k` for `0 ≤ z ≤ w`. -/
theorem nlt_pw {z w : ℝ} (h0 : 0 ≤ z) (h1 : z ≤ w) (k : ℕ) : z ^ (k + 1) ≤ w * z ^ k := by
  rw [pow_succ, mul_comm]; exact mul_le_mul_of_nonneg_right h1 (pow_nonneg h0 k)

/-- Monomial comparison from below: `c xˢ ≤ tʳ xˢ` for `0 ≤ a ≤ t`, `aʳ = c`, `0 ≤ x`. -/
theorem nlt_lo (r s : ℕ) {t x a c : ℝ} (hc : a ^ r = c) (ha : 0 ≤ a) (h : a ≤ t) (hx : 0 ≤ x) :
    c * x ^ s ≤ t ^ r * x ^ s := by
  rw [← hc]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha h r) (pow_nonneg hx s)

/-- Monomial comparison from above: `tʳ xˢ ≤ c xˢ` for `0 ≤ t ≤ b`, `bʳ = c`, `0 ≤ x`. -/
theorem nlt_hi (r s : ℕ) {t x b c : ℝ} (hc : b ^ r = c) (ht : 0 ≤ t) (h : t ≤ b) (hx : 0 ≤ x) :
    t ^ r * x ^ s ≤ c * x ^ s := by
  rw [← hc]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht h r) (pow_nonneg hx s)

/-- **The cubic Taylor lower bound**: if `f''' ≥ c` on `[a, b]`, then for `s ∈ [a, b]`,
`f(s) ≥ f(a) + (s - a)f'(a) + (s - a)²f''(a)/2 + c(s - a)³/6`. -/
theorem nlt_taylor3 {f f1 f2 f3 : ℝ → ℝ} {a b c : ℝ} (hd0 : ∀ s, HasDerivAt f (f1 s) s)
    (hd1 : ∀ s, HasDerivAt f1 (f2 s) s) (hd2 : ∀ s, HasDerivAt f2 (f3 s) s)
    (h3 : ∀ s, a ≤ s → s ≤ b → c ≤ f3 s) {s : ℝ} (has : a ≤ s) (hsb : s ≤ b) :
    f a + (s - a) * f1 a + (s - a) ^ 2 / 2 * f2 a + c * (s - a) ^ 3 / 6 ≤ f s := by
  have g2 : ∀ w, a ≤ w → w ≤ b → f2 a + c * (w - a) ≤ f2 w := by
    intro w h1 h2
    have hd : ∀ v, HasDerivAt (fun v => f2 v - c * (v - a)) (f3 v - c) v := fun v =>
      ((hd2 v).sub (((hasDerivAt_id v).sub_const a).const_mul c)).congr_deriv (by simp)
    have := poly_mono hd (fun v h1 h2 => by linarith [h3 v h1 h2]) le_rfl h1 h2
    simp only [sub_self, mul_zero, sub_zero] at this
    linarith
  have g1 : ∀ w, a ≤ w → w ≤ b → f1 a + (w - a) * f2 a + c * (w - a) ^ 2 / 2 ≤ f1 w := by
    intro w h1 h2
    have hd : ∀ v, HasDerivAt (fun v => f1 v - ((v - a) * f2 a + c * (v - a) ^ 2 / 2))
        (f2 v - (f2 a + c * (v - a))) v := fun v => by
      have e1 := ((hasDerivAt_id v).sub_const a).mul_const (f2 a)
      have e2 := ((((hasDerivAt_id v).sub_const a).pow 2).const_mul c).div_const 2
      exact ((hd1 v).sub (e1.add e2)).congr_deriv (by simp; ring)
    have := poly_mono hd (fun v h1 h2 => by linarith [g2 v h1 h2]) le_rfl h1 h2
    simp only [sub_self, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_div, add_zero, sub_zero] at this
    linarith
  have hd : ∀ v, HasDerivAt
      (fun v => f v - ((v - a) * f1 a + (v - a) ^ 2 / 2 * f2 a + c * (v - a) ^ 3 / 6))
      (f1 v - (f1 a + (v - a) * f2 a + c * (v - a) ^ 2 / 2)) v := fun v => by
    have e1 := ((hasDerivAt_id v).sub_const a).mul_const (f1 a)
    have e2 := ((((hasDerivAt_id v).sub_const a).pow 2).div_const 2).mul_const (f2 a)
    have e3 := ((((hasDerivAt_id v).sub_const a).pow 3).const_mul c).div_const 6
    exact ((hd0 v).sub ((e1.add e2).add e3)).congr_deriv (by simp; ring)
  have := poly_mono hd (fun v h1 h2 => by linarith [g1 v h1 h2]) le_rfl has hsb
  simp only [sub_self, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, mul_zero, add_zero, sub_zero] at this
  linarith

/-- **A unimodal bound**: if `f'''' ≥ 0` on `[0, Y]`,
`f''(0) ≤ 0` and `f'(Y) ≤ 0`, then `f'` changes sign at most once (from `+` to `-`) on `[0, Y]`,
so `f(y) ≥ min (f 0) (f Y)` there. -/
theorem nlt_unimodal {f f1 f2 f3 f4 : ℝ → ℝ} {Y : ℝ} (hd0 : ∀ s, HasDerivAt f (f1 s) s)
    (hd1 : ∀ s, HasDerivAt f1 (f2 s) s) (hd2 : ∀ s, HasDerivAt f2 (f3 s) s)
    (hd3 : ∀ s, HasDerivAt f3 (f4 s) s) (h4 : ∀ s, 0 ≤ s → s ≤ Y → 0 ≤ f4 s)
    (h20 : f2 0 ≤ 0) (h1Y : f1 Y ≤ 0) {y : ℝ} (hy0 : 0 ≤ y) (hyY : y ≤ Y) :
    min (f 0) (f Y) ≤ f y := by
  -- `f'''` increases on `[0, Y]`
  have m3 : ∀ u v, 0 ≤ u → u ≤ v → v ≤ Y → f3 u ≤ f3 v :=
    fun u v hu huv hv => poly_mono hd3 h4 hu huv hv
  -- (A) once `f'' > 0`, it stays positive (`f''` is convex with `f''(0) ≤ 0`)
  have pA : ∀ s1 s2, 0 ≤ s1 → s1 ≤ s2 → s2 ≤ Y → 0 < f2 s1 → 0 < f2 s2 := by
    intro s1 s2 h1 h12 h2 hp
    have hd : ∀ v, HasDerivAt (fun v => f2 v - v * f3 s1) (f3 v - f3 s1) v := fun v =>
      ((hd2 v).sub ((hasDerivAt_id v).mul_const (f3 s1))).congr_deriv (by simp)
    have a1 := poly_anti hd (a := 0) (b := s1)
      (fun v hv1 hv2 => by linarith [m3 v s1 hv1 hv2 (h12.trans h2)]) le_rfl h1 le_rfl
    simp only [zero_mul, sub_zero] at a1
    have hs1 : 0 < s1 * f3 s1 := by linarith
    have hf3 : 0 < f3 s1 := by
      rcases eq_or_lt_of_le h1 with h | h
      · rw [← h] at hs1; simp at hs1
      · exact pos_of_mul_pos_right hs1 h.le
    have := poly_mono hd2 (a := s1) (b := Y)
      (fun v hv1 hv2 => le_trans hf3.le (m3 s1 v h1 hv1 hv2)) le_rfl h12 h2
    linarith
  -- (B) once `f' < 0`, it stays nonpositive
  have pB : ∀ a b, 0 ≤ a → a ≤ b → b ≤ Y → f1 a < 0 → f1 b ≤ 0 := by
    intro a b ha hab hb hneg
    by_contra hpos
    push Not at hpos
    have : ∃ s, a ≤ s ∧ s ≤ b ∧ 0 < f2 s := by
      by_contra hno
      push Not at hno
      have := poly_anti hd1 (a := a) (b := b) (fun v h1 h2 => hno v h1 h2) le_rfl hab le_rfl
      linarith
    obtain ⟨s, hs1, hs2, hs⟩ := this
    have := poly_mono hd1 (a := s) (b := Y)
      (fun v h1 h2 => (pA s v (ha.trans hs1) h1 h2 hs).le) hs2 (le_refl b |>.trans hb) le_rfl
    linarith
  by_cases hA : ∃ a, 0 ≤ a ∧ a ≤ y ∧ f1 a < 0
  · obtain ⟨a, ha0, hay, ha⟩ := hA
    have := poly_anti hd0 (a := y) (b := Y)
      (fun v h1 h2 => pB a v ha0 (hay.trans h1) h2 ha) le_rfl hyY le_rfl
    exact (min_le_right _ _).trans this
  · push Not at hA
    have := poly_mono hd0 (a := 0) (b := y) (fun v h1 h2 => hA v h1 h2) le_rfl hy0 le_rfl
    exact (min_le_left _ _).trans this

/-- **A sextic above its chord**: with `c₃, c₄, c₅ ≤ 0 ≤ c₆` and `c₂ + 5Y⁴c₆ ≤ 0`, the sextic
`P(w) = ∑ cᵢwⁱ` satisfies `Y P(y) ≥ (Y - y)P(0) + yP(Y)` on `[0, Y]`. -/
theorem nlt_poly6_chord {c0 c1 c2 c3 c4 c5 c6 Y y : ℝ} (hy0 : 0 ≤ y) (hyY : y ≤ Y)
    (h3 : c3 ≤ 0) (h4 : c4 ≤ 0) (h5 : c5 ≤ 0) (h6 : 0 ≤ c6) (h2 : c2 + 5 * Y ^ 4 * c6 ≤ 0) :
    (Y - y) * c0 + y * (c0 + c1 * Y + c2 * Y ^ 2 + c3 * Y ^ 3 + c4 * Y ^ 4 + c5 * Y ^ 5
      + c6 * Y ^ 6) ≤
      Y * (c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4 + c5 * y ^ 5 + c6 * y ^ 6) := by
  have hY : 0 ≤ Y := hy0.trans hyY
  have e : Y * (c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4 + c5 * y ^ 5 + c6 * y ^ 6) -
      ((Y - y) * c0 + y * (c0 + c1 * Y + c2 * Y ^ 2 + c3 * Y ^ 3 + c4 * Y ^ 4 + c5 * Y ^ 5
        + c6 * Y ^ 6)) =
      -(y * Y * (Y - y)) * (c2 + c3 * (y + Y) + c4 * (y ^ 2 + y * Y + Y ^ 2)
        + c5 * (y ^ 3 + y ^ 2 * Y + y * Y ^ 2 + Y ^ 3)
        + c6 * (y ^ 4 + y ^ 3 * Y + y ^ 2 * Y ^ 2 + y * Y ^ 3 + Y ^ 4)) := by ring
  have k1 : 0 ≤ y * Y * (Y - y) := mul_nonneg (mul_nonneg hy0 hY) (by linarith)
  have hp : ∀ n : ℕ, y ^ n ≤ Y ^ n := fun n => pow_le_pow_left₀ hy0 hyY n
  have a3 : c3 * (y + Y) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h3 (by positivity)
  have a4 : c4 * (y ^ 2 + y * Y + Y ^ 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h4 (by positivity)
  have a5 : c5 * (y ^ 3 + y ^ 2 * Y + y * Y ^ 2 + Y ^ 3) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg h5 (by positivity)
  have b4 : y ^ 4 + y ^ 3 * Y + y ^ 2 * Y ^ 2 + y * Y ^ 3 + Y ^ 4 ≤ 5 * Y ^ 4 := by
    have := hp 4; have := hp 3; have := hp 2; have := hp 1
    have e1 : y ^ 3 * Y ≤ Y ^ 3 * Y := mul_le_mul_of_nonneg_right (hp 3) hY
    have e2 : y ^ 2 * Y ^ 2 ≤ Y ^ 2 * Y ^ 2 := mul_le_mul_of_nonneg_right (hp 2) (by positivity)
    have e3 : y * Y ^ 3 ≤ Y * Y ^ 3 := mul_le_mul_of_nonneg_right hyY (by positivity)
    nlinarith
  have a6 : c6 * (y ^ 4 + y ^ 3 * Y + y ^ 2 * Y ^ 2 + y * Y ^ 3 + Y ^ 4) ≤ c6 * (5 * Y ^ 4) :=
    mul_le_mul_of_nonneg_left b4 h6
  have hQ : c2 + c3 * (y + Y) + c4 * (y ^ 2 + y * Y + Y ^ 2)
      + c5 * (y ^ 3 + y ^ 2 * Y + y * Y ^ 2 + Y ^ 3)
      + c6 * (y ^ 4 + y ^ 3 * Y + y ^ 2 * Y ^ 2 + y * Y ^ 3 + Y ^ 4) ≤ 0 := by nlinarith
  have := mul_nonneg k1 (by linarith : (0 : ℝ) ≤ -(c2 + c3 * (y + Y) + c4 * (y ^ 2 + y * Y + Y ^ 2)
      + c5 * (y ^ 3 + y ^ 2 * Y + y * Y ^ 2 + Y ^ 3)
      + c6 * (y ^ 4 + y ^ 3 * Y + y ^ 2 * Y ^ 2 + y * Y ^ 3 + Y ^ 4)))
  nlinarith

end SmoothedOctagon
