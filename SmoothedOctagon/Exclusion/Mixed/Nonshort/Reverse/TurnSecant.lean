module

public import SmoothedOctagon.Exclusion.Mixed.Hand.Basic

/-!
# Case M2 by hand: comparisons of turn secants

The secant `Sec(A, B, P)` (`m2Sec`) is the average of `g_B(s) = m2g B s` over `[A, P]`; with the
antiderivative `G_B(s) = s - B log(B + s) - B²/(B + s)` (`nhG`) every comparison of secants used
for the reverse order bound reduces to a monotonicity statement.

## Main API

* `nhG`, `nh_hasDerivAt_G`, `nh_sec_eq_G`; `nh_m2g_sub` (`g_B(s₁) - g_B(s₂)`).
* `nh_G_sub_lt`, `nh_G_sub_gt`: an average of `g_B` below/above a bound of the integrand.
* `nh_sec_swap`: **the swapped secant order** `Sec(a, c, d) < Sec(a, d, c)` for `0 < a ≤ c < d`.
* `nh_sec_start`: `z ↦ Sec(z, d, c)` is strictly decreasing on `(0, c]` for `c ≤ d`.
* `nh_m2F_eq_sec`: `F_{P/(P+C)}(q) = Sec((P + C)/q - P, P, C)`.
* `nh_sec_le_of_rev`: `Sec(A, r, d) ≤ g_r(A)`, `a ≤ A ≤ r` give `Sec(A, r, d) ≤ Sec(a, r, d)`.
* `nh_sec_zero_gt`: `Sec(0, c, d) > v` when `v = Sec(a, c, d) ≤ g_c(a)`, `0 < a < c`, `a < d`.
* `nh_secN_eq`: the normalized secant is `Sec(t, 1 - t, t + x)`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The antiderivative `G_B(s) = s - B log(B + s) - B²/(B + s)` of `g_B(s) = m2g B s`. -/
noncomputable def nhG (B s : ℝ) : ℝ := s - B * Real.log (B + s) - B ^ 2 / (B + s)

theorem nh_hasDerivAt_G {B s : ℝ} (h : 0 < B + s) : HasDerivAt (nhG B) (m2g B s) s := by
  have h1 : HasDerivAt (fun z : ℝ => B + z) 1 s := by simpa using (hasDerivAt_id s).const_add B
  have := ((hasDerivAt_id' s).sub ((h1.log h.ne').const_mul B)).sub
    ((hasDerivAt_const s (B ^ 2)).div h1 h.ne')
  refine this.congr_deriv ?_
  unfold m2g
  field_simp
  ring

theorem nh_sec_eq_G {A B P : ℝ} (hA : 0 ≤ A) (hB : 0 < B) (hP : 0 ≤ P) (h : A ≠ P) :
    m2Sec A B P = (nhG B P - nhG B A) / (P - A) := by
  rw [m2Sec_of_ne h]
  unfold nhG
  have hAB : 0 < A + B := by linarith
  have hPB : 0 < P + B := by linarith
  have hPA : P - A ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  rw [Real.log_div hPB.ne' hAB.ne', add_comm B P, add_comm B A]
  field_simp
  ring

/-- `g_B(s₁) - g_B(s₂) = B(s₂ - s₁)(B² - s₁s₂)/((B + s₁)²(B + s₂)²)`. -/
theorem nh_m2g_sub {B s1 s2 : ℝ} (h1 : 0 < B + s1) (h2 : 0 < B + s2) :
    m2g B s1 - m2g B s2 = B * (s2 - s1) * (B ^ 2 - s1 * s2) / ((B + s1) ^ 2 * (B + s2) ^ 2) := by
  unfold m2g
  field_simp
  ring

/-- If `g_B < c` on `(z, P)`, then `G_B(P) - G_B(z) < c(P - z)`. -/
theorem nh_G_sub_lt {B z P c : ℝ} (hz : 0 < B + z) (hzP : z < P)
    (hg : ∀ s, z < s → s < P → m2g B s < c) : nhG B P - nhG B z < c * (P - z) := by
  have hanti : StrictAntiOn (fun s => nhG B s - c * s) (Set.Icc z P) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc z P)
    · intro s hs
      have : 0 < B + s := by linarith [hs.1]
      exact ((nh_hasDerivAt_G this).sub ((hasDerivAt_id' s).const_mul c)).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have : 0 < B + s := by linarith [hs.1]
      have hd : HasDerivAt (fun s => nhG B s - c * s) (m2g B s - c * 1) s :=
        (nh_hasDerivAt_G this).sub ((hasDerivAt_id' s).const_mul c)
      rw [hd.deriv]
      have := hg s hs.1 hs.2
      simp only [mul_one]
      linarith
  have := hanti (Set.left_mem_Icc.2 hzP.le) (Set.right_mem_Icc.2 hzP.le) hzP
  simp only at this
  linarith

/-- If `g_B > c` on `(z, P)`, then `G_B(P) - G_B(z) > c(P - z)`. -/
theorem nh_G_sub_gt {B z P c : ℝ} (hz : 0 < B + z) (hzP : z < P)
    (hg : ∀ s, z < s → s < P → c < m2g B s) : c * (P - z) < nhG B P - nhG B z := by
  have hmono : StrictMonoOn (fun s => nhG B s - c * s) (Set.Icc z P) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc z P)
    · intro s hs
      have : 0 < B + s := by linarith [hs.1]
      exact ((nh_hasDerivAt_G this).sub ((hasDerivAt_id' s).const_mul c)).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have : 0 < B + s := by linarith [hs.1]
      have hd : HasDerivAt (fun s => nhG B s - c * s) (m2g B s - c * 1) s :=
        (nh_hasDerivAt_G this).sub ((hasDerivAt_id' s).const_mul c)
      rw [hd.deriv]
      have := hg s hs.1 hs.2
      simp only [mul_one]
      linarith
  have := hmono (Set.left_mem_Icc.2 hzP.le) (Set.right_mem_Icc.2 hzP.le) hzP
  simp only at this
  linarith

/-- The pointwise comparison behind the swapped order: `g_d(α) > g_c(β)` when `dβ > cα` and
`αβ < cd`. -/
theorem nh_m2g_cross {c d α β : ℝ} (hc : 0 < c) (hd : 0 < d) (hα : 0 < α) (hβ : 0 < β)
    (h1 : c * α < d * β) (h2 : α * β < c * d) : m2g c β < m2g d α := by
  have e : m2g d α - m2g c β = (d * β - c * α) * (c * d - α * β) / ((α + d) ^ 2 * (β + c) ^ 2) := by
    unfold m2g; field_simp; ring
  have : 0 < (d * β - c * α) * (c * d - α * β) / ((α + d) ^ 2 * (β + c) ^ 2) := by
    apply div_pos (mul_pos (by linarith) (by linarith)); positivity
  linarith

/-- **The swapped secant order**: `Sec(a, c, d) < Sec(a, d, c)` for `0 < a ≤ c < d`. -/
theorem nh_sec_swap {a c d : ℝ} (ha : 0 < a) (hac : a ≤ c) (hcd : c < d) :
    m2Sec a c d < m2Sec a d c := by
  have hc : 0 < c := by linarith
  have hd : 0 < d := by linarith
  rcases eq_or_lt_of_le hac with h | h
  · -- `a = c`: an average of the increasing `g_c` over `[c, d]` is below `g_c(d)`
    subst h
    rw [m2Sec_self, nh_sec_eq_G ha.le ha hd.le hcd.ne]
    have := nh_G_sub_lt (B := a) (z := a) (P := d) (c := m2g a d) (by linarith) hcd
      (fun s hs1 hs2 => by
        have := nh_m2g_sub (B := a) (s1 := s) (s2 := d) (by linarith) (by linarith)
        have has : 0 < a + s := by linarith
        have : a * (d - s) * (a ^ 2 - s * d) / ((a + s) ^ 2 * (a + d) ^ 2) < 0 := by
          apply div_neg_of_neg_of_pos _ (by positivity)
          apply mul_neg_of_pos_of_neg (mul_pos ha (by linarith))
          nlinarith
        linarith)
    rw [div_lt_iff₀ (by linarith)]
    linarith
  · -- `a < c`: the interpolation `H(θ)` increases on `[0, 1]`
    have hca : 0 < c - a := by linarith
    have hda : 0 < d - a := by linarith
    have hderiv : ∀ θ, 0 ≤ θ → HasDerivAt (fun θ => (nhG d (a + θ * (c - a)) - nhG d a) / (c - a) -
        (nhG c (a + θ * (d - a)) - nhG c a) / (d - a))
        (m2g d (a + θ * (c - a)) - m2g c (a + θ * (d - a))) θ := by
      intro θ hθ
      have hα : 0 < d + (a + θ * (c - a)) := by nlinarith
      have hβ : 0 < c + (a + θ * (d - a)) := by nlinarith
      have h1 : HasDerivAt (fun θ : ℝ => a + θ * (c - a)) (c - a) θ := by
        simpa using ((hasDerivAt_id θ).mul_const (c - a)).const_add a
      have h2 : HasDerivAt (fun θ : ℝ => a + θ * (d - a)) (d - a) θ := by
        simpa using ((hasDerivAt_id θ).mul_const (d - a)).const_add a
      have k1 := ((nh_hasDerivAt_G hα).comp θ h1).sub_const (nhG d a) |>.div_const (c - a)
      have k2 := ((nh_hasDerivAt_G hβ).comp θ h2).sub_const (nhG c a) |>.div_const (d - a)
      exact (k1.sub k2).congr_deriv (by field_simp)
    have hmono : StrictMonoOn (fun θ => (nhG d (a + θ * (c - a)) - nhG d a) / (c - a) -
        (nhG c (a + θ * (d - a)) - nhG c a) / (d - a)) (Set.Icc 0 1) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      · exact fun θ hθ => (hderiv θ hθ.1).continuousAt.continuousWithinAt
      · intro θ hθ
        rw [interior_Icc] at hθ
        rw [(hderiv θ hθ.1.le).deriv]
        have hθ1 : θ < 1 := hθ.2
        have hθ0 : 0 < θ := hθ.1
        have := nh_m2g_cross (c := c) (d := d) (α := a + θ * (c - a)) (β := a + θ * (d - a))
          hc hd (by nlinarith) (by nlinarith) (by
            have e : d * (a + θ * (d - a)) - c * (a + θ * (c - a)) =
                (d - c) * (a + θ * (d + c - a)) := by ring
            have : 0 < (d - c) * (a + θ * (d + c - a)) :=
              mul_pos (by linarith) (by nlinarith)
            linarith) (by
            have h1 : a + θ * (c - a) ≤ c := by nlinarith
            have h2 : a + θ * (d - a) < d := by nlinarith
            have h3 : 0 < a + θ * (c - a) := by nlinarith
            calc (a + θ * (c - a)) * (a + θ * (d - a)) < (a + θ * (c - a)) * d :=
                  mul_lt_mul_of_pos_left h2 h3
              _ ≤ c * d := mul_le_mul_of_nonneg_right h1 hd.le)
        linarith
    have := hmono (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_lt_one
    simp only [zero_mul, add_zero, sub_self, zero_div, one_mul, add_sub_cancel] at this
    rw [nh_sec_eq_G ha.le hc hd.le (ne_of_lt (lt_trans h hcd)),
      nh_sec_eq_G ha.le hd hc.le (ne_of_lt h)]
    linarith

/-- **Starting-point monotonicity**: for
`0 < z₁ < z₂ ≤ c ≤ d`, `Sec(z₂, d, c) < Sec(z₁, d, c)`. -/
theorem nh_sec_start {z1 z2 c d : ℝ} (hz1 : 0 < z1) (h12 : z1 < z2) (h2c : z2 ≤ c) (hcd : c ≤ d) :
    m2Sec z2 d c < m2Sec z1 d c := by
  have hd : 0 < d := by linarith
  have hc : 0 < c := by linarith
  -- `g_d` is decreasing on `(0, d]`
  have hdec : ∀ s1 s2, 0 < s1 → s1 < s2 → s2 ≤ d → m2g d s2 < m2g d s1 := by
    intro s1 s2 h1 h2 h3
    have := nh_m2g_sub (B := d) (s1 := s1) (s2 := s2) (by linarith) (by linarith)
    have hds1 : 0 < d + s1 := by linarith
    have hds2 : 0 < d + s2 := by linarith
    have : 0 < d * (s2 - s1) * (d ^ 2 - s1 * s2) / ((d + s1) ^ 2 * (d + s2) ^ 2) := by
      apply div_pos _ (by positivity)
      apply mul_pos (mul_pos hd (by linarith))
      nlinarith
    linarith
  -- average over `[z₁, z₂]` exceeds `g_d(z₂)`
  have hleft : m2g d z2 * (z2 - z1) < nhG d z2 - nhG d z1 :=
    nh_G_sub_gt (by linarith) h12 (fun s hs1 hs2 => hdec s z2 (by linarith) hs2 (by linarith))
  rw [nh_sec_eq_G hz1.le hd hc.le (by linarith : z1 ≠ c)]
  rcases eq_or_lt_of_le h2c with h | h
  · subst h
    rw [m2Sec_self, m2g_comm, lt_div_iff₀ (by linarith)]
    linarith
  · rw [nh_sec_eq_G (by linarith) hd hc.le h.ne]
    have hright : nhG d c - nhG d z2 < m2g d z2 * (c - z2) :=
      nh_G_sub_lt (by linarith) h (fun s hs1 hs2 => hdec z2 s (by linarith) hs1 (by linarith))
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    have e1 : (nhG d c - nhG d z1) = (nhG d c - nhG d z2) + (nhG d z2 - nhG d z1) := by ring
    rw [e1]
    nlinarith

/-- **The missing-control floor as a secant**:
`F_{P/(P+C)}(q) = Sec((P + C)/q - P, P, C)`. -/
theorem nh_m2F_eq_sec {P C q : ℝ} (hP : 0 < P) (hC : 0 < C) (hq : 1 < q) :
    m2F (P / (P + C)) q = m2Sec ((P + C) / q - P) P C := by
  have hq0 : 0 < q := by linarith
  have hA : (P + C) / q - P ≠ C := by
    intro h
    have : (P + C) / q = P + C := by linarith
    rw [div_eq_iff hq0.ne'] at this
    nlinarith
  rw [m2F_of_ne hq.ne', m2Sec_of_ne hA]
  have e1 : (C + P) / ((P + C) / q - P + P) = q := by
    rw [sub_add_cancel, add_comm C P]; field_simp
  rw [e1]
  have hCA : C - ((P + C) / q - P) = (P + C) * (q - 1) / q := by field_simp; ring
  rw [hCA]
  have hq1 : q - 1 ≠ 0 := by linarith
  have hPC : P + C ≠ 0 := by linarith
  rw [show (P + C) / q - P + P = (P + C) / q by ring]
  field_simp
  ring

/-- The reverse successor's secant comparison: if
`Sec(A, r, d) ≤ g_r(A)` with `0 < a ≤ A ≤ r`, `A < d`, then `Sec(A, r, d) ≤ Sec(a, r, d)`. -/
theorem nh_sec_le_of_rev {a A r d : ℝ} (ha : 0 < a) (haA : a ≤ A) (hAr : A ≤ r) (hAd : A < d)
    (hle : m2Sec A r d ≤ m2g r A) : m2Sec A r d ≤ m2Sec a r d := by
  rcases eq_or_lt_of_le haA with h | h
  · rw [h]
  have hr : 0 < r := by linarith
  have hd : 0 < d := by linarith
  have hgt : m2g r A * (A - a) < nhG r A - nhG r a := by
    apply nh_G_sub_gt (by linarith) h
    intro s hs1 hs2
    rw [m2g_comm r A, m2g_comm r s]
    have := nh_m2g_sub (B := r) (s1 := s) (s2 := A) (by linarith) (by linarith)
    rw [m2g_comm s r, m2g_comm A r] at *
    have hrs : 0 < r + s := by linarith
    have hrA : 0 < r + A := by linarith
    have : 0 < r * (A - s) * (r ^ 2 - s * A) / ((r + s) ^ 2 * (r + A) ^ 2) := by
      apply div_pos _ (by positivity)
      apply mul_pos (mul_pos hr (by linarith))
      nlinarith
    linarith
  rw [nh_sec_eq_G (by linarith) hr hd.le hAd.ne] at hle ⊢
  rw [nh_sec_eq_G ha.le hr hd.le (by linarith : a ≠ d)]
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hle' : nhG r d - nhG r A ≤ m2g r A * (d - A) := by
    rwa [div_le_iff₀ (by linarith)] at hle
  have e1 : nhG r d - nhG r a = (nhG r d - nhG r A) + (nhG r A - nhG r a) := by ring
  rw [e1]
  have : (nhG r d - nhG r A) / (d - A) * (A - a) ≤ m2g r A * (A - a) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    rwa [div_le_iff₀ (by linarith)]
  have e2 : (nhG r d - nhG r A) * (d - a) =
      (nhG r d - nhG r A) * (d - A) + (nhG r d - nhG r A) / (d - A) * (A - a) * (d - A) := by
    field_simp; ring
  nlinarith

/-- `Sec(0, c, d) > v` when `v = Sec(a, c, d) ≤ g_c(a)`, `0 < a < c`, `a < d`: the average of
`g_c` over `[0, a]` exceeds `g_c(a) ≥ v`. -/
theorem nh_sec_zero_gt {a c d : ℝ} (ha : 0 < a) (hac : a < c) (had : a < d)
    (hv : m2Sec a c d ≤ m2g a c) : m2Sec a c d < m2Sec 0 c d := by
  have hc : 0 < c := by linarith
  have hd : 0 < d := by linarith
  have hgt : m2g c a * (a - 0) < nhG c a - nhG c 0 := by
    apply nh_G_sub_gt (by linarith) ha
    intro s hs1 hs2
    have := nh_m2g_sub (B := c) (s1 := s) (s2 := a) (by linarith) (by linarith)
    have hcs : 0 < c + s := by linarith
    have : 0 < c * (a - s) * (c ^ 2 - s * a) / ((c + s) ^ 2 * (c + a) ^ 2) := by
      apply div_pos _ (by positivity)
      apply mul_pos (mul_pos hc (by linarith))
      nlinarith
    linarith
  rw [m2g_comm] at hv
  rw [nh_sec_eq_G ha.le hc hd.le had.ne] at hv ⊢
  rw [nh_sec_eq_G le_rfl hc hd.le (ne_of_lt hd), sub_zero]
  rw [div_lt_div_iff₀ (by linarith) hd]
  have hv' : nhG c d - nhG c a ≤ m2g c a * (d - a) := by
    rwa [div_le_iff₀ (by linarith)] at hv
  have e1 : nhG c d - nhG c 0 = (nhG c d - nhG c a) + (nhG c a - nhG c 0) := by ring
  rw [e1]
  have e2 : (nhG c d - nhG c a) * d = (nhG c d - nhG c a) * (d - a) + (nhG c d - nhG c a) * a := by
    ring
  have h3 : (nhG c d - nhG c a) * a ≤ m2g c a * (d - a) * a := mul_le_mul_of_nonneg_right hv' ha.le
  nlinarith

/-- The normalized incoming secant is `Sec(t, 1 - t, t + x)`. -/
theorem nh_secN_eq {t x : ℝ} (hx : 0 < x) : nhSecN t x = m2Sec t (1 - t) (t + x) := by
  rw [m2Sec_of_ne (by linarith : t ≠ t + x)]
  unfold nhSecN
  rw [show t + (1 - t) = 1 by ring, show t + x + (1 - t) = 1 + x by ring,
    show t + x - t = x by ring, div_one]
  have h1 : 1 + x ≠ 0 := by linarith
  field_simp

end SmoothedOctagon
