module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.Order
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Point

/-!
# Case M2, smaller-short side: the secant facts of a short bridge

The regular form of the secant, the bridge order `C ≤ B` and the smaller-turn norm cap
`u ≤ 13/16` of a short bridge.

## Main API

* `ss_sec_logDiv`: the regular form `Sec(A, B, P) = 1 + c²/q - c·logDiv(q)`, `q = (P + B)/(A + B)`,
  `c = B/(A + B)`, of the cover's `u` and `u_a`.
* `ss_bridge_order`: `C ≤ B` for a short bridge with equal secants at a global minimum.
* `ss_u_le`: `u ≤ V(x) ≤ 13/16`.
* `ss_m2U_anti`: `U(s) = 1 - s + s²` decreases on `[0, 1/2]`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmallerShort

/-- **The regular form of the secant**: `Sec(A, B, P) = 1 + c²/q - c·logDiv(q)` with
`q = (P + B)/(A + B)`, `c = B/(A + B)`. -/
theorem ss_sec_logDiv {A B P : ℝ} (hA : 0 < A) (hB : 0 < B) (hP : 0 < P) :
    m2Sec A B P = 1 + (B / (A + B)) ^ 2 / ((P + B) / (A + B)) -
      B / (A + B) * logDiv ((P + B) / (A + B)) := by
  have hAB : 0 < A + B := by positivity
  by_cases h : A = P
  · subst h
    rw [m2Sec_self, div_self hAB.ne']
    simp only [logDiv, ↓reduceIte]
    unfold m2g
    field_simp
    ring
  have hq : (P + B) / (A + B) ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hAB.ne']
    intro e; exact h (by linarith)
  rw [m2Sec_of_ne h]
  simp only [logDiv, hq, ↓reduceIte]
  have hPA : P - A ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have e : (P + B) / (A + B) - 1 = (P - A) / (A + B) := by field_simp; ring
  rw [e]
  have : P + B ≠ 0 := by positivity
  field_simp

/-- **The bridge order**: at a short bridge `(a, C, B, A)` with `a ≤ A < B`, equal turn secants
`u = Sec(a, C, B) = Sec(C, B, A)` and the reverse inequality `u ≤ g(B, A)` at `B → A`, the far turn
is not smaller: `C ≤ B`. Otherwise `Sec(a, B, C) < Sec(a, C, B) = u` (`ss_sec_cross`), while
adding `[a, A]`, where `g_B ≥ g_B(A) ≥ u`, to `Sec(A, B, C) = u` gives `Sec(a, B, C) ≥ u`. -/
theorem ss_bridge_order {a A B C u : ℝ} (ha : 0 < a) (haA : a ≤ A) (hAB : A < B)
    (hu1 : u = m2Sec a C B) (hu2 : u = m2Sec C B A) (hle : u ≤ m2g B A) :
    C ≤ B := by
  by_contra hBC
  push Not at hBC
  have hA : 0 < A := by linarith
  have hB : 0 < B := by linarith
  have hC : 0 < C := by linarith
  have hadd := ss_sec_add ha hB hA hC
  have h1 : u ≤ m2Sec a B A := by
    have := ss_sec_ge_right (B := B) ha haA hAB.le
    rw [← ss_m2g_eq (by linarith), m2g_comm] at this
    linarith
  rw [m2Sec_comm C B A] at hu2
  have h2 : (C - a) * u ≤ (C - a) * m2Sec a B C := by
    rw [hadd, ← hu2]
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ A - a)
    linarith
  have h3 : u ≤ m2Sec a B C := le_of_mul_le_mul_left h2 (by linarith)
  have h4 := ss_sec_cross ha (by linarith) hBC
  linarith

/-- **The smaller-turn norm cap**: for `a < C ≤ B`, `u = Sec(a, C, B)` and the forward
inequality `g(C, B) ≤ u`, `u ≤ V ≤ 13/16`, by additivity of the secant integral (removing
`[C, B]`, where `g_C ≤ g_C(B) ≤ u`). -/
theorem ss_u_le {a B C u : ℝ} (ha : 0 < a) (haC : a < C) (hCB : C ≤ B) (hu : u = m2Sec a C B)
    (hge : m2g C B ≤ u) : u ≤ 13 / 16 := by
  have hC : 0 < C := by linarith
  have hB : 0 < B := by linarith
  have hadd := ss_sec_add ha hC hC hB
  have h1 := ss_sec_le_right hC hCB
  rw [← ss_m2g_eq (by linarith), m2g_comm] at h1
  have hV := ss_V_le ha haC
  have h2 : (B - a) * u ≤ (C - a) * m2Sec a C C + (B - C) * u := by
    rw [hu] at hge ⊢
    rw [hadd]
    have := mul_le_mul_of_nonneg_left (h1.trans hge) (by linarith : (0 : ℝ) ≤ B - C)
    linarith
  have h3 : (C - a) * u ≤ (C - a) * m2Sec a C C := by linarith
  have := le_of_mul_le_mul_left h3 (by linarith)
  linarith

/-- **Every secant is at least `3/4`**, since `g_B(t) = 3/4 + (t - B)²/(4(t + B)²)`. -/
theorem ss_sec_ge_34 {A B P : ℝ} (hA : 0 < A) (hB : 0 < B) (hP : 0 < P) : 3 / 4 ≤ m2Sec A B P := by
  have key : ∀ {A P : ℝ}, 0 < A → A < P → 3 / 4 ≤ m2Sec A B P := fun {A P} hA hAP =>
    ss_sec_ge hA hB hAP fun t ht => by
      have ht0 : 0 < t := by linarith [ht.1]
      unfold ss_gB
      rw [show (1 : ℝ) - B * t / (B + t) ^ 2 = 3 / 4 + (t - B) ^ 2 / (4 * (B + t) ^ 2) by
        field_simp; ring]
      have : 0 ≤ (t - B) ^ 2 / (4 * (B + t) ^ 2) := by positivity
      linarith
  rcases lt_trichotomy A P with h | h | h
  · exact key hA h
  · subst h
    rw [m2Sec_self]
    unfold m2g
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (A - B)]
  · rw [m2Sec_comm]; exact key hP h

/-- `U(s) = 1 - s + s²` decreases on `[0, 1/2]`. -/
theorem ss_m2U_anti {s s' : ℝ} (hs : s ≤ s') (hs' : s + s' ≤ 1) : m2U s' ≤ m2U s := by
  unfold m2U
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (by linarith : (0 : ℝ) ≤ 1 - s - s')]

end SmoothedOctagon
