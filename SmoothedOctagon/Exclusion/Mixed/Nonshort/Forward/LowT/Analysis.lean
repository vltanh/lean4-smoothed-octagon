module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import SmoothedOctagon.Exclusion.Mixed.PolyDeriv

/-!
# Endpoint estimates from the curvature of a derivative

A concave derivative that starts nonnegative allows a maximum inside an
interval, but its function attains a minimum at an endpoint. Reflection
gives the corresponding statement for a convex derivative that ends nonpositive.
-/

@[expose] public section

namespace SmoothedOctagon.LowT

/-- A concave derivative that starts nonnegative permits an interior maximum,
but no interior minimum below both endpoint values. -/
theorem polynomial_floor_of_concave_derivative {p : Polynomial ℝ} {a b m x : ℝ}
    (hx0 : a ≤ x) (hx1 : x ≤ b)
    (h3 : ∀ s, a ≤ s → s ≤ b → p.derivative.derivative.derivative.eval s ≤ 0)
    (hda : 0 ≤ p.derivative.eval a) (ha : m ≤ p.eval a) (hb : m ≤ p.eval b) :
    m ≤ p.eval x := by
  have anti2 {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b) :
      p.derivative.derivative.eval t ≤ p.derivative.derivative.eval s :=
    poly_anti (fun v => p.derivative.derivative.hasDerivAt v) h3 hs hst ht
  have stays {s t : ℝ} (hs : a ≤ s) (hst : s ≤ t) (ht : t ≤ b)
      (hneg : p.derivative.eval s < 0) : p.derivative.eval t ≤ 0 := by
    have sd : p.derivative.derivative.eval s < 0 := by
      by_contra hc
      have hp : 0 ≤ p.derivative.derivative.eval s := le_of_not_gt hc
      have hm := poly_mono (fun v => p.derivative.hasDerivAt v) (a := a) (b := s)
        (fun v hv0 hvs => hp.trans (anti2 hv0 hvs (hst.trans ht))) le_rfl hs le_rfl
      linarith only [hm, hda, hneg]
    have hm := poly_anti (fun v => p.derivative.hasDerivAt v) (a := s) (b := t)
      (fun v hsv hvt => (anti2 hs hsv (hvt.trans ht)).trans sd.le) le_rfl hst le_rfl
    exact hm.trans hneg.le
  by_cases hc : ∃ s, a ≤ s ∧ s ≤ x ∧ p.derivative.eval s < 0
  · obtain ⟨s, hs, hsx, hneg⟩ := hc
    have hm := poly_anti (fun v => p.hasDerivAt v) (a := x) (b := b)
      (fun v hxv hvb => stays hs (hsx.trans hxv) hvb hneg) le_rfl hx1 le_rfl
    exact hb.trans hm
  · push Not at hc
    have hm := poly_mono (fun v => p.hasDerivAt v) (a := a) (b := x)
      (fun v hav hvx => hc v hav hvx) le_rfl hx0 le_rfl
    exact ha.trans hm

/-- The reflected endpoint estimate for a convex derivative. -/
theorem polynomial_floor_of_convex_derivative {p : Polynomial ℝ} {a b m x : ℝ}
    (hx0 : a ≤ x) (hx1 : x ≤ b)
    (h3 : ∀ s, a ≤ s → s ≤ b → 0 ≤ p.derivative.derivative.derivative.eval s)
    (hdb : p.derivative.eval b ≤ 0) (ha : m ≤ p.eval a) (hb : m ≤ p.eval b) :
    m ≤ p.eval x := by
  let q := p.comp (Polynomial.C (a + b) - Polynomial.X)
  have e0 (s : ℝ) : q.eval s = p.eval (a + b - s) := by simp [q]
  have e1 (s : ℝ) : q.derivative.eval s = -p.derivative.eval (a + b - s) := by
    simp [q, Polynomial.derivative_comp, Polynomial.derivative_sub]
  have e3 (s : ℝ) : q.derivative.derivative.derivative.eval s =
      -p.derivative.derivative.derivative.eval (a + b - s) := by
    simp [q, Polynomial.derivative_comp, Polynomial.derivative_sub]
  have hf := polynomial_floor_of_concave_derivative (p := q) (x := a + b - x)
    (a := a) (b := b) (m := m) (by linarith only [hx1]) (by linarith only [hx0])
    (by
      intro s hs0 hs1
      rw [e3]
      exact neg_nonpos.mpr (h3 _ (by linarith only [hs1]) (by linarith only [hs0])))
    (by simpa only [e1, add_sub_cancel_left, neg_nonneg] using hdb)
    (by simpa only [e0, add_sub_cancel_left] using hb)
    (by simpa only [e0, add_sub_cancel_right] using ha)
  simpa only [e0, sub_sub_cancel] using hf

end SmoothedOctagon.LowT
