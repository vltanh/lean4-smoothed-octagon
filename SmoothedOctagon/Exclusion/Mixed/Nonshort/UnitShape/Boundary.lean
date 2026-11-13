module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Coordinates
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Tactic.GCongr

/-!
# Boundary estimates for the unit face

The lower boundary of the order gap is `max 0 (1/4-x)`.
On the order edge `r = 0`, the relevant polynomials increase with `x`.
On the cap edge `t = 3/8`, elementary concavity bounds reduce the
estimates to the two endpoints. No subdivision of the shape interval
is needed.
-/

@[expose] public section

namespace SmoothedOctagon.UnitShape

theorem polynomial_mono {p : Polynomial ℝ} {a b : ℝ}
    (hab : a ≤ b) (hp : ∀ z, a ≤ z → z ≤ b → 0 ≤ p.derivative.eval z) :
    p.eval a ≤ p.eval b := by
  have hm : MonotoneOn (fun z => p.eval z) (Set.Icc a b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun z _ => (p.hasDerivAt z).continuousAt.continuousWithinAt)
      (fun z _ => (p.hasDerivAt z).hasDerivWithinAt)
    intro z hz
    rw [interior_Icc] at hz
    exact hp z hz.1.le hz.2.le
  exact hm ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

theorem polynomial_floor {p : Polynomial ℝ} {a b x m : ℝ}
    (hx : a ≤ x) (hx1 : x ≤ b)
    (hp : ∀ z, a ≤ z → z ≤ b → p.derivative.derivative.eval z ≤ 0)
    (ha : m ≤ p.eval a) (hb : m ≤ p.eval b) : m ≤ p.eval x := by
  have hc : ConcaveOn ℝ (Set.Icc a b) (fun z => p.eval z) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (fun z _ => (p.hasDerivAt z).continuousAt.continuousWithinAt)
      (fun z _ => (p.hasDerivAt z).hasDerivWithinAt)
      (fun z _ => (p.derivative.hasDerivAt z).hasDerivWithinAt)
    intro z hz
    rw [interior_Icc] at hz
    exact hp z hz.1.le hz.2.le
  have hmin := hc.min_le_of_mem_Icc (show a ∈ Set.Icc a b from ⟨le_rfl, hx.trans hx1⟩)
    (show b ∈ Set.Icc a b from ⟨hx.trans hx1, le_rfl⟩) ⟨hx, hx1⟩
  exact (le_min ha hb).trans hmin

private def capValue {R : Type*} [CommRing R] (x : R) : R :=
  96 * x ^ 7 + 2037 * x ^ 6 + 15627 * x ^ 5 + 51426 * x ^ 4
    + 82825 * x ^ 3 + 60375 * x ^ 2 + 8130 * x - 7320

private def capCross {R : Type*} [CommRing R] (x : R) : R :=
  384 * x ^ 9 + 6228 * x ^ 8 + 41748 * x ^ 7 + 106284 * x ^ 6 + 82000 * x ^ 5
    - 103601 * x ^ 4 - 215937 * x ^ 3 - 94932 * x ^ 2 + 14394 * x + 6210

private def capWedge {R : Type*} [CommRing R] (x : R) : R :=
  -2976 * x ^ 9 - 66699 * x ^ 8 - 554811 * x ^ 7 - 2119125 * x ^ 6 - 4275532 * x ^ 5
    - 4608244 * x ^ 4 - 2245863 * x ^ 3 - 49278 * x ^ 2 + 237876 * x + 1440

private def orderWedge {R : Type*} [CommRing R] (x : R) : R :=
  93 * x ^ 8 + 939 * x ^ 7 + 4291 * x ^ 6 + 10763 * x ^ 5 + 15366 * x ^ 4
    + 11926 * x ^ 3 + 3894 * x ^ 2 - 324 * x - 420

private theorem order_value_pos {x : ℝ} (hx : 1 / 4 ≤ x) : 0 < value0 x := by
  let p : Polynomial ℝ := value0 Polynomial.X
  have hm := polynomial_mono (p := p) hx (by
    intro z hz _
    have hz0 : 0 ≤ z := by linarith only [hz]
    have hp : 0 ≤ 24 * z ^ 7 + 210 * z ^ 6 + 816 * z ^ 5 + 1690 * z ^ 4
        + 1908 * z ^ 3 + 1092 * z ^ 2 := by positivity
    norm_num [p, value0, Polynomial.derivative_mul, Polynomial.derivative_pow]
    linarith only [hp, hz])
  have hv : 0 < p.eval (1 / 4) := by norm_num [p, value0]
  have he : p.eval x = value0 x := by simp [p, value0]
  linarith only [hm, hv, he]

private theorem order_wedge_pos {x : ℝ} (hx : 1 / 4 ≤ x) : 0 < orderWedge x := by
  let p : Polynomial ℝ := orderWedge Polynomial.X
  have hm := polynomial_mono (p := p) hx (by
    intro z hz _
    have hz0 : 0 ≤ z := by linarith only [hz]
    have hp : 0 ≤ 744 * z ^ 7 + 6573 * z ^ 6 + 25746 * z ^ 5 + 53815 * z ^ 4
        + 61464 * z ^ 3 + 35778 * z ^ 2 := by positivity
    norm_num [p, orderWedge, Polynomial.derivative_mul, Polynomial.derivative_pow]
    linarith only [hp, hz])
  have hv : 0 < p.eval (1 / 4) := by norm_num [p, orderWedge]
  have he : p.eval x = orderWedge x := by simp [p, orderWedge]
  linarith only [hm, hv, he]

private theorem cap_cross_pos {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4) : 0 < capCross x := by
  let p : Polynomial ℝ := capCross Polynomial.X
  have hp : ∀ z, 0 ≤ z → z ≤ 1 / 4 → p.derivative.derivative.eval z ≤ 0 := by
    intro z hz hz1
    have h3 := pow_le_pow_left₀ hz hz1 3
    have h4 := pow_le_pow_left₀ hz hz1 4
    have h5 := pow_le_pow_left₀ hz hz1 5
    have h6 := pow_le_pow_left₀ hz hz1 6
    have h7 := pow_le_pow_left₀ hz hz1 7
    norm_num [p, capCross, Polynomial.derivative_mul, Polynomial.derivative_pow]
    nlinarith only [h3, h4, h5, h6, h7, sq_nonneg z, hz]
  have hm := polynomial_floor (p := p) (m := 1) hx hx1 hp
    (by norm_num [p, capCross]) (by norm_num [p, capCross])
  have he : p.eval x = capCross x := by simp [p, capCross]
  linarith only [hm, he]

private theorem cap_wedge_pos {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 4) : 0 < capWedge x := by
  let p : Polynomial ℝ := capWedge Polynomial.X
  have hp : ∀ z, 0 ≤ z → z ≤ 1 / 4 → p.derivative.derivative.eval z ≤ 0 := by
    intro z hz _
    have hn : 0 ≤ 214272 * z ^ 7 + 3735144 * z ^ 6 + 23302062 * z ^ 5
        + 63573750 * z ^ 4 + 85510640 * z ^ 3 + 55298928 * z ^ 2 + 13475178 * z := by positivity
    norm_num [p, capWedge, Polynomial.derivative_mul, Polynomial.derivative_pow]
    linarith only [hn]
  have hm := polynomial_floor (p := p) (m := 1) hx hx1 hp
    (by norm_num [p, capWedge]) (by norm_num [p, capWedge])
  have he : p.eval x = capWedge x := by simp [p, capWedge]
  linarith only [hm, he]

/-- Three boundary inequalities used to absorb a possibly negative cross term. -/
theorem lower_boundary_pos {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    let r := max 0 (1 / 4 - x)
    0 < value x r ∧ 0 < constant x r + 8 * cross x r ∧
      0 < cross x r + 32 * value x r := by
  dsimp only
  have hW : 0 < 1 + x := by linarith only [hx]
  by_cases hxquarter : 1 / 4 ≤ x
  · rw [max_eq_left (by linarith only [hxquarter])]
    have hv := order_value_pos hxquarter
    have hw := order_wedge_pos hxquarter
    have eV : value x 0 = x * (1 + x) ^ 2 * value0 x := by unfold value; ring
    have eW : cross x 0 + 32 * value x 0 = x * (1 + x) ^ 2 * orderWedge x := by
      unfold value cross value0 cross0 orderWedge; ring
    have h2 := pow_le_pow_of_le_one hx.le hx1 (by norm_num : (4 : ℕ) ≤ 8)
    have h3 := pow_le_pow_of_le_one hx.le hx1 (by norm_num : (4 : ℕ) ≤ 7)
    have h4 := pow_le_pow_of_le_one hx.le hx1 (by norm_num : (4 : ℕ) ≤ 6)
    have h5 := pow_le_pow_of_le_one hx.le hx1 (by norm_num : (4 : ℕ) ≤ 5)
    have h43 := pow_le_pow_of_le_one hx.le hx1 (by norm_num : (3 : ℕ) ≤ 4)
    have hl2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hxquarter 2
    have hl3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) hxquarter 3
    have hb : 0 < -12 * x ^ 8 - 84 * x ^ 7 - 244 * x ^ 6 - 212 * x ^ 5
        + 411 * x ^ 4 + 1124 * x ^ 3 + 1005 * x ^ 2 + 258 * x - 138 := by
      linarith only [h2, h3, h4, h5, h43, hl2, hl3, hxquarter]
    have eC : constant x 0 + 8 * cross x 0 = 2 * x * (1 + x) ^ 2 *
        (-12 * x ^ 8 - 84 * x ^ 7 - 244 * x ^ 6 - 212 * x ^ 5
          + 411 * x ^ 4 + 1124 * x ^ 3 + 1005 * x ^ 2 + 258 * x - 138) := by
      unfold constant cross cross0; ring
    rw [eW, eC, eV]
    exact ⟨by positivity, by positivity, by positivity⟩
  · have hxquarter : x ≤ 1 / 4 := le_of_lt (lt_of_not_ge hxquarter)
    rw [max_eq_right (by linarith only [hxquarter])]
    have hv : capValue x < 0 := by
      have hm : capValue x ≤ capValue (1 / 4 : ℝ) := by
        unfold capValue
        gcongr
      have hc : capValue (1 / 4 : ℝ) < 0 := by norm_num [capValue]
      exact hm.trans_lt hc
    have hc := cap_cross_pos hx.le hxquarter
    have hw := cap_wedge_pos hx.le hxquarter
    have eV : 64 * value x (1 / 4 - x) = -x * (1 + x) * capValue x := by
      unfold value value0 value1 value2 value3 capValue; ring
    have eC : 32 * (constant x (1 / 4 - x) + 8 * cross x (1 / 4 - x)) = capCross x := by
      unfold constant cross cross0 cross1 cross2 cross3 capCross; ring
    have eW : 64 * (cross x (1 / 4 - x) + 32 * value x (1 / 4 - x)) = capWedge x := by
      unfold cross cross0 cross1 cross2 cross3 value value0 value1 value2 value3 capWedge; ring
    have hp : 0 < -x * (1 + x) * capValue x := mul_pos_of_neg_of_neg (by nlinarith only [hx, hW]) hv
    exact ⟨by linarith only [eV, hp], by linarith only [eC, hc], by linarith only [eW, hw]⟩

end SmoothedOctagon.UnitShape
