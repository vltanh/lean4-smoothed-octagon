module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.LowT.Analysis
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.UnitShape.Boundary
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Concavity after clearing a positive linear denominator

For `f(j) = p(j)/(1+2j)^n`, the numerator of its derivative is
`(1+2j)p'(j)-2n p(j)`. Applying this twice, with `n=6`, gives
`(1+2j)^2 p''(j)-24(1+2j)p'(j)+168p(j)`.
-/

@[expose] public section
namespace SmoothedOctagon.LowTScale

noncomputable def weightedDerivative (n : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  (1 + 2 * Polynomial.X) * p.derivative - Polynomial.C (2 * (n : ℝ)) * p

theorem weighted_hasDerivAt (n : ℕ) (p : Polynomial ℝ) {j : ℝ} (hd : 1 + 2 * j ≠ 0) :
    HasDerivAt (fun s => p.eval s / (1 + 2 * s) ^ n)
      ((weightedDerivative n p).eval j / (1 + 2 * j) ^ (n + 1)) j := by
  have hl : HasDerivAt (fun s : ℝ => 1 + 2 * s) 2 j := by
    simpa using ((hasDerivAt_id j).const_mul 2).const_add 1
  have hq := (p.hasDerivAt j).fun_div (hl.pow n) (pow_ne_zero n hd)
  simp only [Pi.pow_apply] at hq
  apply hq.congr_deriv
  cases n with
  | zero => simp [weightedDerivative, hd]
  | succ n =>
    simp only [weightedDerivative, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_X,
      Polynomial.eval_C, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, pow_succ]
    field_simp

theorem weighted_second (p : Polynomial ℝ) (j : ℝ) :
    (weightedDerivative 7 (weightedDerivative 6 p)).eval j =
      (1 + 2 * j) ^ 2 * p.derivative.derivative.eval j
        - 24 * (1 + 2 * j) * p.derivative.eval j + 168 * p.eval j := by
  norm_num [weightedDerivative, Polynomial.derivative_mul]
  ring

theorem rational_boundary_floor {p : Polynomial ℝ} {a b x m : ℝ}
    (hx0 : a ≤ x) (hx1 : x ≤ b)
    (hd : ∀ s, a ≤ s → s ≤ b → 0 < 1 + 2 * s)
    (h2 : ∀ s, a ≤ s → s ≤ b →
      (weightedDerivative 7 (weightedDerivative 6 p)).eval s ≤ 0)
    (ha : m ≤ p.eval a / (1 + 2 * a) ^ 6)
    (hb : m ≤ p.eval b / (1 + 2 * b) ^ 6) :
    m ≤ p.eval x / (1 + 2 * x) ^ 6 := by
  have hc : ConcaveOn ℝ (Set.Icc a b) (fun s => p.eval s / (1 + 2 * s) ^ 6) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
      (fun s hs => (weighted_hasDerivAt 6 p (hd s hs.1 hs.2).ne').continuousAt.continuousWithinAt)
      (fun s hs => by
        rw [interior_Icc] at hs
        exact (weighted_hasDerivAt 6 p (hd s hs.1.le hs.2.le).ne').hasDerivWithinAt)
      (fun s hs => by
        rw [interior_Icc] at hs
        exact (weighted_hasDerivAt 7 (weightedDerivative 6 p)
          (hd s hs.1.le hs.2.le).ne').hasDerivWithinAt)
    intro s hs
    rw [interior_Icc] at hs
    exact div_nonpos_of_nonpos_of_nonneg (h2 s hs.1.le hs.2.le)
      (pow_nonneg (hd s hs.1.le hs.2.le).le 8)
  have hm := hc.min_le_of_mem_Icc
    (show a ∈ Set.Icc a b from ⟨le_rfl, hx0.trans hx1⟩)
    (show b ∈ Set.Icc a b from ⟨hx0.trans hx1, le_rfl⟩) ⟨hx0, hx1⟩
  exact (le_min ha hb).trans hm

end SmoothedOctagon.LowTScale
