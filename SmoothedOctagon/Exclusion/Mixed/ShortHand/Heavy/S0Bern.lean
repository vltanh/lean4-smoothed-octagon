module

public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic

/-!
# Hand proof of the smaller-short case, heavy S0 signs: Bernstein lemmas

Positivity of a polynomial `∑ cᵢ yⁱ` on an interval `0 ≤ y ≤ gn/gd` from its (scaled) Bernstein
coefficients, with abstract coefficients `cᵢ`, `gn`, `gd` (so that the certificates of
`Heavy/S0*` apply them to polynomial coefficients without expanding them).

## Main API

* `hh0_bpos{n}`: a Bernstein form with positive coefficients is positive.
* `hh0_bern{n}`: Bernstein positivity on `[0, gn/gd]`, degrees 4, 5, 6, 7, 8.
-/

@[expose] public section

namespace SmoothedOctagon

/-- A Bernstein form of degree 4 with positive coefficients is positive. -/
theorem hh0_bpos4 {p r c0 c1 c2 c3 c4 : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (hpr : 0 < p ∨ 0 < r)
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) :
    0 < c0 * r ^ (4 : ℕ) + c1 * p * r ^ (3 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (2 : ℕ) + c3 * p ^ (3 : ℕ) * r + c4 * p ^ (4 : ℕ) := by
  rcases hpr with h | h
  · have h' : 0 < c4 * p ^ (4 : ℕ) := by positivity
    have h'' : 0 ≤ c0 * r ^ (4 : ℕ) + c1 * p * r ^ (3 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (2 : ℕ) + c3 * p ^ (3 : ℕ) * r := by positivity
    linarith
  · have h' : 0 < c0 * r ^ (4 : ℕ) := by positivity
    have h'' : 0 ≤ c1 * p * r ^ (3 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (2 : ℕ) + c3 * p ^ (3 : ℕ) * r + c4 * p ^ (4 : ℕ) := by positivity
    linarith

/-- A Bernstein form of degree 5 with positive coefficients is positive. -/
theorem hh0_bpos5 {p r c0 c1 c2 c3 c4 c5 : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (hpr : 0 < p ∨ 0 < r)
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) :
    0 < c0 * r ^ (5 : ℕ) + c1 * p * r ^ (4 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (3 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (2 : ℕ) + c4 * p ^ (4 : ℕ) * r + c5 * p ^ (5 : ℕ) := by
  rcases hpr with h | h
  · have h' : 0 < c5 * p ^ (5 : ℕ) := by positivity
    have h'' : 0 ≤ c0 * r ^ (5 : ℕ) + c1 * p * r ^ (4 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (3 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (2 : ℕ) + c4 * p ^ (4 : ℕ) * r := by positivity
    linarith
  · have h' : 0 < c0 * r ^ (5 : ℕ) := by positivity
    have h'' : 0 ≤ c1 * p * r ^ (4 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (3 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (2 : ℕ) + c4 * p ^ (4 : ℕ) * r + c5 * p ^ (5 : ℕ) := by positivity
    linarith

/-- A Bernstein form of degree 6 with positive coefficients is positive. -/
theorem hh0_bpos6 {p r c0 c1 c2 c3 c4 c5 c6 : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (hpr : 0 < p ∨ 0 < r)
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) :
    0 < c0 * r ^ (6 : ℕ) + c1 * p * r ^ (5 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (4 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (3 : ℕ) + c4 * p ^ (4 : ℕ) * r ^ (2 : ℕ) + c5 * p ^ (5 : ℕ) * r + c6 * p ^ (6 : ℕ) := by
  rcases hpr with h | h
  · have h' : 0 < c6 * p ^ (6 : ℕ) := by positivity
    have h'' : 0 ≤ c0 * r ^ (6 : ℕ) + c1 * p * r ^ (5 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (4 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (3 : ℕ) + c4 * p ^ (4 : ℕ) * r ^ (2 : ℕ) + c5 * p ^ (5 : ℕ) * r := by positivity
    linarith
  · have h' : 0 < c0 * r ^ (6 : ℕ) := by positivity
    have h'' : 0 ≤ c1 * p * r ^ (5 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (4 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (3 : ℕ) + c4 * p ^ (4 : ℕ) * r ^ (2 : ℕ) + c5 * p ^ (5 : ℕ) * r + c6 * p ^ (6 : ℕ) := by positivity
    linarith

/-- A Bernstein form of degree 7 with positive coefficients is positive. -/
theorem hh0_bpos7 {p r c0 c1 c2 c3 c4 c5 c6 c7 : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (hpr : 0 < p ∨ 0 < r)
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) (h7 : 0 < c7) :
    0 < c0 * r ^ (7 : ℕ) + c1 * p * r ^ (6 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (5 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (4 : ℕ) + c4 * p ^ (4 : ℕ) * r ^ (3 : ℕ) + c5 * p ^ (5 : ℕ) * r ^ (2 : ℕ) + c6 * p ^ (6 : ℕ) * r + c7 * p ^ (7 : ℕ) := by
  rcases hpr with h | h
  · have h' : 0 < c7 * p ^ (7 : ℕ) := by positivity
    have h'' : 0 ≤ c0 * r ^ (7 : ℕ) + c1 * p * r ^ (6 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (5 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (4 : ℕ) + c4 * p ^ (4 : ℕ) * r ^ (3 : ℕ) + c5 * p ^ (5 : ℕ) * r ^ (2 : ℕ) + c6 * p ^ (6 : ℕ) * r := by positivity
    linarith
  · have h' : 0 < c0 * r ^ (7 : ℕ) := by positivity
    have h'' : 0 ≤ c1 * p * r ^ (6 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (5 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (4 : ℕ) + c4 * p ^ (4 : ℕ) * r ^ (3 : ℕ) + c5 * p ^ (5 : ℕ) * r ^ (2 : ℕ) + c6 * p ^ (6 : ℕ) * r + c7 * p ^ (7 : ℕ) := by positivity
    linarith

/-- A Bernstein form of degree 8 with positive coefficients is positive. -/
theorem hh0_bpos8 {p r c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (hpr : 0 < p ∨ 0 < r)
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) (h7 : 0 < c7) (h8 : 0 < c8) :
    0 < c0 * r ^ (8 : ℕ) + c1 * p * r ^ (7 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (6 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (5 : ℕ) + c4 * p ^ (4 : ℕ) * r ^ (4 : ℕ) + c5 * p ^ (5 : ℕ) * r ^ (3 : ℕ) + c6 * p ^ (6 : ℕ) * r ^ (2 : ℕ) + c7 * p ^ (7 : ℕ) * r + c8 * p ^ (8 : ℕ) := by
  rcases hpr with h | h
  · have h' : 0 < c8 * p ^ (8 : ℕ) := by positivity
    have h'' : 0 ≤ c0 * r ^ (8 : ℕ) + c1 * p * r ^ (7 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (6 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (5 : ℕ) + c4 * p ^ (4 : ℕ) * r ^ (4 : ℕ) + c5 * p ^ (5 : ℕ) * r ^ (3 : ℕ) + c6 * p ^ (6 : ℕ) * r ^ (2 : ℕ) + c7 * p ^ (7 : ℕ) * r := by positivity
    linarith
  · have h' : 0 < c0 * r ^ (8 : ℕ) := by positivity
    have h'' : 0 ≤ c1 * p * r ^ (7 : ℕ) + c2 * p ^ (2 : ℕ) * r ^ (6 : ℕ) + c3 * p ^ (3 : ℕ) * r ^ (5 : ℕ) + c4 * p ^ (4 : ℕ) * r ^ (4 : ℕ) + c5 * p ^ (5 : ℕ) * r ^ (3 : ℕ) + c6 * p ^ (6 : ℕ) * r ^ (2 : ℕ) + c7 * p ^ (7 : ℕ) * r + c8 * p ^ (8 : ℕ) := by positivity
    linarith

/-- Bernstein positivity of degree 4 on `[0, gn/gd]`, with abstract coefficients: the
polynomial `∑ cᵢ yⁱ` is positive when its scaled Bernstein coefficients
`∑_{i ≤ k} C(4 - i, k - i) cᵢ gnⁱ gd^(k - i)` are. -/
theorem hh0_bern4 {y gn gd c0 c1 c2 c3 c4 : ℝ} (hy : 0 ≤ y) (hyg : gd * y ≤ gn) (hgd : 0 < gd)
    (h0 : 0 < c0)
    (h1 : 0 < 4 * c0 * gd + c1 * gn)
    (h2 : 0 < 6 * c0 * gd ^ (2 : ℕ) + 3 * c1 * gn * gd + c2 * gn ^ (2 : ℕ))
    (h3 : 0 < 4 * c0 * gd ^ (3 : ℕ) + 3 * c1 * gn * gd ^ (2 : ℕ) + 2 * c2 * gn ^ (2 : ℕ) * gd + c3 * gn ^ (3 : ℕ))
    (h4 : 0 < c0 * gd ^ (4 : ℕ) + c1 * gn * gd ^ (3 : ℕ) + c2 * gn ^ (2 : ℕ) * gd ^ (2 : ℕ) + c3 * gn ^ (3 : ℕ) * gd + c4 * gn ^ (4 : ℕ)) :
    0 < c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ) := by
  have hgn : 0 ≤ gn := le_trans (mul_nonneg hgd.le hy) hyg
  rcases hgn.eq_or_lt with h | h
  · have hy0 : y = 0 := by nlinarith
    subst hy0
    simpa using h0
  · have e : gn ^ (4 : ℕ) * (c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ)) =
        (c0) * (gn - gd * y) ^ (4 : ℕ) + (4 * c0 * gd + c1 * gn) * y * (gn - gd * y) ^ (3 : ℕ) + (6 * c0 * gd ^ (2 : ℕ) + 3 * c1 * gn * gd + c2 * gn ^ (2 : ℕ)) * y ^ (2 : ℕ) * (gn - gd * y) ^ (2 : ℕ) + (4 * c0 * gd ^ (3 : ℕ) + 3 * c1 * gn * gd ^ (2 : ℕ) + 2 * c2 * gn ^ (2 : ℕ) * gd + c3 * gn ^ (3 : ℕ)) * y ^ (3 : ℕ) * (gn - gd * y) + (c0 * gd ^ (4 : ℕ) + c1 * gn * gd ^ (3 : ℕ) + c2 * gn ^ (2 : ℕ) * gd ^ (2 : ℕ) + c3 * gn ^ (3 : ℕ) * gd + c4 * gn ^ (4 : ℕ)) * y ^ (4 : ℕ) := by ring
    have hpr : 0 < y ∨ 0 < gn - gd * y := by
      rcases hy.eq_or_lt with h' | h'
      · right; rw [← h']; simpa using h
      · left; exact h'
    have hpos := hh0_bpos4 hy (by linarith) hpr h0 h1 h2 h3 h4
    rw [← e] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)

/-- Bernstein positivity of degree 5 on `[0, gn/gd]`, with abstract coefficients: the
polynomial `∑ cᵢ yⁱ` is positive when its scaled Bernstein coefficients
`∑_{i ≤ k} C(5 - i, k - i) cᵢ gnⁱ gd^(k - i)` are. -/
theorem hh0_bern5 {y gn gd c0 c1 c2 c3 c4 c5 : ℝ} (hy : 0 ≤ y) (hyg : gd * y ≤ gn) (hgd : 0 < gd)
    (h0 : 0 < c0)
    (h1 : 0 < 5 * c0 * gd + c1 * gn)
    (h2 : 0 < 10 * c0 * gd ^ (2 : ℕ) + 4 * c1 * gn * gd + c2 * gn ^ (2 : ℕ))
    (h3 : 0 < 10 * c0 * gd ^ (3 : ℕ) + 6 * c1 * gn * gd ^ (2 : ℕ) + 3 * c2 * gn ^ (2 : ℕ) * gd + c3 * gn ^ (3 : ℕ))
    (h4 : 0 < 5 * c0 * gd ^ (4 : ℕ) + 4 * c1 * gn * gd ^ (3 : ℕ) + 3 * c2 * gn ^ (2 : ℕ) * gd ^ (2 : ℕ) + 2 * c3 * gn ^ (3 : ℕ) * gd + c4 * gn ^ (4 : ℕ))
    (h5 : 0 < c0 * gd ^ (5 : ℕ) + c1 * gn * gd ^ (4 : ℕ) + c2 * gn ^ (2 : ℕ) * gd ^ (3 : ℕ) + c3 * gn ^ (3 : ℕ) * gd ^ (2 : ℕ) + c4 * gn ^ (4 : ℕ) * gd + c5 * gn ^ (5 : ℕ)) :
    0 < c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ) + c5 * y ^ (5 : ℕ) := by
  have hgn : 0 ≤ gn := le_trans (mul_nonneg hgd.le hy) hyg
  rcases hgn.eq_or_lt with h | h
  · have hy0 : y = 0 := by nlinarith
    subst hy0
    simpa using h0
  · have e : gn ^ (5 : ℕ) * (c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ) + c5 * y ^ (5 : ℕ)) =
        (c0) * (gn - gd * y) ^ (5 : ℕ) + (5 * c0 * gd + c1 * gn) * y * (gn - gd * y) ^ (4 : ℕ) + (10 * c0 * gd ^ (2 : ℕ) + 4 * c1 * gn * gd + c2 * gn ^ (2 : ℕ)) * y ^ (2 : ℕ) * (gn - gd * y) ^ (3 : ℕ) + (10 * c0 * gd ^ (3 : ℕ) + 6 * c1 * gn * gd ^ (2 : ℕ) + 3 * c2 * gn ^ (2 : ℕ) * gd + c3 * gn ^ (3 : ℕ)) * y ^ (3 : ℕ) * (gn - gd * y) ^ (2 : ℕ) + (5 * c0 * gd ^ (4 : ℕ) + 4 * c1 * gn * gd ^ (3 : ℕ) + 3 * c2 * gn ^ (2 : ℕ) * gd ^ (2 : ℕ) + 2 * c3 * gn ^ (3 : ℕ) * gd + c4 * gn ^ (4 : ℕ)) * y ^ (4 : ℕ) * (gn - gd * y) + (c0 * gd ^ (5 : ℕ) + c1 * gn * gd ^ (4 : ℕ) + c2 * gn ^ (2 : ℕ) * gd ^ (3 : ℕ) + c3 * gn ^ (3 : ℕ) * gd ^ (2 : ℕ) + c4 * gn ^ (4 : ℕ) * gd + c5 * gn ^ (5 : ℕ)) * y ^ (5 : ℕ) := by ring
    have hpr : 0 < y ∨ 0 < gn - gd * y := by
      rcases hy.eq_or_lt with h' | h'
      · right; rw [← h']; simpa using h
      · left; exact h'
    have hpos := hh0_bpos5 hy (by linarith) hpr h0 h1 h2 h3 h4 h5
    rw [← e] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)

/-- Bernstein positivity of degree 6 on `[0, gn/gd]`, with abstract coefficients: the
polynomial `∑ cᵢ yⁱ` is positive when its scaled Bernstein coefficients
`∑_{i ≤ k} C(6 - i, k - i) cᵢ gnⁱ gd^(k - i)` are. -/
theorem hh0_bern6 {y gn gd c0 c1 c2 c3 c4 c5 c6 : ℝ} (hy : 0 ≤ y) (hyg : gd * y ≤ gn) (hgd : 0 < gd)
    (h0 : 0 < c0)
    (h1 : 0 < 6 * c0 * gd + c1 * gn)
    (h2 : 0 < 15 * c0 * gd ^ (2 : ℕ) + 5 * c1 * gn * gd + c2 * gn ^ (2 : ℕ))
    (h3 : 0 < 20 * c0 * gd ^ (3 : ℕ) + 10 * c1 * gn * gd ^ (2 : ℕ) + 4 * c2 * gn ^ (2 : ℕ) * gd + c3 * gn ^ (3 : ℕ))
    (h4 : 0 < 15 * c0 * gd ^ (4 : ℕ) + 10 * c1 * gn * gd ^ (3 : ℕ) + 6 * c2 * gn ^ (2 : ℕ) * gd ^ (2 : ℕ) + 3 * c3 * gn ^ (3 : ℕ) * gd + c4 * gn ^ (4 : ℕ))
    (h5 : 0 < 6 * c0 * gd ^ (5 : ℕ) + 5 * c1 * gn * gd ^ (4 : ℕ) + 4 * c2 * gn ^ (2 : ℕ) * gd ^ (3 : ℕ) + 3 * c3 * gn ^ (3 : ℕ) * gd ^ (2 : ℕ) + 2 * c4 * gn ^ (4 : ℕ) * gd + c5 * gn ^ (5 : ℕ))
    (h6 : 0 < c0 * gd ^ (6 : ℕ) + c1 * gn * gd ^ (5 : ℕ) + c2 * gn ^ (2 : ℕ) * gd ^ (4 : ℕ) + c3 * gn ^ (3 : ℕ) * gd ^ (3 : ℕ) + c4 * gn ^ (4 : ℕ) * gd ^ (2 : ℕ) + c5 * gn ^ (5 : ℕ) * gd + c6 * gn ^ (6 : ℕ)) :
    0 < c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ) + c5 * y ^ (5 : ℕ) + c6 * y ^ (6 : ℕ) := by
  have hgn : 0 ≤ gn := le_trans (mul_nonneg hgd.le hy) hyg
  rcases hgn.eq_or_lt with h | h
  · have hy0 : y = 0 := by nlinarith
    subst hy0
    simpa using h0
  · have e : gn ^ (6 : ℕ) * (c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ) + c5 * y ^ (5 : ℕ) + c6 * y ^ (6 : ℕ)) =
        (c0) * (gn - gd * y) ^ (6 : ℕ) + (6 * c0 * gd + c1 * gn) * y * (gn - gd * y) ^ (5 : ℕ) + (15 * c0 * gd ^ (2 : ℕ) + 5 * c1 * gn * gd + c2 * gn ^ (2 : ℕ)) * y ^ (2 : ℕ) * (gn - gd * y) ^ (4 : ℕ) + (20 * c0 * gd ^ (3 : ℕ) + 10 * c1 * gn * gd ^ (2 : ℕ) + 4 * c2 * gn ^ (2 : ℕ) * gd + c3 * gn ^ (3 : ℕ)) * y ^ (3 : ℕ) * (gn - gd * y) ^ (3 : ℕ) + (15 * c0 * gd ^ (4 : ℕ) + 10 * c1 * gn * gd ^ (3 : ℕ) + 6 * c2 * gn ^ (2 : ℕ) * gd ^ (2 : ℕ) + 3 * c3 * gn ^ (3 : ℕ) * gd + c4 * gn ^ (4 : ℕ)) * y ^ (4 : ℕ) * (gn - gd * y) ^ (2 : ℕ) + (6 * c0 * gd ^ (5 : ℕ) + 5 * c1 * gn * gd ^ (4 : ℕ) + 4 * c2 * gn ^ (2 : ℕ) * gd ^ (3 : ℕ) + 3 * c3 * gn ^ (3 : ℕ) * gd ^ (2 : ℕ) + 2 * c4 * gn ^ (4 : ℕ) * gd + c5 * gn ^ (5 : ℕ)) * y ^ (5 : ℕ) * (gn - gd * y) + (c0 * gd ^ (6 : ℕ) + c1 * gn * gd ^ (5 : ℕ) + c2 * gn ^ (2 : ℕ) * gd ^ (4 : ℕ) + c3 * gn ^ (3 : ℕ) * gd ^ (3 : ℕ) + c4 * gn ^ (4 : ℕ) * gd ^ (2 : ℕ) + c5 * gn ^ (5 : ℕ) * gd + c6 * gn ^ (6 : ℕ)) * y ^ (6 : ℕ) := by ring
    have hpr : 0 < y ∨ 0 < gn - gd * y := by
      rcases hy.eq_or_lt with h' | h'
      · right; rw [← h']; simpa using h
      · left; exact h'
    have hpos := hh0_bpos6 hy (by linarith) hpr h0 h1 h2 h3 h4 h5 h6
    rw [← e] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)

/-- Bernstein positivity of degree 7 on `[0, gn/gd]`, with abstract coefficients: the
polynomial `∑ cᵢ yⁱ` is positive when its scaled Bernstein coefficients
`∑_{i ≤ k} C(7 - i, k - i) cᵢ gnⁱ gd^(k - i)` are. -/
theorem hh0_bern7 {y gn gd c0 c1 c2 c3 c4 c5 c6 c7 : ℝ} (hy : 0 ≤ y) (hyg : gd * y ≤ gn) (hgd : 0 < gd)
    (h0 : 0 < c0)
    (h1 : 0 < 7 * c0 * gd + c1 * gn)
    (h2 : 0 < 21 * c0 * gd ^ (2 : ℕ) + 6 * c1 * gn * gd + c2 * gn ^ (2 : ℕ))
    (h3 : 0 < 35 * c0 * gd ^ (3 : ℕ) + 15 * c1 * gn * gd ^ (2 : ℕ) + 5 * c2 * gn ^ (2 : ℕ) * gd + c3 * gn ^ (3 : ℕ))
    (h4 : 0 < 35 * c0 * gd ^ (4 : ℕ) + 20 * c1 * gn * gd ^ (3 : ℕ) + 10 * c2 * gn ^ (2 : ℕ) * gd ^ (2 : ℕ) + 4 * c3 * gn ^ (3 : ℕ) * gd + c4 * gn ^ (4 : ℕ))
    (h5 : 0 < 21 * c0 * gd ^ (5 : ℕ) + 15 * c1 * gn * gd ^ (4 : ℕ) + 10 * c2 * gn ^ (2 : ℕ) * gd ^ (3 : ℕ) + 6 * c3 * gn ^ (3 : ℕ) * gd ^ (2 : ℕ) + 3 * c4 * gn ^ (4 : ℕ) * gd + c5 * gn ^ (5 : ℕ))
    (h6 : 0 < 7 * c0 * gd ^ (6 : ℕ) + 6 * c1 * gn * gd ^ (5 : ℕ) + 5 * c2 * gn ^ (2 : ℕ) * gd ^ (4 : ℕ) + 4 * c3 * gn ^ (3 : ℕ) * gd ^ (3 : ℕ) + 3 * c4 * gn ^ (4 : ℕ) * gd ^ (2 : ℕ) + 2 * c5 * gn ^ (5 : ℕ) * gd + c6 * gn ^ (6 : ℕ))
    (h7 : 0 < c0 * gd ^ (7 : ℕ) + c1 * gn * gd ^ (6 : ℕ) + c2 * gn ^ (2 : ℕ) * gd ^ (5 : ℕ) + c3 * gn ^ (3 : ℕ) * gd ^ (4 : ℕ) + c4 * gn ^ (4 : ℕ) * gd ^ (3 : ℕ) + c5 * gn ^ (5 : ℕ) * gd ^ (2 : ℕ) + c6 * gn ^ (6 : ℕ) * gd + c7 * gn ^ (7 : ℕ)) :
    0 < c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ) + c5 * y ^ (5 : ℕ) + c6 * y ^ (6 : ℕ) + c7 * y ^ (7 : ℕ) := by
  have hgn : 0 ≤ gn := le_trans (mul_nonneg hgd.le hy) hyg
  rcases hgn.eq_or_lt with h | h
  · have hy0 : y = 0 := by nlinarith
    subst hy0
    simpa using h0
  · have e : gn ^ (7 : ℕ) * (c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ) + c5 * y ^ (5 : ℕ) + c6 * y ^ (6 : ℕ) + c7 * y ^ (7 : ℕ)) =
        (c0) * (gn - gd * y) ^ (7 : ℕ) + (7 * c0 * gd + c1 * gn) * y * (gn - gd * y) ^ (6 : ℕ) + (21 * c0 * gd ^ (2 : ℕ) + 6 * c1 * gn * gd + c2 * gn ^ (2 : ℕ)) * y ^ (2 : ℕ) * (gn - gd * y) ^ (5 : ℕ) + (35 * c0 * gd ^ (3 : ℕ) + 15 * c1 * gn * gd ^ (2 : ℕ) + 5 * c2 * gn ^ (2 : ℕ) * gd + c3 * gn ^ (3 : ℕ)) * y ^ (3 : ℕ) * (gn - gd * y) ^ (4 : ℕ) + (35 * c0 * gd ^ (4 : ℕ) + 20 * c1 * gn * gd ^ (3 : ℕ) + 10 * c2 * gn ^ (2 : ℕ) * gd ^ (2 : ℕ) + 4 * c3 * gn ^ (3 : ℕ) * gd + c4 * gn ^ (4 : ℕ)) * y ^ (4 : ℕ) * (gn - gd * y) ^ (3 : ℕ) + (21 * c0 * gd ^ (5 : ℕ) + 15 * c1 * gn * gd ^ (4 : ℕ) + 10 * c2 * gn ^ (2 : ℕ) * gd ^ (3 : ℕ) + 6 * c3 * gn ^ (3 : ℕ) * gd ^ (2 : ℕ) + 3 * c4 * gn ^ (4 : ℕ) * gd + c5 * gn ^ (5 : ℕ)) * y ^ (5 : ℕ) * (gn - gd * y) ^ (2 : ℕ) + (7 * c0 * gd ^ (6 : ℕ) + 6 * c1 * gn * gd ^ (5 : ℕ) + 5 * c2 * gn ^ (2 : ℕ) * gd ^ (4 : ℕ) + 4 * c3 * gn ^ (3 : ℕ) * gd ^ (3 : ℕ) + 3 * c4 * gn ^ (4 : ℕ) * gd ^ (2 : ℕ) + 2 * c5 * gn ^ (5 : ℕ) * gd + c6 * gn ^ (6 : ℕ)) * y ^ (6 : ℕ) * (gn - gd * y) + (c0 * gd ^ (7 : ℕ) + c1 * gn * gd ^ (6 : ℕ) + c2 * gn ^ (2 : ℕ) * gd ^ (5 : ℕ) + c3 * gn ^ (3 : ℕ) * gd ^ (4 : ℕ) + c4 * gn ^ (4 : ℕ) * gd ^ (3 : ℕ) + c5 * gn ^ (5 : ℕ) * gd ^ (2 : ℕ) + c6 * gn ^ (6 : ℕ) * gd + c7 * gn ^ (7 : ℕ)) * y ^ (7 : ℕ) := by ring
    have hpr : 0 < y ∨ 0 < gn - gd * y := by
      rcases hy.eq_or_lt with h' | h'
      · right; rw [← h']; simpa using h
      · left; exact h'
    have hpos := hh0_bpos7 hy (by linarith) hpr h0 h1 h2 h3 h4 h5 h6 h7
    rw [← e] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)

/-- Bernstein positivity of degree 8 on `[0, gn/gd]`, with abstract coefficients: the
polynomial `∑ cᵢ yⁱ` is positive when its scaled Bernstein coefficients
`∑_{i ≤ k} C(8 - i, k - i) cᵢ gnⁱ gd^(k - i)` are. -/
theorem hh0_bern8 {y gn gd c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℝ} (hy : 0 ≤ y) (hyg : gd * y ≤ gn) (hgd : 0 < gd)
    (h0 : 0 < c0)
    (h1 : 0 < 8 * c0 * gd + c1 * gn)
    (h2 : 0 < 28 * c0 * gd ^ (2 : ℕ) + 7 * c1 * gn * gd + c2 * gn ^ (2 : ℕ))
    (h3 : 0 < 56 * c0 * gd ^ (3 : ℕ) + 21 * c1 * gn * gd ^ (2 : ℕ) + 6 * c2 * gn ^ (2 : ℕ) * gd + c3 * gn ^ (3 : ℕ))
    (h4 : 0 < 70 * c0 * gd ^ (4 : ℕ) + 35 * c1 * gn * gd ^ (3 : ℕ) + 15 * c2 * gn ^ (2 : ℕ) * gd ^ (2 : ℕ) + 5 * c3 * gn ^ (3 : ℕ) * gd + c4 * gn ^ (4 : ℕ))
    (h5 : 0 < 56 * c0 * gd ^ (5 : ℕ) + 35 * c1 * gn * gd ^ (4 : ℕ) + 20 * c2 * gn ^ (2 : ℕ) * gd ^ (3 : ℕ) + 10 * c3 * gn ^ (3 : ℕ) * gd ^ (2 : ℕ) + 4 * c4 * gn ^ (4 : ℕ) * gd + c5 * gn ^ (5 : ℕ))
    (h6 : 0 < 28 * c0 * gd ^ (6 : ℕ) + 21 * c1 * gn * gd ^ (5 : ℕ) + 15 * c2 * gn ^ (2 : ℕ) * gd ^ (4 : ℕ) + 10 * c3 * gn ^ (3 : ℕ) * gd ^ (3 : ℕ) + 6 * c4 * gn ^ (4 : ℕ) * gd ^ (2 : ℕ) + 3 * c5 * gn ^ (5 : ℕ) * gd + c6 * gn ^ (6 : ℕ))
    (h7 : 0 < 8 * c0 * gd ^ (7 : ℕ) + 7 * c1 * gn * gd ^ (6 : ℕ) + 6 * c2 * gn ^ (2 : ℕ) * gd ^ (5 : ℕ) + 5 * c3 * gn ^ (3 : ℕ) * gd ^ (4 : ℕ) + 4 * c4 * gn ^ (4 : ℕ) * gd ^ (3 : ℕ) + 3 * c5 * gn ^ (5 : ℕ) * gd ^ (2 : ℕ) + 2 * c6 * gn ^ (6 : ℕ) * gd + c7 * gn ^ (7 : ℕ))
    (h8 : 0 < c0 * gd ^ (8 : ℕ) + c1 * gn * gd ^ (7 : ℕ) + c2 * gn ^ (2 : ℕ) * gd ^ (6 : ℕ) + c3 * gn ^ (3 : ℕ) * gd ^ (5 : ℕ) + c4 * gn ^ (4 : ℕ) * gd ^ (4 : ℕ) + c5 * gn ^ (5 : ℕ) * gd ^ (3 : ℕ) + c6 * gn ^ (6 : ℕ) * gd ^ (2 : ℕ) + c7 * gn ^ (7 : ℕ) * gd + c8 * gn ^ (8 : ℕ)) :
    0 < c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ) + c5 * y ^ (5 : ℕ) + c6 * y ^ (6 : ℕ) + c7 * y ^ (7 : ℕ) + c8 * y ^ (8 : ℕ) := by
  have hgn : 0 ≤ gn := le_trans (mul_nonneg hgd.le hy) hyg
  rcases hgn.eq_or_lt with h | h
  · have hy0 : y = 0 := by nlinarith
    subst hy0
    simpa using h0
  · have e : gn ^ (8 : ℕ) * (c0 + c1 * y + c2 * y ^ (2 : ℕ) + c3 * y ^ (3 : ℕ) + c4 * y ^ (4 : ℕ) + c5 * y ^ (5 : ℕ) + c6 * y ^ (6 : ℕ) + c7 * y ^ (7 : ℕ) + c8 * y ^ (8 : ℕ)) =
        (c0) * (gn - gd * y) ^ (8 : ℕ) + (8 * c0 * gd + c1 * gn) * y * (gn - gd * y) ^ (7 : ℕ) + (28 * c0 * gd ^ (2 : ℕ) + 7 * c1 * gn * gd + c2 * gn ^ (2 : ℕ)) * y ^ (2 : ℕ) * (gn - gd * y) ^ (6 : ℕ) + (56 * c0 * gd ^ (3 : ℕ) + 21 * c1 * gn * gd ^ (2 : ℕ) + 6 * c2 * gn ^ (2 : ℕ) * gd + c3 * gn ^ (3 : ℕ)) * y ^ (3 : ℕ) * (gn - gd * y) ^ (5 : ℕ) + (70 * c0 * gd ^ (4 : ℕ) + 35 * c1 * gn * gd ^ (3 : ℕ) + 15 * c2 * gn ^ (2 : ℕ) * gd ^ (2 : ℕ) + 5 * c3 * gn ^ (3 : ℕ) * gd + c4 * gn ^ (4 : ℕ)) * y ^ (4 : ℕ) * (gn - gd * y) ^ (4 : ℕ) + (56 * c0 * gd ^ (5 : ℕ) + 35 * c1 * gn * gd ^ (4 : ℕ) + 20 * c2 * gn ^ (2 : ℕ) * gd ^ (3 : ℕ) + 10 * c3 * gn ^ (3 : ℕ) * gd ^ (2 : ℕ) + 4 * c4 * gn ^ (4 : ℕ) * gd + c5 * gn ^ (5 : ℕ)) * y ^ (5 : ℕ) * (gn - gd * y) ^ (3 : ℕ) + (28 * c0 * gd ^ (6 : ℕ) + 21 * c1 * gn * gd ^ (5 : ℕ) + 15 * c2 * gn ^ (2 : ℕ) * gd ^ (4 : ℕ) + 10 * c3 * gn ^ (3 : ℕ) * gd ^ (3 : ℕ) + 6 * c4 * gn ^ (4 : ℕ) * gd ^ (2 : ℕ) + 3 * c5 * gn ^ (5 : ℕ) * gd + c6 * gn ^ (6 : ℕ)) * y ^ (6 : ℕ) * (gn - gd * y) ^ (2 : ℕ) + (8 * c0 * gd ^ (7 : ℕ) + 7 * c1 * gn * gd ^ (6 : ℕ) + 6 * c2 * gn ^ (2 : ℕ) * gd ^ (5 : ℕ) + 5 * c3 * gn ^ (3 : ℕ) * gd ^ (4 : ℕ) + 4 * c4 * gn ^ (4 : ℕ) * gd ^ (3 : ℕ) + 3 * c5 * gn ^ (5 : ℕ) * gd ^ (2 : ℕ) + 2 * c6 * gn ^ (6 : ℕ) * gd + c7 * gn ^ (7 : ℕ)) * y ^ (7 : ℕ) * (gn - gd * y) + (c0 * gd ^ (8 : ℕ) + c1 * gn * gd ^ (7 : ℕ) + c2 * gn ^ (2 : ℕ) * gd ^ (6 : ℕ) + c3 * gn ^ (3 : ℕ) * gd ^ (5 : ℕ) + c4 * gn ^ (4 : ℕ) * gd ^ (4 : ℕ) + c5 * gn ^ (5 : ℕ) * gd ^ (3 : ℕ) + c6 * gn ^ (6 : ℕ) * gd ^ (2 : ℕ) + c7 * gn ^ (7 : ℕ) * gd + c8 * gn ^ (8 : ℕ)) * y ^ (8 : ℕ) := by ring
    have hpr : 0 < y ∨ 0 < gn - gd * y := by
      rcases hy.eq_or_lt with h' | h'
      · right; rw [← h']; simpa using h
      · left; exact h'
    have hpos := hh0_bpos8 hy (by linarith) hpr h0 h1 h2 h3 h4 h5 h6 h7 h8
    rw [← e] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)

end SmoothedOctagon
