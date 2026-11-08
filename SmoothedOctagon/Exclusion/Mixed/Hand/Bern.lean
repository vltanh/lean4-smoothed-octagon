module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Case M2 by hand: positivity of Bernstein forms

`nh_bern_pos1`, …, `nh_bern_pos6`: for `a, b ≥ 0` with `a + b > 0` and positive coefficients
`c₀, …, c_d`, the Bernstein form `∑ c_j a^j b^(d-j)` is positive. Used by the generated polynomial
sign certificates of `Hand/Cert*`.
-/

@[expose] public section

namespace SmoothedOctagon

theorem nh_bern_pos1 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) :
    0 < c0 * b + c1 * a := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c1 * a := by positivity
    have h'' : 0 ≤ c0 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b := by positivity
    have h'' : 0 ≤ c1 * a := by positivity
    linarith

theorem nh_bern_pos2 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) :
    0 < c0 * b ^ 2 + c1 * a * b + c2 * a ^ 2 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c2 * a ^ 2 := by positivity
    have h'' : 0 ≤ c0 * b ^ 2 + c1 * a * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 2 := by positivity
    have h'' : 0 ≤ c1 * a * b + c2 * a ^ 2 := by positivity
    linarith

theorem nh_bern_pos3 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) :
    0 < c0 * b ^ 3 + c1 * a * b ^ 2 + c2 * a ^ 2 * b + c3 * a ^ 3 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c3 * a ^ 3 := by positivity
    have h'' : 0 ≤ c0 * b ^ 3 + c1 * a * b ^ 2 + c2 * a ^ 2 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 3 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 2 + c2 * a ^ 2 * b + c3 * a ^ 3 := by positivity
    linarith

theorem nh_bern_pos4 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 c4 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) :
    0 < c0 * b ^ 4 + c1 * a * b ^ 3 + c2 * a ^ 2 * b ^ 2 + c3 * a ^ 3 * b + c4 * a ^ 4 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c4 * a ^ 4 := by positivity
    have h'' : 0 ≤ c0 * b ^ 4 + c1 * a * b ^ 3 + c2 * a ^ 2 * b ^ 2 + c3 * a ^ 3 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 4 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 3 + c2 * a ^ 2 * b ^ 2 + c3 * a ^ 3 * b + c4 * a ^ 4 := by positivity
    linarith

theorem nh_bern_pos5 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 c4 c5 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) :
    0 < c0 * b ^ 5 + c1 * a * b ^ 4 + c2 * a ^ 2 * b ^ 3 + c3 * a ^ 3 * b ^ 2 + c4 * a ^ 4 * b + c5 * a ^ 5 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c5 * a ^ 5 := by positivity
    have h'' : 0 ≤ c0 * b ^ 5 + c1 * a * b ^ 4 + c2 * a ^ 2 * b ^ 3 + c3 * a ^ 3 * b ^ 2 + c4 * a ^ 4 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 5 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 4 + c2 * a ^ 2 * b ^ 3 + c3 * a ^ 3 * b ^ 2 + c4 * a ^ 4 * b + c5 * a ^ 5 := by positivity
    linarith

theorem nh_bern_pos6 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 c4 c5 c6 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) :
    0 < c0 * b ^ 6 + c1 * a * b ^ 5 + c2 * a ^ 2 * b ^ 4 + c3 * a ^ 3 * b ^ 3 + c4 * a ^ 4 * b ^ 2 + c5 * a ^ 5 * b + c6 * a ^ 6 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c6 * a ^ 6 := by positivity
    have h'' : 0 ≤ c0 * b ^ 6 + c1 * a * b ^ 5 + c2 * a ^ 2 * b ^ 4 + c3 * a ^ 3 * b ^ 3 + c4 * a ^ 4 * b ^ 2 + c5 * a ^ 5 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 6 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 5 + c2 * a ^ 2 * b ^ 4 + c3 * a ^ 3 * b ^ 3 + c4 * a ^ 4 * b ^ 2 + c5 * a ^ 5 * b + c6 * a ^ 6 := by positivity
    linarith

theorem nh_bern_pos7 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 c4 c5 c6 c7 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) (h7 : 0 < c7) :
    0 < c0 * b ^ 7 + c1 * a * b ^ 6 + c2 * a ^ 2 * b ^ 5 + c3 * a ^ 3 * b ^ 4 + c4 * a ^ 4 * b ^ 3 + c5 * a ^ 5 * b ^ 2 + c6 * a ^ 6 * b + c7 * a ^ 7 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c7 * a ^ 7 := by positivity
    have h'' : 0 ≤ c0 * b ^ 7 + c1 * a * b ^ 6 + c2 * a ^ 2 * b ^ 5 + c3 * a ^ 3 * b ^ 4 + c4 * a ^ 4 * b ^ 3 + c5 * a ^ 5 * b ^ 2 + c6 * a ^ 6 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 7 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 6 + c2 * a ^ 2 * b ^ 5 + c3 * a ^ 3 * b ^ 4 + c4 * a ^ 4 * b ^ 3 + c5 * a ^ 5 * b ^ 2 + c6 * a ^ 6 * b + c7 * a ^ 7 := by positivity
    linarith

theorem nh_bern_pos8 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 c4 c5 c6 c7 c8 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) (h7 : 0 < c7) (h8 : 0 < c8) :
    0 < c0 * b ^ 8 + c1 * a * b ^ 7 + c2 * a ^ 2 * b ^ 6 + c3 * a ^ 3 * b ^ 5 + c4 * a ^ 4 * b ^ 4 + c5 * a ^ 5 * b ^ 3 + c6 * a ^ 6 * b ^ 2 + c7 * a ^ 7 * b + c8 * a ^ 8 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c8 * a ^ 8 := by positivity
    have h'' : 0 ≤ c0 * b ^ 8 + c1 * a * b ^ 7 + c2 * a ^ 2 * b ^ 6 + c3 * a ^ 3 * b ^ 5 + c4 * a ^ 4 * b ^ 4 + c5 * a ^ 5 * b ^ 3 + c6 * a ^ 6 * b ^ 2 + c7 * a ^ 7 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 8 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 7 + c2 * a ^ 2 * b ^ 6 + c3 * a ^ 3 * b ^ 5 + c4 * a ^ 4 * b ^ 4 + c5 * a ^ 5 * b ^ 3 + c6 * a ^ 6 * b ^ 2 + c7 * a ^ 7 * b + c8 * a ^ 8 := by positivity
    linarith

theorem nh_bern_pos9 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) (h7 : 0 < c7) (h8 : 0 < c8) (h9 : 0 < c9) :
    0 < c0 * b ^ 9 + c1 * a * b ^ 8 + c2 * a ^ 2 * b ^ 7 + c3 * a ^ 3 * b ^ 6 + c4 * a ^ 4 * b ^ 5 + c5 * a ^ 5 * b ^ 4 + c6 * a ^ 6 * b ^ 3 + c7 * a ^ 7 * b ^ 2 + c8 * a ^ 8 * b + c9 * a ^ 9 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c9 * a ^ 9 := by positivity
    have h'' : 0 ≤ c0 * b ^ 9 + c1 * a * b ^ 8 + c2 * a ^ 2 * b ^ 7 + c3 * a ^ 3 * b ^ 6 + c4 * a ^ 4 * b ^ 5 + c5 * a ^ 5 * b ^ 4 + c6 * a ^ 6 * b ^ 3 + c7 * a ^ 7 * b ^ 2 + c8 * a ^ 8 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 9 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 8 + c2 * a ^ 2 * b ^ 7 + c3 * a ^ 3 * b ^ 6 + c4 * a ^ 4 * b ^ 5 + c5 * a ^ 5 * b ^ 4 + c6 * a ^ 6 * b ^ 3 + c7 * a ^ 7 * b ^ 2 + c8 * a ^ 8 * b + c9 * a ^ 9 := by positivity
    linarith

theorem nh_bern_pos10 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) (h7 : 0 < c7) (h8 : 0 < c8) (h9 : 0 < c9) (h10 : 0 < c10) :
    0 < c0 * b ^ 10 + c1 * a * b ^ 9 + c2 * a ^ 2 * b ^ 8 + c3 * a ^ 3 * b ^ 7 + c4 * a ^ 4 * b ^ 6 + c5 * a ^ 5 * b ^ 5 + c6 * a ^ 6 * b ^ 4 + c7 * a ^ 7 * b ^ 3 + c8 * a ^ 8 * b ^ 2 + c9 * a ^ 9 * b + c10 * a ^ 10 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c10 * a ^ 10 := by positivity
    have h'' : 0 ≤ c0 * b ^ 10 + c1 * a * b ^ 9 + c2 * a ^ 2 * b ^ 8 + c3 * a ^ 3 * b ^ 7 + c4 * a ^ 4 * b ^ 6 + c5 * a ^ 5 * b ^ 5 + c6 * a ^ 6 * b ^ 4 + c7 * a ^ 7 * b ^ 3 + c8 * a ^ 8 * b ^ 2 + c9 * a ^ 9 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 10 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 9 + c2 * a ^ 2 * b ^ 8 + c3 * a ^ 3 * b ^ 7 + c4 * a ^ 4 * b ^ 6 + c5 * a ^ 5 * b ^ 5 + c6 * a ^ 6 * b ^ 4 + c7 * a ^ 7 * b ^ 3 + c8 * a ^ 8 * b ^ 2 + c9 * a ^ 9 * b + c10 * a ^ 10 := by positivity
    linarith

theorem nh_bern_pos11 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) (h7 : 0 < c7) (h8 : 0 < c8) (h9 : 0 < c9) (h10 : 0 < c10) (h11 : 0 < c11) :
    0 < c0 * b ^ 11 + c1 * a * b ^ 10 + c2 * a ^ 2 * b ^ 9 + c3 * a ^ 3 * b ^ 8 + c4 * a ^ 4 * b ^ 7 + c5 * a ^ 5 * b ^ 6 + c6 * a ^ 6 * b ^ 5 + c7 * a ^ 7 * b ^ 4 + c8 * a ^ 8 * b ^ 3 + c9 * a ^ 9 * b ^ 2 + c10 * a ^ 10 * b + c11 * a ^ 11 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c11 * a ^ 11 := by positivity
    have h'' : 0 ≤ c0 * b ^ 11 + c1 * a * b ^ 10 + c2 * a ^ 2 * b ^ 9 + c3 * a ^ 3 * b ^ 8 + c4 * a ^ 4 * b ^ 7 + c5 * a ^ 5 * b ^ 6 + c6 * a ^ 6 * b ^ 5 + c7 * a ^ 7 * b ^ 4 + c8 * a ^ 8 * b ^ 3 + c9 * a ^ 9 * b ^ 2 + c10 * a ^ 10 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 11 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 10 + c2 * a ^ 2 * b ^ 9 + c3 * a ^ 3 * b ^ 8 + c4 * a ^ 4 * b ^ 7 + c5 * a ^ 5 * b ^ 6 + c6 * a ^ 6 * b ^ 5 + c7 * a ^ 7 * b ^ 4 + c8 * a ^ 8 * b ^ 3 + c9 * a ^ 9 * b ^ 2 + c10 * a ^ 10 * b + c11 * a ^ 11 := by positivity
    linarith

theorem nh_bern_pos12 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) (h7 : 0 < c7) (h8 : 0 < c8) (h9 : 0 < c9) (h10 : 0 < c10) (h11 : 0 < c11) (h12 : 0 < c12) :
    0 < c0 * b ^ 12 + c1 * a * b ^ 11 + c2 * a ^ 2 * b ^ 10 + c3 * a ^ 3 * b ^ 9 + c4 * a ^ 4 * b ^ 8 + c5 * a ^ 5 * b ^ 7 + c6 * a ^ 6 * b ^ 6 + c7 * a ^ 7 * b ^ 5 + c8 * a ^ 8 * b ^ 4 + c9 * a ^ 9 * b ^ 3 + c10 * a ^ 10 * b ^ 2 + c11 * a ^ 11 * b + c12 * a ^ 12 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c12 * a ^ 12 := by positivity
    have h'' : 0 ≤ c0 * b ^ 12 + c1 * a * b ^ 11 + c2 * a ^ 2 * b ^ 10 + c3 * a ^ 3 * b ^ 9 + c4 * a ^ 4 * b ^ 8 + c5 * a ^ 5 * b ^ 7 + c6 * a ^ 6 * b ^ 6 + c7 * a ^ 7 * b ^ 5 + c8 * a ^ 8 * b ^ 4 + c9 * a ^ 9 * b ^ 3 + c10 * a ^ 10 * b ^ 2 + c11 * a ^ 11 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 12 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 11 + c2 * a ^ 2 * b ^ 10 + c3 * a ^ 3 * b ^ 9 + c4 * a ^ 4 * b ^ 8 + c5 * a ^ 5 * b ^ 7 + c6 * a ^ 6 * b ^ 6 + c7 * a ^ 7 * b ^ 5 + c8 * a ^ 8 * b ^ 4 + c9 * a ^ 9 * b ^ 3 + c10 * a ^ 10 * b ^ 2 + c11 * a ^ 11 * b + c12 * a ^ 12 := by positivity
    linarith

theorem nh_bern_pos13 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) (h7 : 0 < c7) (h8 : 0 < c8) (h9 : 0 < c9) (h10 : 0 < c10) (h11 : 0 < c11) (h12 : 0 < c12) (h13 : 0 < c13) :
    0 < c0 * b ^ 13 + c1 * a * b ^ 12 + c2 * a ^ 2 * b ^ 11 + c3 * a ^ 3 * b ^ 10 + c4 * a ^ 4 * b ^ 9 + c5 * a ^ 5 * b ^ 8 + c6 * a ^ 6 * b ^ 7 + c7 * a ^ 7 * b ^ 6 + c8 * a ^ 8 * b ^ 5 + c9 * a ^ 9 * b ^ 4 + c10 * a ^ 10 * b ^ 3 + c11 * a ^ 11 * b ^ 2 + c12 * a ^ 12 * b + c13 * a ^ 13 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c13 * a ^ 13 := by positivity
    have h'' : 0 ≤ c0 * b ^ 13 + c1 * a * b ^ 12 + c2 * a ^ 2 * b ^ 11 + c3 * a ^ 3 * b ^ 10 + c4 * a ^ 4 * b ^ 9 + c5 * a ^ 5 * b ^ 8 + c6 * a ^ 6 * b ^ 7 + c7 * a ^ 7 * b ^ 6 + c8 * a ^ 8 * b ^ 5 + c9 * a ^ 9 * b ^ 4 + c10 * a ^ 10 * b ^ 3 + c11 * a ^ 11 * b ^ 2 + c12 * a ^ 12 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 13 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 12 + c2 * a ^ 2 * b ^ 11 + c3 * a ^ 3 * b ^ 10 + c4 * a ^ 4 * b ^ 9 + c5 * a ^ 5 * b ^ 8 + c6 * a ^ 6 * b ^ 7 + c7 * a ^ 7 * b ^ 6 + c8 * a ^ 8 * b ^ 5 + c9 * a ^ 9 * b ^ 4 + c10 * a ^ 10 * b ^ 3 + c11 * a ^ 11 * b ^ 2 + c12 * a ^ 12 * b + c13 * a ^ 13 := by positivity
    linarith

theorem nh_bern_pos14 {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) {c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : ℝ}
    (h0 : 0 < c0) (h1 : 0 < c1) (h2 : 0 < c2) (h3 : 0 < c3) (h4 : 0 < c4) (h5 : 0 < c5) (h6 : 0 < c6) (h7 : 0 < c7) (h8 : 0 < c8) (h9 : 0 < c9) (h10 : 0 < c10) (h11 : 0 < c11) (h12 : 0 < c12) (h13 : 0 < c13) (h14 : 0 < c14) :
    0 < c0 * b ^ 14 + c1 * a * b ^ 13 + c2 * a ^ 2 * b ^ 12 + c3 * a ^ 3 * b ^ 11 + c4 * a ^ 4 * b ^ 10 + c5 * a ^ 5 * b ^ 9 + c6 * a ^ 6 * b ^ 8 + c7 * a ^ 7 * b ^ 7 + c8 * a ^ 8 * b ^ 6 + c9 * a ^ 9 * b ^ 5 + c10 * a ^ 10 * b ^ 4 + c11 * a ^ 11 * b ^ 3 + c12 * a ^ 12 * b ^ 2 + c13 * a ^ 13 * b + c14 * a ^ 14 := by
  rcases lt_or_ge 0 a with h | h
  · have h' : 0 < c14 * a ^ 14 := by positivity
    have h'' : 0 ≤ c0 * b ^ 14 + c1 * a * b ^ 13 + c2 * a ^ 2 * b ^ 12 + c3 * a ^ 3 * b ^ 11 + c4 * a ^ 4 * b ^ 10 + c5 * a ^ 5 * b ^ 9 + c6 * a ^ 6 * b ^ 8 + c7 * a ^ 7 * b ^ 7 + c8 * a ^ 8 * b ^ 6 + c9 * a ^ 9 * b ^ 5 + c10 * a ^ 10 * b ^ 4 + c11 * a ^ 11 * b ^ 3 + c12 * a ^ 12 * b ^ 2 + c13 * a ^ 13 * b := by positivity
    linarith
  · have hb' : 0 < b := by linarith
    have h' : 0 < c0 * b ^ 14 := by positivity
    have h'' : 0 ≤ c1 * a * b ^ 13 + c2 * a ^ 2 * b ^ 12 + c3 * a ^ 3 * b ^ 11 + c4 * a ^ 4 * b ^ 10 + c5 * a ^ 5 * b ^ 9 + c6 * a ^ 6 * b ^ 8 + c7 * a ^ 7 * b ^ 7 + c8 * a ^ 8 * b ^ 6 + c9 * a ^ 9 * b ^ 5 + c10 * a ^ 10 * b ^ 4 + c11 * a ^ 11 * b ^ 3 + c12 * a ^ 12 * b ^ 2 + c13 * a ^ 13 * b + c14 * a ^ 14 := by positivity
    linarith

end SmoothedOctagon
