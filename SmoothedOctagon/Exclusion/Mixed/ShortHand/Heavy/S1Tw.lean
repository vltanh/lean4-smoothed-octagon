module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gate S1, heavy faces: termwise bound lemmas

Elementary facts used by the generated polynomial certificates of gate S1 (`hh1` claims): a
polynomial `P(z, A, s, μ)` with `z, A, μ ≥ 0`, `|s| ≤ tA`, `μ ≤ μ₀`, `A ≤ A₀` is bounded below
termwise (`LOW_RATIO_CENTRAL_HAND_SIGN` App. A (A6)): every adverse monomial is compared with its
value at the end of its range.

## Main API

* `hh1_tw_spos`, `hh1_tw_sneg`: `0 ≤ s^k + (tA)^k`, `0 ≤ (tA)^k - s^k` for `|s| ≤ tA`;
* `hh1_tw_sub`: `0 ≤ Y^k - y^k` for `0 ≤ y ≤ Y`.
-/

@[expose] public section

namespace SmoothedOctagon

theorem hh1_tw_abs {s A t : ℝ} (k : ℕ) (hs : |s| ≤ t * A) : |s ^ k| ≤ (t * A) ^ k := by
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg s) hs k

theorem hh1_tw_spos {s A t : ℝ} (k : ℕ) (hs : |s| ≤ t * A) : 0 ≤ s ^ k + (t * A) ^ k := by
  have := (abs_le.1 (hh1_tw_abs k hs)).1; linarith

theorem hh1_tw_sneg {s A t : ℝ} (k : ℕ) (hs : |s| ≤ t * A) : 0 ≤ (t * A) ^ k - s ^ k := by
  have := (abs_le.1 (hh1_tw_abs k hs)).2; linarith

theorem hh1_tw_sub {y Y : ℝ} (k : ℕ) (h0 : 0 ≤ y) (h1 : y ≤ Y) : 0 ≤ Y ^ k - y ^ k :=
  sub_nonneg.2 (pow_le_pow_left₀ h0 h1 k)

end SmoothedOctagon
