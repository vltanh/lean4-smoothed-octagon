module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandCenDefs

/-!
# S2 hand signs: the central terminal numerators

The four central terminal tests at `x = 13/6`, `β = b_+(13/6, α) = (309α + 523)/384`, with the
original incoming norm `u = hsUC(13/6, β)` and the quadratic logarithm bound `Q`
(`hl2ctQ`), are the rational functions
`N/(c·Den)` of `S2HandCenTerm`; this file proves the four numerators `N` negative.
`Den` is `a(693a + 523)(36a² + 325)^m t²(309a + 139)` (`m = 3` for `F₀`, `m = 2` for `F₁`) with
`t = 20/3 - 4a` on the lower interval `[1, 7/6]`, and the same without `t²` on the upper interval
`[7/6, 4/3]` (`t = 2`); each `N` is the exact cleared form, checked against the definitions by
`field_simp; ring` in `S2HandCenTerm`.

Sign rule (termwise with absorption): in a shifted variable `0 ≤ s ≤ w` write `N = Σ c_k s^k`.
A positive term `c_k s^k` (`k ≥ 2`) is bounded by `c_k w^{k-1} s` (linear absorption) or by
`c_k w^{k-2} s²` (quadratic absorption), a negative one by `0`.
* `N_{L0}`: split at `9/8`, `s = 9/8 - a` and `s = 7/6 - a`, linear absorption; the absorbed
  linear coefficient is negative, so `N ≤ c₀ < 0`.
* `N_{H0}`, `N_{H1}`: `s = a - 7/6 ∈ [0, 1/6]`, linear absorption, as above.
* `N_{L1}`: `s = a - 1 ∈ [0, 1/6]`, quadratic absorption; the absorbed quadratic
  `c₀ + c₁s + C₂s²` has `C₂ < 0` and `c₁² < 4c₀C₂` (square completion at `s = 23/200`).

## Main API

* `hl2ctNL0`, `hl2ctNL1`, `hl2ctNH0`, `hl2ctNH1` and their signs `hl2ct_NL0_neg`, ….
-/

@[expose] public section

namespace SmoothedOctagon

/-- The monomial facts of the termwise bound with absorption, `0 ≤ s ≤ w`. -/
theorem hl2ct_box {s w : ℝ} (hs : 0 ≤ s) (hw : s ≤ w) :
    (∀ n : ℕ, 0 ≤ s ^ n) ∧ (∀ n : ℕ, 0 ≤ s * (w ^ n - s ^ n)) ∧
      (∀ n : ℕ, 0 ≤ s ^ 2 * (w ^ n - s ^ n)) :=
  ⟨fun n => pow_nonneg hs n, fun n => mul_nonneg hs (sub_nonneg.2 (pow_le_pow_left₀ hs hw n)),
    fun n => mul_nonneg (pow_nonneg hs 2) (sub_nonneg.2 (pow_le_pow_left₀ hs hw n))⟩

/-- The cleared numerator of the first test on the lower interval, `t = 20/3 - 4a`. -/
noncomputable def hl2ctNL0 (a : ℝ) : ℝ :=
  -387901650180521709659750400 * a ^ 13 + 1312967118744933702115000320 * a ^ 12 -
    3589029801661302053829352620 * a ^ 11 + 6454789484415460100740915416 * a ^ 10 +
    9898985035266438960297814509 * a ^ 9 - 50335729706413660567702681287 * a ^ 8 +
    26013324732267306856222071477 * a ^ 7 + 83877945406405669186200246033 * a ^ 6 -
    76456597889837385187294277889 * a ^ 5 - 60210619510240340304276113325 * a ^ 4 +
    68149888603140248695906008075 * a ^ 3 + 13676610282903499858094068875 * a ^ 2 -
    15362870426761043442536800000 * a - 3091055203886119446600000000

/-- The cleared numerator of the second test on the lower interval. -/
noncomputable def hl2ctNL1 (a : ℝ) : ℝ :=
  -673440364896739079270400 * a ^ 11 + 2279456803376621010616320 * a ^ 10 +
    209614301135183382753420 * a ^ 9 - 9872080436617581234345228 * a ^ 8 +
    10296033925153890012566463 * a ^ 7 + 10362610077613618836095262 * a ^ 6 -
    21674097625973438503061631 * a ^ 5 + 2294717191889450209886088 * a ^ 4 +
    13113250229168482299779025 * a ^ 3 - 5379140354986597387318650 * a ^ 2 -
    1798467284074847460212125 * a + 833512755207507417900000

/-- The cleared numerator of the first test on the upper interval, `t = 2`. -/
noncomputable def hl2ctNH0 (a : ℝ) : ℝ :=
  -24095826894959092018563660 * a ^ 9 - 58760930011302686881896336 * a ^ 8 +
    258072262800291956925194481 * a ^ 7 + 333713236978986324219535887 * a ^ 6 -
    845001737427864864942810882 * a ^ 5 - 667923878104082605393436178 * a ^ 4 +
    1169356662405875812502749869 * a ^ 3 + 338727899054414624444876355 * a ^ 2 -
    372418521940400329250272000 * a - 123642208155444777864000000

/-- The cleared numerator of the second test on the upper interval. -/
noncomputable def hl2ctNH1 (a : ℝ) : ℝ :=
  -2771254855158381810900 * a ^ 7 - 26480532896520201203652 * a ^ 6 +
    38271509844555889364067 * a ^ 5 + 133850796455926833993468 * a ^ 4 -
    94677785527789639213074 * a ^ 3 - 265085404426521213897648 * a ^ 2 +
    133939947857044870450715 * a + 97860695615755528716000

/-- `N_{L0} < 0` on `[1, 7/6]`: split at `9/8`, linear absorption from the right end. -/
theorem hl2ct_NL0_neg {a : ℝ} (h1 : 1 ≤ a) (h2 : a ≤ 7 / 6) : hl2ctNL0 a < 0 := by
  unfold hl2ctNL0
  rcases le_total a (9 / 8) with h | h
  · obtain ⟨hP, hA, -⟩ := hl2ct_box (s := 9 / 8 - a) (w := 1 / 8) (by linarith) (by linarith)
    linarith [hP 1, hP 2, hP 3, hP 4, hA 4, hP 6, hA 6, hP 8, hA 8, hP 10, hA 10, hP 12, hA 12]
  · obtain ⟨hP, hA, -⟩ := hl2ct_box (s := 7 / 6 - a) (w := 1 / 24) (by linarith) (by linarith)
    linarith [hP 1, hP 2, hA 2, hP 4, hA 4, hP 6, hA 6, hP 8, hA 8, hP 10, hA 10, hP 12, hA 12]

/-- `N_{L1} < 0` on `[1, 7/6]`: quadratic absorption in `s = a - 1`, then square completion. -/
theorem hl2ct_NL1_neg {a : ℝ} (h1 : 1 ≤ a) (h2 : a ≤ 7 / 6) : hl2ctNL1 a < 0 := by
  unfold hl2ctNL1
  obtain ⟨hP, -, hB⟩ := hl2ct_box (s := a - 1) (w := 1 / 6) (by linarith) (by linarith)
  have hq := sq_nonneg (a - 1 - 23 / 200)
  linarith [hP 1, hP 2, hB 1, hB 2, hP 5, hP 6, hP 7, hP 8, hP 9, hP 10, hP 11, hq]

/-- `N_{H0} < 0` on `[7/6, 4/3]`: linear absorption in `s = a - 7/6`. -/
theorem hl2ct_NH0_neg {a : ℝ} (h1 : 7 / 6 ≤ a) (h2 : a ≤ 4 / 3) : hl2ctNH0 a < 0 := by
  unfold hl2ctNH0
  obtain ⟨hP, hA, -⟩ := hl2ct_box (s := a - 7 / 6) (w := 1 / 6) (by linarith) (by linarith)
  linarith [hP 1, hP 2, hA 2, hA 3, hP 5, hP 6, hP 7, hP 8, hP 9]

/-- `N_{H1} < 0` on `[7/6, 4/3]`: linear absorption in `s = a - 7/6`. -/
theorem hl2ct_NH1_neg {a : ℝ} (h1 : 7 / 6 ≤ a) (h2 : a ≤ 4 / 3) : hl2ctNH1 a < 0 := by
  unfold hl2ctNH1
  obtain ⟨hP, hA, -⟩ := hl2ct_box (s := a - 7 / 6) (w := 1 / 6) (by linarith) (by linarith)
  linarith [hP 1, hA 1, hA 2, hP 4, hP 5, hP 6, hP 7]

end SmoothedOctagon
