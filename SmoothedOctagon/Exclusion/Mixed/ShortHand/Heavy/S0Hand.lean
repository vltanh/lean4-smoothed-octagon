module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandCenFin
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutL
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutS
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutFTa
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutFTb
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutF8a
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutF8b
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutF2a
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S0HandOutF2b

/-!
# Hand proof of the smaller-short case, gate S0: the three heavy face signs

The leaves `hs0_central_tau_two`, `hs0_central_duration` and `hs0_outer_tests` of gate S0, proved
with their exact statements as `*_proof` by the hand arguments of `archive/lighter-proofs/`
(PR #2 rows S1.3, S1.4):

* `SHORT_DURATION_CENTRAL_TAU_TWO.md` (with `SHORT_DURATION_CENTRAL_LOWER_FACE.md`) for
  `CENTRAL_TAU_TWO_SIGN` (3): beta convexity, the lower face `β = x` and four upper faces
  (`hl0_central_two`, `Heavy/S0HandCen*`);
* `SHORT_DURATION_CENTRAL_UPPER_FACES.md` (with the lower face) for `CENTRAL_DURATION_FACES` (5)
  (`hl0_central_T`, `hl0_central_8`);
* `SHORT_SCALE_OUTER_LARGE_RATIO.md` for `OUTER_SCALE_LARGE_RATIO_SIGN` (7): incoming monotonicity
  and the two majorants (`Heavy/S0HandOut`), the cubic comparison on the large shapes
  `α ≥ (2x + 3)/5` (`Heavy/S0HandOutL`), beta convexity and five faces on the strip
  (`Heavy/S0HandOutS`, `Heavy/S0HandOutF*`); assembled here (`hl0_outer_T`, `hl0_outer_8`,
  `hl0_outer_2`).

The expanded numerators are computed inside Lean from their factored source formulas by products of
coefficient lists (`hl0Mul2`; never printed), every identity between a source formula and its list is
proved generically (`ring` on at most seven atoms) and every sign by the uniform coefficient bound of
the notes (rule (6)) evaluated by `norm_num`. The only printed polynomials are the twelve `P_{ij}` of
the large-shape appendix; there is no generated certificate or coefficient table.

## Main API

* `hs0_central_tau_two_proof`, `hs0_central_duration_proof`, `hs0_outer_tests_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The central face, `τ = 2` test** (`CENTRAL_TAU_TWO_SIGN` (3); inventory HS-S01 B7): the
statement of `hs0_central_tau_two`. -/
theorem hs0_central_tau_two_proof {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hal' : al ≤ (5 * x + 4) / 12) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hsF x be al (hsUhat x be) (hsQc x al) 2
      (5 / (2 * (hsRA al be / hsQc x al)) - 11 / 9) (1 / 2) < 0 :=
  hl0_central_two hx hx9 hal hal' hxb hb

/-- **The central face, `τ = T` and `τ = 8T/9` tests** (`CENTRAL_DURATION_FACES` (5); inventory
HS-S01 B8): the statement of `hs0_central_duration`. -/
theorem hs0_central_duration_proof {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hal' : al ≤ (5 * x + 4) / 12) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hsF x be al (hsUhat x be) (hsQc x al) (hsRA al be / hsQc x al) 0 (1 / 2) < 0 ∧
      hsF x be al (hsUhat x be) (hsQc x al) (8 * (hsRA al be / hsQc x al) / 9) (-1 / 9) (1 / 2) <
        0 :=
  ⟨hl0_central_T hx hx9 hal hal' hxb hb, hl0_central_8 hx hx9 hal hal' hxb hb⟩

/-! ### The outer face -/

/-- The outer domain facts: `α > 1`, `β ≥ x`, `β ≥ x + (3/5)(α - 1)`, `4α ≤ 3β`. -/
theorem hl0_outer_dom {x a b : ℝ} (hx : 12 / 5 ≤ x) (hal : (22 * x + 20) / 55 ≤ a) (hax : a ≤ x)
    (hb : x + 4 * x * (a - 1) / (5 * x + 4) ≤ b) :
    1 < a ∧ x + 3 / 5 * (a - 1) ≤ b ∧ x ≤ b ∧ 4 * a ≤ 3 * b := by
  have ha1 : 1 < a := by linarith
  have h54 : 0 < 5 * x + 4 := by linarith
  have hq : 3 / 5 * (a - 1) ≤ 4 * x * (a - 1) / (5 * x + 4) := by
    rw [le_div_iff₀ h54]; nlinarith
  have h43 : 4 * a ≤ 3 * (x + 4 * x * (a - 1) / (5 * x + 4)) := by
    have e : 3 * (x + 4 * x * (a - 1) / (5 * x + 4)) - 4 * a =
        (15 * x ^ 2 - 8 * a * x - 16 * a) / (5 * x + 4) := by field_simp; ring
    have : 0 ≤ (15 * x ^ 2 - 8 * a * x - 16 * a) / (5 * x + 4) := by
      apply div_nonneg _ h54.le; nlinarith
    linarith
  refine ⟨ha1, by linarith, by nlinarith, by linarith⟩

/-- Strip slope selection: for `x ∈ [l, h]` with `x(7x + 1) ≤ c(4x² + 11x + 1)` and `c ≤ 3/2`, the
upper face `β₁ = x + c(α - 1)` encloses `β` and `β₁ + α ≤ 2x` on the strip. -/
theorem hl0_strip_face_le {x a b c : ℝ} (hx : 12 / 5 ≤ x) (hal : (22 * x + 20) / 55 ≤ a)
    (ham : a ≤ (2 * x + 3) / 5) (hc : x * (7 * x + 1) ≤ c * (4 * x ^ 2 + 11 * x + 1))
    (hc32 : c ≤ 3 / 2) (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    b ≤ x + c * (a - 1) ∧ x + c * (a - 1) + a ≤ 2 * x := by
  have ha1 : 1 ≤ a := by linarith
  refine ⟨hl0_slope_le (by linarith) ha1 hc hb', ?_⟩
  nlinarith

/-- The outer test at the actual shape: the three cases (large shapes, and the strip with the
upper face chosen by `x`). -/
theorem hl0_outer_gen {G : ℝ → ℝ → ℝ → ℝ → ℝ} {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (hal : (22 * x + 20) / 55 ≤ a) (hax : a ≤ x) (hb : x + 4 * x * (a - 1) / (5 * x + 4) ≤ b)
    (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1))
    (hmono : ∀ u u', 4 * a ≤ 3 * b → x ≤ b → u ≤ u' → G x a b u ≤ G x a b u')
    (hlarge : (2 * x + 3) / 5 ≤ a → x + 3 / 5 * (a - 1) ≤ b → b ≤ x + 3 / 2 * (a - 1) →
      G x a b ((x + 74) / 100) < 0)
    (hstrip : a ≤ (2 * x + 3) / 5 → ∀ c, x * (7 * x + 1) ≤ c * (4 * x ^ 2 + 11 * x + 1) →
      c ≤ 3 / 2 → (12 / 5 ≤ x ∧ x ≤ 5 / 2 ∧ c = 7 / 8 ∨ 5 / 2 ≤ x ∧ x ≤ 14 / 5 ∧ c = 11 / 12 ∨
        14 / 5 ≤ x ∧ x ≤ 4 ∧ c = 13 / 12 ∨ 4 ≤ x ∧ x ≤ 9 ∧ c = 3 / 2) →
      b ≤ x + c * (a - 1) → x + c * (a - 1) + a ≤ 2 * x → G x a b (hsUhat x b) < 0) :
    G x a b (hsUbar x b) < 0 := by
  obtain ⟨ha1, hb0, hxb, hb43⟩ := hl0_outer_dom hx hal hax hb
  rcases le_or_gt a ((2 * x + 3) / 5) with ham | ham
  · have hu := hl0_ubar_le_uhat hx hx9 ham hxb hb'
    have hm := hmono _ _ hb43 hxb hu
    have hx0 : 0 < x := by linarith
    have key : ∀ c, x * (7 * x + 1) ≤ c * (4 * x ^ 2 + 11 * x + 1) → c ≤ 3 / 2 →
        (12 / 5 ≤ x ∧ x ≤ 5 / 2 ∧ c = 7 / 8 ∨ 5 / 2 ≤ x ∧ x ≤ 14 / 5 ∧ c = 11 / 12 ∨
          14 / 5 ≤ x ∧ x ≤ 4 ∧ c = 13 / 12 ∨ 4 ≤ x ∧ x ≤ 9 ∧ c = 3 / 2) →
        G x a b (hsUhat x b) < 0 := by
      intro c hc hc32 hrow
      obtain ⟨h1, h2⟩ := hl0_strip_face_le hx hal ham hc hc32 hb'
      exact hstrip ham c hc hc32 hrow h1 h2
    have := (by
      rcases le_or_gt x (5 / 2) with h1 | h1
      · exact key (7 / 8)
          (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 12 / 5) (by linarith : (0 : ℝ) ≤ 5 / 2 - x)])
          (by norm_num) (Or.inl ⟨hx, h1, rfl⟩)
      rcases le_or_gt x (14 / 5) with h2 | h2
      · exact key (11 / 12)
          (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 5 / 2) (by linarith : (0 : ℝ) ≤ 14 / 5 - x)])
          (by norm_num) (Or.inr (Or.inl ⟨h1.le, h2, rfl⟩))
      rcases le_or_gt x 4 with h3 | h3
      · exact key (13 / 12)
          (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 14 / 5) (by linarith : (0 : ℝ) ≤ 4 - x)])
          (by norm_num) (Or.inr (Or.inr (Or.inl ⟨h2.le, h3, rfl⟩)))
      · exact key (3 / 2)
          (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x - 4) (by linarith : (0 : ℝ) ≤ 9 - x)])
          (by norm_num) (Or.inr (Or.inr (Or.inr ⟨h3.le, hx9, rfl⟩))) : G x a b (hsUhat x b) < 0)
    linarith
  · have hu := hl0_ubar_le_ub hx hx9 hax hxb hb'
    have hm := hmono _ _ hb43 hxb hu
    have hb32 : b ≤ x + 3 / 2 * (a - 1) :=
      hl0_slope_le (by linarith) ha1.le
        (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x) (by linarith : (0 : ℝ) ≤ 9 - x)]) hb'
    have := hlarge ham.le hb0 hb32
    linarith

/-- **The outer `τ = T` test** (`OUTER_SCALE_LARGE_RATIO_SIGN` (7)). -/
theorem hl0_outer_T {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : (22 * x + 20) / 55 ≤ a)
    (hax : a ≤ x) (hb : x + 4 * x * (a - 1) / (5 * x + 4) ≤ b)
    (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hl0OT x a b (hsUbar x b) < 0 := by
  apply hl0_outer_gen (G := hl0OT) hx hx9 hal hax hb hb'
  · intro u u' h43 hxb hu; exact hl0_OT_mono hx hx9 (by linarith) hax hxb h43 hu
  · intro ham hb0 hb32
    exact hl0_OT_neg (U := x + 74) (V := 100) (by linarith) (by linarith) (by linarith)
      (by norm_num) (hl0_largeT hx hx9 ham hax hb0 hb32)
  · intro ham c _ _ hrow hbc hbc2
    have hb0 := (hl0_outer_dom hx hal hax hb).2.1
    have hc := hl0_strip_chord_T hx hx9 hal ham hb0 hbc hbc2
    have h0 := hl0ST_0_neg hx hx9 hal ham
    rcases hrow with ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩
    · linarith [max_lt h0 (hl0ST_1_neg h1 h2 hal ham)]
    · linarith [max_lt h0 (hl0ST_2_neg h1 h2 hal ham)]
    · linarith [max_lt h0 (hl0ST_3_neg h1 h2 hal ham)]
    · linarith [max_lt h0 (hl0ST_4_neg h1 h2 hal ham)]

/-- **The outer `τ = 8T/9` test** (`OUTER_SCALE_LARGE_RATIO_SIGN` (7)). -/
theorem hl0_outer_8 {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : (22 * x + 20) / 55 ≤ a)
    (hax : a ≤ x) (hb : x + 4 * x * (a - 1) / (5 * x + 4) ≤ b)
    (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hl0O8 x a b (hsUbar x b) < 0 := by
  apply hl0_outer_gen (G := hl0O8) hx hx9 hal hax hb hb'
  · intro u u' h43 hxb hu; exact hl0_O8_mono hx hx9 (by linarith) hax hxb h43 hu
  · intro ham hb0 hb32
    exact hl0_O8_neg (U := x + 74) (V := 100) (by linarith) (by linarith) (by linarith)
      (by norm_num) (hl0_large8 hx hx9 ham hax hb0 hb32)
  · intro ham c _ _ hrow hbc hbc2
    have hb0 := (hl0_outer_dom hx hal hax hb).2.1
    have hc := hl0_strip_chord_8 hx hx9 hal ham hb0 hbc hbc2
    have h0 := hl0S8_0_neg hx hx9 hal ham
    rcases hrow with ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩
    · linarith [max_lt h0 (hl0S8_1_neg h1 h2 hal ham)]
    · linarith [max_lt h0 (hl0S8_2_neg h1 h2 hal ham)]
    · linarith [max_lt h0 (hl0S8_3_neg h1 h2 hal ham)]
    · linarith [max_lt h0 (hl0S8_4_neg h1 h2 hal ham)]

/-- **The outer `τ = 2` test** (`OUTER_SCALE_LARGE_RATIO_SIGN` (7)). -/
theorem hl0_outer_2 {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : (22 * x + 20) / 55 ≤ a)
    (hax : a ≤ x) (hb : x + 4 * x * (a - 1) / (5 * x + 4) ≤ b)
    (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hl0O2 x a b (hsUbar x b) < 0 := by
  apply hl0_outer_gen (G := hl0O2) hx hx9 hal hax hb hb'
  · intro u u' h43 hxb hu; exact hl0_O2_mono hx hx9 (by linarith) hax hxb h43 hu
  · intro ham hb0 hb32
    exact hl0_O2_neg (U := x + 74) (V := 100) (by linarith) (by linarith) (by linarith)
      (by norm_num) (hl0_large2 hx hx9 ham hax hb0 hb32)
  · intro ham c _ _ hrow hbc _
    have hb0 := (hl0_outer_dom hx hal hax hb).2.1
    have hc := hl0_strip_chord_2 hx hx9 hal ham hb0 hbc
    have h0 := hl0S2_0_neg hx hx9 hal ham
    rcases hrow with ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩
    · linarith [max_lt h0 (hl0S2_1_neg h1 h2 hal ham)]
    · linarith [max_lt h0 (hl0S2_2_neg h1 h2 hal ham)]
    · linarith [max_lt h0 (hl0S2_3_neg h1 h2 hal ham)]
    · linarith [max_lt h0 (hl0S2_4_neg h1 h2 hal ham)]

/-- **The outer face, three tests** (`OUTER_SCALE_LARGE_RATIO_SIGN` (7); inventory HS-S01 B9): the
statement of `hs0_outer_tests`. -/
theorem hs0_outer_tests_proof {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (hal : (22 * x + 20) / 55 ≤ al) (hax : al ≤ x)
    (hb : x + 4 * x * (al - 1) / (5 * x + 4) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    hsF x be al (hsUbar x be) (1 / 7) (7 * hsRA al be) 0 (1 / 2) < 0 ∧
      hsF x be al (hsUbar x be) (1 / 7) (8 * (7 * hsRA al be) / 9) (-1 / 9) (1 / 2) < 0 ∧
      hsF x be al (hsUbar x be) (1 / 7) 2 (5 / (2 * (7 * hsRA al be)) - 11 / 9) (1 / 2) < 0 :=
  ⟨hl0_outer_T hx hx9 hal hax hb hb', hl0_outer_8 hx hx9 hal hax hb hb',
    hl0_outer_2 hx hx9 hal hax hb hb'⟩

end SmoothedOctagon
