module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB0a
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB0b
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB0c
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB0d
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB1a
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB1b
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3OuterB1c

/-!
# Heavy leaf `hs3_outer_face` (`DISPLACEMENT_OUTER_FACE` (4)-(21), inventory HS-S3 R40-R44)

On `2 ≤ x ≤ 13/6`, `a₀(x) = (100x + 77)/240 ≤ α ≤ x`, `β = x(1 + g(α - 1))`, `1/4 ≤ g ≤ 115/304`, at
`q = 1/7`, `u = ū(x, β)`: `F₀ < 0` and `F₁ < 0`.

Route: as in the note, the logarithm is replaced by `L*` (`hs3_log_maj`, `y ≤ 6/7` since `β ≤ 2α`) and
the rational test is cleared; then, instead of expanding the note's numerators `N_i(h, v, t)`
(1173 and 795 terms), the cleared numerator is kept as a polynomial of degree `6 - i` in `β` with
coefficients in `(x, α)` (`hh3_o{i}_clear`), `β = U - W y` with `y ∈ [0, 1]`, Bernstein positivity in
`y` with abstract coefficients (`hh3_bern6`, `hh3_bern5`), and each Bernstein coefficient is certified
separately in `(h, v)` (`hh3_o{i}_b{j}_pos`).

## Main API

* `hh3_outer_F0`, `hh3_outer_F1`.
* `hs3_outer_face_proof`: the statement of `hs3_outer_face`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- Shape facts on the outer domain: `α > 1`, `β > 1`, `β ≤ 2α`. -/
theorem hh3_outer_dom {x al g : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : (100 * x + 77) / 240 ≤ al)
    (hax : al ≤ x) (hg : 1 / 4 ≤ g) (hg' : g ≤ 115 / 304) :
    1 < al ∧ 1 < x * (1 + g * (al - 1)) ∧ x * (1 + g * (al - 1)) ≤ 2 * al := by
  have hal1 : 1 < al := by linarith
  have h1 : 0 ≤ g * (al - 1) := by nlinarith
  refine ⟨hal1, by nlinarith, ?_⟩
  have h2 : 0 ≤ x * (al - 1) * (115 / 304 - g) := by
    have : 0 ≤ x * (al - 1) := by nlinarith
    nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hal) (by linarith : (0 : ℝ) ≤ 608 - 115 * x),
    mul_nonneg (by linarith : (0 : ℝ) ≤ x - 2) (by linarith : (0 : ℝ) ≤ 13 / 6 - x)]

/-- The log argument `y = 2q/r_A` at `q = 1/7` is at most `6/7` when `β ≤ 2α`. -/
theorem hh3_outer_y {al be : ℝ} (hal1 : 1 < al) (hbe1 : 1 < be) (hbe2 : be ≤ 2 * al) :
    2 * (1 / 7) / hsRA al be ≤ 6 / 7 := by
  have e : 2 * (1 / 7 : ℝ) / hsRA al be = 2 * (al + be) / (7 * al) := by
    unfold hsRA; field_simp
  rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- The cleared numerator of the outer test `F̄_0` is positive. -/
theorem hh3_outer_M0 {x al g : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : (100 * x + 77) / 240 ≤ al)
    (hax : al ≤ x) (hg : 1 / 4 ≤ g) (hg' : g ≤ 115 / 304) :
    0 < hh3O0m0 x al + hh3O0m1 x al * (x * (1 + g * (al - 1))) + hh3O0m2 x al * (x * (1 + g * (al - 1))) ^ (2 : ℕ) + hh3O0m3 x al * (x * (1 + g * (al - 1))) ^ (3 : ℕ) + hh3O0m4 x al * (x * (1 + g * (al - 1))) ^ (4 : ℕ) + hh3O0m5 x al * (x * (1 + g * (al - 1))) ^ (5 : ℕ) + hh3O0m6 x al * (x * (1 + g * (al - 1))) ^ (6 : ℕ) := by
  have hy0 : 0 ≤ (115 / 304 - g) * 304 / 39 := by linarith
  have hy1 : (115 / 304 - g) * 304 / 39 ≤ 1 := by linarith
  have hb : x * (1 + g * (al - 1)) = x * (189 + 115 * al) / 304 - 39 * x * (al - 1) / 304 * ((115 / 304 - g) * 304 / 39) := by ring
  rw [hb, hh3_o0_shift]
  apply hh3_bern6 hy0 hy1
  · rw [hh3_o0_b0_eq]; exact hh3_o0_b0_pos hx hx2 hal hax
  · rw [hh3_o0_b1_eq]; exact hh3_o0_b1_pos hx hx2 hal hax
  · rw [hh3_o0_b2_eq]; exact hh3_o0_b2_pos hx hx2 hal hax
  · rw [hh3_o0_b3_eq]; exact hh3_o0_b3_pos hx hx2 hal hax
  · rw [hh3_o0_b4_eq]; exact hh3_o0_b4_pos hx hx2 hal hax
  · rw [hh3_o0_b5_eq]; exact hh3_o0_b5_pos hx hx2 hal hax
  · rw [hh3_o0_b6_eq]; exact hh3_o0_b6_pos hx hx2 hal hax

/-- The outer test `F_0` is negative on the outer face. -/
theorem hh3_outer_F0 {x al g : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : (100 * x + 77) / 240 ≤ al)
    (hax : al ≤ x) (hg : 1 / 4 ≤ g) (hg' : g ≤ 115 / 304) :
    hs3F0 x (x * (1 + g * (al - 1))) al (hsUO x (x * (1 + g * (al - 1)))) (1 / 7) < 0 := by
  obtain ⟨hal1, hbe1, hbe2⟩ := hh3_outer_dom hx hx2 hal hax hg hg'
  have hM := hh3_outer_M0 hx hx2 hal hax hg hg'
  set be := x * (1 + g * (al - 1)) with hbe_def
  have hyp : 0 < 2 * (1 / 7) / hsRA al be := by unfold hsRA; positivity
  have hy7 : 2 * (1 / 7) / hsRA al be ≤ 6 / 7 := hh3_outer_y hal1 hbe1 hbe2
  have hlog := hs3_log_maj hyp hy7
  unfold hs3F0
  refine lt_of_le_of_lt (hh3_fn_log_mono _ _ _ _ _ _ hlog) ?_
  have hD : 0 < 61740000 * al ^ 5 * (al + be) * (5 * al - 1) * (19 * al + 5 * be) * (be - 1) * (1 + x) * (35 * x + 13) := by
    have : 0 < 5 * al - 1 := by linarith
    have : 0 < be - 1 := by linarith
    positivity
  have hcl := hh3_o0_clear x al be (by linarith) hal1 hbe1
  by_contra hc
  push_neg at hc
  have := mul_nonneg hc hD.le
  linarith

/-- The cleared numerator of the outer test `F̄_1` is positive. -/
theorem hh3_outer_M1 {x al g : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : (100 * x + 77) / 240 ≤ al)
    (hax : al ≤ x) (hg : 1 / 4 ≤ g) (hg' : g ≤ 115 / 304) :
    0 < hh3O1m0 x al + hh3O1m1 x al * (x * (1 + g * (al - 1))) + hh3O1m2 x al * (x * (1 + g * (al - 1))) ^ (2 : ℕ) + hh3O1m3 x al * (x * (1 + g * (al - 1))) ^ (3 : ℕ) + hh3O1m4 x al * (x * (1 + g * (al - 1))) ^ (4 : ℕ) + hh3O1m5 x al * (x * (1 + g * (al - 1))) ^ (5 : ℕ) := by
  have hy0 : 0 ≤ (115 / 304 - g) * 304 / 39 := by linarith
  have hy1 : (115 / 304 - g) * 304 / 39 ≤ 1 := by linarith
  have hb : x * (1 + g * (al - 1)) = x * (189 + 115 * al) / 304 - 39 * x * (al - 1) / 304 * ((115 / 304 - g) * 304 / 39) := by ring
  rw [hb, hh3_o1_shift]
  apply hh3_bern5 hy0 hy1
  · rw [hh3_o1_b0_eq]; exact hh3_o1_b0_pos hx hx2 hal hax
  · rw [hh3_o1_b1_eq]; exact hh3_o1_b1_pos hx hx2 hal hax
  · rw [hh3_o1_b2_eq]; exact hh3_o1_b2_pos hx hx2 hal hax
  · rw [hh3_o1_b3_eq]; exact hh3_o1_b3_pos hx hx2 hal hax
  · rw [hh3_o1_b4_eq]; exact hh3_o1_b4_pos hx hx2 hal hax
  · rw [hh3_o1_b5_eq]; exact hh3_o1_b5_pos hx hx2 hal hax

/-- The outer test `F_1` is negative on the outer face. -/
theorem hh3_outer_F1 {x al g : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : (100 * x + 77) / 240 ≤ al)
    (hax : al ≤ x) (hg : 1 / 4 ≤ g) (hg' : g ≤ 115 / 304) :
    hs3F1 x (x * (1 + g * (al - 1))) al (hsUO x (x * (1 + g * (al - 1)))) (1 / 7) < 0 := by
  obtain ⟨hal1, hbe1, hbe2⟩ := hh3_outer_dom hx hx2 hal hax hg hg'
  have hM := hh3_outer_M1 hx hx2 hal hax hg hg'
  set be := x * (1 + g * (al - 1)) with hbe_def
  have hyp : 0 < 2 * (1 / 7) / hsRA al be := by unfold hsRA; positivity
  have hy7 : 2 * (1 / 7) / hsRA al be ≤ 6 / 7 := hh3_outer_y hal1 hbe1 hbe2
  have hlog := hs3_log_maj hyp hy7
  unfold hs3F1
  refine lt_of_le_of_lt (hh3_fn_log_mono _ _ _ _ _ _ hlog) ?_
  have hD : 0 < 8820000 * al ^ 4 * (al + be) * (5 * al - 1) * (19 * al + 5 * be) * (be - 1) * (1 + x) * (35 * x + 13) := by
    have : 0 < 5 * al - 1 := by linarith
    have : 0 < be - 1 := by linarith
    positivity
  have hcl := hh3_o1_clear x al be (by linarith) hal1 hbe1
  by_contra hc
  push_neg at hc
  have := mul_nonneg hc hD.le
  linarith

/-- **`hs3_outer_face`**, with the statement of the skeleton leaf. -/
theorem hs3_outer_face_proof {x al g : ℝ} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6)
    (hal : (100 * x + 77) / 240 ≤ al) (hax : al ≤ x) (hg : 1 / 4 ≤ g) (hg' : g ≤ 115 / 304) :
    hs3F0 x (x * (1 + g * (al - 1))) al (hsUO x (x * (1 + g * (al - 1)))) (1 / 7) < 0 ∧
      hs3F1 x (x * (1 + g * (al - 1))) al (hsUO x (x * (1 + g * (al - 1)))) (1 / 7) < 0 :=
  ⟨hh3_outer_F0 hx hx2 hal hax hg hg', hh3_outer_F1 hx hx2 hal hax hg hg'⟩

end SmoothedOctagon
