module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.CentralFace.Tests
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.LargeShape
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.OuterFace.Strip.Tests

/-!
# Smaller-short window, large ratio: the three face signs

The face signs `lgr_central_tau_two`, `lgr_central_duration` and `lgr_outer_tests` of the
large-ratio bound, proved with their exact statements as `*_proof`:

* the central `τ = 2` test: beta convexity, the lower face `β = x` and the exact upper boundary
  (`lgr_central_two`, `SmallerShort/LargeRatio/CentralFace/`);
* the central `τ = T` and `τ = 8T/9` tests, by the same faces (`lgr_central_T`, `lgr_central_8`);
* the three outer tests at `q = 1/7`: incoming monotonicity and the two majorants
  (`SmallerShort/LargeRatio/OuterFace`), the cubic comparison on the large shapes `α ≥ (2x + 3)/5`
  (`SmallerShort/LargeRatio/OuterFace/LargeShape`), the chord bound and the two beta boundaries on the strip
  (`SmallerShort/LargeRatio/OuterFace/Strip/Tests`); assembled here (`lgr_outer_T`, `lgr_outer_8`, `lgr_outer_2`).

The central upper-boundary signs follow from the expansion in `x - 12/5`
after normalizing alpha to its order interval. Six quadratic minorants and
endpoint power bounds give nonnegative coefficients. The outer strip signs use the same power bounds; the large-shape comparison
uses coefficient-list identities and the coefficient bound `lgrLow`.

## Main API

* `lgr_central_tau_two_proof`, `lgr_central_duration_proof`, `lgr_outer_tests_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **The central face, `τ = 2` test**: the statement of `lgr_central_tau_two`. -/
theorem lgr_central_tau_two_proof {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hal' : al ≤ (5 * x + 4) / 12) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ssF x be al (ssUhat x be) (ssQc x al) 2
      (5 / (2 * (ssRA al be / ssQc x al)) - 11 / 9) (1 / 2) < 0 :=
  lgr_central_two hx hx9 hal hal' hxb hb

/-- **The central face, `τ = T` and `τ = 8T/9` tests**: the statement of
`lgr_central_duration`. -/
theorem lgr_central_duration_proof {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : 1 ≤ al)
    (hal' : al ≤ (5 * x + 4) / 12) (hxb : x ≤ be)
    (hb : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ssF x be al (ssUhat x be) (ssQc x al) (ssRA al be / ssQc x al) 0 (1 / 2) < 0 ∧
      ssF x be al (ssUhat x be) (ssQc x al) (8 * (ssRA al be / ssQc x al) / 9) (-1 / 9) (1 / 2) <
        0 :=
  ⟨lgr_central_T hx hx9 hal hal' hxb hb, lgr_central_8 hx hx9 hal hal' hxb hb⟩

/-! ### The outer face -/

/-- The strong-order slope `c₀(x)` is at most a constant `c` where `x(7x + 1) ≤ c(4x² + 11x + 1)`. -/
theorem lgr_slope_le {x a b c : ℝ} (hx : 0 < x) (ha : 1 ≤ a)
    (hc : x * (7 * x + 1) ≤ c * (4 * x ^ 2 + 11 * x + 1))
    (hb : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) : b ≤ x + c * (a - 1) := by
  have hR : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  have : x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1) ≤ c * (a - 1) := by
    rw [div_le_iff₀ hR]
    have := mul_le_mul_of_nonneg_right hc (by linarith : (0 : ℝ) ≤ a - 1)
    nlinarith
  linarith

/-- The outer domain facts: `α > 1`, `β ≥ x`, `β ≥ x + (3/5)(α - 1)`, `4α ≤ 3β`. -/
theorem lgr_outer_dom {x a b : ℝ} (hx : 12 / 5 ≤ x) (hal : (22 * x + 20) / 55 ≤ a) (hax : a ≤ x)
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

/-- The outer test at the actual shape, split into large shapes and the strip. -/
theorem lgr_outer_gen {G : ℝ → ℝ → ℝ → ℝ → ℝ} {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (hal : (22 * x + 20) / 55 ≤ a) (hax : a ≤ x) (hb : x + 4 * x * (a - 1) / (5 * x + 4) ≤ b)
    (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1))
    (hmono : ∀ u u', 4 * a ≤ 3 * b → x ≤ b → u ≤ u' → G x a b u ≤ G x a b u')
    (hlarge : (2 * x + 3) / 5 ≤ a → x + 3 / 5 * (a - 1) ≤ b → b ≤ x + 3 / 2 * (a - 1) →
      G x a b ((x + 74) / 100) < 0)
    (hstrip : a ≤ (2 * x + 3) / 5 → G x a b (ssUhat x b) < 0) :
    G x a b (ssUbar x b) < 0 := by
  obtain ⟨ha1, hb0, hxb, hb43⟩ := lgr_outer_dom hx hal hax hb
  rcases le_or_gt a ((2 * x + 3) / 5) with ham | ham
  · have hu := lgro_ubar_le_uhat hx hx9 ham hxb hb'
    have hm := hmono _ _ hb43 hxb hu
    exact lt_of_le_of_lt hm (hstrip ham)
  · have hu := lgr_ubar_le_ub hx hx9 hax hxb hb'
    have hm := hmono _ _ hb43 hxb hu
    have hb32 : b ≤ x + 3 / 2 * (a - 1) :=
      lgr_slope_le (by linarith) ha1.le
        (by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x) (by linarith : (0 : ℝ) ≤ 9 - x)]) hb'
    have := hlarge ham.le hb0 hb32
    linarith

/-- **The outer `τ = T` test** at `u = ū(x, β)`, from the two regions of `lgr_outer_gen`. -/
theorem lgr_outer_T {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : (22 * x + 20) / 55 ≤ a)
    (hax : a ≤ x) (hb : x + 4 * x * (a - 1) / (5 * x + 4) ≤ b)
    (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    lgrOT x a b (ssUbar x b) < 0 := by
  apply lgr_outer_gen (G := lgrOT) hx hx9 hal hax hb hb'
  · intro u u' h43 hxb hu; exact lgr_OT_mono hx hx9 (by linarith) hax hxb h43 hu
  · intro ham hb0 hb32
    exact lgr_OT_neg (U := x + 74) (V := 100) (by linarith) (by linarith) (by linarith)
      (by norm_num) (lgr_largeT hx hx9 ham hax hb0 hb32)
  · intro ham
    exact S0Outer.stripT_neg hx hx9 hal ham (lgr_outer_dom hx hal hax hb).2.1 hb'

/-- **The outer `τ = 8T/9` test** at `u = ū(x, β)`, from the two regions of `lgr_outer_gen`. -/
theorem lgr_outer_8 {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : (22 * x + 20) / 55 ≤ a)
    (hax : a ≤ x) (hb : x + 4 * x * (a - 1) / (5 * x + 4) ≤ b)
    (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    lgrO8 x a b (ssUbar x b) < 0 := by
  apply lgr_outer_gen (G := lgrO8) hx hx9 hal hax hb hb'
  · intro u u' h43 hxb hu; exact lgr_O8_mono hx hx9 (by linarith) hax hxb h43 hu
  · intro ham hb0 hb32
    exact lgr_O8_neg (U := x + 74) (V := 100) (by linarith) (by linarith) (by linarith)
      (by norm_num) (lgr_large8 hx hx9 ham hax hb0 hb32)
  · intro ham
    exact S0Outer.strip8_neg hx hx9 hal ham (lgr_outer_dom hx hal hax hb).2.1 hb'

/-- **The outer `τ = 2` test** at `u = ū(x, β)`, from the two regions of `lgr_outer_gen`. -/
theorem lgr_outer_2 {x a b : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9) (hal : (22 * x + 20) / 55 ≤ a)
    (hax : a ≤ x) (hb : x + 4 * x * (a - 1) / (5 * x + 4) ≤ b)
    (hb' : b ≤ x + x * (7 * x + 1) * (a - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    lgrO2 x a b (ssUbar x b) < 0 := by
  apply lgr_outer_gen (G := lgrO2) hx hx9 hal hax hb hb'
  · intro u u' h43 hxb hu; exact lgr_O2_mono hx hx9 (by linarith) hax hxb h43 hu
  · intro ham hb0 hb32
    exact lgr_O2_neg (U := x + 74) (V := 100) (by linarith) (by linarith) (by linarith)
      (by norm_num) (lgr_large2 hx hx9 ham hax hb0 hb32)
  · intro ham
    exact S0Outer.strip2_neg hx hx9 hal ham (lgr_outer_dom hx hal hax hb).2.1 hb'

/-- **The outer face, three tests**: the statement of `lgr_outer_tests`. -/
theorem lgr_outer_tests_proof {x al be : ℝ} (hx : 12 / 5 ≤ x) (hx9 : x ≤ 9)
    (hal : (22 * x + 20) / 55 ≤ al) (hax : al ≤ x)
    (hb : x + 4 * x * (al - 1) / (5 * x + 4) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ssF x be al (ssUbar x be) (1 / 7) (7 * ssRA al be) 0 (1 / 2) < 0 ∧
      ssF x be al (ssUbar x be) (1 / 7) (8 * (7 * ssRA al be) / 9) (-1 / 9) (1 / 2) < 0 ∧
      ssF x be al (ssUbar x be) (1 / 7) 2 (5 / (2 * (7 * ssRA al be)) - 11 / 9) (1 / 2) < 0 :=
  ⟨lgr_outer_T hx hx9 hal hax hb hb', lgr_outer_8 hx hx9 hal hax hb hb',
    lgr_outer_2 hx hx9 hal hax hb hb'⟩

end SmoothedOctagon
