module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.LowerTerminal
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.OuterFace.SmallShape.Norm

/-!
# Smaller-short window, upper ratio: the lower-shape terminal in the coordinates of the face sign

On the curve `α = a_f(x)`, `c = c_+(x) = (24x + 51)/128`, `u = u_s`, `r = r_f = 84/(36x + 25)`,
the outer test with a constant multiplier `n` is the closed-form function `R_n` of `OuterFace/LowerTerminal`;
with `m₀ ≥ n`, `w ≤ 3/4` and `H₁ - H₀ = (2Z - 7)(Z - 4)(w - 3/4)/(4Z) ≤ 0` both outer tests are
negative there.

## Main API

* `ur_link_V`, `ur_link`: the closed forms.
* `ur_term_r`: both tests are negative on the terminal curve.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- On the curve, `u_s - 3/4 = V(r_f)`. -/
theorem ur_link_V {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) :
    ssUs (7 / (3 * r) - 25 / 36) ((7 / (3 * r) - 25 / 36) +
      (24 * (7 / (3 * r) - 25 / 36) + 51) / 128 * (1 / r - 1)) = 3 / 4 + urVc r := by
  have hr : 0 < r := by linarith
  have hK := (ur_KJ_pos h0 h1).1
  unfold urKc at hK
  have hg : 0 < 84 + 11 * r := by linarith
  have hS : 1 + (7 / (3 * r) - 25 / 36) = (84 + 11 * r) / (36 * r) := by field_simp; ring
  have hx1 : 7 / (3 * r) - 25 / 36 - 1 = (84 - 61 * r) / (36 * r) := by field_simp; ring
  have hb1 : (7 / (3 * r) - 25 / 36) + (24 * (7 / (3 * r) - 25 / 36) + 51) / 128 * (1 / r - 1) - 1 =
      (504 + 2493 * r - 2261 * r ^ 2) / (1152 * r ^ 2) := by
    field_simp; ring
  have hbx : (7 / (3 * r) - 25 / 36) + (24 * (7 / (3 * r) - 25 / 36) + 51) / 128 * (1 / r - 1) -
      (7 / (3 * r) - 25 / 36) = (24 * (7 / (3 * r) - 25 / 36) + 51) / 128 * (1 / r - 1) := by ring
  unfold ssUs urVc urFc urqc urKc
  rw [hb1, hx1, hS, hbx]
  have hK' := hK.ne'
  have hK'' : 504 + r * 2493 - r ^ 2 * 2261 ≠ 0 := by
    rw [show 504 + r * 2493 - r ^ 2 * 2261 = 504 + 2493 * r - 2261 * r ^ 2 by ring]; exact hK'
  have hg' := hg.ne'
  have hg'' : 84 + r * 11 ≠ 0 := by linarith
  field_simp
  ring

/-- The closed form of the test with constant multiplier on the curve. -/
theorem ur_link {n CA CL q0 q1 : ℝ} {As Ls Qs : ℝ → ℝ} {r V : ℝ} (h0 : 3 / 4 ≤ r)
    (_h1 : r ≤ 49 / 60)
    (hrat : ∀ V : ℝ, 6 / 7 + (3 / 4 + V - 1) * urZr (7 / (3 * r) - 25 / 36)
        ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) r + 1 / urZr (7 / (3 * r) - 25 / 36)
        ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) r - urELr (7 / (3 * r) - 25 / 36)
        ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) (3 / 4 + V) r +
        n * (urWr (7 / (3 * r) - 25 / 36) ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) (3 / 4 + V) r /
          49 - 3 / 4) =
        Ls r / (CL * r ^ 2) + V * (As r / (CA * r ^ 2)) + Qs r / (q0 * r + q1) + urZi r) :
    urHt n (7 / (3 * r) - 25 / 36) ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) (3 / 4 + V) r =
      Ls r / (CL * r ^ 2) + V * (As r / (CA * r ^ 2)) + Qs r / (q0 * r + q1) + urZi r + urLg r := by
  have hr : 0 < r := by linarith
  have hZ : urZr (7 / (3 * r) - 25 / 36) ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) r =
      urJc r / (1152 * r) := by
    unfold urZr urJc; field_simp; ring
  unfold urHt urLg
  rw [← hrat V, hZ]

/-- The rational part of the closed form, `n = 63 / 25`. -/
theorem ur_rat_h {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) (V : ℝ) :
    6 / 7 + (3 / 4 + V - 1) * urZr (7 / (3 * r) - 25 / 36)
        ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) r + 1 / urZr (7 / (3 * r) - 25 / 36)
        ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) r - urELr (7 / (3 * r) - 25 / 36)
        ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) (3 / 4 + V) r +
        63 / 25 * (urWr (7 / (3 * r) - 25 / 36) ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) (3 / 4 + V) r /
          49 - 3 / 4) =
      urLsh r / (11147673600 * r ^ 2) + V * (urAsh r / (8360755200 * r ^ 2)) + urQsh r / (123200 * r + 940800) +
        urZi r := by
  have hr : 0 < r := by linarith
  have hJ := (ur_KJ_pos h0 h1).2
  unfold urJc at hJ
  have hZ : urZr (7 / (3 * r) - 25 / 36) ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) r =
      (504 + 3645 * r - 1109 * r ^ 2) / (1152 * r) := by
    unfold urZr; field_simp; ring
  have hS : 1 + (7 / (3 * r) - 25 / 36) = (84 + 11 * r) / (36 * r) := by field_simp; ring
  rw [hZ]
  unfold urELr urWr urDr urd1 urd2 urJ2 ssE0
  rw [hS]
  unfold urLsh urAsh urQsh urZi urJc
  have hJ' := hJ.ne'
  have hg : 84 + 11 * r ≠ 0 := by linarith
  have hg' : 84 + r * 11 ≠ 0 := by linarith
  have hq : 123200 * r + 940800 ≠ 0 := by linarith
  field_simp
  ring

/-- The rational part of the closed form, `n = 49 / 20`. -/
theorem ur_rat_l {r : ℝ} (h0 : 3 / 4 ≤ r) (h1 : r ≤ 49 / 60) (V : ℝ) :
    6 / 7 + (3 / 4 + V - 1) * urZr (7 / (3 * r) - 25 / 36)
        ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) r + 1 / urZr (7 / (3 * r) - 25 / 36)
        ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) r - urELr (7 / (3 * r) - 25 / 36)
        ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) (3 / 4 + V) r +
        49 / 20 * (urWr (7 / (3 * r) - 25 / 36) ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) (3 / 4 + V) r /
          49 - 3 / 4) =
      urLsl r / (80263249920 * r ^ 2) + V * (urAsl r / (60197437440 * r ^ 2)) + urQsl r / (887040 * r + 6773760) +
        urZi r := by
  have hr : 0 < r := by linarith
  have hJ := (ur_KJ_pos h0 h1).2
  unfold urJc at hJ
  have hZ : urZr (7 / (3 * r) - 25 / 36) ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128) r =
      (504 + 3645 * r - 1109 * r ^ 2) / (1152 * r) := by
    unfold urZr; field_simp; ring
  have hS : 1 + (7 / (3 * r) - 25 / 36) = (84 + 11 * r) / (36 * r) := by field_simp; ring
  rw [hZ]
  unfold urELr urWr urDr urd1 urd2 urJ2 ssE0
  rw [hS]
  unfold urLsl urAsl urQsl urZi urJc
  have hJ' := hJ.ne'
  have hg : 84 + 11 * r ≠ 0 := by linarith
  have hg' : 84 + r * 11 ≠ 0 := by linarith
  have hq : 887040 * r + 6773760 ≠ 0 := by linarith
  field_simp
  ring

/-- Changing the multiplier of the test. -/
theorem ur_Ht_m (m n x c u r : ℝ) :
    urHt m x c u r - urHt n x c u r = (m - n) * (urWr x c u r / 49 - 3 / 4) := by
  unfold urHt; ring

/-- **The lower-shape terminal** in the curve coordinate `r = r_f`: the multiplier
`m₀ = 4 - Z/2` is at least `n = 63/25` (`x ≤ 9/4`) or `n = 49/20` (`x ≥ 9/4`) and `w ≤ 3/4`, so
`H₀ ≤ R_n < 0`; and `H₁ - H₀ = (2Z - 7)(Z - 4)(w - 3/4)/(4Z) ≤ 0` for `2 ≤ Z ≤ 7/2`. -/
theorem ur_term_r {r : ℝ} (h0 : 420 / 557 ≤ r) (h1 : r ≤ 84 / 103) :
    urH0 (7 / (3 * r) - 25 / 36) ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128)
        (ssUs (7 / (3 * r) - 25 / 36) ((7 / (3 * r) - 25 / 36) +
          (24 * (7 / (3 * r) - 25 / 36) + 51) / 128 * (1 / r - 1))) r < 0 ∧
      urH1 (7 / (3 * r) - 25 / 36) ((24 * (7 / (3 * r) - 25 / 36) + 51) / 128)
        (ssUs (7 / (3 * r) - 25 / 36) ((7 / (3 * r) - 25 / 36) +
          (24 * (7 / (3 * r) - 25 / 36) + 51) / 128 * (1 / r - 1))) r < 0 := by
  have hr : 0 < r := by linarith
  have h0' : 3 / 4 ≤ r := by linarith
  have h1' : r ≤ 49 / 60 := by linarith
  set x := 7 / (3 * r) - 25 / 36 with hxdef
  set c := (24 * x + 51) / 128 with hcdef
  have hx : 13 / 6 ≤ x := by rw [hxdef, le_sub_iff_add_le, le_div_iff₀ (by positivity)]; nlinarith
  have hx2 : x ≤ 12 / 5 := by rw [hxdef, sub_le_iff_le_add, div_le_iff₀ (by positivity)]; nlinarith
  have hc : 5 / 8 ≤ c := by rw [hcdef]; linarith
  have hc2 : c ≤ 7 / 8 := by rw [hcdef]; linarith
  have hrf : 84 / (36 * x + 25) = r := by rw [hxdef]; field_simp; ring
  rw [ur_link_V h0' h1']
  obtain ⟨-, hV⟩ := ur_V_bounds h0' h1'
  have hu := (ur_V_bounds h0' h1').1
  have hw := (ur_af_ELw hx hx2 hc hc2 (u := 3 / 4 + urVc r) (by linarith) (by linarith)).2
  rw [hrf] at hw
  -- the multiplier `m₀ = 4 - Z/2`
  have hZ : urZr x c r = (864 * x ^ 2 + 15780 * x + 191) / (128 * (36 * x + 25)) := by
    rw [← hrf]; unfold urZr; rw [hcdef]; field_simp; ring
  have hZ0 : 2 ≤ urZr x c r ∧ urZr x c r ≤ 7 / 2 := by
    rw [hZ, le_div_iff₀ (by positivity), div_le_iff₀ (by positivity)]
    constructor <;> nlinarith
  have hH0 : urH0 x c (3 / 4 + urVc r) r < 0 := by
    rcases le_total x (9 / 4) with hx9 | hx9
    · have hm : 63 / 25 ≤ 4 - urZr x c r / 2 := by
        have : urZr x c r ≤ 74 / 25 := by
          rw [hZ, div_le_iff₀ (by positivity)]; nlinarith
        linarith
      have e := ur_Ht_m (4 - urZr x c r / 2) (63 / 25) x c (3 / 4 + urVc r) r
      have hle : (4 - urZr x c r / 2 - 63 / 25) * (urWr x c (3 / 4 + urVc r) r / 49 - 3 / 4) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have hR : urHt (63 / 25) x c (3 / 4 + urVc r) r = urRh r := by
        rw [ur_link h0' h1' (ur_rat_h h0' h1')]; rfl
      have := ur_Rh_le h0' h1
      unfold urH0
      linarith
    · have hr42 : r ≤ 42 / 53 := by
        rw [← hrf, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have hm : 49 / 20 ≤ 4 - urZr x c r / 2 := by
        have : urZr x c r ≤ 31 / 10 := by
          rw [hZ, div_le_iff₀ (by positivity)]; nlinarith
        linarith
      have e := ur_Ht_m (4 - urZr x c r / 2) (49 / 20) x c (3 / 4 + urVc r) r
      have hle : (4 - urZr x c r / 2 - 49 / 20) * (urWr x c (3 / 4 + urVc r) r / 49 - 3 / 4) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have hR : urHt (49 / 20) x c (3 / 4 + urVc r) r = urRl r := by
        rw [ur_link h0' h1' (ur_rat_l h0' h1')]; rfl
      have := ur_Rl_le h0' hr42
      unfold urH0
      linarith
  refine ⟨hH0, ?_⟩
  -- `H₁ - H₀ = (2Z - 7)(Z - 4)(w - 3/4)/(4Z) ≤ 0`
  have e := ur_Ht_m (7 / urZr x c r + 1 / 4) (4 - urZr x c r / 2) x c (3 / 4 + urVc r) r
  have hm : 0 ≤ 7 / urZr x c r + 1 / 4 - (4 - urZr x c r / 2) := by
    have hZp : 0 < urZr x c r := by linarith
    have : 7 / urZr x c r + 1 / 4 - (4 - urZr x c r / 2) =
        (2 * urZr x c r - 7) * (urZr x c r - 4) / (4 * urZr x c r) := by
      field_simp; ring
    rw [this]
    apply div_nonneg _ (by positivity)
    nlinarith
  have hle : (7 / urZr x c r + 1 / 4 - (4 - urZr x c r / 2)) *
      (urWr x c (3 / 4 + urVc r) r / 49 - 3 / 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hm (by linarith)
  unfold urH0 at hH0
  unfold urH1
  linarith

end SmoothedOctagon
