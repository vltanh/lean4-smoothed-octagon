module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Window.LogSecant
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Smaller-short window: second-order jets and the four primitive functions

A small calculus of second-order jets
(`SecondJet f f₁ f₂ x`: `f' = f₁` and `f₁' = f₂` at `x`) with the sum, product and chain rules, a
concave-minimum principle, and the four primitive functions of the score decomposition

`k(a) = a/162 + 161a³/1458 - 161a⁵/7290 - a³/(2(3 + a²))`, `g(a) = a/(2(3 + a²))`,
`p(a) = a²/(3 + a²)`, `q(a) = 1/(3 + a²)`,

with their derivatives and elementary bounds on the angle interval
`9/31 ≤ a ≤ 7/19`.

## Main API

* `SecondJet`, `SecondJet.add`, `SecondJet.sub`, `SecondJet.const_mul`, `SecondJet.mul`, `SecondJet.comp`.
* `jet_concave_lt`: `f'' ≤ 0` on `[a, b]` and `c < f a`, `c < f b` give `c < f` on `[a, b]`.
* `jet_anti_of`, `jet_mono_of`: monotonicity from a jet sign.
* `jetk`, `jetg`, `jetp`, `jetq` with derivatives `…1`, `…2`; jets `jet_k_jet`, …;
  bounds `jet_k1_neg`, `jet_k2_le`, `jet_k2_le'`, `jet_g_bounds`, `jet_p_bounds`,
  `jet_q_bounds`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-! ### Second-order jets -/

/-- A second-order jet at `x`: `f' = f₁` at `x` and `f₁' = f₂` at `x`. -/
def SecondJet (f f₁ f₂ : ℝ → ℝ) (x : ℝ) : Prop := HasDerivAt f (f₁ x) x ∧ HasDerivAt f₁ (f₂ x) x

namespace SecondJet

variable {f f₁ f₂ g g₁ g₂ : ℝ → ℝ} {x : ℝ}

theorem add (hf : SecondJet f f₁ f₂ x) (hg : SecondJet g g₁ g₂ x) :
    SecondJet (fun y => f y + g y) (fun y => f₁ y + g₁ y) (fun y => f₂ y + g₂ y) x :=
  ⟨hf.1.fun_add hg.1, hf.2.fun_add hg.2⟩

theorem sub (hf : SecondJet f f₁ f₂ x) (hg : SecondJet g g₁ g₂ x) :
    SecondJet (fun y => f y - g y) (fun y => f₁ y - g₁ y) (fun y => f₂ y - g₂ y) x :=
  ⟨hf.1.fun_sub hg.1, hf.2.fun_sub hg.2⟩

theorem const_mul (c : ℝ) (hf : SecondJet f f₁ f₂ x) :
    SecondJet (fun y => c * f y) (fun y => c * f₁ y) (fun y => c * f₂ y) x :=
  ⟨hf.1.const_mul c, hf.2.const_mul c⟩

theorem mul (hf : SecondJet f f₁ f₂ x) (hg : SecondJet g g₁ g₂ x) :
    SecondJet (fun y => f y * g y) (fun y => f₁ y * g y + f y * g₁ y)
      (fun y => f₂ y * g y + 2 * (f₁ y * g₁ y) + f y * g₂ y) x := by
  refine ⟨hf.1.fun_mul hg.1, ?_⟩
  have := (hf.2.fun_mul hg.1).fun_add (hf.1.fun_mul hg.2)
  convert this using 1
  ring

theorem comp {h h₁ h₂ : ℝ → ℝ} (hh : SecondJet h h₁ h₂ (f x)) (hf : SecondJet f f₁ f₂ x) :
    SecondJet (fun y => h (f y)) (fun y => h₁ (f y) * f₁ y)
      (fun y => h₂ (f y) * f₁ y ^ 2 + h₁ (f y) * f₂ y) x := by
  refine ⟨hh.1.comp x hf.1, ?_⟩
  refine ((hh.2.comp x hf.1).fun_mul hf.2).congr_deriv ?_
  simp only [Function.comp_apply]
  ring

end SecondJet

/-- **Concave minimum principle**: if `f'' ≤ 0` on `[a, b]` and `f` exceeds `c` at both ends, it
exceeds `c` on `[a, b]`. -/
theorem jet_concave_lt {f f₁ f₂ : ℝ → ℝ} {a b c : ℝ}
    (hJ : ∀ x ∈ Icc a b, SecondJet f f₁ f₂ x) (hneg : ∀ x ∈ Icc a b, f₂ x ≤ 0)
    (ha : c < f a) (hb : c < f b) {x : ℝ} (hx : x ∈ Icc a b) : c < f x := by
  have anti : ∀ u v, a ≤ u → u ≤ v → v ≤ b → f₁ v ≤ f₁ u := by
    intro u v hu huv hv
    have := ss_le_of_deriv (f := fun y => -f₁ y) (f' := fun y => -f₂ y) huv
      (fun z hz => (hJ z ⟨hu.trans hz.1, hz.2.trans hv⟩).2.fun_neg)
      (fun z hz => by
        have := hneg z ⟨hu.trans hz.1.le, hz.2.le.trans hv⟩
        linarith)
    linarith
  rcases le_or_gt 0 (f₁ x) with h0 | h0
  · have : f a ≤ f x := ss_le_of_deriv hx.1 (fun z hz => (hJ z ⟨hz.1, hz.2.trans hx.2⟩).1)
      (fun z hz => le_trans h0 (anti z x hz.1.le hz.2.le hx.2))
    linarith
  · have := ss_le_of_deriv (f := fun y => -f y) (f' := fun y => -f₁ y) hx.2
      (fun z hz => (hJ z ⟨hx.1.trans hz.1, hz.2⟩).1.fun_neg)
      (fun z hz => by
        have := anti x z hx.1 hz.1.le hz.2.le
        linarith)
    linarith

/-- A nonpositive derivative on `[a, b]` makes `f` nonincreasing there. -/
theorem jet_anti_of {f f₁ : ℝ → ℝ} {a b : ℝ} (hd : ∀ x ∈ Icc a b, HasDerivAt f (f₁ x) x)
    (hneg : ∀ x ∈ Icc a b, f₁ x ≤ 0) {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    f v ≤ f u := by
  have := ss_le_of_deriv (f := fun y => -f y) (f' := fun y => -f₁ y) huv
    (fun z hz => (hd z ⟨hu.trans hz.1, hz.2.trans hv⟩).fun_neg)
    (fun z hz => by
      have := hneg z ⟨hu.trans hz.1.le, hz.2.le.trans hv⟩
      linarith)
  linarith

/-- A nonnegative derivative on `[a, b]` makes `f` nondecreasing there. -/
theorem jet_mono_of {f f₁ : ℝ → ℝ} {a b : ℝ} (hd : ∀ x ∈ Icc a b, HasDerivAt f (f₁ x) x)
    (hpos : ∀ x ∈ Icc a b, 0 ≤ f₁ x) {u v : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    f u ≤ f v :=
  ss_le_of_deriv huv (fun z hz => hd z ⟨hu.trans hz.1, hz.2.trans hv⟩)
    (fun z hz => hpos z ⟨hu.trans hz.1.le, hz.2.le.trans hv⟩)

/-! ### The four primitive functions -/

/-- `k(a) = a/162 + 161a³/1458 - 161a⁵/7290 - a³/(2(3 + a²))`. -/
noncomputable def jetk (a : ℝ) : ℝ :=
  a / 162 + 161 * a ^ 3 / 1458 - 161 * a ^ 5 / 7290 - a ^ 3 / (2 * (3 + a ^ 2))

/-- `k'`. -/
noncomputable def jetk1 (a : ℝ) : ℝ :=
  -(161 * a ^ 8 + 483 * a ^ 6 - 729 * a ^ 4 + 2160 * a ^ 2 - 81) / (1458 * (a ^ 2 + 3) ^ 2)

/-- `k''`. -/
noncomputable def jetk2 (a : ℝ) : ℝ :=
  -a * (322 * a ^ 8 + 2415 * a ^ 6 + 4347 * a ^ 4 - 6534 * a ^ 2 + 6642) / (729 * (a ^ 2 + 3) ^ 3)

/-- `k'''`. -/
noncomputable def jetk3 (a : ℝ) : ℝ :=
  -(322 * a ^ 10 + 3703 * a ^ 8 + 15456 * a ^ 6 + 28269 * a ^ 4 - 30672 * a ^ 2 + 6642) /
    (243 * (a ^ 2 + 3) ^ 4)

/-- `g(a) = a/(2(3 + a²))`. -/
noncomputable def jetg (a : ℝ) : ℝ := a / (2 * (3 + a ^ 2))

/-- `g'`. -/
noncomputable def jetg1 (a : ℝ) : ℝ := (3 - a ^ 2) / (2 * (3 + a ^ 2) ^ 2)

/-- `g''`. -/
noncomputable def jetg2 (a : ℝ) : ℝ := a * (a ^ 2 - 9) / (3 + a ^ 2) ^ 3

/-- `p(a) = a²/(3 + a²)`. -/
noncomputable def jetp (a : ℝ) : ℝ := a ^ 2 / (3 + a ^ 2)

/-- `p'`. -/
noncomputable def jetp1 (a : ℝ) : ℝ := 6 * a / (3 + a ^ 2) ^ 2

/-- `p''`. -/
noncomputable def jetp2 (a : ℝ) : ℝ := 18 * (1 - a ^ 2) / (3 + a ^ 2) ^ 3

/-- `q(a) = 1/(3 + a²)`. -/
noncomputable def jetq (a : ℝ) : ℝ := 1 / (3 + a ^ 2)

/-- `q'`. -/
noncomputable def jetq1 (a : ℝ) : ℝ := -(2 * a) / (3 + a ^ 2) ^ 2

/-- `q''`. -/
noncomputable def jetq2 (a : ℝ) : ℝ := -(6 * (1 - a ^ 2)) / (3 + a ^ 2) ^ 3

/-- The derivative of `(3 + a²)ⁿ`. -/
private theorem jet_d_den (n : ℕ) (a : ℝ) :
    HasDerivAt (fun a : ℝ => (3 + a ^ 2) ^ n) (n * (3 + a ^ 2) ^ (n - 1) * (2 * a)) a := by
  have := ((hasDerivAt_pow 2 a).const_add 3).fun_pow n
  convert this using 1
  push_cast
  ring

theorem jet_k_jet (a : ℝ) : SecondJet jetk jetk1 jetk2 a := by
  have h3 : (0 : ℝ) < 3 + a ^ 2 := by positivity
  constructor
  · have := ((((hasDerivAt_id' a).div_const 162).fun_add
      (((hasDerivAt_pow 3 a).const_mul 161).div_const 1458)).fun_sub
      (((hasDerivAt_pow 5 a).const_mul 161).div_const 7290)).fun_sub
      ((hasDerivAt_pow 3 a).fun_div (((hasDerivAt_pow 2 a).const_add 3).const_mul 2)
        (by positivity))
    refine this.congr_deriv ?_
    unfold jetk1
    push_cast
    field_simp
    ring
  · have := ((((hasDerivAt_pow 8 a).const_mul 161).fun_add ((hasDerivAt_pow 6 a).const_mul 483)).fun_sub
      ((hasDerivAt_pow 4 a).const_mul 729)).fun_add ((hasDerivAt_pow 2 a).const_mul 2160)
    have := (this.sub_const 81).fun_neg.fun_div
      ((((hasDerivAt_pow 2 a).add_const 3).fun_pow 2).const_mul 1458) (by positivity)
    refine this.congr_deriv ?_
    unfold jetk2
    push_cast
    field_simp
    ring

theorem jet_k2_deriv (a : ℝ) : HasDerivAt jetk2 (jetk3 a) a := by
  have h3 : (0 : ℝ) < 3 + a ^ 2 := by positivity
  have hn := ((((hasDerivAt_pow 8 a).const_mul 322).fun_add ((hasDerivAt_pow 6 a).const_mul 2415)).fun_add
    ((hasDerivAt_pow 4 a).const_mul 4347)).fun_sub ((hasDerivAt_pow 2 a).const_mul 6534)
  have := ((hasDerivAt_id' a).fun_neg.fun_mul (hn.add_const 6642)).fun_div
    ((((hasDerivAt_pow 2 a).add_const 3).fun_pow 3).const_mul 729) (by positivity)
  refine this.congr_deriv ?_
  unfold jetk3
  push_cast
  field_simp
  ring

theorem jet_g_jet (a : ℝ) : SecondJet jetg jetg1 jetg2 a := by
  have h3 : (0 : ℝ) < 3 + a ^ 2 := by positivity
  constructor
  · have := (hasDerivAt_id' a).fun_div (((hasDerivAt_pow 2 a).const_add 3).const_mul 2)
      (by positivity)
    refine this.congr_deriv ?_
    unfold jetg1
    push_cast
    field_simp
    ring
  · have := ((hasDerivAt_pow 2 a).const_sub 3).fun_div
      ((((hasDerivAt_pow 2 a).const_add 3).fun_pow 2).const_mul 2) (by positivity)
    refine this.congr_deriv ?_
    unfold jetg2
    push_cast
    field_simp
    ring

theorem jet_p_jet (a : ℝ) : SecondJet jetp jetp1 jetp2 a := by
  have h3 : (0 : ℝ) < 3 + a ^ 2 := by positivity
  constructor
  · have := (hasDerivAt_pow 2 a).fun_div ((hasDerivAt_pow 2 a).const_add 3) (by positivity)
    refine this.congr_deriv ?_
    unfold jetp1
    push_cast
    field_simp
    ring
  · have := ((hasDerivAt_id' a).const_mul 6).fun_div
      (((hasDerivAt_pow 2 a).const_add 3).fun_pow 2) (by positivity)
    refine this.congr_deriv ?_
    unfold jetp2
    push_cast
    field_simp
    ring

theorem jet_q_jet (a : ℝ) : SecondJet jetq jetq1 jetq2 a := by
  have h3 : (0 : ℝ) < 3 + a ^ 2 := by positivity
  constructor
  · have := (hasDerivAt_const a (1 : ℝ)).fun_div ((hasDerivAt_pow 2 a).const_add 3)
      (by positivity)
    refine this.congr_deriv ?_
    unfold jetq1
    push_cast
    field_simp
    ring
  · have := ((hasDerivAt_id' a).const_mul 2).fun_neg.fun_div
      (((hasDerivAt_pow 2 a).const_add 3).fun_pow 2) (by positivity)
    refine this.congr_deriv ?_
    unfold jetq2
    push_cast
    field_simp
    ring

/-! ### Bounds on the angle interval -/

/-- `k' < 0` for `9/31 ≤ a ≤ 7/19`. -/
theorem jet_k1_neg {a : ℝ} (ha : 9 / 31 ≤ a) (ha' : a ≤ 7 / 19) : jetk1 a < 0 := by
  have hs : 81 / 961 ≤ a ^ 2 := by nlinarith
  have hs' : a ^ 2 ≤ 49 / 361 := by nlinarith
  have hn : 0 < 161 * a ^ 8 + 483 * a ^ 6 - 729 * a ^ 4 + 2160 * a ^ 2 - 81 := by
    have e : 161 * a ^ 8 + 483 * a ^ 6 - 729 * a ^ 4 + 2160 * a ^ 2 - 81 =
        161 * (a ^ 2) ^ 4 + 483 * (a ^ 2) ^ 3 + a ^ 2 * (2160 - 729 * a ^ 2) - 81 := by ring
    rw [e]
    have : 0 ≤ 161 * (a ^ 2) ^ 4 + 483 * (a ^ 2) ^ 3 := by positivity
    nlinarith
  unfold jetk1
  apply div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- `k''' < 0` for `0 ≤ a ≤ 7/19`. -/
theorem jet_k3_neg {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 7 / 19) : jetk3 a < 0 := by
  have hs' : a ^ 2 ≤ 49 / 361 := by nlinarith
  have hn : 0 < 322 * a ^ 10 + 3703 * a ^ 8 + 15456 * a ^ 6 + 28269 * a ^ 4 - 30672 * a ^ 2 + 6642 := by
    have : 0 ≤ 322 * a ^ 10 + 3703 * a ^ 8 + 15456 * a ^ 6 + 28269 * a ^ 4 := by positivity
    nlinarith
  unfold jetk3
  apply div_neg_of_neg_of_pos (by linarith) (by positivity)

/-- `k''` decreases on `[0, 7/19]`. -/
theorem jet_k2_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 7 / 19) : jetk2 b ≤ jetk2 a :=
  jet_anti_of (a := 0) (b := 7 / 19) (fun x _ => jet_k2_deriv x)
    (fun _ hx => (jet_k3_neg hx.1 hx.2).le) ha hab hb

/-- `k'' ≤ -2/25` for `9/31 ≤ a ≤ 7/19`, since `k''` decreases. -/
theorem jet_k2_le {a : ℝ} (ha : 9 / 31 ≤ a) (ha' : a ≤ 7 / 19) : jetk2 a ≤ -2 / 25 := by
  refine (jet_k2_anti (by norm_num) ha ha').trans ?_
  norm_num [jetk2]

/-- `k'' ≤ -9/100` for `1/3 ≤ a ≤ 7/19`, since `k''` decreases. -/
theorem jet_k2_le' {a : ℝ} (ha : 1 / 3 ≤ a) (ha' : a ≤ 7 / 19) : jetk2 a ≤ -9 / 100 := by
  refine (jet_k2_anti (by norm_num) ha ha').trans ?_
  norm_num [jetk2]

/-- The `g` bounds on the angle interval: `0 < g ≤ 3/50`, `0 < g' ≤ 31/200` (`≤ 3/20` for
`a ≥ 1/3`), `g'' ≤ 0`. -/
theorem jet_g_bounds {a : ℝ} (ha : 9 / 31 ≤ a) (ha' : a ≤ 7 / 19) :
    0 < jetg a ∧ jetg a ≤ 3 / 50 ∧ 0 < jetg1 a ∧ jetg1 a ≤ 31 / 200 ∧
      (1 / 3 ≤ a → jetg1 a ≤ 3 / 20) ∧ jetg2 a ≤ 0 := by
  have ha0 : 0 < a := by linarith
  have hs : 81 / 961 ≤ a ^ 2 := by nlinarith
  have hs' : a ^ 2 ≤ 49 / 361 := by nlinarith
  have h3 : (0 : ℝ) < 3 + a ^ 2 := by positivity
  unfold jetg jetg1 jetg2
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · apply div_pos (by linarith) (by positivity)
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · intro h
    have : 1 / 9 ≤ a ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]; nlinarith
  · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    apply mul_nonpos_of_nonneg_of_nonpos ha0.le (by linarith)

/-- The `p` bounds on the angle interval: `0 < p`, `p' ≥ 3/20` (`≥ 1/5` for `a ≥ 1/3`),
`p'' ≥ 1/2`. -/
theorem jet_p_bounds {a : ℝ} (ha : 9 / 31 ≤ a) (ha' : a ≤ 7 / 19) :
    0 < jetp a ∧ 3 / 20 ≤ jetp1 a ∧ (1 / 3 ≤ a → 1 / 5 ≤ jetp1 a) ∧ 1 / 2 ≤ jetp2 a := by
  have ha0 : 0 < a := by linarith
  have hs : 81 / 961 ≤ a ^ 2 := by nlinarith
  have hs' : a ^ 2 ≤ 49 / 361 := by nlinarith
  have h3 : (0 : ℝ) < 3 + a ^ 2 := by positivity
  have hc : (3 + a ^ 2) ^ 2 ≤ (3 + 49 / 361) ^ 2 := pow_le_pow_left₀ h3.le (by linarith) 2
  unfold jetp jetp1 jetp2
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; nlinarith
  · intro h
    rw [le_div_iff₀ (by positivity)]; nlinarith
  · have hc3 : (3 + a ^ 2) ^ 3 ≤ (3 + 49 / 361) ^ 3 := pow_le_pow_left₀ h3.le (by linarith) 3
    rw [le_div_iff₀ (by positivity)]; nlinarith

/-- The `q` bounds for `0 ≤ a ≤ 1`: `0 < q ≤ 1/3`, `q' ≤ 0`, `q'' ≤ 0`. -/
theorem jet_q_bounds {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    0 < jetq a ∧ jetq a ≤ 1 / 3 ∧ jetq1 a ≤ 0 ∧ jetq2 a ≤ 0 := by
  have h3 : (0 : ℝ) < 3 + a ^ 2 := by positivity
  unfold jetq jetq1 jetq2
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ h3]; nlinarith
  · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity); linarith
  · apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have : 0 ≤ 1 - a ^ 2 := by nlinarith
    linarith

end SmoothedOctagon
