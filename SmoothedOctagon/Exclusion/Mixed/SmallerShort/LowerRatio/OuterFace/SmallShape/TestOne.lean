module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.Terminal
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.SmallShape.Curvature
public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.OuterFace.Residue

/-!
# Smaller-short window, lower ratio, outer face, small shapes: the test `F₁`

On `3/2 ≤ x ≤ 2`, `1 ≤ α ≤ 6/5`, `6α² ≥ x(x + 2)`,
`1/2 ≤ C ≤ 10/13`, `3/4 ≤ u ≤ 19/25`:

* `w₀ > 8/9` by the norm comparison and the two shape/ratio increments
  (`SmallShape/Norm`), so `β ↦ F₁` is concave and `C ∈ {1/2, 10/13}`;
* norm concavity gives `u ∈ {3/4, 19/25}`;
* the reciprocal-shape curvature is less than `-1/60` on `r ∈ [5/6, 1]`
  (residue `Q < 0`), so `α` is `6/5` or the lower shape `α_*(x) = 1` (`x ≤ 5/3`),
  `(6x + 3)/13` (`x ≥ 5/3`, below the cap);
* the terminal curves are positive.

The terminal curves use a decreasing derivative numerator and endpoint comparison
(`SmallShape/Terminal`). The uniform comparisons are in `SmallShape/Curvature` and `OuterFace/Residue`.

## Main API

* `lro_B_w0`, `lro_B_recip`, `lro_B_F1`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

theorem lro_B_T65_hf {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 1 / 2 * (6 / 5 - 1)) (3 / 4) := by
  have h := LowerRatioTerminal.lower_bound .fixed (C := 1 / 2) (u := 3 / 4)
    (Or.inl rfl) (Or.inl rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .fixed) x = 6 / 5 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .fixed (Or.inl rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T13_hf {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) (3 / 4) := by
  have h := LowerRatioTerminal.lower_bound .line (C := 1 / 2) (u := 3 / 4)
    (Or.inl rfl) (Or.inl rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .line) x = (6 * x + 3) / 13 := by
    dsimp [LowerRatioTerminal.alpha, polyHorner]
    ring
  rw [LowerRatioTerminal.face_test .line (Or.inl rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T65_hv {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 1 / 2 * (6 / 5 - 1)) (19 / 25) := by
  have h := LowerRatioTerminal.lower_bound .fixed (C := 1 / 2) (u := 19 / 25)
    (Or.inl rfl) (Or.inr rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .fixed) x = 6 / 5 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .fixed (Or.inl rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T13_hv {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 1 / 2 * ((6 * x + 3) / 13 - 1)) (19 / 25) := by
  have h := LowerRatioTerminal.lower_bound .line (C := 1 / 2) (u := 19 / 25)
    (Or.inl rfl) (Or.inr rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .line) x = (6 * x + 3) / 13 := by
    dsimp [LowerRatioTerminal.alpha, polyHorner]
    ring
  rw [LowerRatioTerminal.face_test .line (Or.inl rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T65_tf {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (3 / 4) := by
  have h := LowerRatioTerminal.lower_bound .fixed (C := 10 / 13) (u := 3 / 4)
    (Or.inr rfl) (Or.inl rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .fixed) x = 6 / 5 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .fixed (Or.inr rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T13_tf {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (3 / 4) := by
  have h := LowerRatioTerminal.lower_bound .line (C := 10 / 13) (u := 3 / 4)
    (Or.inr rfl) (Or.inl rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .line) x = (6 * x + 3) / 13 := by
    dsimp [LowerRatioTerminal.alpha, polyHorner]
    ring
  rw [LowerRatioTerminal.face_test .line (Or.inr rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T65_tv {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x (6 / 5) (x + 10 / 13 * (6 / 5 - 1)) (19 / 25) := by
  have h := LowerRatioTerminal.lower_bound .fixed (C := 10 / 13) (u := 19 / 25)
    (Or.inr rfl) (Or.inr rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .fixed) x = 6 / 5 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .fixed (Or.inr rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T13_tv {x : ℝ} (h0 : (5 / 3 : ℝ) ≤ x) (h1 : x ≤ (2 : ℝ)) :
    (0 : ℝ) < lroF1 x ((6 * x + 3) / 13) (x + 10 / 13 * ((6 * x + 3) / 13 - 1)) (19 / 25) := by
  have h := LowerRatioTerminal.lower_bound .line (C := 10 / 13) (u := 19 / 25)
    (Or.inr rfl) (Or.inr rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .line) x = (6 * x + 3) / 13 := by
    dsimp [LowerRatioTerminal.alpha, polyHorner]
    ring
  rw [LowerRatioTerminal.face_test .line (Or.inr rfl) (by linarith), he] at h
  exact lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h

theorem lro_B_T1_f {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (5 / 3 : ℝ)) :
    (0 : ℝ) < lroF1 x (1) (x) (3 / 4) := by
  have h := LowerRatioTerminal.lower_bound .unit (C := 1 / 2) (u := 3 / 4)
    (Or.inl rfl) (Or.inl rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .unit) x = 1 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .unit (Or.inl rfl) (by linarith), he] at h
  simpa only [sub_self, mul_zero, add_zero] using (lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h)

theorem lro_B_T1_v {x : ℝ} (h0 : (3 / 2 : ℝ) ≤ x) (h1 : x ≤ (5 / 3 : ℝ)) :
    (0 : ℝ) < lroF1 x (1) (x) (19 / 25) := by
  have h := LowerRatioTerminal.lower_bound .unit (C := 1 / 2) (u := 19 / 25)
    (Or.inl rfl) (Or.inr rfl) (x := x) h0 h1
  have he : polyHorner (LowerRatioTerminal.alpha .unit) x = 1 := by
    simp [LowerRatioTerminal.alpha, polyHorner]
  rw [LowerRatioTerminal.face_test .unit (Or.inl rfl) (by linarith), he] at h
  simpa only [sub_self, mul_zero, add_zero] using (lt_trans (by norm_num : (0 : ℝ) < 1 / 80000) h)

/-- `w₀ > 6/7` on the small shapes. -/
theorem lro_B_w0 {x a u : ℝ} (hx : 3 / 2 ≤ x) (_hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hu : u ≤ 19 / 25) : 6 / 7 < lrow0 x a u := by
  have h := lro_small_shape_w0 hx ha1 ha2 hu
  linarith only [h]

/-- **Reciprocal-shape concavity of `F₁` on the small shapes**. -/
theorem lro_B_recip {x a aS C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (haS1 : 1 ≤ aS) (haS : aS ≤ a)
    (ha2 : a ≤ 6 / 5) (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 10 / 13) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 19 / 25) :
    min (lroF1 x aS (x + C * (aS - 1)) u) (lroF1 x (6 / 5) (x + C * (6 / 5 - 1)) u) ≤
      lroF1 x a (x + C * (a - 1)) u := by
  have hM := lro_small_shape_curvature hx hx2 hC0 (by linarith) hu0
  have hQ := lro_residue_neg hx hx2 hC0 (by linarith) hu1
  have hx0 : 0 < x := by linarith
  have hb3 := lro_b3_nonpos hx hx2 hC1 (by linarith) hu1
  have hb4 := lrg4_nonpos (u := u) hx0
  have hZ : ∀ a' : ℝ, 1 ≤ a' → a' ≤ 6 / 5 → 0 < 1 + C + (x - C) * (1 / a') := by
    intro a' h1 h2
    have : 0 < (x - C) * (1 / a') := mul_pos (by linarith) (by positivity)
    linarith
  have hrep : ∀ a' : ℝ, 1 ≤ a' → a' ≤ 6 / 5 → lroF1 x a' (x + C * (a' - 1)) u =
      lrG (lrb0 x C u) (lrb1 x C u) (lrb2 x C u) (lrb3 x C u) (lrb4 x u) (lrQ1 x C u)
        (1 + C) (x - C) (1 / a') :=
    fun a' h1 h2 => lro_F1_rG hx0 (by linarith) rfl (by linarith) (hZ a' h1 h2)
  rw [hrep a (by linarith) ha2, hrep aS haS1 (by linarith), hrep (6 / 5) (by norm_num) le_rfl]
  rw [min_comm]
  apply lrG_min (one_div_le_one_div_of_le (by linarith) ha2)
    (one_div_le_one_div_of_le (by linarith) haS)
  · intro s hs
    have h1 : 1 / (6 / 5) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2.trans (by rw [div_le_one (by linarith)]; exact haS1)
    norm_num at h1
    constructor
    · nlinarith
    · nlinarith
  · intro s hs
    have h1 : 1 / (6 / 5) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2.trans (by rw [div_le_one (by linarith)]; exact haS1)
    norm_num at h1
    set Z := 1 + C + (x - C) * s with hZdef
    have hZ0 : 0 < Z := by nlinarith
    have hZe : 11 * (x - C) ≤ 6 * Z := by nlinarith
    have t1 : 12 * lrb4 x u * s ^ 2 ≤ 0 := by nlinarith [sq_nonneg s]
    have t2 : 6 * lrb3 x C u * s ≤ 5 * lrb3 x C u := by nlinarith
    have t3 : 2 * lrQ1 x C u * (x - C) ^ 2 / Z ^ 3 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (x - C)]) (by positivity)
    have t4 : 7 / 96 * (x - C) ^ 2 / Z ^ 2 ≤ 1 / 40 := by
      rw [div_le_iff₀ (by positivity)]
      have : (x - C) ^ 2 ≤ 36 / 121 * Z ^ 2 := by nlinarith
      nlinarith
    nlinarith

/-- **Branch B, `F₁ > 0`.** -/
theorem lro_B_F1 {x a b C u : ℝ} (hx : 3 / 2 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (ha2 : a ≤ 6 / 5)
    (hcap : x * (x + 2) ≤ 6 * a ^ 2) (hC0 : 1 / 2 ≤ C) (hC1 : C ≤ 10 / 13)
    (hb : b = x + C * (a - 1)) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 19 / 25) : 0 < lroF1 x a b u := by
  have hx0 : 0 < x := by linarith
  have ha0 : 0 < a := by linarith
  -- the lower shape below the cap
  obtain ⟨aS, haS1, haS, hlow⟩ : ∃ aS, 1 ≤ aS ∧ aS ≤ a ∧ ∀ C' u', (C' = 1 / 2 ∨ C' = 10 / 13) →
      (u' = 3 / 4 ∨ u' = 19 / 25) → 0 < lroF1 x aS (x + C' * (aS - 1)) u' := by
    rcases le_total x (5 / 3) with h53 | h53
    · refine ⟨1, le_rfl, ha1, fun C' u' _ hu' => ?_⟩
      rw [show x + C' * (1 - 1) = x by ring]
      rcases hu' with rfl | rfl
      · exact lro_B_T1_f hx h53
      · exact lro_B_T1_v hx h53
    · refine ⟨(6 * x + 3) / 13, by linarith, ?_, fun C' u' hC' hu' => ?_⟩
      · have h1 : ((6 * x + 3) / 13) ^ 2 ≤ a ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.2 h53) (sub_nonneg.2 hx2)]
        nlinarith [sq_nonneg (a - (6 * x + 3) / 13)]
      · rcases hC' with rfl | rfl <;> rcases hu' with rfl | rfl
        · exact lro_B_T13_hf h53 hx2
        · exact lro_B_T13_hv h53 hx2
        · exact lro_B_T13_tf h53 hx2
        · exact lro_B_T13_tv h53 hx2
  have hshape : ∀ C' u', (C' = 1 / 2 ∨ C' = 10 / 13) → (u' = 3 / 4 ∨ u' = 19 / 25) →
      0 < lroF1 x a (x + C' * (a - 1)) u' := by
    intro C' u' hC' hu'
    have hu0' : 3 / 4 ≤ u' := by rcases hu' with rfl | rfl <;> norm_num
    have hu1' : u' ≤ 19 / 25 := by rcases hu' with rfl | rfl <;> norm_num
    have hC0' : 1 / 2 ≤ C' := by rcases hC' with rfl | rfl <;> norm_num
    have hC1' : C' ≤ 10 / 13 := by rcases hC' with rfl | rfl <;> norm_num
    have hterminal : 0 < lroF1 x (6 / 5) (x + C' * (6 / 5 - 1)) u' := by
      rcases hC' with rfl | rfl <;> rcases hu' with rfl | rfl
      · exact lro_B_T65_hf hx hx2
      · exact lro_B_T65_hv hx hx2
      · exact lro_B_T65_tf hx hx2
      · exact lro_B_T65_tv hx hx2
    have := lro_B_recip hx hx2 haS1 haS ha2 hC0' hC1' hu0' hu1'
    exact lt_of_lt_of_le (lt_min (hlow C' u' hC' hu') hterminal) this
  have hbeta : ∀ u', (u' = 3 / 4 ∨ u' = 19 / 25) → 0 < lroF1 x a b u' := by
    intro u' hu'
    have hu1' : u' ≤ 19 / 25 := by rcases hu' with rfl | rfl <;> norm_num
    have hw0 := lro_B_w0 (u := u') hx hx2 ha1 ha2 hu1'
    have hA : 0 ≤ a - 1 := by linarith
    have hm := lro_F1_bmin (x := x) (a := a) (b1 := x + 1 / 2 * (a - 1)) (b := b)
      (b2 := x + 10 / 13 * (a - 1)) (u := u') hx0 ha0 (by nlinarith)
      (by rw [hb]; nlinarith) (by rw [hb]; nlinarith) (by nlinarith) (by nlinarith)
    exact lt_of_lt_of_le (lt_min (hshape _ _ (Or.inl rfl) hu') (hshape _ _ (Or.inr rfl) hu')) hm
  have hm := lro_F1_umin (x := x) (a := a) (b := b) hu0 hu1 ha0.ne'
  exact lt_of_lt_of_le (lt_min (hbeta _ (Or.inl rfl)) (hbeta _ (Or.inr rfl))) hm

end SmoothedOctagon
