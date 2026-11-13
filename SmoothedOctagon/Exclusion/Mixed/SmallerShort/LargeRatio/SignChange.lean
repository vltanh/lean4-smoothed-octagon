module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LargeRatio.SignTools

/-!
# Positivity from one coefficient sign change

A polynomial with nonnegative lower coefficients and nonpositive higher
coefficients stays positive between zero and a positive endpoint when
its constant term and endpoint value are positive. The proof compares
`p(L) * X^n` with `p(X) * L^n` term by term.
-/

@[expose] public section
namespace SmoothedOctagon.OneSignChange

theorem powers_compare {X L : ℝ} (hX : 0 ≤ X) (hXL : X ≤ L)
    {i n : ℕ} (hin : i ≤ n) : L ^ i * X ^ n ≤ X ^ i * L ^ n := by
  have hL : 0 ≤ L := hX.trans hXL
  have heX : X ^ n = X ^ i * X ^ (n - i) := by rw [← pow_add, Nat.add_sub_of_le hin]
  have heL : L ^ n = L ^ i * L ^ (n - i) := by rw [← pow_add, Nat.add_sub_of_le hin]
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX hXL (n - i))
    (mul_nonneg (pow_nonneg hX i) (pow_nonneg hL i))
  rw [heX, heL]
  nlinarith only [hp]

theorem sum_pos {c : ℕ → ℝ} {d n : ℕ} {X L : ℝ}
    (hd : 0 < d) (hX : 0 ≤ X) (hXL : X ≤ L)
    (hfirst : ∀ i < d, i ≤ n → 0 ≤ c i)
    (hlast : ∀ i < d, n < i → c i ≤ 0)
    (h0 : 0 < c 0) (hend : 0 < ∑ i ∈ Finset.range d, c i * L ^ i) :
    0 < ∑ i ∈ Finset.range d, c i * X ^ i := by
  rcases eq_or_lt_of_le hX with hX | hX
  · subst X
    cases d with
    | zero => omega
    | succ d => simpa [Finset.sum_range_succ'] using h0
  have hL : 0 < L := hX.trans_le hXL
  have hterm (i : ℕ) (hi : i ∈ Finset.range d) :
      (c i * L ^ i) * X ^ n ≤ (c i * X ^ i) * L ^ n := by
    have hid := Finset.mem_range.mp hi
    rcases le_or_gt i n with hin | hni
    · have hp := mul_le_mul_of_nonneg_left (powers_compare hX.le hXL hin) (hfirst i hid hin)
      nlinarith only [hp]
    · have hp := mul_le_mul_of_nonpos_left (powers_compare hX.le hXL hni.le) (hlast i hid hni)
      nlinarith only [hp]
  have hkey : (∑ i ∈ Finset.range d, c i * L ^ i) * X ^ n ≤
      (∑ i ∈ Finset.range d, c i * X ^ i) * L ^ n := by
    simpa only [Finset.sum_mul] using Finset.sum_le_sum hterm
  have hp : 0 < (∑ i ∈ Finset.range d, c i * X ^ i) * L ^ n :=
    lt_of_lt_of_le (mul_pos hend (pow_pos hX n)) hkey
  exact (mul_pos_iff_of_pos_right (pow_pos hL n)).mp hp

theorem horner_eq_sum (cs : List ℝ) (X : ℝ) :
    polyHorner cs X = ∑ i ∈ Finset.range cs.length, cs.getD i 0 * X ^ i := by
  induction cs with
  | nil => simp [polyHorner]
  | cons c cs ih =>
    simp only [polyHorner, List.length_cons, Finset.sum_range_succ',
      List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one]
    rw [ih, mul_comm X, Finset.sum_mul]
    conv_lhs => rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ]
    ring

theorem horner_pos (cs : List ℝ) (n : ℕ) {X L : ℝ}
    (hd : 0 < cs.length) (hX : 0 ≤ X) (hXL : X ≤ L)
    (hfirst : ∀ i < cs.length, i ≤ n → 0 ≤ cs.getD i 0)
    (hlast : ∀ i < cs.length, n < i → cs.getD i 0 ≤ 0)
    (h0 : 0 < cs.getD 0 0) (hend : 0 < polyHorner cs L) :
    0 < polyHorner cs X := by
  rw [horner_eq_sum] at hend ⊢
  exact sum_pos hd hX hXL hfirst hlast h0 hend

def Conditions (cs : List ℝ) (n : ℕ) (L : ℝ) : Prop :=
  0 < cs.getD 0 0 ∧
    (∀ i < cs.length, if i ≤ n then 0 ≤ cs.getD i 0 else cs.getD i 0 ≤ 0) ∧
    0 < polyHorner cs L

theorem horner_pos_checked (cs : List ℝ) (n : ℕ) {X L : ℝ}
    (h : Conditions cs n L) (hX : 0 ≤ X) (hXL : X ≤ L) : 0 < polyHorner cs X := by
  obtain ⟨h0, hsign, hend⟩ := h
  have hd : 0 < cs.length := by
    cases cs with
    | nil => simp at h0
    | cons c cs => simp
  apply horner_pos cs n hd hX hXL _ _ h0 hend
  · intro i hi hin
    simpa only [hin, ↓reduceIte] using hsign i hi
  · intro i hi hni
    have hn : ¬i ≤ n := Nat.not_le.mpr hni
    simpa only [hn, ↓reduceIte] using hsign i hi

theorem positive_after_shift (cs : List ℝ) (n : ℕ)
    (h : Conditions (lgrShift (2 / 5) cs) n (33 / 5)) :
    ∀ X, 2 / 5 ≤ X → X ≤ 7 → 0 < polyHorner cs X := by
  intro X hX hX7
  have hp := horner_pos_checked (lgrShift (2 / 5) cs) n h
    (show 0 ≤ X - 2 / 5 by linarith only [hX])
    (show X - 2 / 5 ≤ 33 / 5 by linarith only [hX7])
  rw [lgr_horner_shift, show 2 / 5 + (X - 2 / 5) = X by ring] at hp
  exact hp

theorem negative_after_shift (cs : List ℝ) (n : ℕ)
    (h : Conditions (lgrShift (2 / 5) (lgrSmul (-1) cs)) n (33 / 5)) :
    ∀ X, 2 / 5 ≤ X → X ≤ 7 → polyHorner cs X < 0 := by
  intro X hX hX7
  have hp := positive_after_shift (lgrSmul (-1) cs) n h X hX hX7
  rw [lgr_horner_smul] at hp
  linarith only [hp]

end SmoothedOctagon.OneSignChange
