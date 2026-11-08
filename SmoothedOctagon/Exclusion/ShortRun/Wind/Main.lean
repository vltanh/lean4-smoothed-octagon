module

public import SmoothedOctagon.Exclusion.ShortRun.Centre
public import SmoothedOctagon.Exclusion.ShortRun.Wind.Frame

/-!
# Case M1: the winding identity on a window starting at the seam

For an all-short mixed normal period with sign word `(− − +)^m` whose first centre
`c₀ = k₀ + 1` lies in `{0, 1, 2}`, the centre angles `φ_j = arccos(e_c/√(d_{c-1} d_c))`,
`c = c₀ + 3j`, satisfy `∑_{j<m} φ_j = (m + 1) π/3` (`wd_winding_aux`).

Proof: `φ_j = π/3 + κ_j(b_out) - κ_j(b_in)` (`wd_centre`); between two centres the tracked base
vector is an eigenvector of the three tangent factors, so `κ_j(b_out) = κ_{j+1}(b_in)`
(`wd_track_range`, `wd_bout_chain`); the last link crosses the seam, where `κ` gains the exact
`π/3` of the competitive frame (`wd_seam`, `wd_polar`). The sum telescopes to
`m π/3 + π/3`.

## Main API

* `wd_chol`: a factor `S = Qᵀ Q`, `det Q < 0`, of a positive definite symmetric form.
* `wd_sum_shift`: shifting a sum of an `m`-periodic function over `m` consecutive integers.
* `wd_cre_add`, `wd_swd_add`: `N`-periodicity of the centre data.
* `wd_winding_aux`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set SmoothedPolygons
open scoped Matrix

/-- A factor `S = Qᵀ Q` with `det Q < 0` of a positive definite symmetric `2 × 2` form. -/
theorem wd_chol {S : Mat2} (hsym : S 0 1 = S 1 0) (h00 : 0 < S 0 0) (hdet : 0 < S.det) :
    ∃ Q : Mat2, Q.det < 0 ∧
      ∀ x y, elQ S x y = (Q *ᵥ x) 0 * (Q *ᵥ y) 0 + (Q *ᵥ x) 1 * (Q *ᵥ y) 1 := by
  have hp := Real.sqrt_pos.2 h00
  have hΔ := Real.sqrt_pos.2 hdet
  have e : √S.det * √S.det = S 0 0 * S 1 1 - S 0 1 * S 1 0 := by
    rw [Real.mul_self_sqrt hdet.le, Matrix.det_fin_two]
  refine ⟨!![√(S 0 0), S 0 1 / √(S 0 0); 0, -(√S.det / √(S 0 0))], ?_, fun x y ↦ ?_⟩
  · rw [Matrix.det_fin_two_of]
    have : √(S 0 0) * -(√S.det / √(S 0 0)) - S 0 1 / √(S 0 0) * 0 = -√S.det := by
      field_simp; ring
    rw [this]; linarith
  · simp only [elQ, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    field_simp
    have hp2 : √(S 0 0) ^ 2 = S 0 0 := Real.sq_sqrt h00.le
    linear_combination (-(x 1 * y 1)) * e - (x 1 * y 0 * S 0 0 + x 1 * y 1 * S 0 1) * hsym +
      (-(x 0 * y 0 * √(S 0 0) ^ 2) - x 1 * y 0 * (S 0 1 - S 1 0) + x 1 * y 1 * S 1 1) * hp2

/-- Shifting a sum of an `m`-periodic function over `m` consecutive integers. -/
theorem wd_sum_shift {m : ℕ} {f : ℤ → ℝ} (hf : ∀ j, f (j + m) = f j) (d : ℤ) :
    ∑ j ∈ Finset.range m, f (j + d) = ∑ j ∈ Finset.range m, f j := by
  have h1 : ∀ g : ℤ → ℝ, (∀ j, g (j + m) = g j) →
      ∑ j ∈ Finset.range m, g ((j : ℤ) + 1) = ∑ j ∈ Finset.range m, g j := by
    intro g hg
    have h2 := Finset.sum_range_succ' (fun j : ℕ ↦ g j) m
    have h3 := Finset.sum_range_succ (fun j : ℕ ↦ g j) m
    have h4 : g (m : ℤ) = g 0 := by simpa using hg 0
    push_cast at h2
    linarith
  refine Int.induction_on d (by simp) (fun i ih ↦ ?_) (fun i ih ↦ ?_)
  · have := h1 (fun j ↦ f (j + i)) (fun j ↦ by
      rw [show j + m + i = j + i + m by ring]; exact hf _)
    rw [← ih, ← this]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1; ring
  · have := h1 (fun j ↦ f (j + (-i - 1))) (fun j ↦ by
      rw [show j + m + (-i - 1) = j + (-i - 1) + m by ring]; exact hf _)
    rw [← ih, ← this]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1; ring

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

theorem wd_wt_add (k : ℤ) : C.wt (k + N) = C.wt k := by
  simp only [wt, C.lab_add, C.mu_add, add_sub_cancel_right]

theorem wd_cre_add (k : ℤ) : C.cre (k + N) = C.cre k := by
  simp only [cre, C.wd_wt_add, C.act_add]

theorem wd_swd_add (k : ℤ) : C.swd (k + N) = C.swd k := by
  simp only [swd, show k + N + 1 = k + 1 + N by ring, C.wd_wt_add, C.act_add]

end CostateCycle

/-- **The winding identity on a window starting at the seam**: `∑_{j<m} φ_j = (m + 1)π/3`. -/
theorem wd_winding_aux (P : NormalPeriod) (hc : P.IsCompetitive) {k₀ : ℤ} {m : ℕ}
    (hpat : P.m1_IsPattern k₀) (hN : P.N = 3 * m) (hpos : 0 < P.costateCycle.gam2 0)
    (hk0 : 0 ≤ k₀ + 1) (hk2 : k₀ + 1 ≤ 2) :
    ∑ j ∈ Finset.range m, Real.arccos (P.costateCycle.cre (m1_centre k₀ j) /
      √(P.costateCycle.swd (m1_centre k₀ j - 1) * P.costateCycle.swd (m1_centre k₀ j))) =
      (m + 1) * π / 3 := by
  set C := P.costateCycle with hC
  have hNm : (P.N : ℤ) = 3 * m := by exact_mod_cast hN
  have hmix : P.rep.IsMixed := ⟨⟨k₀ + 3 * 0 + 2, (hpat 0).2.2⟩, ⟨k₀ + 3 * 0, (hpat 0).1⟩⟩
  have hm : 0 < m := by
    have := P.rep.N_pos
    rw [show P.rep.N = P.N from rfl, hN] at this; omega
  -- the costate metric and its factor
  have hsym := C.Sloc_symm 0
  have hdetS : (C.Sloc 0).det = C.gam2 0 := by
    rw [CostateCycle.Sloc, Matrix.det_neg, Matrix.det_mul, C.det_Mloc]
    simp [elJ0, Matrix.det_fin_two]
  have hS00 : 0 < C.Sloc 0 0 0 := by
    have hq : 0 < elQ (C.Sloc 0) (C.yv 0) (C.yv 0) := by
      rw [C.yv_norm]
      have := P.swd_ge_of_mixed hmix 0
      exact_mod_cast (by linarith : (0 : ℝ) < C.swd 0)
    have hdS := hdetS
    rw [Matrix.det_fin_two] at hdS
    set y := C.yv 0
    have e : C.Sloc 0 0 0 * elQ (C.Sloc 0) y y = (C.Sloc 0 0 0 * y 0 + C.Sloc 0 0 1 * y 1) ^ 2 +
        (C.Sloc 0 0 0 * C.Sloc 0 1 1 - C.Sloc 0 0 1 * C.Sloc 0 1 0) * y 1 ^ 2 := by
      simp only [elQ, hsym]; ring
    have hne : C.Sloc 0 0 0 ≠ 0 := by
      intro h0; rw [h0, hsym] at hdS; nlinarith [sq_nonneg (C.Sloc 0 1 0)]
    have : 0 ≤ C.Sloc 0 0 0 * elQ (C.Sloc 0) y y := by
      rw [e, hdS]; positivity
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith
    · exact h
  obtain ⟨Q, hQ, hS⟩ := wd_chol hsym hS00 (by rw [hdetS]; exact hpos)
  have hL : 0 < (Q * wd_K P).det := by
    rw [Matrix.det_mul, wd_det_K]; have : (0 : ℝ) < √3 := by positivity
    nlinarith
  obtain ⟨Φ, hΦc, hΦT, hΦ⟩ := wd_polar P hc
  set κ : ℝ → (Fin 2 → ℝ) → ℝ := fun t ω ↦ wd_kap (Q * wd_K P) (P.g t) (P.X t) (Φ t) ω
    with hκ
  -- the window
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℕ, (c₀ : ℤ) = k₀ + 1 := ⟨(k₀ + 1).toNat, Int.toNat_of_nonneg hk0⟩
  have hc₀2 : c₀ ≤ 2 := by omega
  have hcen : ∀ j : ℤ, m1_centre k₀ j = c₀ + 3 * j := fun j ↦ by simp only [m1_centre]; omega
  -- the labels
  set Lab : ℤ → Fin 3 := fun j ↦ P.rep.label (m1_centre k₀ j) with hLab
  have hL1 : ∀ j, P.rep.label (m1_centre k₀ j + 1) = Lab j - 1 := fun j ↦ (hpat j).2.1
  have hL2 : ∀ j, P.rep.label (m1_centre k₀ j + 2) = Lab j := by
    intro j
    have h := (hpat j).2.2
    unfold VertexRepresentation.IsForward at h
    rw [show k₀ + 3 * j + 2 + 1 = m1_centre k₀ j + 2 by simp only [m1_centre]; ring,
      show k₀ + 3 * j + 2 = m1_centre k₀ j + 1 by simp only [m1_centre]; ring, hL1] at h
    rw [h]; abel
  have hLn : ∀ j, Lab (j + 1) = Lab j - 1 := by
    intro j
    have h := (hpat (j + 1)).1
    unfold VertexRepresentation.IsReverse at h
    simp only [hLab]
    rw [show m1_centre k₀ (j + 1) = k₀ + 3 * (j + 1) + 1 from rfl, h,
      show k₀ + 3 * (j + 1) = m1_centre k₀ j + 2 by simp only [m1_centre]; ring, hL2]
  have hin : ∀ j, P.rep.label (m1_centre k₀ j) = P.rep.label (m1_centre k₀ j - 1) - 1 := by
    intro j
    have h := (hpat j).1
    unfold VertexRepresentation.IsReverse at h
    rw [show m1_centre k₀ j - 1 = k₀ + 3 * j by simp only [m1_centre]; ring]
    exact h
  have hLm : ∀ j, Lab (j + m) = Lab j + 1 := by
    intro j
    simp only [hLab]
    rw [show m1_centre k₀ (j + m) = m1_centre k₀ j + P.rep.N by
      simp only [m1_centre]; rw [show (P.rep.N : ℤ) = P.N from rfl, hNm]; ring,
      P.rep.label_add_period]
  have heig : ∀ (j n : ℤ), m1_centre k₀ j ≤ n → n < m1_centre k₀ j + 3 →
      wd_IsEig (P.rep.label n) (wd_bout (Lab j)) := by
    intro j n h1 h2
    rcases (show n = m1_centre k₀ j ∨ n = m1_centre k₀ j + 1 ∨ n = m1_centre k₀ j + 2 by omega)
      with h | h | h <;> rw [h]
    · exact wd_eig_self _
    · rw [hL1]; exact wd_eig_pred _
    · rw [hL2]; exact wd_eig_self _
  -- the per-centre identity
  set A : ℕ → ℝ := fun j ↦ κ (P.rep.τ ((c₀ + 3 * j : ℕ) : ℤ)) (wd_bin (Lab j)) with hA
  set B : ℕ → ℝ := fun j ↦ κ (P.rep.τ ((c₀ + 3 * j : ℕ) : ℤ)) (wd_bout (Lab j)) with hB
  have hcast : ∀ j : ℕ, m1_centre k₀ j = ((c₀ + 3 * j : ℕ) : ℤ) := fun j ↦ by
    rw [hcen]; push_cast; ring
  have hterm : ∀ j ∈ Finset.range m, Real.arccos (C.cre (m1_centre k₀ j) /
      √(C.swd (m1_centre k₀ j - 1) * C.swd (m1_centre k₀ j))) = π / 3 + B j - A j := by
    intro j hj
    have hjm := Finset.mem_range.1 hj
    have hcN : c₀ + 3 * j < P.N := by rw [hN]; omega
    have hlab : P.rep.label ((c₀ + 3 * j : ℕ) : ℤ) = Lab j := by simp only [hLab, hcast]
    have hin' := hin j
    have hout' := hL1 j
    rw [hcast] at hin' hout'
    have := wd_centre P hΦ hQ hS hcN hin' (by rw [hout']; simp only [hLab, hcast])
    rw [hcast, this, hlab]
  -- the links between consecutive centres
  have hlink : ∀ j : ℕ, j + 1 < m → B j = A (j + 1) := by
    intro j hj
    have htr := wd_track_range P hΦc hΦ hL (wd_bout_ne (Lab j))
      (a := c₀ + 3 * j) (b := c₀ + 3 * j + 3) (by omega) (by rw [hN]; omega)
      (fun n h1 h2 ↦ heig j n (by rw [hcen]; omega) (by rw [hcen]; omega))
    simp only [hA, hB, hκ]
    rw [show c₀ + 3 * (j + 1) = c₀ + 3 * j + 3 by ring, ← htr]
    have hl : Lab ((j + 1 : ℕ) : ℤ) = Lab j - 1 := by push_cast; exact hLn j
    rw [hl]
    rcases wd_bout_chain (Lab j) with h | h
    · rw [h]
    · rw [h, wd_kap_neg]
  -- the last link crosses the seam
  have hlast : B (m - 1) = A 0 + π / 3 := by
    have hT := P.T_pos
    have h1 := wd_track_range P hΦc hΦ hL (wd_bout_ne (Lab ((m - 1 : ℕ) : ℤ)))
      (a := c₀ + 3 * (m - 1)) (b := P.N) (by rw [hN]; omega) le_rfl
      (fun n h1 h2 ↦ heig (m - 1 : ℕ) n (by rw [hcen]; push_cast [Nat.cast_sub hm]; omega)
        (by rw [hcen]; push_cast [Nat.cast_sub hm]; rw [hN] at h2; omega))
    have hτN : P.rep.τ (P.N : ℕ) = P.T := P.rep.τ_N
    rw [hτN] at h1
    have h2 := wd_seam P hΦT hΦ hL (wd_bout_ne (Lab ((m - 1 : ℕ) : ℤ)))
    have hlabm : Lab ((m - 1 : ℕ) : ℤ) = Lab (-1) + 1 := by
      rw [← hLm]; congr 1; push_cast [Nat.cast_sub hm]; ring
    have h3 : wd_kap (Q * wd_K P) (P.g 0) (P.X 0) (Φ 0) (R *ᵥ wd_bout (Lab ((m - 1 : ℕ) : ℤ))) =
        wd_kap (Q * wd_K P) (P.g 0) (P.X 0) (Φ 0) (wd_bout (Lab (-1))) := by
      rw [hlabm]
      rcases wd_bout_seam (Lab (-1)) with h | h
      · rw [h]
      · rw [h, wd_kap_neg]
    have h4 := wd_track_range P hΦc hΦ hL (wd_bout_ne (Lab (-1))) (a := 0) (b := c₀)
      (Nat.zero_le _) (by rw [hN]; omega)
      (fun n h1 h2 ↦ heig (-1) n (by rw [hcen]; omega) (by rw [hcen]; omega))
    have hτ0 : P.rep.τ ((0 : ℕ) : ℤ) = 0 := by simpa using P.rep.τ_zero
    rw [hτ0] at h4
    have h5 : wd_kap (Q * wd_K P) (P.g (P.rep.τ (c₀ : ℕ))) (P.X (P.rep.τ (c₀ : ℕ)))
        (Φ (P.rep.τ (c₀ : ℕ))) (wd_bout (Lab (-1))) = A 0 := by
      simp only [hA, hκ, mul_zero, add_zero, Nat.cast_zero]
      have hl0 : Lab 0 = Lab (-1) - 1 := by
        have := hLn (-1); simpa using this
      rw [hl0]
      rcases wd_bout_chain (Lab (-1)) with h | h
      · rw [h]
      · rw [h, wd_kap_neg]
    simp only [hB, hκ]
    rw [← h1, h2, h3, ← h4, h5]
  -- telescoping
  rw [Finset.sum_congr rfl hterm]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have htel : ∑ j ∈ Finset.range (m' + 1), (B j - A j) = π / 3 := by
    rw [Finset.sum_range_succ]
    have hlink' : ∑ j ∈ Finset.range m', (B j - A j) =
        ∑ j ∈ Finset.range m', (A (j + 1) - A j) :=
      Finset.sum_congr rfl fun j hj ↦ by rw [hlink j (by have := Finset.mem_range.1 hj; omega)]
    rw [hlink', Finset.sum_range_sub, show m' = m' + 1 - 1 by omega, hlast]
    ring
  rw [show (∑ j ∈ Finset.range (m' + 1), (π / 3 + B j - A j)) =
      ∑ j ∈ Finset.range (m' + 1), (π / 3) + ∑ j ∈ Finset.range (m' + 1), (B j - A j) by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ ↦ by ring,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, htel]
  push_cast
  ring

end SmoothedOctagon
