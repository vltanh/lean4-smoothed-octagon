module

public import SmoothedOctagon.Exclusion.ShortRun.Wind.Main

/-!
# The winding of the costate-metric angles over a whole period

`MIXED_GLOBAL_PROJECTIVE_WINDING` for an arbitrary normal period (any sign word), in the form used
by `MIXED_GLOBAL_REVERSE_ANGLE_DENSITY` (9): with the continuous angle `κ` of
`Exclusion/ShortRun/Wind` (`wd_kap`, for `L = Q K`), every piece `n` carries an incoming and an
outgoing base vector (`cg_inB`, `cg_outB`: the physical directions of the switch vectors
`y_{n-1}`, `y_n`, up to sign and positive factors), and the increments `δ_n = κ_n(out) - κ_n(in)`
sum to exactly `π/3` over one period (`cg_winding`). At a turn `δ_n = 0` (`cg_turn_fr`,
`cg_turn_rf`); at a reverse centre `- -` the costate angle is `π/3 + δ_n` (`cg_angle_mm`, which is
`wd_centre`) and at a forward piece `+ +` it is `π/3 - δ_n` (`cg_angle_pp`).

Route: the generalization of `wd_winding_aux` from the all-short word to every word. The base
vectors of a piece are eigenvectors of its tangent factor (`cg_eig_inB`, `cg_eig_outB`), so `κ` is
constant along the piece (`wd_track_piece`); consecutive pieces share their switch direction
(`cg_link`), and the seam gains the `π/3` of the competitive frame (`wd_seam`, `cg_seam_vec`).

## Main API

* `cg_inB`, `cg_outB`, `cg_eig_bin`, `cg_eig_inB`, `cg_eig_outB`, `cg_inB_ne`, `cg_outB_ne`.
* `cg_link`, `cg_turn_fr`, `cg_turn_rf`, `cg_seam_vec`.
* `cg_winding`: `∑_{n<N} (κ_n(out_n) - κ_n(in_n)) = π/3`.
* `cg_angle_pp`, `cg_angle_mm`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set PlaneCurve SmoothedPolygons
open scoped Matrix

/-! ### The base vectors of a piece -/

/-- The incoming base vector of piece `n`: `b_out` after a forward switch, `b_in` after a reverse
one (the direction of `y_{n-1}` in the physical frame, up to sign). -/
noncomputable def cg_inB (P : NormalPeriod) (n : ℤ) : Fin 2 → ℝ :=
  if P.rep.label n = P.rep.label (n - 1) + 1 then wd_bout (P.rep.label n)
  else wd_bin (P.rep.label n)

/-- The outgoing base vector of piece `n`: `b_in` before a forward switch, `b_out` before a reverse
one (the direction of `y_n` in the physical frame, up to sign). -/
noncomputable def cg_outB (P : NormalPeriod) (n : ℤ) : Fin 2 → ℝ :=
  if P.rep.label (n + 1) = P.rep.label n + 1 then wd_bin (P.rep.label n)
  else wd_bout (P.rep.label n)

private lemma cg_fin_ne (i : Fin 3) : ¬ (i - 1 = i + 1) := by revert i; decide

theorem cg_eig_neg {i : Fin 3} {v : Fin 2 → ℝ} (h : wd_IsEig i v) : wd_IsEig i (-v) := by
  intro w hw
  obtain ⟨c, hc, hv⟩ := h w hw
  exact ⟨c, hc, by rw [Matrix.mulVec_neg, hv, smul_neg]⟩

/-- `b_in(L)` is an eigenvector of the tangent factor of `L`. -/
theorem cg_eig_bin (L : Fin 3) : wd_IsEig L (wd_bin L) := by
  have h := wd_eig_pred (L + 1)
  rw [add_sub_cancel_right] at h
  rcases wd_bout_chain (L + 1) with e | e <;> rw [add_sub_cancel_right] at e <;> rw [e] at h
  · exact h
  · simpa using cg_eig_neg h

theorem cg_eig_inB (P : NormalPeriod) (n : ℤ) : wd_IsEig (P.rep.label n) (cg_inB P n) := by
  unfold cg_inB; split_ifs
  · exact wd_eig_self _
  · exact cg_eig_bin _

theorem cg_eig_outB (P : NormalPeriod) (n : ℤ) : wd_IsEig (P.rep.label n) (cg_outB P n) := by
  unfold cg_outB; split_ifs
  · exact cg_eig_bin _
  · exact wd_eig_self _

theorem cg_inB_ne (P : NormalPeriod) (n : ℤ) : cg_inB P n ≠ 0 := by
  unfold cg_inB; split_ifs
  · exact wd_bout_ne _
  · exact wd_bin_ne _

theorem cg_outB_ne (P : NormalPeriod) (n : ℤ) : cg_outB P n ≠ 0 := by
  unfold cg_outB; split_ifs
  · exact wd_bin_ne _
  · exact wd_bout_ne _

/-- Consecutive pieces share the direction of their common switch. -/
theorem cg_link (P : NormalPeriod) (n : ℤ) :
    cg_inB P (n + 1) = cg_outB P n ∨ cg_inB P (n + 1) = -cg_outB P n := by
  unfold cg_inB cg_outB
  rw [add_sub_cancel_right]
  rcases P.rep.el_fwd_or_rev n with h | h
  · have h' : P.rep.label (n + 1) = P.rep.label n + 1 := h
    rw [ite_eq_left h', ite_eq_left h', h']
    have := wd_bout_chain (P.rep.label n + 1)
    rwa [add_sub_cancel_right] at this
  · have h' : P.rep.label (n + 1) = P.rep.label n - 1 := h
    have hne : ¬ P.rep.label (n + 1) = P.rep.label n + 1 := by
      rw [h']; exact cg_fin_ne _
    rw [ite_eq_right hne, ite_eq_right hne, h']
    rcases wd_bout_chain (P.rep.label n) with e | e
    · left; exact e.symm
    · right; rw [e, neg_neg]

/-- At a turn `+ -` both base vectors coincide. -/
theorem cg_turn_fr (P : NormalPeriod) {n : ℤ} (hin : P.rep.label n = P.rep.label (n - 1) + 1)
    (hout : P.rep.label (n + 1) = P.rep.label n - 1) : cg_inB P n = cg_outB P n := by
  have hne : ¬ P.rep.label (n + 1) = P.rep.label n + 1 := by rw [hout]; exact cg_fin_ne _
  unfold cg_inB cg_outB
  rw [ite_eq_left hin, ite_eq_right hne]

/-- At a turn `- +` both base vectors coincide. -/
theorem cg_turn_rf (P : NormalPeriod) {n : ℤ} (hin : P.rep.label n = P.rep.label (n - 1) - 1)
    (hout : P.rep.label (n + 1) = P.rep.label n + 1) : cg_inB P n = cg_outB P n := by
  have hne : ¬ P.rep.label n = P.rep.label (n - 1) + 1 := by rw [hin]; exact cg_fin_ne _
  unfold cg_inB cg_outB
  rw [ite_eq_right hne, ite_eq_left hout]

/-- The seam: the rotation `R` carries the outgoing base vector of the last piece to the incoming
base vector of the first one, up to sign. -/
theorem cg_seam_vec (P : NormalPeriod) :
    R *ᵥ cg_outB P ((P.N : ℤ) - 1) = cg_inB P 0 ∨
      R *ᵥ cg_outB P ((P.N : ℤ) - 1) = -cg_inB P 0 := by
  have hl1 : P.rep.label ((P.N : ℤ) - 1) = P.rep.label (-1) + 1 := by
    rw [show (P.N : ℤ) - 1 = -1 + P.rep.N from by simp [NormalPeriod.N]; ring,
      P.rep.label_add_period]
  have hlN : P.rep.label ((P.N : ℤ) - 1 + 1) = P.rep.label 0 + 1 := by
    rw [sub_add_cancel, show (P.N : ℤ) = 0 + P.rep.N from by simp [NormalPeriod.N],
      P.rep.label_add_period]
  unfold cg_inB cg_outB
  rw [hlN, hl1, show (0 : ℤ) - 1 = -1 by norm_num]
  rcases P.rep.el_fwd_or_rev (-1) with h | h
  · have h' : P.rep.label 0 = P.rep.label (-1) + 1 := by
      have e : P.rep.label (-1 + 1) = P.rep.label (-1) + 1 := h
      rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at e
    rw [ite_eq_left h', ← h', ite_eq_left (rfl : P.rep.label 0 + 1 = P.rep.label 0 + 1)]
    left; exact (wd_bout_eq_R _).symm
  · have h' : P.rep.label 0 = P.rep.label (-1) - 1 := by
      have e : P.rep.label (-1 + 1) = P.rep.label (-1) - 1 := h
      rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at e
    have hm : P.rep.label (-1) = P.rep.label 0 + 1 := by rw [h', sub_add_cancel]
    have hne : ¬ P.rep.label 0 = P.rep.label (-1) + 1 := by rw [h']; exact cg_fin_ne _
    have hne' : ¬ P.rep.label 0 + 1 = P.rep.label (-1) + 1 + 1 := by
      intro e; exact hne (add_right_cancel e)
    rw [ite_eq_right hne, ite_eq_right hne', hm]
    have hc := wd_bout_chain (P.rep.label 0 + 1)
    rw [add_sub_cancel_right] at hc
    rcases wd_bout_seam (P.rep.label 0 + 1) with e | e <;> rw [e] <;> rcases hc with f | f <;>
      rw [f]
    · left; rfl
    · right; rfl
    · right; rfl
    · left; rw [neg_neg]

/-! ### The winding over one period -/

/-- **The winding identity** (MGPW, all words): the increments of the canonical angle between the
incoming and the outgoing base vector of each piece sum to `π/3` over one period. -/
theorem cg_winding (P : NormalPeriod) {Φ : ℝ → ℝ} (hΦc : ContinuousOn Φ (Icc 0 P.T))
    (hΦT : Φ P.T - Φ 0 = π / 3)
    (hΦ : ∀ t ∈ Icc 0 P.T, wd_IsAng (Φ t) (Reduction.scb_zc (P.g t))) {L : Mat2}
    (hL : 0 < L.det) :
    ∑ n ∈ Finset.range P.N,
      (wd_kap L (P.g (P.rep.τ n)) (P.X (P.rep.τ n)) (Φ (P.rep.τ n)) (cg_outB P n) -
        wd_kap L (P.g (P.rep.τ n)) (P.X (P.rep.τ n)) (Φ (P.rep.τ n)) (cg_inB P n)) = π / 3 := by
  set κ : ℝ → (Fin 2 → ℝ) → ℝ := fun t ω ↦ wd_kap L (P.g t) (P.X t) (Φ t) ω with hκ
  set A : ℕ → ℝ := fun n ↦ κ (P.rep.τ n) (cg_inB P n) with hA
  set B : ℕ → ℝ := fun n ↦ κ (P.rep.τ n) (cg_outB P n) with hB
  have hN : 0 < P.N := P.rep.N_pos
  -- `κ` of the outgoing vector is constant along the piece
  have htrack : ∀ n : ℕ, n < P.N → κ (P.rep.τ ((n + 1 : ℕ) : ℤ)) (cg_outB P n) = B n := by
    intro n hn
    exact wd_track_piece P hΦc hΦ hL (cg_outB_ne P n) hn (cg_eig_outB P n)
  have hlink : ∀ n : ℕ, n + 1 < P.N → A (n + 1) = B n := by
    intro n hn
    rw [← htrack n (by omega)]
    simp only [hA, hκ]
    rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring]
    rcases cg_link P n with e | e <;> rw [e]
    rw [wd_kap_neg]
  have htel : ∀ k : ℕ, k < P.N →
      ∑ n ∈ Finset.range (k + 1), (B n - A n) = B k - A 0 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ, ih (by omega), hlink k hk]
      ring
  have hlast : B (P.N - 1) = A 0 + π / 3 := by
    have hc : (((P.N - 1 : ℕ) : ℤ)) = (P.N : ℤ) - 1 := by push_cast [Nat.cast_sub hN]; ring
    have h1 := htrack (P.N - 1) (by omega)
    have hτN : P.rep.τ (P.N : ℕ) = P.T := P.rep.τ_N
    rw [show P.N - 1 + 1 = P.N by omega, hτN] at h1
    have h2 := wd_seam P hΦT hΦ hL (cg_outB_ne P ((P.N - 1 : ℕ) : ℤ))
    have hA0 : A 0 = wd_kap L (P.g 0) (P.X 0) (Φ 0) (cg_inB P 0) := by
      simp only [hA, hκ, Nat.cast_zero, P.rep.τ_zero]
    rw [hA0, ← h1]
    simp only [hκ]
    rw [h2, hc]
    rcases cg_seam_vec P with e | e <;> rw [e]
    rw [wd_kap_neg]
  have := htel (P.N - 1) (by omega)
  rw [show P.N - 1 + 1 = P.N by omega, hlast] at this
  show ∑ n ∈ Finset.range P.N, (B n - A n) = π / 3
  rw [this]
  ring

/-! ### The costate angles -/

/-- **The angle at a reverse centre** `- -`: `arccos(e_c/√(d_{c-1} d_c)) = π/3 + δ_c`. -/
theorem cg_angle_mm (P : NormalPeriod) {Φ : ℝ → ℝ}
    (hΦ : ∀ t ∈ Icc 0 P.T, wd_IsAng (Φ t) (Reduction.scb_zc (P.g t))) {Q : Mat2}
    (hQ : Q.det < 0)
    (hS : ∀ x y, elQ (P.costateCycle.Sloc 0) x y =
      (Q *ᵥ x) 0 * (Q *ᵥ y) 0 + (Q *ᵥ x) 1 * (Q *ᵥ y) 1)
    {c : ℕ} (hcN : c < P.N) (hin : P.rep.label c = P.rep.label (c - 1) - 1)
    (hout : P.rep.label (c + 1) = P.rep.label c - 1) :
    Real.arccos (P.costateCycle.cre c /
        √(P.costateCycle.swd (c - 1) * P.costateCycle.swd c)) =
      π / 3 + (wd_kap (Q * wd_K P) (P.g (P.rep.τ c)) (P.X (P.rep.τ c)) (Φ (P.rep.τ c))
          (cg_outB P c) -
        wd_kap (Q * wd_K P) (P.g (P.rep.τ c)) (P.X (P.rep.τ c)) (Φ (P.rep.τ c))
          (cg_inB P c)) := by
  have hne : ¬ P.rep.label c = P.rep.label ((c : ℤ) - 1) + 1 := by rw [hin]; exact cg_fin_ne _
  have hne' : ¬ P.rep.label ((c : ℤ) + 1) = P.rep.label c + 1 := by rw [hout]; exact cg_fin_ne _
  rw [wd_centre P hΦ hQ hS hcN hin hout]
  unfold cg_inB cg_outB
  rw [ite_eq_right hne, ite_eq_right hne']
  ring

/-- **The angle at a forward piece** `+ +`: `arccos(e_c/√(d_{c-1} d_c)) = π/3 - δ_c`. -/
theorem cg_angle_pp (P : NormalPeriod) {Φ : ℝ → ℝ}
    (hΦ : ∀ t ∈ Icc 0 P.T, wd_IsAng (Φ t) (Reduction.scb_zc (P.g t))) {Q : Mat2}
    (hQ : Q.det < 0)
    (hS : ∀ x y, elQ (P.costateCycle.Sloc 0) x y =
      (Q *ᵥ x) 0 * (Q *ᵥ y) 0 + (Q *ᵥ x) 1 * (Q *ᵥ y) 1)
    {c : ℕ} (hcN : c < P.N) (hin : P.rep.label c = P.rep.label (c - 1) + 1)
    (hout : P.rep.label (c + 1) = P.rep.label c + 1) :
    Real.arccos (P.costateCycle.cre c /
        √(P.costateCycle.swd (c - 1) * P.costateCycle.swd c)) =
      π / 3 - (wd_kap (Q * wd_K P) (P.g (P.rep.τ c)) (P.X (P.rep.τ c)) (Φ (P.rep.τ c))
          (cg_outB P c) -
        wd_kap (Q * wd_K P) (P.g (P.rep.τ c)) (P.X (P.rep.τ c)) (Φ (P.rep.τ c))
          (cg_inB P c)) := by
  set C := P.costateCycle with hC
  have hin' : C.lab c = C.lab (c - 1) + 1 := hin
  have hout' : C.lab ((c : ℤ) + 1) = C.lab c + 1 := hout
  obtain ⟨hcre, hdet⟩ := C.cross_pp hin' hout'
  have hsin := C.Sloc_in c
  have hsout := C.Sloc_out c
  set a := C.pre c *ᵥ C.inc c with ha
  set b := C.pre c *ᵥ C.outv c with hb
  have hsym : ∀ x y, elQ (C.Sloc 0) x y = elQ (C.Sloc 0) y x := elQ_comm (C.Sloc_symm 0)
  have e1 : C.cre c = elQ (C.Sloc 0) b a := by rw [hsym, ← hcre, ha, hb, C.elQ_pre]
  have e2 : C.swd (c - 1) = elQ (C.Sloc 0) a a := by rw [← hsin, ha, C.elQ_pre]
  have e3 : C.swd c = elQ (C.Sloc 0) b b := by rw [← hsout, hb, C.elQ_pre]
  have hba : elDet b a < 0 := by
    have hab : elDet a b = 1 / (C.act c ^ 2 + 4) := by rw [ha, hb, C.elDet_pre, hdet]
    have : elDet b a = -elDet a b := by simp only [elDet]; ring
    rw [this, hab]
    have : 0 < 1 / (C.act c ^ 2 + 4) := by positivity
    linarith
  rw [e1, e2, e3, mul_comm (elQ (C.Sloc 0) a a), wd_arccos_eq_arg hQ hS hba]
  -- the switch vectors in the physical frame
  obtain ⟨s, hs, hpre⟩ := wd_pre_phys P hcN.le
  set V := P.g (P.rep.τ c) * P.X (P.rep.τ c) with hV
  have hss : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hsw1 := C.sw_pos (c - 1)
  have hsw2 := C.sw_pos c
  have hq := C.q_pos c
  have hinc : C.inc c = (-(1 / C.sw (c - 1))) • ![0, 1] := by
    rw [C.inc_fwd hin']; ext i; fin_cases i <;> simp
  have houtv : C.outv c = (-(C.q c / C.sw c)) • ![-1, 0] := by
    rw [C.outv_fwd hout']; ext i; fin_cases i <;> simp
  have hQa : Q *ᵥ a = (s * -(1 / C.sw (c - 1))) • ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ
      (P.X (P.rep.τ c) *ᵥ wd_bout (P.rep.label c)))) := by
    rw [ha, hpre, hinc, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, smul_smul, ← wd_triCinv_out]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hV]
  have hQb : Q *ᵥ b = (s * -(C.q c / C.sw c)) • ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ
      (P.X (P.rep.τ c) *ᵥ wd_bin (P.rep.label c)))) := by
    rw [hb, hpre, houtv, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, smul_smul, ← wd_triCinv_in]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, hV]
  have hdetL : 0 < (Q * wd_K P).det := by
    rw [Matrix.det_mul, wd_det_K]; have : (0 : ℝ) < √3 := by positivity
    nlinarith
  have hG := wd_good P hΦ hdetL (wd_τ_mem P hcN.le)
  have hMin := wd_toC_ne (wd_mulVec_ne hdetL.ne' (hG.gXne (wd_bin_ne (P.rep.label c))))
  rw [hQa, hQb, sc_toC_smul, sc_toC_smul]
  have hpos : 0 < (s * -(1 / C.sw (c - 1))) / (s * -(C.q c / C.sw c)) := by
    have : (s * -(1 / C.sw (c - 1))) / (s * -(C.q c / C.sw c)) =
        C.sw c / (C.q c * C.sw (c - 1)) := by field_simp
    rw [this]; positivity
  rw [show ((s * -(1 / C.sw (c - 1)) : ℝ) : ℂ) * sc_toC ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ
      (P.X (P.rep.τ c) *ᵥ wd_bout (P.rep.label c)))) /
      (((s * -(C.q c / C.sw c) : ℝ) : ℂ) * sc_toC ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ
      (P.X (P.rep.τ c) *ᵥ wd_bin (P.rep.label c))))) =
      (((s * -(1 / C.sw (c - 1))) / (s * -(C.q c / C.sw c)) : ℝ) : ℂ) *
        (sc_toC ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ (P.X (P.rep.τ c) *ᵥ
          wd_bout (P.rep.label c)))) /
        sc_toC ((Q * wd_K P) *ᵥ (P.g (P.rep.τ c) *ᵥ (P.X (P.rep.τ c) *ᵥ
          wd_bin (P.rep.label c))))) by
    have h0 : s * -(C.q c / C.sw c) ≠ 0 := by
      have : 0 < C.q c / C.sw c := by positivity
      exact mul_ne_zero hss (by linarith)
    have : ((s * -(C.q c / C.sw c) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0
    push_cast
    field_simp]
  rw [Complex.arg_real_mul _ hpos, wd_kap_seg hG (wd_det_bin_bout _), wd_arg_bout_bin]
  unfold cg_inB cg_outB
  rw [ite_eq_left hin, ite_eq_left hout]
  ring

end SmoothedOctagon
