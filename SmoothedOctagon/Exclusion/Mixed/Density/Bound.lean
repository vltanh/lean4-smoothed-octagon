module

public import SmoothedOctagon.Exclusion.Mixed.Density.Winding
public import SmoothedOctagon.Exclusion.Mixed.Density.Local

/-!
# The lower Casimir bound of a competitive mixed period

`MIXED_GLOBAL_REVERSE_ANGLE_DENSITY` §3, (10): a competitive mixed normal period has
`γ² > 27/256` (`NormalPeriod.cg_cas_gt`).

Proof. Suppose `γ² ≤ 27/256`. At every piece with equal incident signs the Gram identity
`d_- d_+ - e² = γ²/K²`, `K > 4`, `d_± ≥ 3/32` forces `4 e² > d_- d_+` (`cg_good`), i.e. the
costate angle avoids `[π/3, 2π/3]`. At a forward piece `+ +` the angle is at most `2π/3`
(`CostateCycle.cg_pp_bound`), hence below `π/3`: its increment `δ = π/3 - angle` is positive
(`cg_angle_pp`). At a reverse centre `- -` the angle exceeds `2π/5` (`m1_angle_gap` through
`NormalPeriod.cg_centreData`), hence `2π/3`: its increment `δ = angle - π/3` exceeds `π/3`
(`cg_angle_mm`). At a turn `δ = 0`. A mixed period has a reverse centre, so `∑ δ > π/3`,
against the winding identity `∑ δ = π/3` (`cg_winding`).

Route: MGRAD §3 selects an edge with gauged angle in `[π/3, 2π/3)` from the count `n/P ≥ 1/3`
of the whole-period winding; here the same winding is used in its telescoped form
`∑ δ = π/3`. The reverse bound is the proved `cos φ < 3/10` (MGSRAE (1)) instead of MGRAD (1)
`cos φ < 1/4` (only `cos φ < 1/2` is needed), and forward acuteness is replaced by the weaker
`cg_pp_bound`.

## Main API

* `NormalPeriod.cg_cas_gt`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set SmoothedPolygons
open scoped Matrix

namespace NormalPeriod

/-- **The lower Casimir bound of a competitive mixed period** (MGRAD (10)): `γ² > 27/256`. -/
theorem cg_cas_gt (P : NormalPeriod) (hc : P.IsCompetitive) (hmix : P.rep.IsMixed) :
    27 / 256 < P.costateCycle.gam2 0 := by
  set C := P.costateCycle with hC
  by_contra hle
  push Not at hle
  have hpos := P.gam2_pos_of_mixed hmix
  have hdge := P.swd_ge_of_mixed hmix
  have hd0 : 0 < C.swd 0 := by have := hdge 0; linarith
  have hcap := P.gam2_le_cap hc hpos hd0
  -- no piece with equal incident signs has `4 e² ≤ d_- d_+`
  have hbad : ∀ k : ℤ,
      C.swd (k - 1) * C.swd k - C.cre k ^ 2 = C.gam2 k / (C.act k ^ 2 + 4) ^ 2 →
      C.swd (k - 1) * C.swd k < 4 * C.cre k ^ 2 := by
    intro k hg
    by_contra h4
    push Not at h4
    rw [C.gam2_eq] at hg
    have := cg_good (C.act_pos k) (hdge (k - 1)) (hdge k) hg h4
    linarith
  have hW : ∀ k : ℤ, 0 < √(C.swd (k - 1) * C.swd k) := fun k ↦
    Real.sqrt_pos.2 (mul_pos (by linarith [hdge (k - 1)]) (by linarith [hdge k]))
  have hW2 : ∀ k : ℤ, √(C.swd (k - 1) * C.swd k) ^ 2 = C.swd (k - 1) * C.swd k := fun k ↦
    Real.sq_sqrt (mul_pos (by linarith [hdge (k - 1)]) (by linarith [hdge k])).le
  -- the costate metric and its factor
  have hsym := C.Sloc_symm 0
  have hdetS : (C.Sloc 0).det = C.gam2 0 := by
    rw [CostateCycle.Sloc, Matrix.det_neg, Matrix.det_mul, C.det_Mloc]
    simp [elJ0, Matrix.det_fin_two]
  have hS00 : 0 < C.Sloc 0 0 0 := by
    have hq : 0 < elQ (C.Sloc 0) (C.yv 0) (C.yv 0) := by
      rw [C.yv_norm]; exact_mod_cast hd0
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
  set δ : ℕ → ℝ := fun n ↦
    wd_kap (Q * wd_K P) (P.g (P.rep.τ n)) (P.X (P.rep.τ n)) (Φ (P.rep.τ n)) (cg_outB P n) -
      wd_kap (Q * wd_K P) (P.g (P.rep.τ n)) (P.X (P.rep.τ n)) (Φ (P.rep.τ n)) (cg_inB P n)
    with hδ
  have hw : ∑ n ∈ Finset.range P.N, δ n = π / 3 := cg_winding P hΦc hΦT hΦ hL
  -- a reverse centre has `δ > π/3`
  have hmm : ∀ n : ℕ, n < P.N → P.rep.IsReverse ((n : ℤ) - 1) → P.rep.IsReverse n →
      π / 3 < δ n := by
    intro n hn hr1 hr0
    have hf : P.rep.IsForward ((n : ℤ) - 2) ∧ P.rep.IsForward ((n : ℤ) + 1) := by
      rcases P.rev_run hmix hr1 with ⟨h1, -, h3⟩ | ⟨-, -, h3⟩
      · refine ⟨by rw [show (n : ℤ) - 2 = (n : ℤ) - 1 - 1 by ring]; exact h1, ?_⟩
        rw [show (n : ℤ) + 1 = (n : ℤ) - 1 + 2 by ring]; exact h3
      · rw [sub_add_cancel] at h3; exact absurd ⟨h3, hr0⟩ (P.rep.el_not_fwd_rev _)
    have hin : P.rep.label n = P.rep.label ((n : ℤ) - 1) - 1 := by
      have h : P.rep.label ((n : ℤ) - 1 + 1) = P.rep.label ((n : ℤ) - 1) - 1 := hr1
      rwa [sub_add_cancel] at h
    have hout : P.rep.label ((n : ℤ) + 1) = P.rep.label n - 1 := hr0
    have hD := P.cg_centreData hmix hf.1 hr1 hr0 hf.2
    have hgap := m1_angle_gap hD hcap
    simp only [m1_E, m1_u, m1_v] at hgap
    rw [show 8 * C.swd ((n : ℤ) - 1) * (8 * C.swd n) =
        8 ^ 2 * (C.swd ((n : ℤ) - 1) * C.swd n) by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)] at hgap
    have hg := hbad n (C.gram_mm hin hout)
    have hx : C.cre n / √(C.swd ((n : ℤ) - 1) * C.swd n) < -1 / 2 := by
      have hW' := hW n
      have hW2' := hW2 n
      rw [div_lt_iff₀ hW']
      by_contra hcon
      push Not at hcon
      have h1 : 0 ≤ √(C.swd ((n : ℤ) - 1) * C.swd n) / 2 + C.cre n := by linarith
      have h2 : 0 ≤ √(C.swd ((n : ℤ) - 1) * C.swd n) / 2 - C.cre n := by linarith
      nlinarith [mul_nonneg h1 h2]
    have hang := cg_angle_mm P hΦ hQ hS hn hin hout
    have := cg_arccos_gt hx
    rw [hang] at this
    simp only [hδ]
    linarith
  -- every increment is nonnegative
  have hnn : ∀ n ∈ Finset.range P.N, 0 ≤ δ n := by
    intro n hn
    have hnN := Finset.mem_range.1 hn
    rcases P.rep.el_fwd_or_rev ((n : ℤ) - 1) with hf1 | hr1 <;>
      rcases P.rep.el_fwd_or_rev (n : ℤ) with hf0 | hr0
    · -- `+ +`
      have hin : P.rep.label n = P.rep.label ((n : ℤ) - 1) + 1 := by
        have h : P.rep.label ((n : ℤ) - 1 + 1) = P.rep.label ((n : ℤ) - 1) + 1 := hf1
        rwa [sub_add_cancel] at h
      have hout : P.rep.label ((n : ℤ) + 1) = P.rep.label n + 1 := hf0
      have hg := hbad n (C.gram_pp hin hout)
      have hb := C.cg_pp_bound (k := n) hin hout
      have he : 0 ≤ C.cre n := by
        rcases hb with h | h
        · exact h
        · linarith
      have hx : 1 / 2 < C.cre n / √(C.swd ((n : ℤ) - 1) * C.swd n) := by
        have hW' := hW n
        have hW2' := hW2 n
        rw [lt_div_iff₀ hW']
        by_contra hcon
        push Not at hcon
        have h2 : C.cre n ≤ √(C.swd ((n : ℤ) - 1) * C.swd n) / 2 := by linarith
        have h3 := pow_le_pow_left₀ he h2 2
        nlinarith
      have hang := cg_angle_pp P hΦ hQ hS hnN hin hout
      have := cg_arccos_lt hx
      rw [hang] at this
      simp only [hδ]
      linarith
    · -- the turn `+ -`
      have hin : P.rep.label n = P.rep.label ((n : ℤ) - 1) + 1 := by
        have h : P.rep.label ((n : ℤ) - 1 + 1) = P.rep.label ((n : ℤ) - 1) + 1 := hf1
        rwa [sub_add_cancel] at h
      simp only [hδ, cg_turn_fr P hin hr0, sub_self, le_refl]
    · -- the turn `- +`
      have hin : P.rep.label n = P.rep.label ((n : ℤ) - 1) - 1 := by
        have h : P.rep.label ((n : ℤ) - 1 + 1) = P.rep.label ((n : ℤ) - 1) - 1 := hr1
        rwa [sub_add_cancel] at h
      simp only [hδ, cg_turn_rf P hin hf0, sub_self, le_refl]
    · -- `- -`
      have := hmm n hnN hr1 hr0
      have := Real.pi_pos
      linarith
  -- a reverse centre in the first period
  obtain ⟨c, hc1, hc0⟩ : ∃ c : ℤ, P.rep.IsReverse (c - 1) ∧ P.rep.IsReverse c := by
    obtain ⟨k, hk⟩ := hmix.2
    rcases P.rev_run hmix hk with ⟨-, h2, -⟩ | ⟨-, h2, -⟩
    · exact ⟨k + 1, by rw [add_sub_cancel_right]; exact hk, h2⟩
    · exact ⟨k, h2, hk⟩
  have hN : (0 : ℤ) < P.N := by exact_mod_cast P.rep.N_pos
  set c' := c % (P.N : ℤ) with hc'
  have hc'0 : 0 ≤ c' := Int.emod_nonneg _ hN.ne'
  have hc'N : c' < P.N := Int.emod_lt_of_pos _ hN
  have hcc : c' + (c / (P.N : ℤ)) * P.N = c := by
    rw [hc', Int.emod_def]; ring
  have hr0' : P.rep.IsReverse c' := by
    rw [← P.rep.el_rev_shift c' (c / (P.N : ℤ))]
    rw [show c' + c / (P.N : ℤ) * (P.rep.N : ℤ) = c by exact hcc]; exact hc0
  have hr1' : P.rep.IsReverse (c' - 1) := by
    rw [← P.rep.el_rev_shift (c' - 1) (c / (P.N : ℤ))]
    rw [show c' - 1 + c / (P.N : ℤ) * (P.rep.N : ℤ) = c - 1 by
      have : c' + c / (P.N : ℤ) * (P.rep.N : ℤ) = c := hcc
      linarith]
    exact hc1
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = c' := ⟨c'.toNat, Int.toNat_of_nonneg hc'0⟩
  have hnN : n < P.N := by omega
  rw [← hn] at hr0' hr1'
  have hbig := hmm n hnN hr1' hr0'
  have hle' := Finset.single_le_sum hnn (Finset.mem_range.2 hnN)
  rw [hw] at hle'
  linarith

end NormalPeriod

end SmoothedOctagon
