module

public import SmoothedOctagon.Exclusion.Mixed.Defect.Frame

/-!
# Case M2, smaller-short window: the window defect of a two-piece window

The spectral cost bound on the window of the two pieces `k`, `k + 1` (switch `k → k + 1` forward)
of a competitive normal period with negative elliptic `Λ₁(0)`, with the endpoint traces read in
rotated triangular coordinates.

The window angle is `θ = Θ(τ_{k+2}) - Θ(τ_k)` for the continuous polar angle `Θ` of
`NormalPeriod.df_angle`; the whole period turns by exactly `π/3` (the cost cap excludes the other
windings), so `0 < θ < π/3` (the complement of the window has positive duration), and integrating
`3 m_b ≥ (κ + 3/2) θ'` over the complement gives `C_W + (κ + 3/2)(π/3 - θ) ≤ C`. The endpoint
product `4 z(B(τ_{k+2})) conj z(B(τ_k))` is `ρ_W e^{iθ}` with `ρ_W ≥ 4`, and its real and imaginary
parts are `tr M + tr(J Λ M)/κ` and `tr(Λ M)/κ - tr(J M)` (`df_zc_prod`). A window across the seam
`τ_N = T` is read through the twist (`g(T) = R`, `X(T) = R⁻¹ X(0) R`).

## Main API

* `df_Xs`, `df_Xt`, `df_Mw`, `df_Lw`: the window frame and costate in rotated triangular
  coordinates, from the costate cycle (all `N`-periodic: `df_Mw_add`, `df_Lw_add`, ...).
* `df_polar_prod`, `NormalPeriod.df_m_eq'`.
* `NormalPeriod.df_window0` (`0 ≤ k < N`), `NormalPeriod.df_window` (every `k : ℤ`): the window
  defect inequality with its polar data.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Real Set Reduction MeasureTheory

section Data

variable {N : ℕ} (C : CostateCycle N)

/-- The state at the switch `k`, rotated to the label of piece `k`. -/
noncomputable def df_Xs (k : ℤ) : Mat2 := triY fun j ↦ C.m k (j + C.lab k)

/-- The state at the switch `k + 2`, rotated to the label of piece `k`. -/
noncomputable def df_Xt (k : ℤ) : Mat2 := triY fun j ↦ C.m (k + 2) (j + C.lab k)

/-- The relative frame of the window of the pieces `k`, `k + 1`. -/
noncomputable def df_Mw (k : ℤ) : Mat2 :=
  -(df_Xs C k * Term.triFactor 0 (C.q k) * Term.triFactor 1 (C.q (k + 1)) * df_Xt C k)

/-- The costate at the switch `k`. -/
noncomputable def df_Lw (k : ℤ) : Mat2 := -√12 • (df_Xs C k * C.Mloc k * df_Xs C k)

theorem df_Xs_add (k : ℤ) : df_Xs C (k + N) = df_Xs C k := by
  simp only [df_Xs, C.m_add, C.lab_add]
  congr 1; funext j; congr 1; abel

theorem df_Xt_add (k : ℤ) : df_Xt C (k + N) = df_Xt C k := by
  simp only [df_Xt, show k + N + 2 = k + 2 + N by ring, C.m_add, C.lab_add]
  congr 1; funext j; congr 1; abel

theorem df_Mloc_add (k : ℤ) : C.Mloc (k + N) = C.Mloc k := by
  simp only [CostateCycle.Mloc, C.mu_add, C.lab_add]
  congr 1; funext j; congr 1; abel

theorem df_Mw_add (k : ℤ) : df_Mw C (k + N) = df_Mw C k := by
  simp only [df_Mw, df_Xs_add, df_Xt_add, C.q_add, show k + N + 1 = k + 1 + N by ring]

theorem df_Lw_add (k : ℤ) : df_Lw C (k + N) = df_Lw C k := by
  simp only [df_Lw, df_Xs_add, df_Mloc_add]

theorem df_fwd_add (k : ℤ) : C.m2Fwd (k + N) ↔ C.m2Fwd k := by
  simp only [CostateCycle.m2Fwd, show k + N + 1 = k + 1 + N by ring, C.lab_add]
  constructor
  · intro h; exact add_right_cancel h
  · intro h; rw [h]

end Data

/-- `4 z₀ e^{L₁} e^{iφ} conj(z₀ e^{L₂}) = 4 |z₀|² e^{Re L₁ + Re L₂} e^{i(Im L₁ - Im L₂ + φ)}`. -/
theorem df_polar_prod (z0 L1 L2 : ℂ) (φ : ℝ) :
    (4 * (z0 * Complex.exp L1 * Complex.exp (φ * Complex.I) *
        (starRingEnd ℂ) (z0 * Complex.exp L2))).re =
      4 * Complex.normSq z0 * Real.exp (L1.re + L2.re) * Real.cos (L1.im - L2.im + φ) ∧
    (4 * (z0 * Complex.exp L1 * Complex.exp (φ * Complex.I) *
        (starRingEnd ℂ) (z0 * Complex.exp L2))).im =
      4 * Complex.normSq z0 * Real.exp (L1.re + L2.re) * Real.sin (L1.im - L2.im + φ) := by
  have e : z0 * Complex.exp L1 * Complex.exp (φ * Complex.I) *
      (starRingEnd ℂ) (z0 * Complex.exp L2) =
      (Complex.normSq z0 : ℂ) * Complex.exp (L1 + φ * Complex.I + (starRingEnd ℂ) L2) := by
    rw [map_mul, ← Complex.exp_conj, Complex.exp_add, Complex.exp_add, ← Complex.mul_conj]
    ring
  have hre : (L1 + φ * Complex.I + (starRingEnd ℂ) L2).re = L1.re + L2.re := by simp
  have him : (L1 + φ * Complex.I + (starRingEnd ℂ) L2).im = L1.im - L2.im + φ := by
    simp; ring
  rw [e]
  constructor
  · rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul, Complex.exp_re, hre, him]
    ring
  · rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.im_ofReal_mul, Complex.exp_im, hre, him]
    ring

namespace NormalPeriod

variable (P : NormalPeriod)

/-- The switch margins at `τ_k`, `0 ≤ k ≤ N`. -/
theorem df_m_eq' {k : ℤ} (hk0 : 0 ≤ k) (hkN : k ≤ P.N) (j : Fin 3) :
    P.costateCycle.m k j = margin j (P.X (P.rep.τ k)) := by
  rcases lt_or_eq_of_le hkN with h | h
  · exact P.df_m_eq hk0 h j
  · subst h
    have e := P.costateCycle.m_add 0 j
    rw [zero_add] at e
    rw [e, P.df_m_eq le_rfl (by exact_mod_cast P.rep.N_pos), P.margin_τ_N, P.rep.τ_zero]

/-- **The window defect of the two pieces `k`, `k + 1`**, `0 ≤ k < N`. -/
theorem df_window0 (hc : P.IsCompetitive) (hdet : 0 < (P.Λ₁ 0).det) (h10 : (P.Λ₁ 0) 1 0 < 0)
    (hN : 3 ≤ P.N) {k : ℤ} (hk0 : 0 ≤ k) (hkN : k < P.N) (hf : P.costateCycle.m2Fwd k) :
    ∃ θ ρw : ℝ, 0 < θ ∧ θ < π / 3 ∧ 4 ≤ ρw ∧
      (df_Mw P.costateCycle k).trace +
          (df_Jt * df_Lw P.costateCycle k * df_Mw P.costateCycle k).trace / √(P.Λ₁ 0).det =
        ρw * Real.cos θ ∧
      (df_Lw P.costateCycle k * df_Mw P.costateCycle k).trace / √(P.Λ₁ 0).det -
          (df_Jt * df_Mw P.costateCycle k).trace = ρw * Real.sin θ ∧
      √3 / 4 * (P.costateCycle.arc k + P.costateCycle.arc (k + 1)) +
          (√(P.Λ₁ 0).det + 3 / 2) * (π / 3 - θ) ≤ P.cost := by
  obtain ⟨h₀, hh₀, hrep, L, hL0, hz, hmono, hbd⟩ := P.df_angle hdet h10
  set κ := √(P.Λ₁ 0).det with hκ
  have hκpos : 0 < κ := Real.sqrt_pos.2 hdet
  have hT := P.T_pos
  set C := P.costateCycle with hC
  have hNz : (0 : ℤ) < P.N := by exact_mod_cast P.rep.N_pos
  have hN3 : (3 : ℤ) ≤ P.N := by exact_mod_cast hN
  have hτ : ∀ j : ℤ, 0 ≤ j → j ≤ P.N → P.rep.τ j ∈ Icc 0 P.T := fun j h0 h1 ↦
    ⟨P.rep.τ_nonneg h0, P.rep.τ_le_T h1⟩
  have hτlt : ∀ j j' : ℤ, j < j' → P.rep.τ j < P.rep.τ j' := fun j j' h ↦ P.rep.τ_strictMono h
  -- the frame `B = h₀⁻¹ g`
  have hdg : ∀ t ∈ Icc 0 P.T, (P.g t).det = 1 := fun t ht ↦
    (P.isStateTrajectory.2.2.2.1 t ht).1
  set B : ℝ → Mat2 := fun t ↦ h₀.adjugate * P.g t with hB
  have hdetadj : h₀.adjugate.det = 1 := by rw [Matrix.det_adjugate, hh₀]; simp
  have hBdet : ∀ t ∈ Icc 0 P.T, (B t).det = 1 := fun t ht ↦ by
    simp only [hB, Matrix.det_mul, hdetadj, hdg t ht, mul_one]
  have hz0 : scb_zc h₀.adjugate ≠ 0 := by
    intro h0
    have := scb_zc_normSq_ge hdetadj
    rw [h0, map_zero] at this; linarith
  set Θ : ℝ → ℝ := fun t ↦ (L t).im with hΘ
  have hΘ0 : Θ 0 = 0 := by simp [hΘ, hL0]
  have hmono' : ∀ s t, 0 ≤ s → s ≤ t → t ≤ P.T → Θ s ≤ Θ t := by
    intro s t hs hst htT
    rcases eq_or_lt_of_le hst with h | h
    · rw [h]
    · exact (hmono s t hs h htT).le
  -- `Λ₁(s) = κ Λ̂(s)`, `Λ̂ = -B⁻¹ J B`
  have hΛs : ∀ s ∈ Icc 0 P.T, P.Λ₁ s = κ • (-((B s).adjugate * J * B s)) := by
    intro s hs
    have hinv : (P.g s)⁻¹ = (P.g s).adjugate := by rw [Matrix.inv_def, hdg s hs]; simp
    have hadjB : (B s).adjugate = (P.g s).adjugate * h₀ := by
      simp only [hB, Matrix.adjugate_mul_distrib]
      rw [Matrix.adjugate_adjugate _ (by simp)]
      simp
    rw [scb_conservation P.extremal s hs, hrep, hinv, hadjB]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_neg, Matrix.neg_mul, smul_neg,
      neg_smul, hB, Matrix.mul_assoc]
  -- the endpoint identity
  have hend : ∀ s ∈ Icc 0 P.T, ∀ M : Mat2,
      (4 * (scb_zc (B s * M) * (starRingEnd ℂ) (scb_zc (B s)))).re =
        M.trace + (J * P.Λ₁ s * M).trace / κ ∧
      (4 * (scb_zc (B s * M) * (starRingEnd ℂ) (scb_zc (B s)))).im =
        (P.Λ₁ s * M).trace / κ - (J * M).trace := by
    intro s hs M
    obtain ⟨h1, h2⟩ := df_zc_prod (M := M) (hBdet s hs)
    have e1 : (4 * (scb_zc (B s * M) * (starRingEnd ℂ) (scb_zc (B s)))).re =
        4 * (scb_zc (B s * M) * (starRingEnd ℂ) (scb_zc (B s))).re := by
      rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.re_ofReal_mul]
    have e2 : (4 * (scb_zc (B s * M) * (starRingEnd ℂ) (scb_zc (B s)))).im =
        4 * (scb_zc (B s * M) * (starRingEnd ℂ) (scb_zc (B s))).im := by
      rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.im_ofReal_mul]
    rw [e1, e2, h1, h2, hΛs s hs]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    constructor <;> field_simp
  -- the total angle is `π/3`
  have hcost : P.cost = 3 * ∫ t in (0 : ℝ)..P.T, scb_rho (P.X t) := by
    simp only [cost, reinhardtCost, scb_rho, intervalIntegral.integral_const_mul]; ring
  have hΘT : Θ P.T = π / 3 := by
    have hzT := hz P.T ⟨hT.le, le_rfl⟩
    have hR : scb_zc (h₀.adjugate * P.g P.T) =
        scb_zc h₀.adjugate * Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I) := by
      rw [P.g_T, el_zc_mul_R]
    rw [hR] at hzT
    have hexp : Complex.exp (L P.T) = Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I) :=
      (mul_left_cancel₀ hz0 hzT).symm
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have hLT : Θ P.T = π / 3 + 2 * π * n := by
      simp only [hΘ, hn]
      simp
      ring
    have hpos : 0 < Θ P.T := by
      have := hmono 0 P.T le_rfl hT le_rfl
      rw [← hΘ0]; exact this
    have hb := hbd 0 P.T le_rfl hT.le le_rfl
    rw [← hcost] at hb
    have hc' : P.cost ≤ octagonCost := hc
    have hA := ifc_octagonCost_lt
    have hpi := Real.pi_gt_three
    have hpi' := Real.pi_lt_d2
    have hn0 : n = 0 := by
      have h1 : (-1 : ℝ) < n := by
        by_contra h; push Not at h
        rw [hLT] at hpos; nlinarith
      have h2 : (n : ℝ) < 1 := by
        by_contra h; push Not at h
        have : (3 / 2) * (π / 3 + 2 * π * n) ≤ (κ + 3 / 2) * (Θ P.T - Θ 0) := by
          rw [hΘ0, sub_zero, hLT]
          apply mul_le_mul_of_nonneg_right (by linarith) (by rw [← hLT]; exact hpos.le)
        nlinarith
      have h1' : (-1 : ℤ) < n := by exact_mod_cast h1
      have h2' : n < (1 : ℤ) := by exact_mod_cast h2
      omega
    rw [hLT, hn0]; simp
  -- integrals of `ρ`
  have hρc : ContinuousOn (fun t ↦ scb_rho (P.X t)) (Icc 0 P.T) :=
    scb_continuousOn_rho P.isStateTrajectory
  have hint : ∀ a b, a ∈ Icc 0 P.T → b ∈ Icc 0 P.T →
      IntervalIntegrable (fun t ↦ scb_rho (P.X t)) volume a b := fun a b ha hb ↦
    (hρc.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have hadd : ∀ a b c, a ∈ Icc 0 P.T → b ∈ Icc 0 P.T → c ∈ Icc 0 P.T →
      (∫ t in a..b, scb_rho (P.X t)) + (∫ t in b..c, scb_rho (P.X t)) =
        ∫ t in a..c, scb_rho (P.X t) := fun a b c ha hb hc ↦
    intervalIntegral.integral_add_adjacent_intervals (hint a b ha hb) (hint b c hb hc)
  have hpiece : ∀ j : ℤ, 0 ≤ j → j < P.N →
      3 * ∫ t in P.rep.τ j..P.rep.τ (j + 1), scb_rho (P.X t) = √3 / 4 * C.arc j := by
    intro j hj0 hjN
    have hp := P.piece_cost hj0 hjN
    have hmod : j % P.N = j := Int.emod_eq_of_lt hj0 hjN
    have e : 3 * ∫ t in P.rep.τ j..P.rep.τ (j + 1), scb_rho (P.X t) =
        -(3 / 2) * ∫ t in P.rep.τ j..P.rep.τ (j + 1), traceForm J (P.X t) := by
      simp only [scb_rho, intervalIntegral.integral_const_mul]; ring
    rw [e, hp]
    simp only [hC, costateCycle, Term.Cycle.arc, termCycle, termMargin, hmod, sub_self, sub_zero,
      arcCost, Term.rawArc, P.activeMargin_eq hj0 hjN]
    ring
  -- rotated triangular coordinates at the switch `k`
  set i := P.rep.label k with hi
  have hsk := hτ k hk0 hkN.le
  have hXs : df_W i * P.X (P.rep.τ k) * df_Wi i = df_Xs C k := by
    rw [df_W_conj_traceless _ (P.isStarState hsk).1, df_Xs]
    congr 1; funext j
    rw [P.df_m_eq hk0 hkN, hC, costateCycle_lab]
  have hLw : df_W i * P.Λ₁ (P.rep.τ k) * df_Wi i = df_Lw C k := by
    rw [P.df_Λ hsk, df_W_conj_smul, df_W_conj_mul, df_W_conj_mul, hXs, ← P.df_Mloc hk0 hkN,
      df_Lw]
  have hf' : P.rep.label (k + 1) = i + 1 := hf
  have hq0 : P.factor k ≠ 0 := (P.factor_pos k).ne'
  -- the traces of a window frame `M` with `W M W⁻¹ = M_w`
  have htr : ∀ M : Mat2, df_W i * M * df_Wi i = df_Mw C k →
      M.trace + (J * P.Λ₁ (P.rep.τ k) * M).trace / κ =
          (df_Mw C k).trace + (df_Jt * df_Lw C k * df_Mw C k).trace / κ ∧
        (P.Λ₁ (P.rep.τ k) * M).trace / κ - (J * M).trace =
          (df_Lw C k * df_Mw C k).trace / κ - (df_Jt * df_Mw C k).trace := by
    intro M hM
    rw [← hM, ← hLw, ← df_W_conj_J i, ← df_W_conj_mul, ← df_W_conj_mul, ← df_W_conj_mul,
      ← df_W_conj_mul, df_trace_conj, df_trace_conj, df_trace_conj, df_trace_conj]
    exact ⟨rfl, rfl⟩
  have hr4 : ∀ s ∈ Icc 0 P.T, ∀ t ∈ Icc 0 P.T,
      4 ≤ 4 * Complex.normSq (scb_zc h₀.adjugate) * Real.exp ((L t).re + (L s).re) := by
    intro s hs t ht
    have h1 := scb_zc_normSq_ge (hBdet s hs)
    have h2 := scb_zc_normSq_ge (hBdet t ht)
    have es : Complex.normSq (scb_zc (B s)) =
        Complex.normSq (scb_zc h₀.adjugate) * Real.exp ((L s).re) ^ 2 := by
      rw [show scb_zc (B s) = _ from hz s hs, map_mul, Complex.normSq_eq_norm_sq (Complex.exp _),
        Complex.norm_exp]
    have et : Complex.normSq (scb_zc (B t)) =
        Complex.normSq (scb_zc h₀.adjugate) * Real.exp ((L t).re) ^ 2 := by
      rw [show scb_zc (B t) = _ from hz t ht, map_mul, Complex.normSq_eq_norm_sq (Complex.exp _),
        Complex.norm_exp]
    rw [es] at h1; rw [et] at h2
    set n0 := Complex.normSq (scb_zc h₀.adjugate)
    have hn0 : 0 ≤ n0 := Complex.normSq_nonneg _
    have hx : Real.exp ((L t).re + (L s).re) = Real.exp ((L t).re) * Real.exp ((L s).re) :=
      Real.exp_add _ _
    have hp : 1 ≤ (n0 * (Real.exp ((L t).re) * Real.exp ((L s).re))) ^ 2 := by
      have := mul_le_mul h1 h2 zero_le_one (by positivity)
      nlinarith
    have hq : 0 ≤ n0 * (Real.exp ((L t).re) * Real.exp ((L s).re)) := by positivity
    have : 1 ≤ n0 * (Real.exp ((L t).re) * Real.exp ((L s).re)) := by nlinarith
    rw [hx]; nlinarith
  by_cases hcase : k + 2 ≤ P.N
  · -- the window lies in `[0, T]`
    set s := P.rep.τ k with hs
    set t := P.rep.τ (k + 2) with ht
    have hst := hτlt k (k + 2) (by omega)
    have htT := hτ (k + 2) (by omega) hcase
    have hk1 := hτ (k + 1) (by omega) (by omega)
    refine ⟨Θ t - Θ s, 4 * Complex.normSq (scb_zc h₀.adjugate) * Real.exp ((L t).re + (L s).re),
      ?_, ?_, hr4 s hsk t htT, ?_, ?_, ?_⟩
    · have := hmono s t hsk.1 hst htT.2; linarith
    · rcases eq_or_lt_of_le hk0 with h0 | h0
      · -- `k = 0`: the window ends before `T`
        have htT' : t < P.T := by
          have := hτlt (k + 2) P.N (by omega); rwa [P.rep.τ_N] at this
        have h1 := hmono t P.T htT.1 htT' le_rfl
        have h2 : Θ s = 0 := by rw [hs, ← h0, P.rep.τ_zero, hΘ0]
        linarith
      · have hs0 : 0 < s := by rw [hs, ← P.rep.τ_zero]; exact hτlt _ _ h0
        have h1 := hmono 0 s le_rfl hs0 hsk.2
        have h2 := hmono' t P.T htT.1 htT.2 le_rfl
        linarith
    all_goals
      have hM : df_W i * ((P.g s)⁻¹ * P.g t) * df_Wi i = df_Mw C k := by
        have e1 := P.df_piece_frame hk0 hkN
        have e2 := P.df_piece_frame (k := k + 1) (by omega) (by omega)
        rw [show k + 1 + 1 = k + 2 by ring] at e2
        have hdg1 := hdg _ hk1
        have hinv1 : P.g (P.rep.τ (k + 1)) * (P.g (P.rep.τ (k + 1)))⁻¹ = 1 :=
          Matrix.mul_nonsing_inv _ (by rw [hdg1]; exact isUnit_one)
        have hX1 := P.isStarState hk1
        have hXX := mul_self_eq_neg_one _ hX1.1 hX1.2.1
        have e : (P.g s)⁻¹ * P.g t = -(P.X s * tangentFactor i (P.factor k) *
            tangentFactor (i + 1) (P.factor (k + 1)) * P.X t) := by
          calc (P.g s)⁻¹ * P.g t =
              ((P.g s)⁻¹ * P.g (P.rep.τ (k + 1))) *
                ((P.g (P.rep.τ (k + 1)))⁻¹ * P.g t) := by
                simp only [Matrix.mul_assoc]
                rw [← Matrix.mul_assoc (P.g (P.rep.τ (k + 1))), hinv1, Matrix.one_mul]
            _ = _ := by
                rw [e1, e2, hf']
                simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
                rw [← Matrix.mul_assoc (P.X (P.rep.τ (k + 1))) (P.X (P.rep.τ (k + 1))), hXX]
                simp only [Matrix.neg_mul, Matrix.one_mul, Matrix.mul_neg]
                rfl
        rw [e, df_W_conj_neg, df_W_conj_mul, df_W_conj_mul, df_W_conj_mul, hXs,
          df_W_conj_tangent0 i hq0, df_W_conj_tangent1 i (P.factor_pos _).ne',
          df_W_conj_traceless _ (P.isStarState htT).1, df_Mw, df_Xt]
        congr 3
        funext j
        rw [P.df_m_eq' (by omega) hcase, hC, costateCycle_lab]
      have hBt : B s * ((P.g s)⁻¹ * P.g t) = B t := by
        have hinv : P.g s * (P.g s)⁻¹ = 1 :=
          Matrix.mul_nonsing_inv _ (by rw [hdg s hsk]; exact isUnit_one)
        simp only [hB, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (P.g s), hinv, Matrix.one_mul]
      obtain ⟨hre, him⟩ := hend s hsk ((P.g s)⁻¹ * P.g t)
      obtain ⟨tr1, tr2⟩ := htr _ hM
      have hzt := hz t htT
      have hzs := hz s hsk
      obtain ⟨p1, p2⟩ := df_polar_prod (scb_zc h₀.adjugate) (L t) (L s) 0
      simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, add_zero] at p1 p2
      rw [hBt] at hre him
      rw [show scb_zc (B t) = _ from hzt, show scb_zc (B s) = _ from hzs] at hre him
    · rw [← tr1, ← hre, p1]
    · rw [← tr2, ← him, p2]
    · -- the cost of the complement
      have i1 := hbd 0 s le_rfl hsk.1 hsk.2
      have i2 := hbd t P.T htT.1 htT.2 le_rfl
      have c1 := hpiece k hk0 hkN
      have c2 := hpiece (k + 1) (by omega) (by omega)
      rw [show k + 1 + 1 = k + 2 by ring] at c2
      have a1 := hadd 0 s t ⟨le_rfl, hT.le⟩ hsk htT
      have a2 := hadd 0 t P.T ⟨le_rfl, hT.le⟩ htT ⟨hT.le, le_rfl⟩
      have a3 := hadd s (P.rep.τ (k + 1)) t hsk hk1 htT
      have hL0' : (L 0).im = 0 := by simp [hL0]
      have hLT' : (L P.T).im = π / 3 := hΘT
      rw [hL0'] at i1
      rw [hLT'] at i2
      show √3 / 4 * (C.arc k + C.arc (k + 1)) + (κ + 3 / 2) * (π / 3 - ((L t).im - (L s).im)) ≤
        P.cost
      calc √3 / 4 * (C.arc k + C.arc (k + 1)) + (κ + 3 / 2) * (π / 3 - ((L t).im - (L s).im)) =
            (κ + 3 / 2) * ((L s).im - 0) + √3 / 4 * C.arc k + √3 / 4 * C.arc (k + 1) +
              (κ + 3 / 2) * (π / 3 - (L t).im) := by ring
        _ ≤ 3 * (∫ r in (0 : ℝ)..s, scb_rho (P.X r)) +
              3 * (∫ r in s..P.rep.τ (k + 1), scb_rho (P.X r)) +
              3 * (∫ r in P.rep.τ (k + 1)..t, scb_rho (P.X r)) +
              3 * (∫ r in t..P.T, scb_rho (P.X r)) := by linarith
        _ = P.cost := by rw [hcost, ← a2, ← a1, ← a3]; ring
  · -- the window crosses the seam: `k = N - 1`
    have hkN1 : k = P.N - 1 := by omega
    set s := P.rep.τ k with hs
    set t := P.rep.τ 1 with ht
    have h1 : (1 : ℤ) ≤ P.N := by omega
    have htT := hτ 1 (by norm_num) h1
    have hts : t < s := hτlt 1 k (by omega)
    refine ⟨Θ t - Θ s + π / 3,
      4 * Complex.normSq (scb_zc h₀.adjugate) * Real.exp ((L t).re + (L s).re),
      ?_, ?_, hr4 s hsk t htT, ?_, ?_, ?_⟩
    · have hsT : s < P.T := by
        have := hτlt k P.N (by omega); rwa [P.rep.τ_N] at this
      have h1 := hmono s P.T hsk.1 hsT le_rfl
      have h2 := hmono' 0 t le_rfl htT.1 htT.2
      linarith
    · have := hmono t s htT.1 hts hsk.2; linarith
    all_goals
      have hM : df_W i * ((P.g s)⁻¹ * P.g t * R) * df_Wi i = df_Mw C k := by
        have e1 := P.df_piece_frame hk0 hkN
        have e0 := P.df_piece_frame (k := 0) le_rfl hNz
        rw [show k + 1 = (P.N : ℤ) by omega, P.rep.τ_N, P.g_T] at e1
        rw [zero_add, P.rep.τ_zero, P.g_zero, inv_one, Matrix.one_mul] at e0
        have hX0 := P.isStarState (t := 0) ⟨le_rfl, hT.le⟩
        have hXX := mul_self_eq_neg_one _ hX0.1 hX0.2.1
        have hlab : P.rep.label 0 + 1 = i + 1 := by
          have := P.rep.label_add_period 0
          rw [zero_add] at this
          rw [← this, ← hf', show k + 1 = (P.N : ℤ) by omega]
        have hfac : P.factor 0 = P.factor (k + 1) := by
          rw [show k + 1 = 0 + (P.N : ℤ) by omega, P.factor_add_N]
        have hRR : R * R⁻¹ = (1 : Mat2) := poly_R_mul_inv
        have hRR' : R⁻¹ * R = (1 : Mat2) := poly_inv_mul_R
        have hRl : ∀ Y : Mat2, R * (R⁻¹ * Y) = Y := fun Y ↦ by
          rw [← Matrix.mul_assoc, hRR, Matrix.one_mul]
        have hXl : ∀ Y : Mat2, P.X 0 * (P.X 0 * Y) = -Y := fun Y ↦ by
          rw [← Matrix.mul_assoc, hXX, Matrix.neg_mul, Matrix.one_mul]
        have hTi : tangentFactor (i + 1) (P.factor (k + 1)) =
            R⁻¹ * tangentFactor (P.rep.label 0) (P.factor 0) * R := by
          rw [tangentFactor_Rinv_conj, hlab, hfac]
        have e : (P.g s)⁻¹ * P.g t * R = -(P.X s * tangentFactor i (P.factor k) *
            tangentFactor (i + 1) (P.factor (k + 1)) * (R⁻¹ * P.X t * R)) := by
          have hgs : (P.g s)⁻¹ = -(P.X s * tangentFactor i (P.factor k) * P.X P.T) * R⁻¹ := by
            have e1' : (P.g s)⁻¹ * R = -(P.X s * tangentFactor i (P.factor k) * P.X P.T) := e1
            rw [← e1', Matrix.mul_assoc, hRR, Matrix.mul_one]
          have e0' : P.g t = -(P.X 0 * tangentFactor (P.rep.label 0) (P.factor 0) * P.X t) := e0
          rw [hgs, e0', P.X_T, hTi]
          simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc, hRl, hXl]
        rw [e, df_W_conj_neg, df_W_conj_mul, df_W_conj_mul, df_W_conj_mul, hXs,
          df_W_conj_tangent0 i hq0, df_W_conj_tangent1 i (P.factor_pos _).ne',
          df_W_conj_traceless _ (by
            rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
            exact (P.isStarState htT).1), df_Mw, df_Xt]
        congr 3
        funext j
        rw [margin_Rinv_conj, show k + 2 = 1 + (P.N : ℤ) by omega, C.m_add,
          P.df_m_eq (by norm_num) (by omega), hC, costateCycle_lab]
      have hBt : B s * ((P.g s)⁻¹ * P.g t * R) = B t * R := by
        have hinv : P.g s * (P.g s)⁻¹ = 1 :=
          Matrix.mul_nonsing_inv _ (by rw [hdg s hsk]; exact isUnit_one)
        simp only [hB, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (P.g s), hinv, Matrix.one_mul]
      obtain ⟨hre, him⟩ := hend s hsk ((P.g s)⁻¹ * P.g t * R)
      obtain ⟨tr1, tr2⟩ := htr _ hM
      have hzt := hz t htT
      have hzs := hz s hsk
      obtain ⟨p1, p2⟩ := df_polar_prod (scb_zc h₀.adjugate) (L t) (L s) (π / 3)
      rw [hBt, el_zc_mul_R] at hre him
      rw [show scb_zc (B t) = _ from hzt, show scb_zc (B s) = _ from hzs] at hre him
    · rw [← tr1, ← hre, p1]
    · rw [← tr2, ← him, p2]
    · -- the cost of the complement
      have i1 := hbd t s htT.1 hts.le hsk.2
      have c1 := hpiece k hk0 hkN
      have c0 := hpiece 0 le_rfl hNz
      rw [show k + 1 = (P.N : ℤ) by omega, P.rep.τ_N] at c1
      rw [zero_add, P.rep.τ_zero] at c0
      have harc : C.arc (k + 1) = C.arc 0 := by
        rw [show k + 1 = 0 + (P.N : ℤ) by omega]; exact C.arc_add 0
      have a1 := hadd 0 t s ⟨le_rfl, hT.le⟩ htT hsk
      have a2 := hadd 0 s P.T ⟨le_rfl, hT.le⟩ hsk ⟨hT.le, le_rfl⟩
      have hL0' : (L 0).im = 0 := by simp [hL0]
      have hLT' : (L P.T).im = π / 3 := hΘT
      show √3 / 4 * (C.arc k + C.arc (k + 1)) +
        (κ + 3 / 2) * (π / 3 - ((L t).im - (L s).im + π / 3)) ≤ P.cost
      rw [harc]
      calc √3 / 4 * (C.arc k + C.arc 0) +
            (κ + 3 / 2) * (π / 3 - ((L t).im - (L s).im + π / 3)) =
            √3 / 4 * C.arc 0 + (κ + 3 / 2) * ((L s).im - (L t).im) + √3 / 4 * C.arc k := by ring
        _ ≤ 3 * (∫ r in (0 : ℝ)..t, scb_rho (P.X r)) + 3 * (∫ r in t..s, scb_rho (P.X r)) +
              3 * (∫ r in s..P.T, scb_rho (P.X r)) := by linarith
        _ = P.cost := by rw [hcost, ← a2, ← a1]; ring

/-- **The window defect of the two pieces `k`, `k + 1`** (any `k : ℤ`, switch `k` forward). -/
theorem df_window (hc : P.IsCompetitive) (hdet : 0 < (P.Λ₁ 0).det) (h10 : (P.Λ₁ 0) 1 0 < 0)
    (hN : 3 ≤ P.N) (k : ℤ) (hf : P.costateCycle.m2Fwd k) :
    ∃ θ ρw : ℝ, 0 < θ ∧ θ < π / 3 ∧ 4 ≤ ρw ∧
      (df_Mw P.costateCycle k).trace +
          (df_Jt * df_Lw P.costateCycle k * df_Mw P.costateCycle k).trace / √(P.Λ₁ 0).det =
        ρw * Real.cos θ ∧
      (df_Lw P.costateCycle k * df_Mw P.costateCycle k).trace / √(P.Λ₁ 0).det -
          (df_Jt * df_Mw P.costateCycle k).trace = ρw * Real.sin θ ∧
      √3 / 4 * (P.costateCycle.arc k + P.costateCycle.arc (k + 1)) +
          (√(P.Λ₁ 0).det + 3 / 2) * (π / 3 - θ) ≤ P.cost := by
  set C := P.costateCycle with hC
  have hNz : (0 : ℤ) < P.N := by exact_mod_cast P.rep.N_pos
  have hk : k % P.N = k - (k / P.N) * P.N := by rw [Int.emod_def]; ring
  have p1 : Function.Periodic (df_Mw C) (P.N : ℤ) := df_Mw_add C
  have p2 : Function.Periodic (df_Lw C) (P.N : ℤ) := df_Lw_add C
  have p3 : Function.Periodic C.arc (P.N : ℤ) := C.arc_add
  have p4 : Function.Periodic (fun x ↦ C.arc (x + 1)) (P.N : ℤ) := fun x ↦ by
    simp only [show x + (P.N : ℤ) + 1 = x + 1 + P.N by ring, C.arc_add]
  have p5 : Function.Periodic (fun x ↦ C.m2Fwd x) (P.N : ℤ) := fun x ↦
    propext (df_fwd_add C x)
  have q1 : df_Mw C (k % P.N) = df_Mw C k := by rw [hk]; exact p1.sub_int_mul_eq _
  have q2 : df_Lw C (k % P.N) = df_Lw C k := by rw [hk]; exact p2.sub_int_mul_eq _
  have q3 : C.arc (k % P.N) = C.arc k := by rw [hk]; exact p3.sub_int_mul_eq _
  have q4 : C.arc (k % P.N + 1) = C.arc (k + 1) := by
    rw [hk]; exact p4.sub_int_mul_eq (x := k) _
  have q5 : C.m2Fwd (k % P.N) = C.m2Fwd k := by rw [hk]; exact p5.sub_int_mul_eq (x := k) _
  have h := P.df_window0 hc hdet h10 hN (Int.emod_nonneg _ hNz.ne') (Int.emod_lt_of_pos _ hNz)
    (by rw [q5]; exact hf)
  rw [q1, q2, q3, q4] at h
  exact h

end NormalPeriod

end SmoothedOctagon
