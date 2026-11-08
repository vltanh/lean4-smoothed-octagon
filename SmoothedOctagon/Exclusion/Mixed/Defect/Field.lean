module

public import SmoothedOctagon.Exclusion.Mixed.Defect.Window

/-!
# Case M2, smaller-short window: the window-defect field

The window-defect field for the two-turn window `C, B` (pieces `m + 1`, `m + 2`) after a reverse
centre `a` (piece `m`) whose outgoing turn `C` has a short forward bridge: the field
`M2Short.defect` of `m2_short_window`.

The proof applies the window defect `NormalPeriod.df_window` at `k = m + 1`, with its frame and
costate identified with the cover's rational expressions by `df_alg_traces` and its cost by
`df_alg_cost`; the polar angle `θ ∈ (0, π/3)` of the endpoint product `ρ_W e^{iθ}` (`ρ_W ≥ 4`)
gives `𝒜 = T_κ ρ_W cos θ > 0`, `√3 ℬ = T_κ ρ_W sin θ`, hence `0 < ℬ < 𝒜`,
`𝒜 + ℬ ≥ T_κ ρ_W ≥ 4 T_κ` (the modulus filter) and `θ = arctan(√3 ℬ/𝒜)`. The data `(u, v, E)` of
an arbitrary covector calculus are those of the concrete one, `df_calc` (`M = Mloc`), since both
are fixed by the secants and centre stationarity.

## Main API

* `NormalPeriod.df_calc` (`df_calc_M`, `df_calc_Γ`): the covector calculus with `M = Mloc`,
  `Γ = γ²`.
* `df_rot_vec`: a labelled triple rotated to the label `i`.
* `df_final`: the field from the polar data `𝒜 = T ρ cos θ`, `√3 ℬ = T ρ sin θ`.
* `NormalPeriod.df_defect`: the field `M2Short.defect`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Real Set Certificates.SmallerShort

namespace NormalPeriod

/-- **The covector calculus with `M = Mloc`** (the construction of `m2_calculus`). -/
noncomputable def df_calc (P : NormalPeriod) : P.M2Calculus := by
  set C := P.costateCycle with hC
  have hA : ∀ i, C.m2A i = C.Amat i := fun i ↦ rfl
  have hnorm : ∀ i, C.m2Norm C.Mloc i = 8 * C.swd i := fun i ↦ by
    unfold CostateCycle.m2Norm
    split_ifs with h
    · exact C.ifc_norm_fwd h
    · rcases C.lab_cases i with h' | h'
      · exact absurd h' h
      · exact C.ifc_norm_rev h'
  have hsgn : ∀ i, (C.m2Fwd (i - 1) ↔ C.m2Fwd i) → C.sgn (i - 1) = C.sgn i := by
    intro i h
    simp only [CostateCycle.sgn]
    by_cases h1 : C.m2Fwd i
    · have h0 := h.2 h1
      simp only [CostateCycle.m2Fwd] at h0 h1
      simp only [h0, h1, ↓reduceIte]
    · have h0 : ¬ C.m2Fwd (i - 1) := fun h' ↦ h1 (h.1 h')
      simp only [CostateCycle.m2Fwd] at h0 h1
      simp only [h0, h1, ↓reduceIte]
  have hturn : ∀ i, ¬ (C.m2Fwd (i - 1) ↔ C.m2Fwd i) → C.sgn (i - 1) = -C.sgn i := by
    intro i h
    simp only [CostateCycle.sgn]
    by_cases h1 : C.m2Fwd i
    · have h0 : ¬ C.m2Fwd (i - 1) := fun h' ↦ h ⟨fun _ ↦ h1, fun _ ↦ h'⟩
      simp only [CostateCycle.m2Fwd] at h0 h1
      simp only [h0, h1, ↓reduceIte]
    · have h0 : C.m2Fwd (i - 1) := by
        by_contra h'; exact h ⟨fun h'' ↦ absurd h'' h', fun h'' ↦ absurd h'' h1⟩
      simp only [CostateCycle.m2Fwd] at h0 h1
      simp only [h0, h1, ↓reduceIte]; norm_num
  have hin : ∀ i, C.m2Fwd (i - 1) → C.lab i = C.lab (i - 1) + 1 := fun i h ↦ by
    have := h; simp only [CostateCycle.m2Fwd, sub_add_cancel] at this; exact this
  refine ⟨C.Mloc, C.gam2 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simp [CostateCycle.Mloc, triY, Matrix.trace_fin_two]
    ring
  · intro i
    rw [C.det_Mloc, C.gam2_eq]
  · intro i
    rw [hA, Matrix.inv_eq_left_inv (C.Ainv_Amat i), C.Mloc_succ]
  · intro i h
    rw [hnorm, hnorm, ifc_m2Stat_eq]
    exact C.ifc_stat_M (hsgn i h)
  · intro i h
    rw [hnorm, hnorm]
    exact C.ifc_turn_sec (hturn i h)
  · intro i h
    rw [hnorm, ifc_m2g_eq]
    have := C.swd_fwd (k := i) h
    linarith
  · intro i h
    rw [hnorm, ifc_m2g_eq]
    rcases C.lab_cases i with h' | h'
    · exact absurd h' h
    · have := C.swd_rev h'
      linarith
  · intro i h1 h2
    rw [hnorm, ifc_m2F_eq (C.one_lt_q i)]
    exact C.ifc_floor_in (hin i h1) h2
  · intro i h1 h2
    rw [hnorm, ifc_m2F_eq (C.one_lt_q i)]
    exact C.ifc_floor_out (hin i h1) h2
  · intro i h
    exact C.ifc_mc (hin i h)
  · exact fun hc ↦ P.ifc_cas_lt hc
  · exact fun hc hD hmix ↦ P.ifc_cas_gt hc hD hmix

theorem df_calc_M (P : NormalPeriod) : P.df_calc.M = P.costateCycle.Mloc := rfl

theorem df_calc_Γ (P : NormalPeriod) : P.df_calc.Γ = P.costateCycle.gam2 0 := rfl

/-- A function on the labels, rotated to the label `i`, is `(f i, f (i + 1), f (i - 1))`. -/
theorem df_rot_vec (f : Fin 3 → ℝ) (i : Fin 3) :
    (fun j ↦ f (j + i)) = ![f i, f (i + 1), f (i - 1)] := by
  have e1 : ∀ x : Fin 3, 1 + x = x + 1 := by decide
  have e2 : ∀ x : Fin 3, 2 + x = x - 1 := by decide
  funext j; fin_cases j <;> simp [e1, e2]

/-- The polar endpoint data give the window-defect field: from `𝒜 = T ρ cos θ`,
`√3 ℬ = T ρ sin θ`, `0 < θ < π/3`, `ρ ≥ 4`, `T > 0`. -/
theorem df_final {AA BB Tk κ cost Cper θ ρw : ℝ} (hTk : 0 < Tk) (hθ0 : 0 < θ)
    (hθ1 : θ < π / 3) (hρ4 : 4 ≤ ρw) (hAA : AA = Tk * (ρw * Real.cos θ))
    (hBB : √3 * BB = Tk * (ρw * Real.sin θ))
    (hcost : cost + (κ + 3 / 2) * (π / 3 - θ) ≤ Cper) :
    2 * Tk ≤ AA ∧ 0 < BB ∧ BB < AA ∧ 4 * Tk ≤ AA + BB ∧
      cost + (κ + 3 / 2) * (Real.pi / 3 - Real.arctan (Real.sqrt 3 * BB / AA)) ≤ Cper := by
  have hpi := Real.pi_pos
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith)
  have hs3 : (0 : ℝ) < √3 := by positivity
  have hs3sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hρ : 0 < ρw := by linarith
  have htan : Real.sin θ < √3 * Real.cos θ := by
    have := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) (by linarith) hθ1
    rw [Real.tan_pi_div_three, Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos] at this
    exact this
  have hsc := Real.sin_sq_add_cos_sq θ
  have hBBe : BB = Tk * (ρw * Real.sin θ) / √3 := by
    rw [eq_div_iff hs3.ne', mul_comm]; exact hBB
  have hTr : 0 < Tk * ρw := mul_pos hTk hρ
  have hBpos : 0 < BB := by rw [hBBe]; positivity
  have hBlt : BB < AA := by
    rw [hBBe, hAA, div_lt_iff₀ hs3]
    have := mul_lt_mul_of_pos_left htan hTr
    nlinarith
  have hsum : 1 ≤ Real.cos θ + Real.sin θ / √3 := by
    set t := Real.sin θ / √3 with ht
    have hst : Real.sin θ = √3 * t := by rw [ht]; field_simp
    rw [hst] at htan hsc
    have ht0 : 0 < t := by positivity
    have htc : t < Real.cos θ := by nlinarith
    have hq : 1 ≤ (Real.cos θ + t) ^ 2 := by nlinarith
    nlinarith
  have hA4 : 4 * Tk ≤ AA + BB := by
    rw [hBBe, hAA]
    have e : Tk * (ρw * Real.cos θ) + Tk * (ρw * Real.sin θ) / √3 =
        Tk * ρw * (Real.cos θ + Real.sin θ / √3) := by ring
    rw [e]
    have h1 : 4 * Tk ≤ Tk * ρw := by nlinarith
    have h2 : Tk * ρw * 1 ≤ Tk * ρw * (Real.cos θ + Real.sin θ / √3) :=
      mul_le_mul_of_nonneg_left hsum hTr.le
    linarith
  have harctan : Real.arctan (Real.sqrt 3 * BB / AA) = θ := by
    have e : Real.sqrt 3 * BB / AA = Real.tan θ := by
      rw [hBB, hAA, Real.tan_eq_sin_div_cos]
      field_simp
    rw [e, Real.arctan_tan (by linarith) (by linarith)]
  refine ⟨by linarith, hBpos, hBlt, hA4, ?_⟩
  rw [harctan]
  exact hcost

/-- **The window-defect field** `M2Short.defect` of a smaller-short window. The endpoint traces
come from the costate transport in rotated triangular coordinates (`df_alg_m`, `df_alg_h`). -/
theorem df_defect (P : NormalPeriod) (hc : P.IsCompetitive) (hmix : P.rep.IsMixed)
    (hN : 3 ≤ P.N) (K : P.M2Calculus) {m : ℤ}
    (h2 : P.costateCycle.m2Fwd (m - 2)) (h1 : ¬ P.costateCycle.m2Fwd (m - 1))
    (h0 : ¬ P.costateCycle.m2Fwd m) (h3 : P.costateCycle.m2Fwd (m + 1))
    (h4 : ¬ P.costateCycle.m2Fwd (m + 2))
    (hAC : P.costateCycle.act (m + 3) < P.costateCycle.act (m + 1)) :
    let pt : Point :=
      ⟨P.costateCycle.act m / (P.costateCycle.act m + P.costateCycle.act (m + 1)),
        P.costateCycle.act (m + 2) / P.costateCycle.act (m + 1) - 1,
        P.costateCycle.act (m + 3) / P.costateCycle.act m,
        P.costateCycle.act m ^ 2 / (P.costateCycle.act m ^ 2 + 4),
        P.costateCycle.m2Norm K.M (m - 1),
        16 * K.M m 0 0 / (P.costateCycle.act m ^ 2 + 4)⟩
    2 * pt.Tk ≤ pt.AA ∧ 0 < pt.BB ∧ pt.BB < pt.AA ∧ 4 * pt.Tk ≤ pt.AA + pt.BB ∧
      pt.cost + (pt.kap + 3 / 2) * (Real.pi / 3 - Real.arctan (Real.sqrt 3 * pt.BB / pt.AA)) ≤
        octagonCost := by
  intro pt
  set Y := P.costateCycle with hY
  set K' := P.df_calc with hK'
  have hM' : K'.M = Y.Mloc := rfl
  have hΓ' : K'.Γ = Y.gam2 0 := rfl
  -- margins and positivity
  set a := Y.act m with ha_def
  set b := Y.act (m - 1) with hb_def
  set C := Y.act (m + 1) with hC_def
  set B := Y.act (m + 2) with hB_def
  set A := Y.act (m + 3) with hA_def
  have a0 : 0 < a := Y.act_pos m
  have b0 : 0 < b := Y.act_pos _
  have c0 : 0 < C := Y.act_pos _
  have B0 : 0 < B := Y.act_pos _
  have A0 : 0 < A := Y.act_pos _
  have hK0 : (0 : ℝ) < a ^ 2 + 4 := by positivity
  -- signs at shifted indices
  have h1' : ¬ Y.m2Fwd (m + 1 - 1) := by rw [add_sub_cancel_right]; exact h0
  have h3' : Y.m2Fwd (m + 2 - 1) := by rw [show m + 2 - 1 = m + 1 by ring]; exact h3
  -- factors
  have qm := Y.m2_factor_rr h1 h0
  have q1 := Y.m2_factor_rf h1' h3
  rw [add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring] at q1
  have q2 := Y.m2_factor_fr h3' h4
  rw [show m + 2 - 1 = m + 1 by ring, show m + 2 + 1 = m + 3 by ring] at q2
  have hqm : Y.q m = (a ^ 2 + 4) / ((b + a) * (a + C)) := by
    rw [eq_div_iff (by positivity)]; exact qm
  have hq1 : Y.q (m + 1) = (C + B) / (a + C) := by
    rw [eq_div_iff (by positivity)]; exact q1
  have hq2 : Y.q (m + 2) = (C + B) / (B + A) := by
    rw [eq_div_iff (by positivity)]; exact q2
  have haB : a < B := by
    have := Y.one_lt_q (m + 1)
    rw [hq1, one_lt_div (by positivity)] at this
    linarith
  -- labels
  set i := Y.lab (m + 1) with hi
  have hlm : Y.lab m = i + 1 := by
    have := Y.m2_lab_next_rev h0
    rw [← hi] at this
    rw [this]; abel
  have hl2 : Y.lab (m + 2) = i + 1 := by
    have : Y.lab (m + 1 + 1) = Y.lab (m + 1) + 1 := h3
    rwa [show m + 1 + 1 = m + 2 by ring] at this
  have hl3 : Y.lab (m + 3) = i := by
    have := Y.m2_lab_next_rev h4
    rw [show m + 2 + 1 = m + 3 by ring, hl2] at this
    rw [this]; abel
  -- switch margins
  set n := Y.m (m + 1) (i - 1) with hn
  set p := Y.m (m + 3) (i - 1) with hp
  have e1i : Y.m (m + 1) i = C := rfl
  have e1s : Y.m (m + 1) (i + 1) = a := by
    rw [← hlm]; exact Y.m_act m
  have e3i : Y.m (m + 3) i = A := by rw [← hl3]; rfl
  have e3s : Y.m (m + 3) (i + 1) = B := by
    rw [← hl2]
    have := Y.m_act (m + 2)
    rwa [show m + 2 + 1 = m + 3 by ring] at this
  have e2s : Y.m (m + 2) (i + 1) = B := by rw [← hl2]; rfl
  have e2i : Y.m (m + 2) i = C := by
    have := Y.m_act (m + 1)
    rwa [show m + 1 + 1 = m + 2 by ring] at this
  have e2d : Y.m (m + 2) (i - 1) = (C + n) / Y.q (m + 1) - C := by
    have := Y.m_decr (m + 1)
    rwa [show m + 1 + 1 = m + 2 by ring] at this
  have quad1 := Y.quad_rot (m + 1) i
  rw [e1i, e1s] at quad1
  have quad3 := Y.quad_rot (m + 3) i
  rw [e3i, e3s] at quad3
  -- the window data in the cover's coordinates
  have hXs : df_Xs Y (m + 1) = df_tri C a := by
    rw [df_Xs, df_rot_vec, e1i, e1s, df_triY_eq quad1 (by positivity)]
  have hXt : df_Xt Y (m + 1) = df_tri A B := by
    rw [df_Xt, show m + 1 + 2 = m + 3 by ring, df_rot_vec, e3i, e3s,
      df_triY_eq quad3 (by positivity)]
  have hMw : df_Mw Y (m + 1) = -(df_tri C a * Term.triFactor 0 ((C + B) / (a + C)) *
      Term.triFactor 1 ((C + B) / (B + A)) * df_tri A B) := by
    rw [df_Mw, hXs, hXt, hq1, show m + 1 + 1 = m + 2 by ring, hq2]
  have hLw : df_Lw Y (m + 1) = -√12 • (df_tri C a * Y.Mloc (m + 1) * df_tri C a) := by
    rw [df_Lw, hXs]
  -- the secants and the centre data of `K` and of `K'`
  have hsb : ¬ (Y.m2Fwd (m - 1 - 1) ↔ Y.m2Fwd (m - 1)) := by
    rw [show m - 1 - 1 = m - 2 by ring]; exact fun e => h1 (e.1 h2)
  have hsC : ¬ (Y.m2Fwd (m + 1 - 1) ↔ Y.m2Fwd (m + 1)) := by
    rw [add_sub_cancel_right]; exact fun e => h0 (e.2 h3)
  have hsB : ¬ (Y.m2Fwd (m + 2 - 1) ↔ Y.m2Fwd (m + 2)) := by
    rw [show m + 2 - 1 = m + 1 by ring]; exact fun e => h4 (e.1 h3)
  have sbK := (K.secant (m - 1) hsb).2
  have sbK' := (K'.secant (m - 1) hsb).2
  have sCK := K.secant (m + 1) hsC
  have sCK' := (K'.secant (m + 1) hsC).1
  have sBK := (K.secant (m + 2) hsB).1
  rw [add_sub_cancel_right] at sCK sCK'
  rw [show m + 2 - 1 = m + 1 by ring, show m + 2 + 1 = m + 3 by ring] at sBK
  set u := Y.m2Norm K.M m with hu_def
  set v := Y.m2Norm K.M (m - 1) with hv_def
  set E := 16 * K.M m 0 0 / (a ^ 2 + 4) with hE_def
  have hu_eq : Y.m2Norm K'.M m = u := by rw [sCK', sCK.1]
  have hv_eq : Y.m2Norm K'.M (m - 1) = v := by rw [sbK', sbK]
  have hu1 : u = m2Sec a C B := by
    have := sCK.1
    rw [show m + 1 + 1 = m + 2 by ring] at this
    exact this
  have hu2 : u = m2Sec C B A := sCK.1.trans (sCK.2.symm.trans sBK)
  obtain ⟨cE, cΓ⟩ := ss_centre_frame P K h1 h0
  obtain ⟨cE', cΓ'⟩ := ss_centre_frame P K' h1 h0
  rw [hu_eq, hv_eq] at cE' cΓ'
  have hE_eq : 16 * K'.M m 0 0 / (a ^ 2 + 4) = E := cE'.trans cE.symm
  have hΓ : Y.gam2 0 = m2Gam a v u E := by rw [← hΓ', cΓ', hE_eq]
  -- the multiplier of the first piece of the window
  have tr0 := K'.trace_eq m
  rw [Matrix.trace_fin_two] at tr0
  have e11 : K'.M m 1 1 = -K'.M m 0 0 := by linarith
  have hv' : Y.m2Norm K'.M (m - 1) = 8 * K'.M m 1 0 / (b + a) ^ 2 := by
    have := Y.m2_norm_next K'.transport (m - 1)
    simp only [h1, ↓reduceIte, sub_add_cancel] at this
    exact this
  have hu' : Y.m2Norm K'.M m = -8 * K'.M m 0 1 / (Y.q m ^ 2 * (a + C) ^ 2) := by
    unfold CostateCycle.m2Norm; simp only [h0, ↓reduceIte]; rfl
  rw [hv_eq] at hv'
  rw [hu_eq] at hu'
  obtain ⟨x1, y1, z1, w1⟩ := Y.wx_next_rev K'.transport h0
  rw [hM'] at x1 y1 z1 w1 e11 hE_eq hv' hu'
  have hqpos : 0 < Y.q m := Y.q_pos m
  have hh : Y.Mloc m 0 0 = E * (a ^ 2 + 4) / 16 := by
    rw [← hE_eq]; field_simp
  have hy : Y.Mloc m 0 1 / Y.q m ^ 2 = -(u * (a + C) ^ 2 / 8) := by
    rw [hu']; field_simp
  have hz : Y.q m ^ 2 * Y.Mloc m 1 0 = v * (a ^ 2 + 4) ^ 2 / (8 * (a + C) ^ 2) := by
    rw [hv', hqm]; field_simp
  have hU00 : Y.Mloc (m + 1) 0 0 = -(E * (a ^ 2 + 4) / 16) + u * (a + C) ^ 2 / 8 := by
    rw [x1, e11, hh, hy]; ring
  have hU01 : Y.Mloc (m + 1) 0 1 = E * (a ^ 2 + 4) / 8 - v * (a ^ 2 + 4) ^ 2 / (8 * (a + C) ^ 2) -
      u * (a + C) ^ 2 / 8 := by
    rw [y1, e11, hh, hy, hz]; ring
  have hU10 : Y.Mloc (m + 1) 1 0 = u * (a + C) ^ 2 / 8 := by rw [z1, hy]; ring
  have hU11 : Y.Mloc (m + 1) 1 1 = E * (a ^ 2 + 4) / 16 - u * (a + C) ^ 2 / 8 := by
    rw [w1, hh, hy]; ring
  -- the cover's `u` and `κ`
  have hptu : pt.u = u := by rw [hu1]; exact ss_point_u a0 c0 B0
  have hpos := P.gam2_pos_of_mixed hmix
  have hdet : 0 < (P.Λ₁ 0).det := by rw [P.det_Λ₁_zero]; positivity
  have hkap : √(P.Λ₁ 0).det = pt.kap := by
    rw [P.det_Λ₁_zero, Point.kap, ← hY, hΓ]
    congr 2
    simp only [Point.gam, hptu, m2Gam]
    ring
  have hkpos : 0 < pt.kap := by rw [← hkap]; exact Real.sqrt_pos.2 hdet
  -- the window
  have hd : 0 < Y.swd ((0 : ℕ) : ℤ) := by
    exact lt_of_lt_of_le (by norm_num) (P.swd_ge_of_mixed hmix ((0 : ℕ) : ℤ))
  have h10 := (P.ifc_negEll hpos hd).2
  obtain ⟨θ, ρw, hθ0, hθ1, hρ4, hre, him, hcost⟩ := P.df_window hc hdet h10 hN (m + 1) h3
  rw [hMw, hLw, hkap, show df_Jt = triY (fun _ ↦ 2 / √3) from rfl] at hre him
  obtain ⟨hAA, hBB⟩ := df_alg_traces (B := B) (A := A) (v := v) (E := E) a0 c0 B0 A0 hptu hkpos
    hU00 hU01 hU10 hU11
  -- the window cost
  have harc1 : Y.arc (m + 1) = Term.rawArc C a n ((C + B) / (a + C)) := by
    show Term.rawArc C (Y.m (m + 1) (i + 1)) n (Y.q (m + 1)) = _
    rw [e1s, hq1]
  have hi2 : i + 1 + 1 = i - 1 := by generalize i = x; revert x; decide
  have harc2 : Y.arc (m + 1 + 1) =
      Term.rawArc B ((C + n) / ((C + B) / (a + C)) - C) C ((C + B) / (B + A)) := by
    show Term.rawArc (Y.m (m + 1 + 1) (Y.lab (m + 1 + 1))) (Y.m (m + 1 + 1) (Y.lab (m + 1 + 1) + 1))
      (Y.m (m + 1 + 1) (Y.lab (m + 1 + 1) - 1)) (Y.q (m + 1 + 1)) = _
    rw [show m + 1 + 1 = m + 2 by ring, hl2, hi2, add_sub_cancel_right, e2s, e2d, e2i, hq2, hq1]
  have hcostW := df_alg_cost (v := v) (E := E) a0 c0 B0 A0 (n := n) (by linarith [quad1]) haB hAC
    hptu hu1 hu2
  rw [harc1, harc2, hkap, hcostW] at hcost
  -- the polar data
  have hTk : 0 < pt.Tk := by
    have : (0 : ℝ) < 1 - a ^ 2 / (a ^ 2 + 4) := by
      rw [sub_pos, div_lt_one hK0]; linarith
    simp only [Point.Tk]
    positivity
  rw [hre] at hAA
  rw [him] at hBB
  exact df_final hTk hθ0 hθ1 hρ4 hAA hBB (hcost.trans hc)

end NormalPeriod

end SmoothedOctagon
