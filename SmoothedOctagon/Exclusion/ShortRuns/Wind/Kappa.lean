module

public import SmoothedOctagon.Exclusion.ShortRun.Wind.Polar

/-!
# The canonical angle from a vector to its image under `L g X`

For a star state `X` (`det(ω, X ω) > 0`), a frame `g` with `det g = 1` together with an angle `φ`
of its polar number `z(g)`, and a fixed matrix `L` with `det L > 0`, the angle from `ω ≠ 0` to
`L g X ω` has the canonical continuous choice

`κ(ω) = arg(X ω / ω) + (φ + arg(g u / (z(g) u))) + Λ_L(g u)`, `u = X ω`,

each principal argument being taken in the slit plane (`wd_kap`, `wd_kap_isAng`).

* `wd_kap_seg`: for independent `a, b`, `arg(M b / M a) = arg(b / a) + κ(b) - κ(a)`,
  `M = L g X` (continuation along the segment from `a` to `b`).
* `wd_kap_track`: if along `t ∈ [a, b]` the data are continuous and `g(t) X(t) ω` keeps the
  direction of `g(a) X(a) ω`, then `κ_b(ω) = κ_a(ω)`.

## Main API

* `wd_lam`, `wd_lam_isAng`, `wd_lam_neg`, `wd_cOn_lam`.
* `wd_Good`, `wd_kap`, `wd_kap_isAng`, `wd_kap_neg`, `wd_kap_continuousOn`, `wd_kap_seg`,
  `wd_kap_track`.
* `wd_star_det_pos`: `det(ω, X ω) > 0` for a star state.
-/

@[expose] public section

namespace SmoothedOctagon

open Complex Set PlaneCurve SmoothedPolygons
open scoped Matrix

/-! ### The angle of a fixed matrix of positive determinant -/

/-- An angle from `u` to `L u`, continuous in `u ≠ 0`, for `det L > 0`. -/
noncomputable def wd_lam (L : Mat2) (u : Fin 2 → ℝ) : ℝ :=
  arg (sc_toC (L *ᵥ ![1, 0])) + arg (sc_toC (L *ᵥ u) / (sc_toC (L *ᵥ ![1, 0]) * sc_toC u))

theorem wd_lam_e1_ne {L : Mat2} (hL : 0 < L.det) : sc_toC (L *ᵥ ![1, 0]) ≠ 0 := by
  refine wd_toC_mulVec_ne hL.ne' ?_
  intro h; have := congrFun h 0; simp at this

theorem wd_lam_slit {L : Mat2} (hL : 0 < L.det) {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    sc_toC (L *ᵥ u) / (sc_toC (L *ᵥ ![1, 0]) * sc_toC u) ∈ slitPlane := by
  refine wd_div_mem_slit (mul_ne_zero (wd_lam_e1_ne hL) (wd_toC_ne hu)) ?_
  rw [mem_slitPlane_iff]
  rw [Matrix.det_fin_two] at hL
  set N := sc_toC (L *ᵥ u) * (starRingEnd ℂ) (sc_toC (L *ᵥ ![1, 0]) * sc_toC u) with hN
  have hre : N.re = (L 0 0 ^ 2 + L 1 0 ^ 2) * u 0 ^ 2 + (L 0 0 * L 0 1 + L 1 0 * L 1 1) * u 0 * u 1
      + (L 0 0 * L 1 1 - L 0 1 * L 1 0) * u 1 ^ 2 := by
    simp only [hN, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, sc_toC_re,
      sc_toC_im, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have him : N.im = (L 0 0 * L 1 1 - L 0 1 * L 1 0 - (L 0 0 ^ 2 + L 1 0 ^ 2)) * u 0 * u 1
      - (L 0 0 * L 0 1 + L 1 0 * L 1 1) * u 1 ^ 2 := by
    simp only [hN, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, sc_toC_re,
      sc_toC_im, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have hxy : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra h; push Not at h; apply hu; ext i; fin_cases i <;> simp [h.1, h.2]
  by_cases h0 : N.im = 0
  · left
    rw [hre]
    rw [him] at h0
    rcases eq_or_ne (u 1) 0 with hy | hy
    · have hx : u 0 ≠ 0 := hxy.resolve_right (not_not.2 hy)
      rw [hy]
      have hac : 0 < L 0 0 ^ 2 + L 1 0 ^ 2 := by
        by_contra h; push Not at h
        have ha : L 0 0 = 0 := by nlinarith [sq_nonneg (L 0 0), sq_nonneg (L 1 0)]
        have hc : L 1 0 = 0 := by nlinarith [sq_nonneg (L 0 0), sq_nonneg (L 1 0)]
        rw [ha, hc] at hL; linarith
      have : 0 < (L 0 0 ^ 2 + L 1 0 ^ 2) * u 0 ^ 2 := by positivity
      nlinarith
    · have hkey : (L 0 0 * L 0 1 + L 1 0 * L 1 1) * u 1 =
          (L 0 0 * L 1 1 - L 0 1 * L 1 0 - (L 0 0 ^ 2 + L 1 0 ^ 2)) * u 0 := by
        have : u 1 * ((L 0 0 * L 0 1 + L 1 0 * L 1 1) * u 1 -
            (L 0 0 * L 1 1 - L 0 1 * L 1 0 - (L 0 0 ^ 2 + L 1 0 ^ 2)) * u 0) = 0 := by
          linear_combination -h0
        have := (mul_eq_zero.1 this).resolve_left hy
        linarith
      have hpos : 0 < (L 0 0 * L 1 1 - L 0 1 * L 1 0) * (u 0 ^ 2 + u 1 ^ 2) := by
        have : 0 < u 1 ^ 2 := by positivity
        have : 0 < u 0 ^ 2 + u 1 ^ 2 := by positivity
        positivity
      have e : (L 0 0 ^ 2 + L 1 0 ^ 2) * u 0 ^ 2 + (L 0 0 * L 0 1 + L 1 0 * L 1 1) * u 0 * u 1
          + (L 0 0 * L 1 1 - L 0 1 * L 1 0) * u 1 ^ 2 =
          (L 0 0 * L 1 1 - L 0 1 * L 1 0) * (u 0 ^ 2 + u 1 ^ 2) := by
        linear_combination u 0 * hkey
      rw [e]; exact hpos
  · right; exact h0

theorem wd_lam_isAng {L : Mat2} (hL : 0 < L.det) {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    wd_IsAng (wd_lam L u) (sc_toC (L *ᵥ u) / sc_toC u) := by
  have h1 := wd_isAng_arg (wd_lam_e1_ne hL)
  have h2 := wd_isAng_arg (slitPlane_ne_zero (wd_lam_slit hL hu))
  have := h1.mul h2
  rw [wd_lam]
  convert this using 1
  have := wd_lam_e1_ne hL
  have := wd_toC_ne hu
  field_simp

theorem wd_lam_neg (L : Mat2) (u : Fin 2 → ℝ) : wd_lam L (-u) = wd_lam L u := by
  simp only [wd_lam, Matrix.mulVec_neg, wd_toC_neg, mul_neg, neg_div_neg_eq]

theorem wd_cOn_lam {L : Mat2} (hL : 0 < L.det) {s : Set ℝ} {u : ℝ → Fin 2 → ℝ}
    (hu : ContinuousOn u s) (hu0 : ∀ t ∈ s, u t ≠ 0) : ContinuousOn (fun t ↦ wd_lam L (u t)) s := by
  refine continuousOn_const.add (wd_continuousOn_arg ?_ fun t ht ↦ wd_lam_slit hL (hu0 t ht))
  refine ContinuousOn.div (wd_cOn_toC (wd_cOn_mulVec continuousOn_const hu))
    (continuousOn_const.mul (wd_cOn_toC hu)) fun t ht ↦ ?_
  exact mul_ne_zero (wd_lam_e1_ne hL) (wd_toC_ne (hu0 t ht))

/-! ### Star states turn every vector positively -/

theorem wd_star_det_pos {X : Mat2} (hX : IsStarState X) {ω : Fin 2 → ℝ} (hω : ω ≠ 0) :
    0 < elDet ω (X *ᵥ ω) := by
  have hz : (![ω 1, ω 0] : Fin 2 → ℝ) ≠ 0 := by
    intro h; apply hω
    have h0 := congrFun h 0; have h1 := congrFun h 1
    simp at h0 h1
    ext i; fin_cases i <;> simp [h0, h1]
  have hq := starRowQuadratic_pos hX hz
  have htr := hX.1
  rw [Matrix.trace_fin_two] at htr
  have e : elDet ω (X *ᵥ ω) = starRowQuadratic X ![ω 1, ω 0] := by
    simp only [elDet, starRowQuadratic, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have : X 1 1 = -X 0 0 := by linarith
    rw [this]; ring
  linarith

theorem wd_star_slit {X : Mat2} (hX : IsStarState X) {ω : Fin 2 → ℝ} (hω : ω ≠ 0) :
    sc_toC (X *ᵥ ω) / sc_toC ω ∈ slitPlane := by
  refine wd_div_mem_slit (wd_toC_ne hω) ?_
  rw [mem_slitPlane_iff]; right
  rw [(wd_toC_mul_conj ω (X *ᵥ ω)).1]
  exact (wd_star_det_pos hX hω).ne'

/-! ### The canonical angle -/

/-- The data of a frozen time: `det L > 0`, `det g = 1`, `X` a star state, `φ` an angle of
`z(g)`. -/
def wd_Good (L g X : Mat2) (φ : ℝ) : Prop :=
  0 < L.det ∧ g.det = 1 ∧ IsStarState X ∧ wd_IsAng φ (Reduction.scb_zc g)

/-- The canonical angle from `ω` to `L g X ω`. -/
noncomputable def wd_kap (L g X : Mat2) (φ : ℝ) (ω : Fin 2 → ℝ) : ℝ :=
  arg (sc_toC (X *ᵥ ω) / sc_toC ω) +
    (φ + arg (sc_toC (g *ᵥ (X *ᵥ ω)) / (Reduction.scb_zc g * sc_toC (X *ᵥ ω)))) +
    wd_lam L (g *ᵥ (X *ᵥ ω))

theorem wd_Good.Xne {L g X : Mat2} {φ : ℝ} (hG : wd_Good L g X φ) {ω : Fin 2 → ℝ}
    (hω : ω ≠ 0) : X *ᵥ ω ≠ 0 :=
  wd_mulVec_ne (by rw [hG.2.2.1.2.1]; norm_num) hω

theorem wd_Good.gXne {L g X : Mat2} {φ : ℝ} (hG : wd_Good L g X φ) {ω : Fin 2 → ℝ}
    (hω : ω ≠ 0) : g *ᵥ (X *ᵥ ω) ≠ 0 :=
  wd_mulVec_ne (by rw [hG.2.1]; norm_num) (hG.Xne hω)

theorem wd_Good.zne {L g X : Mat2} {φ : ℝ} (hG : wd_Good L g X φ) : Reduction.scb_zc g ≠ 0 :=
  hG.2.2.2.ne_zero

theorem wd_kap_isAng {L g X : Mat2} {φ : ℝ} (hG : wd_Good L g X φ) {ω : Fin 2 → ℝ}
    (hω : ω ≠ 0) :
    wd_IsAng (wd_kap L g X φ ω) (sc_toC (L *ᵥ (g *ᵥ (X *ᵥ ω))) / sc_toC ω) := by
  have hω' := wd_toC_ne hω
  have hu := wd_toC_ne (hG.Xne hω)
  have hgu := wd_toC_ne (hG.gXne hω)
  have hz := hG.zne
  have hXne := hG.Xne hω
  have hgXne := hG.gXne hω
  obtain ⟨hL, hg, hX, hφ⟩ := hG
  have h1 := wd_isAng_arg (slitPlane_ne_zero (wd_star_slit hX hω))
  have h2 := hφ.mul (wd_isAng_arg (slitPlane_ne_zero (wd_frame_slit hg hXne)))
  have h3 := wd_lam_isAng hL hgXne
  have := (h1.mul h2).mul h3
  rw [wd_kap]
  convert this using 1
  field_simp

theorem wd_kap_neg (L g X : Mat2) (φ : ℝ) (ω : Fin 2 → ℝ) :
    wd_kap L g X φ (-ω) = wd_kap L g X φ ω := by
  simp only [wd_kap, Matrix.mulVec_neg, wd_toC_neg, mul_neg, neg_div_neg_eq, wd_lam_neg]

/-- Continuity of the canonical angle along continuous data. -/
theorem wd_kap_continuousOn {L : Mat2} {s : Set ℝ} {g X : ℝ → Mat2} {φ : ℝ → ℝ}
    {ω : ℝ → Fin 2 → ℝ} (hg : ContinuousOn g s) (hX : ContinuousOn X s) (hφ : ContinuousOn φ s)
    (hω : ContinuousOn ω s) (hG : ∀ t ∈ s, wd_Good L (g t) (X t) (φ t))
    (hω0 : ∀ t ∈ s, ω t ≠ 0) :
    ContinuousOn (fun t ↦ wd_kap L (g t) (X t) (φ t) (ω t)) s := by
  have hXω := wd_cOn_mulVec hX hω
  have hgXω := wd_cOn_mulVec hg hXω
  refine ((wd_continuousOn_arg ?_ fun t ht ↦ wd_star_slit (hG t ht).2.2.1 (hω0 t ht)).add
    (hφ.add (wd_continuousOn_arg ?_ fun t ht ↦
      wd_frame_slit (hG t ht).2.1 ((hG t ht).Xne (hω0 t ht))))).add ?_
  · exact (wd_cOn_toC hXω).div (wd_cOn_toC hω) fun t ht ↦ wd_toC_ne (hω0 t ht)
  · refine (wd_cOn_toC hgXω).div
      ((Reduction.scb_continuous_zc.comp_continuousOn hg).mul (wd_cOn_toC hXω)) fun t ht ↦ ?_
    exact mul_ne_zero (hG t ht).zne (wd_toC_ne ((hG t ht).Xne (hω0 t ht)))
  · rcases s.eq_empty_or_nonempty with hs | ⟨t₀, ht₀⟩
    · rw [hs]; exact continuousOn_empty _
    · exact (wd_cOn_lam (hG t₀ ht₀).1 hgXω fun t ht ↦ (hG t ht).gXne (hω0 t ht))

/-- **The segment identity** at a frozen time. -/
theorem wd_kap_seg {L g X : Mat2} {φ : ℝ} (hG : wd_Good L g X φ) {a b : Fin 2 → ℝ}
    (hab : elDet a b ≠ 0) :
    arg (sc_toC (L *ᵥ (g *ᵥ (X *ᵥ b))) / sc_toC (L *ᵥ (g *ᵥ (X *ᵥ a)))) =
      arg (sc_toC b / sc_toC a) + wd_kap L g X φ b - wd_kap L g X φ a := by
  set M := L * g * X with hM
  have hMv : ∀ v, L *ᵥ (g *ᵥ (X *ᵥ v)) = M *ᵥ v := fun v ↦ by
    simp only [hM, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hdM : 0 < M.det := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, hG.2.1, hG.2.2.1.2.1]; simpa using hG.1
  simp only [hMv]
  set ω : ℝ → Fin 2 → ℝ := fun r ↦ (1 - r) • a + r • b with hω
  have hω0 : ω 0 = a := by simp [hω]
  have hω1 : ω 1 = b := by simp [hω]
  have hdetω : ∀ r, elDet a (ω r) = r * elDet a b := fun r ↦ by
    simp only [hω, elDet_add_right, elDet_smul_right, elDet_self]; ring
  have hdetω' : ∀ r, elDet (ω r) b = (1 - r) * elDet a b := fun r ↦ by
    simp only [hω, elDet_add_left, elDet_smul_left, elDet_self]; ring
  have hωne : ∀ r, ω r ≠ 0 := by
    intro r h
    have h1 := hdetω r; have h2 := hdetω' r
    rw [h] at h1 h2
    simp only [elDet, Pi.zero_apply, mul_zero, zero_mul, sub_zero] at h1 h2
    rcases mul_eq_zero.1 h1.symm with h | h
    · rw [h] at h2; simp at h2; exact hab h2.symm
    · exact hab h
  have ha : a ≠ 0 := by rw [← hω0]; exact hωne 0
  have hMa := wd_toC_mulVec_ne hdM.ne' ha
  have hωc : Continuous ω := by
    simp only [hω]; fun_prop
  -- the two quotients stay in the slit plane
  have hslit : ∀ (N : Mat2), 0 < N.det → ∀ r ∈ Icc (0 : ℝ) 1,
      sc_toC (N *ᵥ ω r) / sc_toC (N *ᵥ a) ∈ slitPlane := by
    intro N hN r hr
    have hNa := wd_mulVec_ne hN.ne' ha
    refine wd_div_mem_slit (wd_toC_ne hNa) ?_
    rw [mem_slitPlane_iff]
    rcases eq_or_lt_of_le hr.1 with h0 | hpos
    · left; rw [← h0, hω0, (wd_toC_mul_conj _ _).2]
      have : (N *ᵥ a) 0 ≠ 0 ∨ (N *ᵥ a) 1 ≠ 0 := by
        by_contra h; push Not at h; apply hNa; ext i; fin_cases i <;> simp [h.1, h.2]
      rcases this with h | h
      · nlinarith [mul_self_pos.2 h, mul_self_nonneg ((N *ᵥ a) 1)]
      · nlinarith [mul_self_pos.2 h, mul_self_nonneg ((N *ᵥ a) 0)]
    · right; rw [(wd_toC_mul_conj _ _).1]
      have : elDet (N *ᵥ a) (N *ᵥ ω r) = N.det * (r * elDet a b) := by
        rw [elDet_mulVec, hdetω]
      simp only [elDet] at this
      rw [this]
      exact mul_ne_zero hN.ne' (mul_ne_zero hpos.ne' hab)
  have hI : (1 : Mat2).det = 1 := Matrix.det_one
  set F : ℝ → ℝ := fun r ↦ arg (sc_toC (M *ᵥ ω r) / sc_toC (M *ᵥ a)) -
    arg (sc_toC (ω r) / sc_toC a) - wd_kap L g X φ (ω r) + wd_kap L g X φ a with hF
  have hF0 : F 0 = 0 := by
    simp only [hF, hω0, div_self hMa, div_self (wd_toC_ne ha), arg_one]; ring
  have hFc : ContinuousOn F (Icc 0 1) := by
    have hcM : ContinuousOn (fun r ↦ arg (sc_toC (M *ᵥ ω r) / sc_toC (M *ᵥ a))) (Icc 0 1) :=
      wd_continuousOn_arg ((wd_cOn_toC (wd_cOn_mulVec continuousOn_const
        hωc.continuousOn)).div_const _) (hslit M hdM)
    have hcI : ContinuousOn (fun r ↦ arg (sc_toC (ω r) / sc_toC a)) (Icc 0 1) := by
      have := wd_continuousOn_arg ((wd_cOn_toC (wd_cOn_mulVec continuousOn_const
        hωc.continuousOn)).div_const (sc_toC ((1 : Mat2) *ᵥ a))) (hslit 1 (by rw [hI]; norm_num))
      simpa only [Matrix.one_mulVec] using this
    have hcK := wd_kap_continuousOn (L := L) (s := Icc (0 : ℝ) 1) continuousOn_const
      continuousOn_const continuousOn_const hωc.continuousOn (fun _ _ ↦ hG) fun r _ ↦ hωne r
    exact ((hcM.sub hcI).sub hcK).add continuousOn_const
  have hF1 : F 1 = F 0 := by
    refine wd_eq_of_int zero_le_one hFc fun r hr ↦ ?_
    have hωr := hωne r
    have hA : wd_IsAng (arg (sc_toC (M *ᵥ ω r) / sc_toC (M *ᵥ a)) + wd_kap L g X φ a)
        (sc_toC (M *ᵥ ω r) / sc_toC a) := by
      have := (wd_isAng_arg (slitPlane_ne_zero (hslit M hdM r hr))).mul (wd_kap_isAng hG ha)
      simp only [hMv] at this
      convert this using 1
      field_simp
    have hB : wd_IsAng (arg (sc_toC (ω r) / sc_toC a) + wd_kap L g X φ (ω r))
        (sc_toC (M *ᵥ ω r) / sc_toC a) := by
      have h1 := hslit 1 (by rw [hI]; norm_num) r hr
      simp only [Matrix.one_mulVec] at h1
      have := (wd_isAng_arg (slitPlane_ne_zero h1)).mul (wd_kap_isAng hG hωr)
      simp only [hMv] at this
      convert this using 1
      have := wd_toC_ne hωr
      field_simp
    obtain ⟨n, hn⟩ := hA.unique hB
    exact ⟨-n, by rw [hF0]; simp only [hF]; push_cast; linarith⟩
  rw [hF0] at hF1
  simp only [hF, hω1] at hF1
  linarith

/-- **Tracking**: if `g(t) X(t) ω` keeps its direction on `[a, b]`, the canonical angle of `ω` is
the same at both ends. -/
theorem wd_kap_track {L : Mat2} {g X : ℝ → Mat2} {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hX : ContinuousOn X (Icc a b))
    (hφ : ContinuousOn φ (Icc a b)) (hG : ∀ t ∈ Icc a b, wd_Good L (g t) (X t) (φ t))
    {ω : Fin 2 → ℝ} (hω : ω ≠ 0)
    (hdir : ∀ t ∈ Icc a b, ∃ c : ℝ, 0 < c ∧ g t *ᵥ (X t *ᵥ ω) = c • (g a *ᵥ (X a *ᵥ ω))) :
    wd_kap L (g b) (X b) (φ b) ω = wd_kap L (g a) (X a) (φ a) ω := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  refine wd_angle_const (f := fun t ↦ wd_kap L (g t) (X t) (φ t) ω)
    (z := sc_toC (L *ᵥ (g a *ᵥ (X a *ᵥ ω))) / sc_toC ω) hab
    (wd_kap_continuousOn hg hX hφ continuousOn_const hG fun _ _ ↦ hω) (fun t ht ↦ ?_)
    (wd_kap_isAng (hG a ha) hω)
  obtain ⟨c, hc, hct⟩ := hdir t ht
  refine ⟨c, hc, ?_⟩
  have := wd_kap_isAng (hG t ht) hω
  rw [hct, Matrix.mulVec_smul, sc_toC_smul] at this
  convert this using 1
  ring

end SmoothedOctagon
