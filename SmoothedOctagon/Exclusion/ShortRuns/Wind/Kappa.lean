module

public import SmoothedOctagon.Exclusion.ShortRuns.Wind.Polar

/-!
# The canonical angle from a vector to its image under `L g X`

For a star state `X` (`det(ω, X ω) > 0`), a frame `g` with `det g = 1` together with an angle `φ`
of its polar number `z(g)`, and a fixed matrix `L` with `det L > 0`, the angle from `ω ≠ 0` to
`L g X ω` has the canonical continuous choice

`κ(ω) = arg(X ω / ω) + (φ + arg(g u / (z(g) u))) + Λ_L(g u)`, `u = X ω`,

each principal argument being taken in the slit plane (`wind_kap`, `wind_kap_isAng`).

* `wind_kap_seg`: for independent `a, b`, `arg(M b / M a) = arg(b / a) + κ(b) - κ(a)`,
  `M = L g X` (continuation along the segment from `a` to `b`).
* `wind_kap_track`: if along `t ∈ [a, b]` the data are continuous and `g(t) X(t) ω` keeps the
  direction of `g(a) X(a) ω`, then `κ_b(ω) = κ_a(ω)`.

## Main API

* `wind_lam`, `wind_lam_isAng`, `wind_lam_neg`, `wind_cOn_lam`.
* `wind_Good`, `wind_kap`, `wind_kap_isAng`, `wind_kap_neg`, `wind_kap_continuousOn`, `wind_kap_seg`,
  `wind_kap_track`.
* `wind_star_det_pos`: `det(ω, X ω) > 0` for a star state.
-/

@[expose] public section

namespace SmoothedOctagon

open Complex Set PlaneCurve SmoothedPolygons
open scoped Matrix

/-! ### The angle of a fixed matrix of positive determinant -/

/-- An angle from `u` to `L u`, continuous in `u ≠ 0`, for `det L > 0`. -/
noncomputable def wind_lam (L : Mat2) (u : Fin 2 → ℝ) : ℝ :=
  arg (sc_toC (L *ᵥ ![1, 0])) + arg (sc_toC (L *ᵥ u) / (sc_toC (L *ᵥ ![1, 0]) * sc_toC u))

theorem wind_lam_e1_ne {L : Mat2} (hL : 0 < L.det) : sc_toC (L *ᵥ ![1, 0]) ≠ 0 := by
  refine wind_toC_mulVec_ne hL.ne' ?_
  intro h; have := congrFun h 0; simp at this

theorem wind_lam_slit {L : Mat2} (hL : 0 < L.det) {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    sc_toC (L *ᵥ u) / (sc_toC (L *ᵥ ![1, 0]) * sc_toC u) ∈ slitPlane := by
  refine wind_div_mem_slit (mul_ne_zero (wind_lam_e1_ne hL) (wind_toC_ne hu)) ?_
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

theorem wind_lam_isAng {L : Mat2} (hL : 0 < L.det) {u : Fin 2 → ℝ} (hu : u ≠ 0) :
    wind_IsAng (wind_lam L u) (sc_toC (L *ᵥ u) / sc_toC u) := by
  have h1 := wind_isAng_arg (wind_lam_e1_ne hL)
  have h2 := wind_isAng_arg (slitPlane_ne_zero (wind_lam_slit hL hu))
  have := h1.mul h2
  rw [wind_lam]
  convert this using 1
  have := wind_lam_e1_ne hL
  have := wind_toC_ne hu
  field_simp

theorem wind_lam_neg (L : Mat2) (u : Fin 2 → ℝ) : wind_lam L (-u) = wind_lam L u := by
  simp only [wind_lam, Matrix.mulVec_neg, wind_toC_neg, mul_neg, neg_div_neg_eq]

theorem wind_cOn_lam {L : Mat2} (hL : 0 < L.det) {s : Set ℝ} {u : ℝ → Fin 2 → ℝ}
    (hu : ContinuousOn u s) (hu0 : ∀ t ∈ s, u t ≠ 0) : ContinuousOn (fun t ↦ wind_lam L (u t)) s := by
  refine continuousOn_const.add (wind_continuousOn_arg ?_ fun t ht ↦ wind_lam_slit hL (hu0 t ht))
  refine ContinuousOn.div (wind_cOn_toC (wind_cOn_mulVec continuousOn_const hu))
    (continuousOn_const.mul (wind_cOn_toC hu)) fun t ht ↦ ?_
  exact mul_ne_zero (wind_lam_e1_ne hL) (wind_toC_ne (hu0 t ht))

/-! ### Star states turn every vector positively -/

theorem wind_star_det_pos {X : Mat2} (hX : IsStarState X) {ω : Fin 2 → ℝ} (hω : ω ≠ 0) :
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

theorem wind_star_slit {X : Mat2} (hX : IsStarState X) {ω : Fin 2 → ℝ} (hω : ω ≠ 0) :
    sc_toC (X *ᵥ ω) / sc_toC ω ∈ slitPlane := by
  refine wind_div_mem_slit (wind_toC_ne hω) ?_
  rw [mem_slitPlane_iff]; right
  rw [(wind_toC_mul_conj ω (X *ᵥ ω)).1]
  exact (wind_star_det_pos hX hω).ne'

/-! ### The canonical angle -/

/-- The data of a frozen time: `det L > 0`, `det g = 1`, `X` a star state, `φ` an angle of
`z(g)`. -/
def wind_Good (L g X : Mat2) (φ : ℝ) : Prop :=
  0 < L.det ∧ g.det = 1 ∧ IsStarState X ∧ wind_IsAng φ (Reduction.clr_zc g)

/-- The canonical angle from `ω` to `L g X ω`. -/
noncomputable def wind_kap (L g X : Mat2) (φ : ℝ) (ω : Fin 2 → ℝ) : ℝ :=
  arg (sc_toC (X *ᵥ ω) / sc_toC ω) +
    (φ + arg (sc_toC (g *ᵥ (X *ᵥ ω)) / (Reduction.clr_zc g * sc_toC (X *ᵥ ω)))) +
    wind_lam L (g *ᵥ (X *ᵥ ω))

theorem wind_Good.Xne {L g X : Mat2} {φ : ℝ} (hG : wind_Good L g X φ) {ω : Fin 2 → ℝ}
    (hω : ω ≠ 0) : X *ᵥ ω ≠ 0 :=
  wind_mulVec_ne (by rw [hG.2.2.1.2.1]; norm_num) hω

theorem wind_Good.gXne {L g X : Mat2} {φ : ℝ} (hG : wind_Good L g X φ) {ω : Fin 2 → ℝ}
    (hω : ω ≠ 0) : g *ᵥ (X *ᵥ ω) ≠ 0 :=
  wind_mulVec_ne (by rw [hG.2.1]; norm_num) (hG.Xne hω)

theorem wind_Good.zne {L g X : Mat2} {φ : ℝ} (hG : wind_Good L g X φ) : Reduction.clr_zc g ≠ 0 :=
  hG.2.2.2.ne_zero

theorem wind_kap_isAng {L g X : Mat2} {φ : ℝ} (hG : wind_Good L g X φ) {ω : Fin 2 → ℝ}
    (hω : ω ≠ 0) :
    wind_IsAng (wind_kap L g X φ ω) (sc_toC (L *ᵥ (g *ᵥ (X *ᵥ ω))) / sc_toC ω) := by
  have hω' := wind_toC_ne hω
  have hu := wind_toC_ne (hG.Xne hω)
  have hgu := wind_toC_ne (hG.gXne hω)
  have hz := hG.zne
  have hXne := hG.Xne hω
  have hgXne := hG.gXne hω
  obtain ⟨hL, hg, hX, hφ⟩ := hG
  have h1 := wind_isAng_arg (slitPlane_ne_zero (wind_star_slit hX hω))
  have h2 := hφ.mul (wind_isAng_arg (slitPlane_ne_zero (wind_frame_slit hg hXne)))
  have h3 := wind_lam_isAng hL hgXne
  have := (h1.mul h2).mul h3
  rw [wind_kap]
  convert this using 1
  field_simp

theorem wind_kap_neg (L g X : Mat2) (φ : ℝ) (ω : Fin 2 → ℝ) :
    wind_kap L g X φ (-ω) = wind_kap L g X φ ω := by
  simp only [wind_kap, Matrix.mulVec_neg, wind_toC_neg, mul_neg, neg_div_neg_eq, wind_lam_neg]

/-- Continuity of the canonical angle along continuous data. -/
theorem wind_kap_continuousOn {L : Mat2} {s : Set ℝ} {g X : ℝ → Mat2} {φ : ℝ → ℝ}
    {ω : ℝ → Fin 2 → ℝ} (hg : ContinuousOn g s) (hX : ContinuousOn X s) (hφ : ContinuousOn φ s)
    (hω : ContinuousOn ω s) (hG : ∀ t ∈ s, wind_Good L (g t) (X t) (φ t))
    (hω0 : ∀ t ∈ s, ω t ≠ 0) :
    ContinuousOn (fun t ↦ wind_kap L (g t) (X t) (φ t) (ω t)) s := by
  have hXω := wind_cOn_mulVec hX hω
  have hgXω := wind_cOn_mulVec hg hXω
  refine ((wind_continuousOn_arg ?_ fun t ht ↦ wind_star_slit (hG t ht).2.2.1 (hω0 t ht)).add
    (hφ.add (wind_continuousOn_arg ?_ fun t ht ↦
      wind_frame_slit (hG t ht).2.1 ((hG t ht).Xne (hω0 t ht))))).add ?_
  · exact (wind_cOn_toC hXω).div (wind_cOn_toC hω) fun t ht ↦ wind_toC_ne (hω0 t ht)
  · refine (wind_cOn_toC hgXω).div
      ((Reduction.clr_continuous_zc.comp_continuousOn hg).mul (wind_cOn_toC hXω)) fun t ht ↦ ?_
    exact mul_ne_zero (hG t ht).zne (wind_toC_ne ((hG t ht).Xne (hω0 t ht)))
  · rcases s.eq_empty_or_nonempty with hs | ⟨t₀, ht₀⟩
    · rw [hs]; exact continuousOn_empty _
    · exact (wind_cOn_lam (hG t₀ ht₀).1 hgXω fun t ht ↦ (hG t ht).gXne (hω0 t ht))

/-- **The segment identity** at a frozen time. -/
theorem wind_kap_seg {L g X : Mat2} {φ : ℝ} (hG : wind_Good L g X φ) {a b : Fin 2 → ℝ}
    (hab : elDet a b ≠ 0) :
    arg (sc_toC (L *ᵥ (g *ᵥ (X *ᵥ b))) / sc_toC (L *ᵥ (g *ᵥ (X *ᵥ a)))) =
      arg (sc_toC b / sc_toC a) + wind_kap L g X φ b - wind_kap L g X φ a := by
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
  have hMa := wind_toC_mulVec_ne hdM.ne' ha
  have hωc : Continuous ω := by
    simp only [hω]; fun_prop
  -- the two quotients stay in the slit plane
  have hslit : ∀ (N : Mat2), 0 < N.det → ∀ r ∈ Icc (0 : ℝ) 1,
      sc_toC (N *ᵥ ω r) / sc_toC (N *ᵥ a) ∈ slitPlane := by
    intro N hN r hr
    have hNa := wind_mulVec_ne hN.ne' ha
    refine wind_div_mem_slit (wind_toC_ne hNa) ?_
    rw [mem_slitPlane_iff]
    rcases eq_or_lt_of_le hr.1 with h0 | hpos
    · left; rw [← h0, hω0, (wind_toC_mul_conj _ _).2]
      have : (N *ᵥ a) 0 ≠ 0 ∨ (N *ᵥ a) 1 ≠ 0 := by
        by_contra h; push Not at h; apply hNa; ext i; fin_cases i <;> simp [h.1, h.2]
      rcases this with h | h
      · nlinarith [mul_self_pos.2 h, mul_self_nonneg ((N *ᵥ a) 1)]
      · nlinarith [mul_self_pos.2 h, mul_self_nonneg ((N *ᵥ a) 0)]
    · right; rw [(wind_toC_mul_conj _ _).1]
      have : elDet (N *ᵥ a) (N *ᵥ ω r) = N.det * (r * elDet a b) := by
        rw [elDet_mulVec, hdetω]
      simp only [elDet] at this
      rw [this]
      exact mul_ne_zero hN.ne' (mul_ne_zero hpos.ne' hab)
  have hI : (1 : Mat2).det = 1 := Matrix.det_one
  set F : ℝ → ℝ := fun r ↦ arg (sc_toC (M *ᵥ ω r) / sc_toC (M *ᵥ a)) -
    arg (sc_toC (ω r) / sc_toC a) - wind_kap L g X φ (ω r) + wind_kap L g X φ a with hF
  have hF0 : F 0 = 0 := by
    simp only [hF, hω0, div_self hMa, div_self (wind_toC_ne ha), arg_one]; ring
  have hFc : ContinuousOn F (Icc 0 1) := by
    have hcM : ContinuousOn (fun r ↦ arg (sc_toC (M *ᵥ ω r) / sc_toC (M *ᵥ a))) (Icc 0 1) :=
      wind_continuousOn_arg ((wind_cOn_toC (wind_cOn_mulVec continuousOn_const
        hωc.continuousOn)).div_const _) (hslit M hdM)
    have hcI : ContinuousOn (fun r ↦ arg (sc_toC (ω r) / sc_toC a)) (Icc 0 1) := by
      have := wind_continuousOn_arg ((wind_cOn_toC (wind_cOn_mulVec continuousOn_const
        hωc.continuousOn)).div_const (sc_toC ((1 : Mat2) *ᵥ a))) (hslit 1 (by rw [hI]; norm_num))
      simpa only [Matrix.one_mulVec] using this
    have hcK := wind_kap_continuousOn (L := L) (s := Icc (0 : ℝ) 1) continuousOn_const
      continuousOn_const continuousOn_const hωc.continuousOn (fun _ _ ↦ hG) fun r _ ↦ hωne r
    exact ((hcM.sub hcI).sub hcK).add continuousOn_const
  have hF1 : F 1 = F 0 := by
    refine wind_eq_of_int zero_le_one hFc fun r hr ↦ ?_
    have hωr := hωne r
    have hA : wind_IsAng (arg (sc_toC (M *ᵥ ω r) / sc_toC (M *ᵥ a)) + wind_kap L g X φ a)
        (sc_toC (M *ᵥ ω r) / sc_toC a) := by
      have := (wind_isAng_arg (slitPlane_ne_zero (hslit M hdM r hr))).mul (wind_kap_isAng hG ha)
      simp only [hMv] at this
      convert this using 1
      field_simp
    have hB : wind_IsAng (arg (sc_toC (ω r) / sc_toC a) + wind_kap L g X φ (ω r))
        (sc_toC (M *ᵥ ω r) / sc_toC a) := by
      have h1 := hslit 1 (by rw [hI]; norm_num) r hr
      simp only [Matrix.one_mulVec] at h1
      have := (wind_isAng_arg (slitPlane_ne_zero h1)).mul (wind_kap_isAng hG hωr)
      simp only [hMv] at this
      convert this using 1
      have := wind_toC_ne hωr
      field_simp
    obtain ⟨n, hn⟩ := hA.unique hB
    exact ⟨-n, by rw [hF0]; simp only [hF]; push_cast; linarith⟩
  rw [hF0] at hF1
  simp only [hF, hω1] at hF1
  linarith

/-- **Tracking**: if `g(t) X(t) ω` keeps its direction on `[a, b]`, the canonical angle of `ω` is
the same at both ends. -/
theorem wind_kap_track {L : Mat2} {g X : ℝ → Mat2} {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hX : ContinuousOn X (Icc a b))
    (hφ : ContinuousOn φ (Icc a b)) (hG : ∀ t ∈ Icc a b, wind_Good L (g t) (X t) (φ t))
    {ω : Fin 2 → ℝ} (hω : ω ≠ 0)
    (hdir : ∀ t ∈ Icc a b, ∃ c : ℝ, 0 < c ∧ g t *ᵥ (X t *ᵥ ω) = c • (g a *ᵥ (X a *ᵥ ω))) :
    wind_kap L (g b) (X b) (φ b) ω = wind_kap L (g a) (X a) (φ a) ω := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  refine wind_angle_const (f := fun t ↦ wind_kap L (g t) (X t) (φ t) ω)
    (z := sc_toC (L *ᵥ (g a *ᵥ (X a *ᵥ ω))) / sc_toC ω) hab
    (wind_kap_continuousOn hg hX hφ continuousOn_const hG fun _ _ ↦ hω) (fun t ht ↦ ?_)
    (wind_kap_isAng (hG a ha) hω)
  obtain ⟨c, hc, hct⟩ := hdir t ht
  refine ⟨c, hc, ?_⟩
  have := wind_kap_isAng (hG t ht) hω
  rw [hct, Matrix.mulVec_smul, sc_toC_smul] at this
  convert this using 1
  ring

end SmoothedOctagon
