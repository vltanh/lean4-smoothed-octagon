module

public import SmoothedOctagon.Reduction.Normal.Flow
public import SmoothedOctagon.Period.Hamiltonian
public import SmoothedPolygons.Ch7.Isolated.VertexFlow
public import SmoothedPolygons.Ch7.ConstantControl

/-!
# From an abnormal extremal with a vertex representation to an abnormal sequence

Let `(T, u, g, X, Λ₁, Λ_R)` be a Pontryagin extremal with cost multiplier `λ = 0` whose control
has a finite vertex representation. On every vertex piece the active Hamiltonian vanishes and the
coordinates `μ_j` (`Normal/Flow.lean`) of `X`, `a = -XΛ₁X` and `b = Λ_R + 2Λ₁ + ⟨Λ₁, X⟩X` are
transported by the one-arc map (`gn_piece`). Continuing the switching-time data through the twist
`X(T) = R⁻¹ X(0) R`, `Λ₁(T) = R⁻¹ Λ₁(0) R`, `Λ_R(T) = R⁻¹ Λ_R(0) R`, which relabels the
coordinates (`gnMu_Rinv_conj`), gives an abstract abnormal sequence `GnSeq` whose labels satisfy
`i_{k+N} = i_k + 1` (`gn_abnormal_seq`).

## Main API

* `gn_margin_pos` (margins of star states are positive), `gn_trace_controlMatrix_vertex`,
  `gnL_neg`.
* `gn_piece`: one vertex piece of an abnormal extremal (active Hamiltonian zero, transports).
* `gn_ofNat_succ`, `gnL_shift`, `gn_extend_succ`, `gn_label_add_mul`: continuation of piecewise
  transported data through the twist.
* `gn_abnormal_seq`: the abnormal sequence of an abnormal extremal with a vertex representation.
-/

@[expose] public section

namespace SmoothedOctagon.Reduction

open SmoothedPolygons MeasureTheory Set

theorem gn_margin_pos {X : Mat2} (hX : IsStarState X) (i : Fin 3) : 0 < margin i X := by
  have := poly_traceForm_neg (poly_vertex_mem i) hX
  rw [margin]; nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < 3 by norm_num)]

theorem gn_trace_controlMatrix_vertex (i : Fin 3) : (controlMatrix (vertex i)).trace = 0 := by
  fin_cases i <;> simp [controlMatrix, vertex, Matrix.trace_fin_two] <;> ring

theorem gnL_neg (i : Fin 3) (q : ℝ) (v : Fin 3 → ℝ) :
    gnL i q (fun j ↦ -v j) = fun j ↦ -gnL i q v j := by
  funext j; unfold gnL; split_ifs <;> ring

/-- **One vertex piece of an abnormal extremal.** On a piece `[s₀, s₁] ⊆ [0, T]` where the control
is a.e. the vertex `e_i`, the active Hamiltonian vanishes at `s₀`, and with
`q = exp(2 (s₁ - s₀) / p_i(X(s₀)))` the coordinates of `X` and `b` are transported by `L_i(q)` and
those of `a` by `L_i(q²)`. -/
theorem gn_piece {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR 0) {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀) (h01 : s₀ < s₁)
    (h1 : s₁ ≤ T) {i : Fin 3} (hu : ∀ᵐ t, t ∈ Ioo s₀ s₁ → u t = vertex i) :
    hamiltonian 0 (Λ₁ s₀) (ΛR s₀) (X s₀) (vertex i) = 0 ∧
      (fun j ↦ gnMu j (X s₁)) =
        gnL i (Real.exp (2 * (s₁ - s₀) / margin i (X s₀))) (fun j ↦ gnMu j (X s₀)) ∧
      (fun j ↦ gnMu j (gnA (Λ₁ s₁) (X s₁))) =
        gnL i (Real.exp (2 * (s₁ - s₀) / margin i (X s₀)) ^ 2)
          (fun j ↦ gnMu j (gnA (Λ₁ s₀) (X s₀))) ∧
      (fun j ↦ gnMu j (gnB (Λ₁ s₁) (ΛR s₁) (X s₁))) =
        gnL i (Real.exp (2 * (s₁ - s₀) / margin i (X s₀)))
          (fun j ↦ gnMu j (gnB (Λ₁ s₀) (ΛR s₀) (X s₀))) := by
  have hHc := IsPontryaginExtremal.continuousOn_vertexHamiltonian h i
  obtain ⟨⟨-, -, -, hst, -, hXI⟩, -, -, -, -, -, -, hcost, hΛ₁I, hΛRI, hH⟩ := h
  have hsub : Icc s₀ s₁ ⊆ Icc 0 T := Icc_subset_Icc h0 h1
  have hs₀ : s₀ ∈ Icc s₀ s₁ := ⟨le_rfl, h01.le⟩
  have hXc : ContinuousOn X (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hXI
  have hΛ₁c : ContinuousOn Λ₁ (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hΛ₁I
  have hΛRc : ContinuousOn ΛR (Icc 0 T) := Matrix.continuousOn_of_eq_add_integral hΛRI
  have hstar : ∀ t ∈ Icc s₀ s₁, IsStarState (X t) := fun t ht ↦ (hst t (hsub ht)).2
  have hvi : vertex i ∈ controlSimplex := poly_vertex_mem i
  set p := margin i (X s₀) with hp
  have hp0 : 0 < p := gn_margin_pos (hstar s₀ hs₀) i
  -- the state equation on the piece, with the continuous right-hand side
  have hwX : ContinuousOn (fun t ↦ controlP (vertex i) (X t) * X t -
      X t * controlP (vertex i) (X t)) (Icc s₀ s₁) :=
    ((poly_controlP_continuousOn (hXc.mono hsub) hvi hstar).mul (hXc.mono hsub)).sub
      ((hXc.mono hsub).mul (poly_controlP_continuousOn (hXc.mono hsub) hvi hstar))
  have hformX := ivf_integral_form_restrict_ae hXI h0 h01.le h1 hwX (by
    filter_upwards [hu] with t ht htI
    rw [ht htI])
  have hXd := fun t (ht : t ∈ Icc s₀ s₁) ↦
    Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hformX ht (hwX t ht)
  -- `P = Z_i / ⟨Z_i, X⟩` is constant on the piece (Lemma 7.1.1)
  have hconst := lemma7_1_1 _ X _ _ hXd
  set P₀ := controlP (vertex i) (X s₀) with hP₀
  have hP : ∀ t ∈ Icc s₀ s₁, controlP (vertex i) (X t) = P₀ := by
    intro t ht
    unfold controlP
    rw [poly_traceForm_comm _ (X t), hconst t ht, poly_traceForm_comm (X _)]
    rfl
  have hZX : traceForm (controlMatrix (vertex i)) (X s₀) ≠ 0 :=
    (poly_traceForm_neg hvi (hstar s₀ hs₀)).ne
  have hP₀form : P₀ = (-(1 / p)) • gnS i := by
    rw [hP₀, controlP, gnS, smul_smul, hp, margin]
    congr 1
    field_simp
  have hPtr : P₀.trace = 0 := by
    rw [hP₀form, gnS, Matrix.trace_smul, Matrix.trace_smul, gn_trace_controlMatrix_vertex,
      smul_zero, smul_zero]
  have hXd' : ∀ t ∈ Icc s₀ s₁, Matrix.HasDerivWithinAtEntrywise X (P₀ * X t - X t * P₀)
      (Icc s₀ s₁) t := fun t ht ↦ by
    have := hXd t ht; rwa [hP t ht] at this
  -- the costate equations on the piece
  have hΛ₁d : ∀ t ∈ Icc s₀ s₁, Matrix.HasDerivWithinAtEntrywise Λ₁ (Λ₁ t * X t - X t * Λ₁ t)
      (Icc s₀ s₁) t := fun t ht ↦
    (Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hΛ₁I (hsub ht)
      (((hΛ₁c.mul hXc).sub (hXc.mul hΛ₁c)) t (hsub ht))).mono hsub
  have hwR : ContinuousOn (fun t ↦ costateRHS 0 (Λ₁ t) (ΛR t) (X t) (vertex i)) (Icc s₀ s₁) :=
    poly_costateRHS_continuousOn 0 hvi (hΛ₁c.mono hsub) (hΛRc.mono hsub) (hXc.mono hsub) hstar
  have hformR := ivf_integral_form_restrict_ae hΛRI h0 h01.le h1 hwR (by
    filter_upwards [hu] with t ht htI
    rw [ht htI]
    rfl)
  have hRd := fun t (ht : t ∈ Icc s₀ s₁) ↦
    Matrix.hasDerivWithinAtEntrywise_of_eq_add_integral hformR ht (hwR t ht)
  -- the active Hamiltonian vanishes on the closed piece
  have hHae : ∀ᵐ t, t ∈ Ioo s₀ s₁ → hamiltonian 0 (Λ₁ t) (ΛR t) (X t) (vertex i) = 0 := by
    filter_upwards [hH, hu] with t hHt hut ht
    have := (hHt ⟨h0.trans_lt ht.1, ht.2.trans_le h1⟩).1
    rwa [hut ht] at this
  have hHz : ∀ t ∈ Icc s₀ s₁, hamiltonian 0 (Λ₁ t) (ΛR t) (X t) (vertex i) = 0 := by
    have hae : (fun t ↦ hamiltonian 0 (Λ₁ t) (ΛR t) (X t) (vertex i)) =ᵐ[volume.restrict
        (Icc s₀ s₁)] fun _ ↦ (0 : ℝ) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hHae, (countable_singleton s₀).ae_notMem volume,
        (countable_singleton s₁).ae_notMem volume] with t h1' h2' h3' ht
      exact h1' ⟨lt_of_le_of_ne ht.1 (Ne.symm h2'), lt_of_le_of_ne ht.2 h3'⟩
    exact Measure.eqOn_of_ae_eq hae (hHc.mono hsub) continuousOn_const
      (by rw [interior_Icc, closure_Ioo h01.ne])
  -- pointwise facts on the piece
  have hX2 : ∀ t ∈ Icc s₀ s₁, X t * X t = -1 := fun t ht ↦
    gn_mul_self (hstar t ht).1 (hstar t ht).2.1
  have hPX : ∀ t ∈ Icc s₀ s₁, traceForm P₀ (X t) = 1 := by
    intro t ht
    have hne : traceForm (controlMatrix (vertex i)) (X t) ≠ 0 :=
      (poly_traceForm_neg hvi (hstar t ht)).ne
    rw [← hP t ht, controlP, traceForm, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
      ← traceForm, inv_mul_cancel₀ hne]
  have hPX' : ∀ t ∈ Icc s₀ s₁, P₀ * X t + X t * P₀ = 1 := by
    intro t ht
    rw [(lemma3_4_1).2.2.1 _ _ hPtr (hstar t ht).1, hPX t ht, one_smul]
  have hHt : ∀ t ∈ Icc s₀ s₁, traceForm (Λ₁ t) (X t) - traceForm (ΛR t) P₀ = 0 := by
    intro t ht
    have hne : traceForm (controlMatrix (vertex i)) (X t) ≠ 0 :=
      (poly_traceForm_neg hvi (hstar t ht)).ne
    have h := hHz t ht
    rw [hamiltonian] at h
    simp only [mul_zero, zero_smul, sub_zero] at h
    have e : traceForm (ΛR t) P₀ = traceForm (ΛR t) (controlMatrix (vertex i)) /
        traceForm (X t) (controlMatrix (vertex i)) := by
      rw [← hP t ht, controlP]
      unfold traceForm
      rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
        Matrix.trace_mul_comm (controlMatrix (vertex i)) (X t), div_eq_inv_mul]
    rw [e]; exact h
  -- the derivatives of `a` and `b`
  have hA : ∀ t ∈ Icc s₀ s₁, Matrix.HasDerivWithinAtEntrywise (fun t ↦ gnA (Λ₁ t) (X t))
      ((2 : ℝ) • (P₀ * gnA (Λ₁ t) (X t) - gnA (Λ₁ t) (X t) * P₀)) (Icc s₀ s₁) t :=
    fun t ht ↦ (((hXd' t ht).mul (hΛ₁d t ht)).mul (hXd' t ht)).neg.congr_deriv
      (gnA_deriv_eq (hX2 t ht) (hPX' t ht))
  have hB : ∀ t ∈ Icc s₀ s₁, Matrix.HasDerivWithinAtEntrywise
      (fun t ↦ gnB (Λ₁ t) (ΛR t) (X t))
      ((1 : ℝ) • (P₀ * gnB (Λ₁ t) (ΛR t) (X t) - gnB (Λ₁ t) (ΛR t) (X t) * P₀))
      (Icc s₀ s₁) t := by
    intro t ht
    obtain ⟨h1t, hRt, -, -⟩ := hcost t (hsub ht)
    rw [one_smul]
    exact (((hRd t ht).add ((hΛ₁d t ht).const_smul (2 : ℝ))).add
      (Matrix.HasDerivWithinAtEntrywise.smul ((hΛ₁d t ht).mul (hXd' t ht)).trace
        (hXd' t ht))).congr_deriv
      (gnB_deriv_eq (hstar t ht).1 h1t hRt hPtr (hstar t ht).2.1 (hPX t ht) (hHt t ht) rfl rfl
        (by unfold costateRHS; rw [hP t ht]))
  have hXf : ∀ t ∈ Icc s₀ s₁, Matrix.HasDerivWithinAtEntrywise X
      ((1 : ℝ) • ((-(1 / p)) • gnS i * X t - X t * (-(1 / p)) • gnS i)) (Icc s₀ s₁) t :=
    fun t ht ↦ (hXd' t ht).congr_deriv (by rw [one_smul, hP₀form])
  rw [hP₀form] at hA hB
  have e1 : -2 * 1 * -(1 / p) * (s₁ - s₀) = 2 * (s₁ - s₀) / p := by ring
  have e2 : Real.exp (-2 * 2 * -(1 / p) * (s₁ - s₀)) = Real.exp (2 * (s₁ - s₀) / p) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  refine ⟨hHz s₀ hs₀, ?_, ?_, ?_⟩
  · have := gnMu_flow i h01.le hXf
    rwa [e1] at this
  · have := gnMu_flow i h01.le hA
    rwa [e2] at this
  · have := gnMu_flow i h01.le hB
    rwa [e1] at this

/-! ### Continuation through the twist -/

theorem gn_ofNat_succ (m : ℕ) : Fin.ofNat 3 (m + 1) = Fin.ofNat 3 m + 1 := by
  ext; simp [Fin.ofNat, Fin.val_add]

/-- Relabeling commutes with the one-arc map: `L_{i+n}(q)(v(· - n)) = L_i(q)(v)(· - n)`. -/
theorem gnL_shift (i n : Fin 3) (q : ℝ) (v : Fin 3 → ℝ) :
    gnL (i + n) q (fun j ↦ v (j - n)) = fun j ↦ gnL i q v (j - n) := by
  funext j
  obtain ⟨k, rfl⟩ : ∃ k, j = k + n := ⟨j - n, by simp⟩
  simp only [gnL, add_sub_cancel_right, show i + n + 1 = i + 1 + n from add_right_comm i n 1,
    add_left_inj]

/-- Data transported piece by piece on one period and relabeled by the twist at its end continue
to all later pieces: with `W k = V_{k mod N}(· - ⌊k / N⌋)`, `W (k + 1) = L_{i_k}(q) W k`. -/
theorem gn_extend_succ {N : ℕ} (hN : 0 < N) (lab : ℕ → Fin 3)
    (hlab : ∀ k, lab k = lab (k % N) + Fin.ofNat 3 (k / N)) (q : ℕ → ℝ)
    (V : ℕ → Fin 3 → ℝ) (hV : ∀ r, r < N → V (r + 1) = gnL (lab r) (q r) (V r))
    (htw : ∀ j, V N j = V 0 (j - 1)) (k : ℕ) :
    (fun j ↦ V ((k + 1) % N) (j - Fin.ofNat 3 ((k + 1) / N))) =
      gnL (lab k) (q (k % N)) (fun j ↦ V (k % N) (j - Fin.ofNat 3 (k / N))) := by
  have hk := Nat.div_add_mod k N
  have hr : k % N < N := Nat.mod_lt k hN
  rw [hlab k, gnL_shift, ← hV _ hr]
  generalize ha : k / N = a at hk ⊢
  generalize hb : k % N = b at hk hr ⊢
  rcases Nat.lt_or_ge (b + 1) N with h | h
  · have e := (Nat.div_mod_unique hN).2 (⟨by linarith, h⟩ : b + 1 + N * a = k + 1 ∧ b + 1 < N)
    rw [e.1, e.2]
  · have hrN : b + 1 = N := by omega
    have e := (Nat.div_mod_unique hN).2 (⟨by rw [mul_add, mul_one]; linarith, hN⟩ :
      0 + N * (a + 1) = k + 1 ∧ 0 < N)
    rw [e.1, e.2, hrN]
    funext j
    rw [htw, gn_ofNat_succ, sub_sub]

/-- The labels of a vertex representation: `i_{r + mN} = i_r + m`. -/
theorem gn_label_add_mul {T : ℝ} {u : ℝ → Fin 3 → ℝ} (ρ : VertexRepresentation T u) (m : ℕ)
    (r : ℤ) : ρ.label (r + m * ρ.N) = ρ.label r + Fin.ofNat 3 m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show r + ((m + 1 : ℕ) : ℤ) * ρ.N = r + (m : ℕ) * ρ.N + ρ.N by push_cast; ring,
      ρ.label_add_period, ih, gn_ofNat_succ, add_assoc]

/-! ### The abnormal sequence -/

/-- **The abnormal sequence of an abnormal extremal.** A Pontryagin extremal with `λ = 0` whose
control has a finite vertex representation yields an abnormal sequence whose labels satisfy the
twist `i_{k+N} = i_k + 1`. -/
theorem gn_abnormal_seq {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X Λ₁ ΛR : ℝ → Mat2}
    (h : IsPontryaginExtremal T u g X Λ₁ ΛR 0) (ρ : VertexRepresentation T u) :
    ∃ S : GnSeq, ∀ k, S.lab (k + ρ.N) = S.lab k + 1 := by
  have hmax := IsPontryaginExtremal.vertexHamiltonian_max_eq_zero h
  have hst := h.1.2.2.2.1
  have hXT : X T = R⁻¹ * X 0 * R := h.2.2.2.1
  have hΛ₁T : Λ₁ T = R⁻¹ * Λ₁ 0 * R := h.2.2.2.2.1
  have hΛRT : ΛR T = R⁻¹ * ΛR 0 * R := h.2.2.2.2.2.1
  have hcost := h.2.2.2.2.2.2.2.1
  set N := ρ.N with hNdef
  have hN : 0 < N := ρ.N_pos
  -- the switching times of one period
  obtain ⟨τ', hτ'⟩ : ∃ f : ℕ → ℝ, f = fun r : ℕ ↦ ρ.τ (r : ℤ) := ⟨_, rfl⟩
  have hτ0 : τ' 0 = 0 := by rw [hτ']; exact ρ.τ_zero
  have hτN : τ' N = T := by
    have := ρ.τ_add_period 0
    rw [zero_add, ρ.τ_zero, zero_add] at this
    rw [hτ']; exact this
  have hτlt : ∀ r, τ' r < τ' (r + 1) := fun r ↦ by
    rw [hτ']; exact ρ.τ_strictMono (by push_cast; linarith)
  have hτmem : ∀ r, r ≤ N → τ' r ∈ Icc 0 T := by
    intro r hr
    refine ⟨?_, ?_⟩
    · rw [← hτ0, hτ']; exact ρ.τ_strictMono.monotone (by positivity)
    · rw [← hτN, hτ']; exact ρ.τ_strictMono.monotone (by exact_mod_cast hr)
  have hstar : ∀ r, r ≤ N → IsStarState (X (τ' r)) := fun r hr ↦ (hst _ (hτmem r hr)).2
  -- labels, factors and coordinates on one period
  obtain ⟨lab, hlab'⟩ : ∃ f : ℕ → Fin 3, f = fun k : ℕ ↦ ρ.label (k : ℤ) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ f : ℕ → ℝ,
      f = fun r ↦ Real.exp (2 * (τ' (r + 1) - τ' r) / margin (lab r) (X (τ' r))) := ⟨_, rfl⟩
  obtain ⟨mB, hmB⟩ : ∃ f : ℕ → Fin 3 → ℝ, f = fun r j ↦ margin j (X (τ' r)) := ⟨_, rfl⟩
  obtain ⟨αB, hαB⟩ : ∃ f : ℕ → Fin 3 → ℝ,
      f = fun r j ↦ gnMu j (gnA (Λ₁ (τ' r)) (X (τ' r))) := ⟨_, rfl⟩
  obtain ⟨βB, hβB⟩ : ∃ f : ℕ → Fin 3 → ℝ,
      f = fun r j ↦ gnMu j (gnB (Λ₁ (τ' r)) (ΛR (τ' r)) (X (τ' r))) := ⟨_, rfl⟩
  have hlab : ∀ k, lab k = lab (k % N) + Fin.ofNat 3 (k / N) := by
    intro k
    have e : ((k % N : ℕ) : ℤ) + ((k / N : ℕ) : ℤ) * (N : ℤ) = (k : ℤ) := by
      norm_cast; exact Nat.mod_add_div' k N
    rw [hlab']
    have := gn_label_add_mul ρ (k / N) (k % N : ℕ)
    rw [e] at this
    exact this
  -- one vertex piece
  have hpiece : ∀ r, r < N → _ := fun r hr ↦ gn_piece h (hτmem r hr.le).1 (hτlt r)
    (hτmem (r + 1) hr).2 (i := lab r) (u := u) (by
      have := ρ.ae_eq_vertex r (by positivity) (by exact_mod_cast hr)
      rw [hτ', hlab']
      simpa [Nat.cast_succ] using this)
  have hqdef : ∀ r, q r = Real.exp (2 * (τ' (r + 1) - τ' r) / margin (lab r) (X (τ' r))) :=
    fun r ↦ by rw [hq]
  -- transport over one period
  have hVm : ∀ r, r < N → mB (r + 1) = gnL (lab r) (q r) (mB r) := by
    intro r hr
    have e := (hpiece r hr).2.1
    rw [← hqdef] at e
    rw [hmB]
    simp only [gn_margin_eq_neg_gnMu]
    rw [gnL_neg, ← e]
  have hVα : ∀ r, r < N → αB (r + 1) = gnL (lab r) (q r ^ 2) (αB r) := by
    intro r hr
    have e := (hpiece r hr).2.2.1
    rw [← hqdef] at e
    rw [hαB]; exact e
  have hVβ : ∀ r, r < N → βB (r + 1) = gnL (lab r) (q r) (βB r) := by
    intro r hr
    have e := (hpiece r hr).2.2.2
    rw [← hqdef] at e
    rw [hβB]; exact e
  -- the twist at the end of the period
  have htwm : ∀ j, mB N j = mB 0 (j - 1) := by
    intro j
    rw [hmB]
    simp only [hτN, hτ0, hXT, gn_margin_eq_neg_gnMu, gnMu_Rinv_conj]
  have htwα : ∀ j, αB N j = αB 0 (j - 1) := by
    intro j
    rw [hαB]
    simp only [hτN, hτ0, hXT, hΛ₁T, gnA_conj, gnMu_Rinv_conj]
  have htwβ : ∀ j, βB N j = βB 0 (j - 1) := by
    intro j
    rw [hβB]
    simp only [hτN, hτ0, hXT, hΛ₁T, hΛRT, gnB_conj, gnMu_Rinv_conj]
  -- pointwise facts at the switching times of one period
  have hr_lt : ∀ k, k % N < N := fun k ↦ Nat.mod_lt k hN
  have hmemk : ∀ k, τ' (k % N) ∈ Icc 0 T := fun k ↦ hτmem _ (hr_lt k).le
  have hstark : ∀ k, IsStarState (X (τ' (k % N))) := fun k ↦ hstar _ (hr_lt k).le
  have hsig : ∀ r, r ≤ N → ∀ j, 2 * αB r j + βB r j =
      hamiltonian 0 (Λ₁ (τ' r)) (ΛR (τ' r)) (X (τ' r)) (vertex j) * margin j (X (τ' r)) := by
    intro r hr j
    rw [hαB, hβB]
    exact (gn_hamiltonian_mul_margin j (hstar r hr).1 (hstar r hr).2.1
      (hcost _ (hτmem r hr)).1 (gn_margin_pos (hstar r hr) j).ne').symm
  refine ⟨{
    lab := lab
    Q := fun k ↦ q (k % N)
    m := fun k j ↦ mB (k % N) (j - Fin.ofNat 3 (k / N))
    α := fun k j ↦ αB (k % N) (j - Fin.ofNat 3 (k / N))
    β := fun k j ↦ βB (k % N) (j - Fin.ofNat 3 (k / N))
    one_lt_Q := ?_
    m_pos := ?_
    m_succ := gn_extend_succ hN lab hlab q mB hVm htwm
    α_succ := gn_extend_succ hN lab hlab (fun r ↦ q r ^ 2) αB hVα htwα
    β_succ := gn_extend_succ hN lab hlab q βB hVβ htwβ
    perp := ?_
    active := ?_
    sig_nonpos := ?_
    nontriv := ?_
    lab_succ_ne := ?_ }, ?_⟩
  · intro k
    show 1 < q (k % N)
    rw [hqdef, Real.one_lt_exp_iff]
    exact div_pos (by linarith [hτlt (k % N)]) (gn_margin_pos (hstark k) _)
  · intro k j
    show 0 < mB (k % N) (j - Fin.ofNat 3 (k / N))
    rw [hmB]; exact gn_margin_pos (hstark k) _
  · intro k
    show βB (k % N) (0 - Fin.ofNat 3 (k / N)) * (mB (k % N) (1 - Fin.ofNat 3 (k / N)) +
        mB (k % N) (2 - Fin.ofNat 3 (k / N))) + βB (k % N) (1 - Fin.ofNat 3 (k / N)) *
        (mB (k % N) (0 - Fin.ofNat 3 (k / N)) + mB (k % N) (2 - Fin.ofNat 3 (k / N))) +
        βB (k % N) (2 - Fin.ofNat 3 (k / N)) * (mB (k % N) (0 - Fin.ofNat 3 (k / N)) +
        mB (k % N) (1 - Fin.ofNat 3 (k / N))) = 0
    rw [zero_sub, sub_eq_neg_add, sub_eq_neg_add, ← gn_perp_rel, hβB, hmB]
    obtain ⟨htr, hdet, -⟩ := hstark k
    obtain ⟨h1t, hRt, hRX, -⟩ := hcost _ (hmemk k)
    have hXX : traceForm (X (τ' (k % N))) (X (τ' (k % N))) = -2 := by
      rw [(lemma3_4_1).1 _ htr, hdet]; ring
    rw [gn_perp_eq (gnB_trace htr h1t hRt) htr, gn_traceForm_gnB hXX, hRX, mul_zero]
  · intro k
    show 2 * αB (k % N) (lab k - Fin.ofNat 3 (k / N)) +
      βB (k % N) (lab k - Fin.ofNat 3 (k / N)) = 0
    conv_lhs => rw [hlab k, add_sub_cancel_right]
    rw [hsig _ (hr_lt k).le, (hpiece _ (hr_lt k)).1, zero_mul]
  · intro k j
    show 2 * αB (k % N) (j - Fin.ofNat 3 (k / N)) + βB (k % N) (j - Fin.ofNat 3 (k / N)) ≤ 0
    rw [hsig _ (hr_lt k).le]
    exact mul_nonpos_of_nonpos_of_nonneg ((hmax _ (hmemk k)).1 _)
      (gn_margin_pos (hstark k) _).le
  · intro k
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨hα0, hβ0⟩ := hcon
    obtain ⟨htr, hdet, -⟩ := hstark k
    obtain ⟨h1t, hRt, -, hnt⟩ := hcost _ (hmemk k)
    have hXX := gn_mul_self htr hdet
    have hαj : ∀ j, αB (k % N) j = 0 := fun j ↦ by
      have := congrFun hα0 (j + Fin.ofNat 3 (k / N))
      simpa only [add_sub_cancel_right, Pi.zero_apply] using this
    have hβj : ∀ j, βB (k % N) j = 0 := fun j ↦ by
      have := congrFun hβ0 (j + Fin.ofNat 3 (k / N))
      simpa only [add_sub_cancel_right, Pi.zero_apply] using this
    have hA : gnA (Λ₁ (τ' (k % N))) (X (τ' (k % N))) = 0 :=
      gn_eq_zero_of_gnMu (gnA_trace hXX h1t) fun j ↦ by
        have := hαj j; rw [hαB] at this; exact this
    have hL : Λ₁ (τ' (k % N)) = 0 := gn_eq_zero_of_gnA hXX hA
    have hB : gnB (Λ₁ (τ' (k % N))) (ΛR (τ' (k % N))) (X (τ' (k % N))) = 0 :=
      gn_eq_zero_of_gnMu (gnB_trace htr h1t hRt) fun j ↦ by
        have := hβj j; rw [hβB] at this; exact this
    rw [hL, gnB_zero_left] at hB
    rcases hnt with h0 | h0 | h0
    · exact h0 rfl
    · exact h0 hL
    · exact h0 hB
  · intro k
    show lab (k + 1) ≠ lab k
    rw [hlab']
    have := ρ.label_ne k
    simpa [Nat.cast_succ] using this
  · intro k
    show lab (k + N) = lab k + 1
    rw [hlab']
    have := ρ.label_add_period k
    simpa using this

end SmoothedOctagon.Reduction
