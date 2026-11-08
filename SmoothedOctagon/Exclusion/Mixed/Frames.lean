module

public import SmoothedOctagon.Exclusion.Mixed.Interface

/-!
# Case M2: factors, star inequalities and frame changes on the costate cycle

`MIXED_GLOBAL_COSTATE_ELLIPTIC` (CE) (2), (10)-(13) and inventory E2 §1.4, on the cycle of a normal
vertex period and its covector calculus.

* `VertexRepresentation.m2_fwd_or_rev`, `m2_not_fwd_and_rev`, `m2_rev_iff_not_fwd`: every switch
  is forward or reverse, not both.
* `m2_quad_rot`, `m2_m_prev`: the switch margins of piece `k` (the previous active margin, the
  quadric); `m2_star`: strict star `a_{k-1} a_k < 4` at every switch; `m2_third`: the third
  margin `(4 - a_{k-1} a_k)/(a_{k-1} + a_k)`.
* The factor formulas CE (2): `m2_factor_ff` (`q K = (p + a)(a + n)`), `m2_factor_rr`
  (`q (p + a)(a + n) = K`), `m2_factor_rf` (`q (p + a) = a + n`), `m2_factor_fr`
  (`q (a + n) = p + a`), with `p = a_{k-1}`, `a = a_k`, `n = a_{k+1}`, `K = a² + 4`.
* `m2A_det`, `m2_transport_mul`: `det A_i = 1`, `A_i M (i + 1) = M i A_i`.
* `m2_norm_next`: the norm of switch `i` read in the frame of piece `i + 1`: `8 (M (i+1))₂₁/s²`
  after a reverse switch, `-8 (M (i+1))₁₂/s²` after a forward one (E2 §1.4, "incoming" norms).
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons

namespace VertexRepresentation

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} (ρ : VertexRepresentation T u)

/-- Every switch is forward or reverse. -/
theorem m2_fwd_or_rev (k : ℤ) : ρ.IsForward k ∨ ρ.IsReverse k := by
  have h := ρ.label_ne k
  unfold IsForward IsReverse
  generalize ρ.label (k + 1) = x at h ⊢
  generalize ρ.label k = y at h ⊢
  revert x y; decide

/-- No switch is both forward and reverse. -/
theorem m2_not_fwd_and_rev (k : ℤ) : ¬ (ρ.IsForward k ∧ ρ.IsReverse k) := by
  unfold IsForward IsReverse
  rintro ⟨h1, h2⟩
  rw [h1] at h2
  generalize ρ.label k = y at h2
  revert y; decide

theorem m2_rev_iff_not_fwd (k : ℤ) : ρ.IsReverse k ↔ ¬ ρ.IsForward k :=
  ⟨fun h hf => ρ.m2_not_fwd_and_rev k ⟨hf, h⟩, fun h => (ρ.m2_fwd_or_rev k).resolve_left h⟩

end VertexRepresentation

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

/-- The quadric in the label order `i, i + 1, i - 1`. -/
theorem m2_quad_rot (k : ℤ) (i : Fin 3) :
    C.m k i * C.m k (i + 1) + C.m k (i + 1) * C.m k (i - 1) + C.m k (i - 1) * C.m k i = 4 := by
  have h := C.m_quad k
  fin_cases i
  · simp only [Fin.zero_eta, zero_add, show (0 : Fin 3) - 1 = 2 from rfl]; linarith
  · simp only [Fin.mk_one, show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) - 1 = 0 from rfl]
    linarith
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      show (2 : Fin 3) - 1 = 1 from rfl]
    linarith

/-- At the start of piece `k`, the label of piece `k - 1` carries the active margin `a_{k-1}`. -/
theorem m2_m_prev (k : ℤ) : C.m k (C.lab (k - 1)) = C.act (k - 1) := by
  have := C.m_act (k - 1)
  rw [sub_add_cancel] at this
  exact this

theorem m2_lab_prev_fwd {k : ℤ} (h : C.m2Fwd (k - 1)) : C.lab (k - 1) = C.lab k - 1 := by
  unfold m2Fwd at h; rw [sub_add_cancel] at h; rw [h]; abel

theorem m2_lab_prev_rev {k : ℤ} (h : ¬ C.m2Fwd (k - 1)) : C.lab (k - 1) = C.lab k + 1 := by
  unfold m2Fwd at h
  rw [sub_add_cancel] at h
  have hne := C.lab_ne (k - 1)
  rw [sub_add_cancel] at hne
  generalize C.lab k = x at h hne ⊢
  generalize C.lab (k - 1) = y at h hne ⊢
  revert x y; decide

theorem m2_lab_next_rev {k : ℤ} (h : ¬ C.m2Fwd k) : C.lab (k + 1) = C.lab k - 1 := by
  unfold m2Fwd at h
  have hne := C.lab_ne k
  generalize C.lab k = x at h hne ⊢
  generalize C.lab (k + 1) = y at h hne ⊢
  revert x y; decide

/-- The third margin at the start of piece `k`, after a forward switch: label `i_k + 1`. -/
theorem m2_third_fwd {k : ℤ} (h : C.m2Fwd (k - 1)) :
    C.m k (C.lab k + 1) * (C.act (k - 1) + C.act k) = 4 - C.act (k - 1) * C.act k := by
  have hq := C.m2_quad_rot k (C.lab k)
  have hp := C.m2_m_prev k
  rw [C.m2_lab_prev_fwd h] at hp
  rw [hp] at hq
  have ha : C.m k (C.lab k) = C.act k := rfl
  rw [ha] at hq
  linarith

/-- The third margin at the start of piece `k`, after a reverse switch: label `i_k - 1`. -/
theorem m2_third_rev {k : ℤ} (h : ¬ C.m2Fwd (k - 1)) :
    C.m k (C.lab k - 1) * (C.act (k - 1) + C.act k) = 4 - C.act (k - 1) * C.act k := by
  have hq := C.m2_quad_rot k (C.lab k)
  have hp := C.m2_m_prev k
  rw [C.m2_lab_prev_rev h] at hp
  rw [hp] at hq
  have ha : C.m k (C.lab k) = C.act k := rfl
  rw [ha] at hq
  linarith

/-- **Strict star at every switch**: `a_{k-1} a_k < 4`. -/
theorem m2_star (k : ℤ) : C.act (k - 1) * C.act k < 4 := by
  have h1 := C.act_pos (k - 1)
  have h2 := C.act_pos k
  by_cases h : C.m2Fwd (k - 1)
  · have := C.m2_third_fwd h
    have := C.m_pos k (C.lab k + 1)
    nlinarith
  · have := C.m2_third_rev h
    have := C.m_pos k (C.lab k - 1)
    nlinarith

/-- **Factor `++`** (CE (2)): `q_k K_k = (a_{k-1} + a_k)(a_k + a_{k+1})`. -/
theorem m2_factor_ff {k : ℤ} (h1 : C.m2Fwd (k - 1)) (h0 : C.m2Fwd k) :
    C.q k * (C.act k ^ 2 + 4) = (C.act (k - 1) + C.act k) * (C.act k + C.act (k + 1)) := by
  have ht := C.m2_third_fwd h1
  have hg := C.m_grow k
  have hn : C.act (k + 1) = C.m (k + 1) (C.lab k + 1) := by
    unfold act; rw [show C.lab (k + 1) = C.lab k + 1 from h0]
  have ha : C.m k (C.lab k) = C.act k := rfl
  rw [ha] at hg
  have hs : 0 < C.act (k - 1) + C.act k := by linarith [C.act_pos (k - 1), C.act_pos k]
  rw [hn, hg]
  have e : C.m k (C.lab k + 1) = (4 - C.act (k - 1) * C.act k) / (C.act (k - 1) + C.act k) := by
    rw [eq_div_iff hs.ne']; exact ht
  rw [e]
  field_simp
  ring

/-- **Factor `--`** (CE (2)): `q_k (a_{k-1} + a_k)(a_k + a_{k+1}) = K_k`. -/
theorem m2_factor_rr {k : ℤ} (h1 : ¬ C.m2Fwd (k - 1)) (h0 : ¬ C.m2Fwd k) :
    C.q k * ((C.act (k - 1) + C.act k) * (C.act k + C.act (k + 1))) = C.act k ^ 2 + 4 := by
  have ht := C.m2_third_rev h1
  have hd := C.m_decr k
  have hn : C.act (k + 1) = C.m (k + 1) (C.lab k - 1) := by
    unfold act; rw [C.m2_lab_next_rev h0]
  have ha : C.m k (C.lab k) = C.act k := rfl
  rw [ha] at hd
  have hs : 0 < C.act (k - 1) + C.act k := by linarith [C.act_pos (k - 1), C.act_pos k]
  have hq := C.q_pos k
  rw [hn, hd]
  have e : C.m k (C.lab k - 1) = (4 - C.act (k - 1) * C.act k) / (C.act (k - 1) + C.act k) := by
    rw [eq_div_iff hs.ne']; exact ht
  rw [e]
  field_simp
  ring

/-- **Factor `-+`** (CE (2)): `q_k (a_{k-1} + a_k) = a_k + a_{k+1}`. -/
theorem m2_factor_rf {k : ℤ} (h1 : ¬ C.m2Fwd (k - 1)) (h0 : C.m2Fwd k) :
    C.q k * (C.act (k - 1) + C.act k) = C.act k + C.act (k + 1) := by
  have hp := C.m2_m_prev k
  rw [C.m2_lab_prev_rev h1] at hp
  have hg := C.m_grow k
  have hn : C.act (k + 1) = C.m (k + 1) (C.lab k + 1) := by
    unfold act; rw [show C.lab (k + 1) = C.lab k + 1 from h0]
  have ha : C.m k (C.lab k) = C.act k := rfl
  rw [ha, hp] at hg
  rw [hn, hg]
  ring

/-- **Factor `+-`** (CE (2)): `q_k (a_k + a_{k+1}) = a_{k-1} + a_k`. -/
theorem m2_factor_fr {k : ℤ} (h1 : C.m2Fwd (k - 1)) (h0 : ¬ C.m2Fwd k) :
    C.q k * (C.act k + C.act (k + 1)) = C.act (k - 1) + C.act k := by
  have hp := C.m2_m_prev k
  rw [C.m2_lab_prev_fwd h1] at hp
  have hd := C.m_decr k
  have hn : C.act (k + 1) = C.m (k + 1) (C.lab k - 1) := by
    unfold act; rw [C.m2_lab_next_rev h0]
  have ha : C.m k (C.lab k) = C.act k := rfl
  rw [ha, hp] at hd
  have hq := C.q_pos k
  rw [hn, hd]
  field_simp
  ring

/-- `det A_i = 1`. -/
theorem m2A_det (i : ℤ) : (C.m2A i).det = 1 := by
  have hq := (C.q_pos i).ne'
  unfold m2A m2T0
  split_ifs <;>
    simp [Matrix.det_fin_two_of, Term.triR, Term.triRinv, hq]

/-- `A_i (M (i + 1)) = (M i) A_i`, from the transport. -/
theorem m2_transport_mul {M : ℤ → Mat2} (hM : ∀ i, M (i + 1) = (C.m2A i)⁻¹ * M i * C.m2A i)
    (i : ℤ) : C.m2A i * M (i + 1) = M i * C.m2A i := by
  have hu : IsUnit (C.m2A i).det := by rw [C.m2A_det]; exact isUnit_one
  rw [hM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

/-- **The norm of switch `i` in the frame of piece `i + 1`** (E2 §1.4): `8 (M (i+1))₂₁/s²` after a
reverse switch and `-8 (M (i+1))₁₂/s²` after a forward one, `s = a_i + a_{i+1}`. -/
theorem m2_norm_next {M : ℤ → Mat2} (hM : ∀ i, M (i + 1) = (C.m2A i)⁻¹ * M i * C.m2A i)
    (i : ℤ) :
    C.m2Norm M i = if C.m2Fwd i then -8 * M (i + 1) 0 1 / (C.act i + C.act (i + 1)) ^ 2
      else 8 * M (i + 1) 1 0 / (C.act i + C.act (i + 1)) ^ 2 := by
  have h := C.m2_transport_mul hM i
  have hq := (C.q_pos i).ne'
  unfold m2Norm
  unfold m2A m2T0 at h
  split_ifs with hf
  · simp only [hf, ↓reduceIte] at h
    have e := congrFun (congrFun h 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Term.triRinv] at e
    have e' : M i 1 0 = -M (i + 1) 0 1 / C.q i ^ 2 := by
      field_simp; field_simp at e; linarith
    rw [e']
    field_simp
  · simp only [hf, ↓reduceIte] at h
    have e := congrFun (congrFun h 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, Term.triR] at e
    have e' : M i 0 1 = -(C.q i ^ 2 * M (i + 1) 1 0) := by
      field_simp at e; linarith
    rw [e']
    field_simp

end CostateCycle

end SmoothedOctagon
