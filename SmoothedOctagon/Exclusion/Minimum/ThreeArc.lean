module

public import SmoothedOctagon.Exclusion.Reverse.Four

/-!
# Three alternating pieces: strict log-concavity of the active margins

`MIXED_GLOBAL_MINIMUM_STRUCTURE` (12) and (16). On three consecutive pieces of a normal vertex
period with labels `i, j, i` the active margins satisfy `a_0 a_2 < a_1²`; on a turn the outer
active margins are ordered by the switch signs.

Route: the edge clock and covector transformation MGMS (13)-(14) (legacy note) are not used. On the
middle piece (label `j`, active margin `a`) the inactive Hamiltonian `σ_i = p_i H_i` of the outer
label is explicit (`Period/Costate.lean`): with `s` the running factor and `Y = α_j + α_i` at the
start, `σ_{j-1}(s) = -(2/s) (Y (1 - 1/s) + (√3 a/2) h(s))`,
`h(s) = (a + c) log s - a (s - 1) - c (1 - 1/s)` (decreasing outer margin `c`), and
`σ_{j+1}(s) = 2 s (Y (s - 1) + (√3 a/2) F(s))`,
`F(s) = (a + b) log s - (a + b)(s - 1) + a (s - 1)²/s` (growing outer margin `b`). It vanishes at
both ends of the piece and is `≤ 0` on it. A one-sided derivative at one end fixes the sign of `Y`,
and the value at the other end then contradicts `a_1² ≤ a_0 a_2`.

## Main API

* `cst_deriv_nonneg_of_left`, `cst_deriv_nonpos_of_right`: one-sided derivative signs at a zero
  of a nonpositive function.
* `cst_log_two`, `cst_qlog`: `(q + 1) log q > 2 (q - 1)`, `q log q > q - 1` for `q > 1`.
* `cst_three_decr`, `cst_three_grow`: the two scalar lemmas.
* `CostateCycle.three_arc`: `a_k a_{k+2} < a_{k+1}²` when `i_{k+2} = i_k`.
* `CostateCycle.turn_up`, `CostateCycle.turn_down`: MGMS (16).
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set Filter Topology

/-! ### One-sided derivatives -/

/-- At a right endpoint `x₀` where `f` vanishes and is `≤ 0` on `[x₁, x₀]`, `f'(x₀) ≥ 0`. -/
theorem cst_deriv_nonneg_of_left {f : ℝ → ℝ} {f' x₀ x₁ : ℝ} (hd : HasDerivAt f f' x₀)
    (h01 : x₁ < x₀) (h0 : f x₀ = 0) (hle : ∀ s ∈ Icc x₁ x₀, f s ≤ 0) : 0 ≤ f' := by
  have hT : Tendsto (slope f x₀) (𝓝[<] x₀) (𝓝 f') :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x₀)).1 hd.hasDerivWithinAt
  refine ge_of_tendsto hT ?_
  filter_upwards [Ioo_mem_nhdsLT h01] with s hs
  rw [slope_def_field, h0, sub_zero]
  exact div_nonneg_of_nonpos (hle s ⟨hs.1.le, hs.2.le⟩) (by linarith [hs.2])

/-- At a left endpoint `x₀` where `f` vanishes and is `≤ 0` on `[x₀, x₁]`, `f'(x₀) ≤ 0`. -/
theorem cst_deriv_nonpos_of_right {f : ℝ → ℝ} {f' x₀ x₁ : ℝ} (hd : HasDerivAt f f' x₀)
    (h01 : x₀ < x₁) (h0 : f x₀ = 0) (hle : ∀ s ∈ Icc x₀ x₁, f s ≤ 0) : f' ≤ 0 := by
  have hT : Tendsto (slope f x₀) (𝓝[>] x₀) (𝓝 f') :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x₀)).1 hd.hasDerivWithinAt
  refine le_of_tendsto hT ?_
  filter_upwards [Ioo_mem_nhdsGT h01] with s hs
  rw [slope_def_field, h0, sub_zero]
  exact div_nonpos_of_nonpos_of_nonneg (hle s ⟨hs.1.le, hs.2.le⟩) (by linarith [hs.1])

/-! ### Elementary logarithm bounds -/

theorem cst_log_two {q : ℝ} (hq : 1 < q) : 2 * (q - 1) < (q + 1) * Real.log q := by
  have h := cst_log_pade hq
  have hL : 0 < Real.log q := Real.log_pos hq
  have hden : 0 < q ^ 2 + 4 * q + 1 := by positivity
  have h1 : 0 ≤ (q - 1) ^ 3 := by
    have : 0 ≤ q - 1 := by linarith
    positivity
  have key : (q ^ 2 + 4 * q + 1) * (2 * (q - 1)) <
      (q ^ 2 + 4 * q + 1) * ((q + 1) * Real.log q) := by
    nlinarith
  exact lt_of_mul_lt_mul_left key hden.le

theorem cst_qlog {q : ℝ} (hq : 1 < q) : q - 1 < q * Real.log q := by
  have hq0 : 0 < q := by linarith
  have h := Real.log_lt_sub_one_of_pos (inv_pos.2 hq0) (by
    rw [Ne, inv_eq_one]; exact hq.ne')
  rw [Real.log_inv] at h
  have : q * (q⁻¹ - 1) = 1 - q := by field_simp
  nlinarith

/-! ### The two scalar lemmas -/

/-- **Three pieces, decreasing outer label.** On the middle piece (active margin `a`, factor `q`)
with decreasing outer margin `c` at its start, if the inactive Hamiltonian
`σ(s) = 2 (s⁻² Y + costateADecr a c s) + (s⁻¹ B + costateBDecr a c s)` (`2Y + B = 0`) is `≤ 0` for
`s ∈ [1, q]` and vanishes at `s = q`, then `c ((a + c)/q - a) < a²`. -/
theorem cst_three_decr {a c q Y B : ℝ} (ha : 0 < a) (hc : 0 < c) (hq : 1 < q)
    (hYB : 2 * Y + B = 0)
    (hle : ∀ s ∈ Icc 1 q,
      2 * (s⁻¹ ^ 2 * Y + costateADecr a c s) + (s⁻¹ * B + costateBDecr a c s) ≤ 0)
    (hend : 2 * (q⁻¹ ^ 2 * Y + costateADecr a c q) + (q⁻¹ * B + costateBDecr a c q) = 0) :
    c * ((a + c) / q - a) < a ^ 2 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hq0 : 0 < q := by linarith
  -- `σ(s) = -(2/s) g(s)`
  set g : ℝ → ℝ := fun s ↦ Y * (1 - s⁻¹) +
    √3 * a / 2 * ((a + c) * Real.log s - a * (s - 1) - c * (1 - s⁻¹)) with hg
  have hσ : ∀ s, 0 < s → 2 * (s⁻¹ ^ 2 * Y + costateADecr a c s) +
      (s⁻¹ * B + costateBDecr a c s) = -(2 / s) * g s := by
    intro s hs
    have hB : B = -2 * Y := by linarith
    simp only [hg, costateADecr, costateBDecr, hB]
    field_simp
    ring
  -- `g ≥ 0` on `[1, q]`, `g(1) = 0`, so `Y = g'(1) ≥ 0`
  have hgd : HasDerivAt (fun s ↦ -g s)
      (-(Y * 1 + √3 * a / 2 * ((a + c) * 1 - a - c * 1))) 1 := by
    have hi : HasDerivAt (fun s : ℝ ↦ s⁻¹) (-1) 1 := by
      simpa using hasDerivAt_inv (one_ne_zero (α := ℝ))
    have hlog : HasDerivAt Real.log 1 1 := by simpa using Real.hasDerivAt_log one_ne_zero
    have := (((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub hi).const_mul Y).add
      (((((hlog.const_mul (a + c)).sub (((hasDerivAt_id (1 : ℝ)).sub_const 1).const_mul a)).sub
        (((hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub hi).const_mul c))).const_mul (√3 * a / 2))
    refine this.neg.congr_deriv ?_
    ring
  have hY : 0 ≤ Y := by
    have := cst_deriv_nonpos_of_right hgd hq (by simp [hg]) (fun s hs ↦ by
      have hs0 : 0 < s := lt_of_lt_of_le one_pos hs.1
      have h1 := hle s hs
      rw [hσ s hs0] at h1
      have : 0 ≤ g s := by
        by_contra hneg
        push Not at hneg
        have : 0 < -(2 / s) * g s := mul_pos_of_neg_of_neg (by
          have : 0 < 2 / s := by positivity
          linarith) hneg
        linarith
      linarith)
    linarith
  -- the end value
  by_contra hcon
  push Not at hcon
  have haq : a * q ≤ c := by
    have hac : 0 < a + c := by linarith
    have : a * q * (a + c) ≤ c * (a + c) := by
      rw [mul_sub, mul_div_assoc'] at hcon
      rw [le_sub_iff_add_le, le_div_iff₀ hq0] at hcon
      nlinarith
    exact le_of_mul_le_mul_right this hac
  have hL := cst_log_two hq
  have hL2 : 1 - q⁻¹ < Real.log q := by
    have := cst_qlog hq
    rw [show 1 - q⁻¹ = (q - 1) / q by field_simp]
    rw [div_lt_iff₀ hq0]; linarith
  have hh : 0 < (a + c) * Real.log q - a * (q - 1) - c * (1 - q⁻¹) := by
    -- linear in `c`, increasing, and positive at `c = a q`
    have h1 : 0 ≤ (c - a * q) * (Real.log q - (1 - q⁻¹)) := by
      have : 0 ≤ c - a * q := by linarith
      have : 0 ≤ Real.log q - (1 - q⁻¹) := by linarith
      positivity
    have h2 : 0 < a * ((q + 1) * Real.log q - 2 * (q - 1)) := by
      have : 0 < (q + 1) * Real.log q - 2 * (q - 1) := by linarith
      positivity
    have e : (a + c) * Real.log q - a * (q - 1) - c * (1 - q⁻¹) =
        (c - a * q) * (Real.log q - (1 - q⁻¹)) + a * ((q + 1) * Real.log q - 2 * (q - 1)) := by
      field_simp; ring
    rw [e]; linarith
  have hgq : 0 < g q := by
    simp only [hg]
    have : 0 ≤ Y * (1 - q⁻¹) := by
      have : 0 < 1 - q⁻¹ := by
        have : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
        linarith
      positivity
    have : 0 < √3 * a / 2 * ((a + c) * Real.log q - a * (q - 1) - c * (1 - q⁻¹)) := by positivity
    linarith
  have := hσ q hq0
  rw [hend] at this
  have : 0 < 2 / q * g q := by positivity
  linarith

/-- **Three pieces, growing outer label.** On the middle piece (active margin `a`, factor `q`)
with growing outer margin `b` at its start, if the inactive Hamiltonian
`σ(s) = 2 (s² Y + costateAGrow a b s) + (s B + costateBGrow a b s)` (`2Y + B = 0`) is `≤ 0` for
`s ∈ [1, q]` and vanishes at `s = q`, then `b ((a + b) q - a) < a²`. -/
theorem cst_three_grow {a b q Y B : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : 1 < q)
    (hYB : 2 * Y + B = 0)
    (hle : ∀ s ∈ Icc 1 q,
      2 * (s ^ 2 * Y + costateAGrow a b s) + (s * B + costateBGrow a b s) ≤ 0)
    (hend : 2 * (q ^ 2 * Y + costateAGrow a b q) + (q * B + costateBGrow a b q) = 0) :
    b * ((a + b) * q - a) < a ^ 2 := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hq0 : 0 < q := by linarith
  -- `σ(s) = 2 s g(s)`
  set F : ℝ → ℝ := fun s ↦
    (a + b) * Real.log s - (a + b) * (s - 1) + a * ((s - 1) ^ 2 / s) with hF
  set F' : ℝ := (a + b) / q - (a + b) + a * ((2 * (q - 1) * q - (q - 1) ^ 2) / q ^ 2) with hF'
  set g : ℝ → ℝ := fun s ↦ Y * (s - 1) + √3 * a / 2 * F s with hg
  have hσ : ∀ s, 0 < s → 2 * (s ^ 2 * Y + costateAGrow a b s) + (s * B + costateBGrow a b s) =
      2 * s * g s := by
    intro s hs
    have hB : B = -2 * Y := by linarith
    simp only [hg, hF, costateAGrow, costateBGrow, hB]
    field_simp
    ring
  -- `g ≤ 0` on `[1, q]` and `g(q) = 0`, so `g'(q) ≥ 0`
  have hFd : HasDerivAt F F' q := by
    have hlog : HasDerivAt Real.log q⁻¹ q := Real.hasDerivAt_log hq0.ne'
    have h1 : HasDerivAt (fun s : ℝ ↦ (s - 1) ^ 2) (2 * (q - 1)) q := by
      simpa using ((hasDerivAt_id' q).sub_const 1).fun_pow 2
    have hsq : HasDerivAt (fun s : ℝ ↦ (s - 1) ^ 2 / s)
        ((2 * (q - 1) * q - (q - 1) ^ 2 * 1) / q ^ 2) q := h1.div (hasDerivAt_id' q) hq0.ne'
    have := ((hlog.const_mul (a + b)).sub (((hasDerivAt_id' q).sub_const 1).const_mul (a + b))).add
      (hsq.const_mul a)
    refine this.congr_deriv ?_
    simp only [hF']
    field_simp
  have hgd : HasDerivAt g (Y + √3 * a / 2 * F') q := by
    have := (((hasDerivAt_id' q).sub_const 1).const_mul Y).add (hFd.const_mul (√3 * a / 2))
    exact this.congr_deriv (by ring)
  have hgq : g q = 0 := by
    have := hσ q hq0
    rw [hend] at this
    have h2q : 2 * q ≠ 0 := by positivity
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h h2q
    · exact h
  have hder := cst_deriv_nonneg_of_left hgd hq hgq (fun s hs ↦ by
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs.1
    have h1 := hle s hs
    rw [hσ s hs0] at h1
    by_contra hpos
    push Not at hpos
    have : 0 < 2 * s * g s := by positivity
    linarith)
  -- the contradiction
  by_contra hcon
  push Not at hcon
  have hab : a ≤ b * q := by
    have hab0 : 0 < a + b := by linarith
    have : a * (a + b) ≤ b * q * (a + b) := by nlinarith
    exact le_of_mul_le_mul_right this hab0
  have hL := cst_log_two hq
  have hL2 := cst_qlog hq
  -- `(q - 1) F'(q) - F(q) < 0`
  have hΦ : (q - 1) * (2 * a * q - a + b * q) < (a + b) * q ^ 2 * Real.log q := by
    have hcB : 0 < q ^ 2 * Real.log q - q * (q - 1) := by nlinarith
    by_cases hcA : 0 ≤ q ^ 2 * Real.log q - (q - 1) * (2 * q - 1)
    · have := mul_nonneg ha.le hcA
      have := mul_pos hb hcB
      nlinarith
    · push Not at hcA
      have h1 : b * q * (q ^ 2 * Real.log q - (q - 1) * (2 * q - 1)) ≤
          a * (q ^ 2 * Real.log q - (q - 1) * (2 * q - 1)) :=
        mul_le_mul_of_nonpos_right hab hcA.le
      have h2 : 0 < b * q ^ 2 * ((q + 1) * Real.log q - 2 * (q - 1)) := by
        have : 0 < (q + 1) * Real.log q - 2 * (q - 1) := by linarith
        positivity
      nlinarith
  have hq1 : 0 < q - 1 := by linarith
  have hc : 0 < √3 * a / 2 := by positivity
  have hgq' : Y * (q - 1) + √3 * a / 2 * F q = 0 := hgq
  have h1 : 0 ≤ (q - 1) * (Y + √3 * a / 2 * F') := mul_nonneg hq1.le hder
  have h2 : (q - 1) * (Y + √3 * a / 2 * F') = √3 * a / 2 * ((q - 1) * F' - F q) := by
    linear_combination hgq'
  rw [h2] at h1
  have h3 : 0 ≤ (q - 1) * F' - F q := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hc hneg
    linarith
  have e2 : (q - 1) * F' - F q =
      ((q - 1) * (2 * a * q - a + b * q) - (a + b) * q ^ 2 * Real.log q) / q ^ 2 := by
    simp only [hF, hF']
    field_simp
    ring
  rw [e2] at h3
  have : ((q - 1) * (2 * a * q - a + b * q) - (a + b) * q ^ 2 * Real.log q) / q ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by positivity)
  linarith

/-! ### On a costate cycle -/

theorem cst_fin_ne_cases {i j : Fin 3} (h : i ≠ j) : i = j + 1 ∨ i = j - 1 := by
  revert i j; decide

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

/-- **Three-arc strict log-concavity** (MGMS (12)). If pieces `k` and `k + 2` have the same label,
then `a_k a_{k+2} < a_{k+1}²`; in particular the middle active margin is not at most both outer
ones. -/
theorem three_arc (k : ℤ) (h : C.lab (k + 2) = C.lab k) :
    C.act k * C.act (k + 2) < C.act (k + 1) ^ 2 := by
  have hne : C.lab k ≠ C.lab (k + 1) := (C.lab_ne k).symm
  obtain ⟨M0, M1, M2, T1, T2, T3, T4, T5, T6⟩ := C.transport (k + 1) (i := C.lab (k + 1)) rfl
  rw [show k + 1 + 1 = k + 2 by ring] at M0 M1 M2 T1 T2 T3 T4 T5 T6
  have s1 := C.sig_act (k + 1)
  have s2 := C.sig_act_succ k
  have s3 := C.sig_act (k + 2)
  rw [h] at s3
  simp only [sig] at s2
  have a0 : C.act k = C.m (k + 1) (C.lab k) := (C.m_act k).symm
  have a2 : C.act (k + 2) = C.m (k + 2) (C.lab k) := by simp only [act, h]
  have a1 : C.act (k + 1) = C.m (k + 1) (C.lab (k + 1)) := rfl
  rcases cst_fin_ne_cases hne with hi | hi
  · -- growing outer label
    rw [hi] at s2 s3 a0 a2
    rw [a0, a2, a1, M1]
    refine cst_three_grow (C.m_pos _ _) (C.m_pos _ _) (C.one_lt_q _) (by linarith)
      (C.sig_grow_le (k + 1)) ?_
    rw [← T2, ← T5]
    linarith
  · -- decreasing outer label
    rw [hi] at s2 s3 a0 a2
    rw [a0, a2, a1, M2]
    refine cst_three_decr (C.m_pos _ _) (C.m_pos _ _) (C.one_lt_q _) (by linarith)
      (C.sig_decr_le (k + 1)) ?_
    rw [← T3, ← T6]
    linarith

/-- The middle of three pieces with labels `i, j, i` is not a weak minimum of the three. -/
theorem three_arc_not_min (k : ℤ) (h : C.lab (k + 2) = C.lab k) :
    ¬ (C.act (k + 1) ≤ C.act k ∧ C.act (k + 1) ≤ C.act (k + 2)) := by
  rintro ⟨h0, h2⟩
  have := C.three_arc k h
  have p1 := C.act_pos (k + 1)
  nlinarith

/-- **Turn feasibility** (MGMS (16), first row). A reverse switch followed by a forward switch:
the active margin grows across the turn, `a_k < a_{k+2}`. -/
theorem turn_up (k : ℤ) (h1 : C.lab (k + 1) = C.lab k - 1)
    (h2 : C.lab (k + 2) = C.lab (k + 1) + 1) :
    C.act k < C.act (k + 2) := by
  obtain ⟨-, M1, -, -⟩ := C.transport (k + 1) (i := C.lab (k + 1)) rfl
  rw [show k + 1 + 1 = k + 2 by ring] at M1
  have hk : C.lab (k + 1) + 1 = C.lab k := by rw [h1]; exact sub_add_cancel _ _
  have a2 : C.act (k + 2) = C.m (k + 2) (C.lab (k + 1) + 1) := by simp only [act, h2]
  have a0 : C.act k = C.m (k + 1) (C.lab (k + 1) + 1) := by rw [hk]; exact (C.m_act k).symm
  rw [a2, M1, a0]
  have hq := C.one_lt_q (k + 1)
  have hp := C.m_pos (k + 1) (C.lab (k + 1))
  have hp' := C.m_pos (k + 1) (C.lab (k + 1) + 1)
  nlinarith

/-- **Turn feasibility** (MGMS (16), second row). A forward switch followed by a reverse switch:
the active margin drops across the turn, `a_{k+2} < a_k`. -/
theorem turn_down (k : ℤ) (h1 : C.lab (k + 1) = C.lab k + 1)
    (h2 : C.lab (k + 2) = C.lab (k + 1) - 1) : C.act (k + 2) < C.act k := by
  obtain ⟨-, -, M2, -⟩ := C.transport (k + 1) (i := C.lab (k + 1)) rfl
  rw [show k + 1 + 1 = k + 2 by ring] at M2
  have hk : C.lab (k + 1) - 1 = C.lab k := by rw [h1]; exact add_sub_cancel_right _ _
  have a2 : C.act (k + 2) = C.m (k + 2) (C.lab (k + 1) - 1) := by simp only [act, h2]
  have a0 : C.act k = C.m (k + 1) (C.lab (k + 1) - 1) := by rw [hk]; exact (C.m_act k).symm
  rw [a2, M2, a0]
  have hq := C.one_lt_q (k + 1)
  have hp := C.m_pos (k + 1) (C.lab (k + 1))
  have hp' := C.m_pos (k + 1) (C.lab (k + 1) - 1)
  have hq0 : 0 < C.q (k + 1) := by linarith
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hq0]
  nlinarith

end CostateCycle

end SmoothedOctagon
