module

public import SmoothedOctagon.Exclusion.ShortRuns.Centre

/-!
# The local angle facts of a mixed period

The local inputs of the angle-density bound, at the pieces with equal incident signs of a mixed
normal period:

* `NormalPeriod.dens_centreData`: every reverse centre (switches `c - 2, c - 1, c, c + 1` signed
  `+ - - +`) carries the scalar data `m1_CentreData`, so the angle gap
  `m1_angle_gap` (`cos φ < 3/10`) applies to it. This is `NormalPeriod.m1_centreData` without the
  all-short pattern: its proof only reads the four switches around the centre.
* `CostateCycle.dens_pp_bound`: at a forward piece `+ +`, `e ≥ 0` or `4 e² ≤ d_- d_+` (the angle is
  at most `2π/3`). It follows from the lower bound `e ≥ X = (-1 + 2r + 2t - ρ + log q)/16`,
  `ρ < r`, and the polynomial inequality
  `(1 - r - 2t)² ≤ (1 - r + r²)(1 - t + t²)` (`dens_pp_scalar`).
* `dens_good`: the Gram identity `d_- d_+ - e² = γ²/K²` with `d_± ≥ 3/32` and `4 e² ≤ d_- d_+`
  gives `γ² > 27/256`.
* `dens_arccos_lt`, `dens_arccos_gt`: `arccos x < π/3` for `x > 1/2`, `arccos x > 2π/3` for
  `x < -1/2`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- **The Gram bound**: `d_- d_+ - e² = γ²/K²`, `d_± ≥ 3/32`, `K = a² + 4`, `a > 0`
and `4 e² ≤ d_- d_+` give `γ² > 27/256`. -/
theorem dens_good {γ2 a dm dp e : ℝ} (ha : 0 < a) (hdm : 3 / 32 ≤ dm) (hdp : 3 / 32 ≤ dp)
    (hgram : dm * dp - e ^ 2 = γ2 / (a ^ 2 + 4) ^ 2) (h4 : 4 * e ^ 2 ≤ dm * dp) :
    27 / 256 < γ2 := by
  have hK : 16 < (a ^ 2 + 4) ^ 2 := by nlinarith [sq_nonneg a, pow_pos ha 2]
  have hK0 : 0 < (a ^ 2 + 4) ^ 2 := by positivity
  have hg : γ2 = (a ^ 2 + 4) ^ 2 * (dm * dp - e ^ 2) := by
    rw [hgram]; field_simp
  have hdd : 9 / 1024 ≤ dm * dp := by nlinarith
  have h3 : 27 / 4096 ≤ dm * dp - e ^ 2 := by nlinarith
  rw [hg]
  nlinarith

/-- `arccos x < π/3` for `x > 1/2`. -/
theorem dens_arccos_lt {x : ℝ} (hx : 1 / 2 < x) : Real.arccos x < π / 3 := by
  have hpi := Real.pi_pos
  rcases le_or_gt x 1 with h1 | h1
  · have h := Real.arccos_lt_arccos (by norm_num) hx h1
    have e : Real.arccos (1 / 2) = π / 3 :=
      Real.arccos_eq_of_eq_cos (by positivity) (by linarith) Real.cos_pi_div_three.symm
    linarith
  · rw [Real.arccos_of_one_le h1.le]; positivity

/-- `arccos x > 2π/3` for `x < -1/2`. -/
theorem dens_arccos_gt {x : ℝ} (hx : x < -1 / 2) : 2 * π / 3 < Real.arccos x := by
  have hpi := Real.pi_pos
  rcases le_or_gt (-1) x with h1 | h1
  · have h := Real.arccos_lt_arccos h1 hx (by norm_num)
    have e : Real.arccos (-1 / 2) = 2 * π / 3 := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.arccos_neg,
        Real.arccos_eq_of_eq_cos (by positivity) (by linarith) Real.cos_pi_div_three.symm]
      ring
    linarith
  · rw [Real.arccos_of_le_neg_one h1.le]; linarith

/-- The polynomial inequality of a forward piece: `(1 - r - 2t)² ≤ (1 - r + r²)(1 - t + t²)` for
`r, t > 0`, `r + 2t < 1`. -/
theorem dens_pp_poly {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (h : r + 2 * t < 1) :
    (1 - r - 2 * t) ^ 2 ≤ (1 - r + r ^ 2) * (1 - t + t ^ 2) := by
  have h1 : 0 ≤ (1 - r - 2 * t) * r := mul_nonneg (by linarith) hr.le
  have h2 : 0 ≤ t * (3 - r - 4 * t) := mul_nonneg ht.le (by linarith)
  have h3 : 0 ≤ (1 - r) * t ^ 2 := mul_nonneg (by linarith) (sq_nonneg t)
  have h4 : 0 ≤ r ^ 2 * (1 - t + t ^ 2) := mul_nonneg (sq_nonneg r) (by nlinarith)
  nlinarith

/-- **The scalar bound of a forward piece**: with `e ≥ X = (-1 + 2r + 2t - ρ + L)/16`, `L > 0`,
`ρ < r` (`a p < 4`) and the forward switching bounds `d_- ≥ j(p,a)/2`, `d_+ ≥ j(a,n)/2`, either
`e ≥ 0` or `4 e² ≤ d_- d_+`. -/
theorem dens_pp_scalar {a p n dm dp e L : ℝ} (ha : 0 < a) (hp : 0 < p) (hn : 0 < n)
    (hap : a * p < 4) (hL : 0 < L)
    (heX : (-1 + 2 * a * (1 / (a + p) + 1 / (a + n)) - a ^ 2 / (a ^ 2 + 4) + L) / 16 ≤ e)
    (hdm : elJ p a / 2 ≤ dm) (hdp : elJ a n / 2 ≤ dp) : 0 ≤ e ∨ 4 * e ^ 2 ≤ dm * dp := by
  rcases le_or_gt 0 e with h | he
  · exact Or.inl h
  right
  set r := a / (a + p) with hr
  set t := a / (a + n) with ht
  have hr0 : 0 < r := by positivity
  have ht0 : 0 < t := by positivity
  have hρ : a ^ 2 / (a ^ 2 + 4) < r := by
    rw [hr, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have e1 : 2 * a * (1 / (a + p) + 1 / (a + n)) = 2 * r + 2 * t := by
    rw [hr, ht]; field_simp
  rw [e1] at heX
  -- `0 < -e ≤ -X < (1 - r - 2t)/16`
  have hD : 0 < 1 - r - 2 * t := by linarith
  have hneg : -e < (1 - r - 2 * t) / 16 := by linarith
  have hfm : dm ≥ (1 - r + r ^ 2) / 8 := by
    have : elJ p a / 2 = (1 - r + r ^ 2) / 8 := by
      simp only [elJ, hr]; field_simp; ring
    linarith
  have hfp : dp ≥ (1 - t + t ^ 2) / 8 := by
    have : elJ a n / 2 = (1 - t + t ^ 2) / 8 := by
      simp only [elJ, ht]; field_simp; ring
    linarith
  have hpoly := dens_pp_poly hr0 ht0 (by linarith)
  have hf1 : 0 < (1 - r + r ^ 2) / 8 := by nlinarith
  have hf2 : 0 < (1 - t + t ^ 2) / 8 := by nlinarith
  have hprod : (1 - r + r ^ 2) / 8 * ((1 - t + t ^ 2) / 8) ≤ dm * dp :=
    mul_le_mul hfm hfp hf2.le (by linarith)
  have hsq : e ^ 2 < ((1 - r - 2 * t) / 16) ^ 2 := by nlinarith
  nlinarith

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

/-- **A forward piece `+ +` has angle at most `2π/3`**: `e_k ≥ 0` or `4 e_k² ≤ d_{k-1} d_k`. -/
theorem dens_pp_bound {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1)
    (hout : C.lab (k + 1) = C.lab k + 1) :
    0 ≤ C.cre k ∨ 4 * C.cre k ^ 2 ≤ C.swd (k - 1) * C.swd k := by
  have ha := C.act_pos k
  have hp := C.act_pos (k - 1)
  have hn := C.act_pos (k + 1)
  -- the stationarity at a same-sign forward piece
  have hst := C.stationarity k
  rw [C.sgn_fwd (by rw [sub_add_cancel]; exact hin), C.sgn_fwd hout] at hst
  have he : C.cre k = ((C.act k + C.act (k - 1)) * C.swd (k - 1) +
      (C.act k + C.act (k + 1)) * C.swd k -
      (elGa (C.act k) (C.act (k - 1)) + elGa (C.act k) (C.act (k + 1))) / 16) / (2 * C.act k) := by
    field_simp
    linarith
  have hd1 := C.swd_fwd (k := k - 1) (by rw [sub_add_cancel]; exact hin)
  have hd2 := C.swd_fwd hout
  rw [sub_add_cancel] at hd1
  have hX := el_cross_bound ha hp hn
  have hge : ((C.act k + C.act (k - 1)) * (elJ (C.act (k - 1)) (C.act k) / 2) +
      (C.act k + C.act (k + 1)) * (elJ (C.act k) (C.act (k + 1)) / 2) -
      (elGa (C.act k) (C.act (k - 1)) + elGa (C.act k) (C.act (k + 1))) / 16) / (2 * C.act k) ≤
      C.cre k := by
    rw [he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  rw [hX] at hge
  -- `q > 1`
  have hfac := C.factor_pp hin hout
  have hq := C.one_lt_q k
  have hlog : 0 < Real.log ((C.act k + C.act (k - 1)) * (C.act k + C.act (k + 1)) /
      (C.act k ^ 2 + 4)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity), one_mul]
    simp only [sw, sub_add_cancel] at hfac
    have : C.act k ^ 2 + 4 < C.q k * (C.act k ^ 2 + 4) := by
      have : 0 < C.act k ^ 2 + 4 := by positivity
      nlinarith
    rw [hfac] at this; linarith
  -- `a p < 4`
  have hap : C.act k * C.act (k - 1) < 4 := by
    have hq4 := C.quad_rot k (C.lab k)
    have hp' : C.act (k - 1) = C.m k (C.lab k - 1) := by
      rw [C.act_pred, show C.lab (k - 1) = C.lab k - 1 by rw [hin, add_sub_cancel_right]]
    have := C.m_pos k (C.lab k + 1)
    rw [hp']; simp only [act]
    nlinarith [C.m_pos k (C.lab k), C.m_pos k (C.lab k - 1)]
  exact dens_pp_scalar ha hp hn hap hlog hge hd1 hd2

end CostateCycle

namespace NormalPeriod

variable (P : NormalPeriod)

/-- **The centre data at any reverse centre of a mixed period**: the switches
`c - 2, c - 1, c, c + 1` are `+ - - +`. -/
theorem dens_centreData (hmix : P.rep.IsMixed) {c : ℤ} (hf2 : P.rep.IsForward (c - 2))
    (hr1 : P.rep.IsReverse (c - 1)) (hr0 : P.rep.IsReverse c) (hf1 : P.rep.IsForward (c + 1)) :
    m1_CentreData (P.costateCycle.gam2 0) (P.m1_r c) (P.m1_t c) (P.m1_ρ c) (P.m1_u c)
      (P.m1_v c) (P.m1_E c) := by
  set C := P.costateCycle with hC
  -- signs around the centre
  have hin : C.lab c = C.lab (c - 1) - 1 := by
    have h : P.rep.label (c - 1 + 1) = P.rep.label (c - 1) - 1 := hr1
    rw [sub_add_cancel] at h; exact h
  have hout : C.lab (c + 1) = C.lab c - 1 := hr0
  have hfin : C.lab (c - 1) = C.lab (c - 1 - 1) + 1 := by
    have h : P.rep.label (c - 2 + 1) = P.rep.label (c - 2) + 1 := hf2
    rw [show c - 2 + 1 = c - 1 by ring, show c - 2 = c - 1 - 1 by ring] at h; exact h
  have hfout : C.lab (c + 1 + 1) = C.lab (c + 1) + 1 := hf1
  -- the two turns
  have ht1 : C.sgn (c - 1 - 1) = -C.sgn (c - 1) := by
    rw [C.sgn_fwd (by rw [sub_add_cancel]; exact hfin),
      C.sgn_rev (by rw [sub_add_cancel]; exact hin)]
    norm_num
  have ht2 : C.sgn (c + 1 - 1) = -C.sgn (c + 1) := by
    rw [add_sub_cancel_right, C.sgn_rev hout, C.sgn_fwd hfout]
  have hu0 := C.turn_swd_ge ht1
  have hv0 := C.turn_swd_ge ht2
  have hvv : C.swd c = C.swd (c + 1) := by
    have := (C.turn_secant ht2).1; rwa [add_sub_cancel_right] at this
  have hu1 := C.swd_rev (k := c - 1) (by rw [sub_add_cancel]; exact hin)
  have hv1 := C.swd_rev (k := c) hout
  rw [sub_add_cancel] at hu1
  -- the strict centre minimum
  have hrun : P.rep.IsReverseRun (c - 1) 2 := by
    refine ⟨by norm_num, by rw [show c - 1 - 1 = c - 2 by ring]; exact hf2,
      by rw [show c - 1 + ((2 : ℕ) : ℤ) = c + 1 by push_cast; ring]; exact hf1,
      fun i hi1 hi2 ↦ ?_⟩
    push_cast at hi2
    rcases (show i = c - 1 ∨ i = c by omega) with h | h <;> rw [h]
    · exact hr1
    · exact hr0
  have hmin := reverseRun_two_and_centre_min P hmix hrun
  rw [sub_add_cancel, show c - 1 + 2 = c + 1 by ring] at hmin
  obtain ⟨-, -, hap, han, -⟩ := hmin
  have hact : ∀ k, P.activeMargin k = C.act k := fun k ↦ (P.costateCycle_m_lab k).symm
  rw [hact, hact] at hap
  rw [hact, hact] at han
  -- positivity
  have ha := C.act_pos c
  have hp := C.act_pos (c - 1)
  have hn := C.act_pos (c + 1)
  have hK : 0 < C.act c ^ 2 + 4 := by positivity
  have hfac := C.centre_factor hin hout
  have hq := C.one_lt_q c
  have hstat := C.centre_stat hin hout
  have hgram := C.gram_mm hin hout
  rw [C.gam2_eq] at hgram
  have hJu : 8 * (elJ (C.act (c - 1)) (C.act c) / 2) =
      1 - C.act c / (C.act c + C.act (c - 1)) + (C.act c / (C.act c + C.act (c - 1))) ^ 2 := by
    simp only [elJ]; field_simp; ring
  have hJv : 8 * (elJ (C.act c) (C.act (c + 1)) / 2) =
      1 - C.act c / (C.act c + C.act (c + 1)) + (C.act c / (C.act c + C.act (c + 1))) ^ 2 := by
    simp only [elJ]; field_simp; ring
  simp only [m1_r, m1_t, m1_ρ, m1_u, m1_v, m1_E]
  refine ⟨by positivity, ?_, by positivity, ?_, by positivity, ?_, by linarith, by linarith,
    by linarith, by linarith, hstat, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · rw [div_lt_iff₀ (by positivity)]; linarith
  · -- `ρ < r t` from the centre factor
    rw [div_mul_div_comm, div_lt_div_iff₀ hK (by positivity)]
    have : (C.act c + C.act (c - 1)) * (C.act c + C.act (c + 1)) < C.act c ^ 2 + 4 := by
      rw [← hfac]
      have hpos : 0 < (C.act c + C.act (c - 1)) * (C.act c + C.act (c + 1)) := by positivity
      nlinarith
    have : 0 < C.act c ^ 2 := by positivity
    nlinarith
  · -- the Gram identity
    have e : 1 - C.act c ^ 2 / (C.act c ^ 2 + 4) = 4 / (C.act c ^ 2 + 4) := by field_simp; ring
    rw [e]
    have e2 : 16 * (4 / (C.act c ^ 2 + 4)) ^ 2 * C.gam2 0 =
        256 * (C.gam2 0 / (C.act c ^ 2 + 4) ^ 2) := by field_simp; ring
    rw [e2, ← hgram]
    ring

end NormalPeriod

end SmoothedOctagon
