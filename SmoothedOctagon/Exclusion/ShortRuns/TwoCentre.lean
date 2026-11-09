module

public import SmoothedOctagon.Exclusion.ShortRuns.Centre
public import SmoothedOctagon.Foundations.ReciprocalMidpoint

/-!
# Case M1: the two-centre period

A normal period with the sign word `(− − +)²` has cost greater than
`√3(2√2 - 1)`, which exceeds the octagon cost.

The two-centre Jacobi recurrence forces opposite monodromy, equal active margins
and vanishing diagonal terms. Euler's identity gives the cost `8√3/K`, with
`K = a² + 4`. The bridge products are at least `(1 + √2)² a²`; multiplying the
strict centre-factor bounds gives `a² < 4/(5 + 4√2)`. The reciprocal midpoint
inequality completes the exact comparison with the octagon.

## Main API

* `m1_two_centre`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real SmoothedPolygons Set
open scoped Matrix

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

/-- The recurrence in the global frame: `K_{n+3} y_{n+3} = -K_n y_{n-1} + D_n y_n`. -/
theorem m1_next_centre (n : ℕ) (hn : 1 ≤ n) (h0 : C.lab n = C.lab ((n : ℤ) - 1) - 1)
    (h1 : C.lab ((n : ℤ) + 1) = C.lab n - 1) (h2 : C.lab ((n : ℤ) + 2) = C.lab ((n : ℤ) + 1) + 1)
    (h3 : C.lab ((n : ℤ) + 3) = C.lab ((n : ℤ) + 2) - 1)
    (h4 : C.lab ((n : ℤ) + 4) = C.lab ((n : ℤ) + 3) - 1) :
    (C.act ((n : ℤ) + 3) ^ 2 + 4) • C.yv (n + 3) =
      -(C.act n ^ 2 + 4) • C.yv (n - 1) +
        (C.sw n ^ 2 + C.sw ((n : ℤ) + 2) ^ 2 - C.sw ((n : ℤ) + 1) ^ 2) • C.yv n := by
  have hloc := C.next_centre_local n h0 h1 h2 h3 h4
  have hpre : C.pre (n + 3) = C.pre n * (C.Amat n * C.Amat ((n : ℤ) + 1) * C.Amat ((n : ℤ) + 2)) := by
    simp only [pre, Nat.cast_add, Nat.cast_one, Matrix.mul_assoc]
    push_cast
    ring_nf
  have hy1 : C.yv (n - 1) = C.pre n *ᵥ C.inc n := by
    have := C.yv_eq_inc (n - 1)
    rw [Nat.sub_add_cancel hn] at this
    exact this.symm
  have hy3 : C.yv (n + 3) = C.pre n *ᵥ ((C.Amat n * C.Amat ((n : ℤ) + 1) * C.Amat ((n : ℤ) + 2)) *ᵥ
      C.outv ((n : ℤ) + 3)) := by
    rw [yv, hpre, ← Matrix.mulVec_mulVec]; push_cast; rfl
  rw [hy3, hy1, yv, ← Matrix.mulVec_smul, hloc, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul]

/-- At a turn piece `n + 1` the switch vector flips: `y_{n+1} = -y_n`. -/
theorem m1_yv_turn (n : ℕ) (hturn : C.sgn (((n + 1 : ℕ) : ℤ) - 1) = -C.sgn ((n + 1 : ℕ) : ℤ)) :
    C.yv (n + 1) = -C.yv n := by
  rw [← C.yv_eq_inc n, yv, C.outv_turn hturn, Matrix.mulVec_neg]

end CostateCycle

/-- Shifting the window of a sum over one period. -/
theorem m1_sum_window {N : ℕ} (f : ℤ → ℝ) (hf : ∀ k, f (k + N) = f k) (r : ℕ) :
    ∑ j ∈ Finset.range N, f ((j : ℤ) + r) = ∑ j ∈ Finset.range N, f j := by
  induction r with
  | zero => simp
  | succ r ih =>
    have := CostateCycle.el_sum_shift (N := N) (fun k ↦ f (k + r)) (fun k ↦ by
      rw [show k + N + r = k + r + N by ring, hf])
    rw [← ih, ← this]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    congr 1; push_cast; ring

/-- Expanding a sum over a window of six. -/
theorem m1_sum_six (f : ℤ → ℝ) (c : ℤ) :
    ∑ j ∈ Finset.range 6, f ((j : ℤ) + c) =
      f c + f (c + 1) + f (c + 2) + f (c + 3) + f (c + 4) + f (c + 5) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero, zero_add]
  rw [add_comm (1 : ℤ) c, add_comm (2 : ℤ) c, add_comm (3 : ℤ) c, add_comm (4 : ℤ) c,
    add_comm (5 : ℤ) c]

/-- The bridge relation gives the sharp product bound and exact centre-factor identity. -/
theorem m1_bc_bound {a b c : ℝ} (ha : 0 < a) (hb : a < b) (hc : a < c)
    (h : (b-a)*(c-a) = 2*a^2) :
    (1+sqrt 2)^2*a^2 ≤ b*c ∧ (a+b)*(a+c) = 2*b*c := by
  have hs0 : 0 ≤ sqrt (2:ℝ) := sqrt_nonneg _
  have hs2 : (sqrt (2:ℝ))^2 = 2 := sq_sqrt (by norm_num)
  have hs : 0 ≤ b+c-2*a := by linarith only [hb,hc]
  have h8 : 8*a^2 ≤ (b+c-2*a)^2 := by nlinarith only [h,sq_nonneg (b-c)]
  have hroot : (2*sqrt 2*a)^2 = 8*a^2 := by
    calc
      (2*sqrt 2*a)^2 = 4*(sqrt (2:ℝ))^2*a^2 := by ring
      _ = 8*a^2 := by rw [hs2]; ring
  have hsum : 2*sqrt 2*a ≤ b+c-2*a :=
    (sq_le_sq₀ (by positivity) hs).mp (by rw [hroot]; exact h8)
  have hr : (1+sqrt (2:ℝ))^2 = 3+2*sqrt 2 := by nlinarith only [hs2]
  constructor
  · rw [hr]
    have hm := mul_le_mul_of_nonneg_left hsum ha.le
    nlinarith only [h,hm]
  · nlinarith only [h]

/-- Dimensionless version of the exact product bound. -/
theorem m1_xz_bound {x z : ℝ} (hx : 1 < x) (hz : 1 < z)
    (h : x*z = x+z+1) : (1+sqrt 2)^2 ≤ x*z := by
  have hh : (x-1)*(z-1) = 2*(1:ℝ)^2 := by nlinarith only [h]
  simpa using (m1_bc_bound (by norm_num : (0:ℝ) < 1) hx hz hh).1

/-- The positive centre factors bound the margin and exact cost. -/
theorem m1_two_centre_bounds {a b₀ c₀ b₁ c₁ K : ℝ}
    (ha : 0 < a) (hK : K = a^2+4)
    (m1 : a < c₁) (m2 : a < b₀) (m3 : a < c₀) (m4 : a < b₁)
    (hD0 : (b₀-a)*(c₀-a) = 2*a^2) (hD1 : (b₁-a)*(c₁-a) = 2*a^2)
    (l0 : (a+c₁)*(a+b₀) < K) (l1 : (a+c₀)*(a+b₁) < K) :
    a^2 < 4/(5+4*sqrt 2) ∧ sqrt 3*(2*sqrt 2-1) < 8*sqrt 3/K := by
  obtain ⟨bc0,p0⟩ := m1_bc_bound ha m2 m3 hD0
  obtain ⟨bc1,p1⟩ := m1_bc_bound ha m4 m1 hD1
  have hs2 : (sqrt (2:ℝ))^2 = 2 := sq_sqrt (by norm_num)
  have hs0 : 0 < sqrt (2:ℝ) := by positivity
  have hs1 : 1 < sqrt (2:ℝ) := by rw [lt_sqrt (by norm_num)]; norm_num
  have hKpos : 0 < K := by rw [hK]; positivity
  have hfactor0 : 0 ≤ (a+c₁)*(a+b₀) :=
    mul_nonneg (by linarith only [ha,m1]) (by linarith only [ha,m2])
  have hfactor1 : 0 ≤ (a+c₀)*(a+b₁) :=
    mul_nonneg (by linarith only [ha,m3]) (by linarith only [ha,m4])
  have hprod := mul_lt_mul'' l0 l1 hfactor0 hfactor1
  have hsq : 4*(b₀*c₀)*(b₁*c₁) < K^2 := by
    have hid : (a+c₁)*(a+b₀)*((a+c₀)*(a+b₁)) =
        ((a+b₀)*(a+c₀))*((a+b₁)*(a+c₁)) := by ring
    rw [hid,p0,p1] at hprod
    nlinarith only [hprod]
  have hbc0 : 0 ≤ (1+sqrt (2:ℝ))^2*a^2 := by positivity
  have hbc1 : 0 ≤ b₀*c₀ := by linarith only [hbc0,bc0]
  have hbcprod := mul_le_mul bc0 bc1 hbc0 hbc1
  have hsq' : (2*(1+sqrt 2)^2*a^2)^2 < K^2 := by nlinarith only [hbcprod,hsq]
  have hKexact : 2*(1+sqrt 2)^2*a^2 < K :=
    (sq_lt_sq₀ (by positivity) hKpos.le).mp hsq'
  have hr : (1+sqrt (2:ℝ))^2 = 3+2*sqrt 2 := by nlinarith only [hs2]
  rw [hr] at hKexact
  have hden : 0 < 5+4*sqrt (2:ℝ) := by positivity
  have haBound : a^2 < 4/(5+4*sqrt 2) := by
    rw [lt_div_iff₀ hden]
    nlinarith only [hKexact,hK]
  have hKBound : K < 4+4/(5+4*sqrt 2) := by linarith only [haBound,hK]
  have hcap : (2*sqrt 2-1)*(4+4/(5+4*sqrt 2)) = 8 := by
    field_simp
    nlinarith only [hs2]
  have hmul := mul_lt_mul_of_pos_left hKBound (show 0 < 2*sqrt 2-1 by linarith only [hs1])
  have hcost : sqrt 3*(2*sqrt 2-1) < 8*sqrt 3/K := by
    rw [lt_div_iff₀ hKpos]
    have hstrict : (2*sqrt 2-1)*K < 8 := by linarith only [hmul,hcap]
    have hp := mul_lt_mul_of_pos_left hstrict (show 0 < sqrt (3:ℝ) by positivity)
    nlinarith only [hp]
  exact ⟨haBound,hcost⟩




/-- The exact reciprocal midpoint gap beats the two-centre density barrier. -/
theorem m1_octagonCost_lt_two_centre : octagonCost < sqrt 3*(2*sqrt 2-1) := by
  have hs0 : 0 ≤ sqrt (2:ℝ) := sqrt_nonneg _
  have hs1 : 1 < sqrt (2:ℝ) := by rw [lt_sqrt (by norm_num)]; norm_num
  have hs2 : (sqrt (2:ℝ))^2 = 2 := sq_sqrt (by norm_num)
  have hlog := ra_log_two_gt_midpoint
  have emid : 4*(sqrt 2-1)/(sqrt 2+1) = 12-8*sqrt 2 := by
    field_simp
    nlinarith only [hs2]
  rw [emid] at hlog
  have h32 : 0 < 3-2*sqrt (2:ℝ) := by nlinarith only [hs2,hs0]
  have hrem : (17/2:ℝ)-6*sqrt 2 = (3-2*sqrt 2)^2/2 := by nlinarith only [hs2]
  have hgap : 0 < log 2+2*sqrt 2-7/2 := by
    have hp : 0 < (3-2*sqrt (2:ℝ))^2/2 := by positivity
    linarith only [hlog,hrem,hp]
  have hs12 : sqrt (12:ℝ) = 2*sqrt 3 := by
    rw [show (12:ℝ) = 2^2*3 by norm_num,sqrt_mul (by positivity),sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hs32 : sqrt (32:ℝ) = 4*sqrt 2 := by
    rw [show (32:ℝ) = 4^2*2 by norm_num,sqrt_mul (by positivity),sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
  have hs8 : sqrt (8:ℝ) = 2*sqrt 2 := by
    rw [show (8:ℝ) = 2^2*2 by norm_num,sqrt_mul (by positivity),sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hD : 0 < 2*sqrt (2:ℝ)-1 := by linarith only [hs1]
  have hid : (2*sqrt 2-1)*((2*sqrt 2-1)/2-octagonDensity) = log 2+2*sqrt 2-7/2 := by
    unfold octagonDensity
    rw [hs32,hs8]
    field_simp
    nlinarith only [hs2]
  have hprod : 0 < (2*sqrt 2-1)*((2*sqrt 2-1)/2-octagonDensity) := by rw [hid]; exact hgap
  have hdensity : octagonDensity < (2*sqrt 2-1)/2 := by
    have hp : 0 < (2*sqrt 2-1)/2-octagonDensity := (mul_pos_iff_of_pos_left hD).mp hprod
    linarith only [hp]
  have hm := mul_lt_mul_of_pos_left hdensity (show 0 < 2*sqrt (3:ℝ) by positivity)
  rw [octagonCost,hs12]
  nlinarith only [hm]


/-- The two-centre exclusion: the exact period cost exceeds the octagon cost. -/
theorem m1_two_centre (P : NormalPeriod) (hc : P.IsCompetitive) {k₀ : ℤ}
    (hpat : P.m1_IsPattern k₀) (hN : P.N = 6) : False := by
  set C := P.costateCycle with hC
  -- normalize the start of the pattern to `k₁ ∈ [0, 3)`
  set k₁ := k₀ % 3 with hk₁
  have hk1a : 0 ≤ k₁ := Int.emod_nonneg _ (by norm_num)
  have hk1b : k₁ < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hpat1 : ∀ j : ℤ, P.rep.IsReverse (k₁ + 3 * j) ∧ P.rep.IsReverse (k₁ + 3 * j + 1) ∧
      P.rep.IsForward (k₁ + 3 * j + 2) := by
    intro j
    have := hpat (j - k₀ / 3)
    have e : k₀ + 3 * (j - k₀ / 3) = k₁ + 3 * j := by rw [hk₁, Int.emod_def]; ring
    rwa [e] at this
  -- the first centre `n₀ = k₁ + 1 ∈ [1, 3]`
  set n₀ : ℕ := (k₁ + 1).toNat with hn₀
  have hn0 : (n₀ : ℤ) = k₁ + 1 := Int.toNat_of_nonneg (by omega)
  have hn1 : 1 ≤ n₀ := by omega
  -- signs: `rev(n₀ + 3j - 1)`, `rev(n₀ + 3j)`, `fwd(n₀ + 3j + 1)`
  have sR : ∀ j x y : ℤ, x = (n₀ : ℤ) + 3 * j → y = x - 1 → C.lab x = C.lab y - 1 := by
    intro j x y hx hy
    have := (hpat1 j).1
    rw [hy, hx, show (n₀ : ℤ) + 3 * j = k₁ + 3 * j + 1 by rw [hn0]; ring,
      show k₁ + 3 * j + 1 - 1 = k₁ + 3 * j by ring]
    exact this
  have sR' : ∀ j x y : ℤ, y = (n₀ : ℤ) + 3 * j → x = y + 1 → C.lab x = C.lab y - 1 := by
    intro j x y hy hx
    have := (hpat1 j).2.1
    rw [hx, hy, show (n₀ : ℤ) + 3 * j = k₁ + 3 * j + 1 by rw [hn0]; ring]
    exact this
  have sF : ∀ j x y : ℤ, y = (n₀ : ℤ) + 3 * j + 1 → x = y + 1 → C.lab x = C.lab y + 1 := by
    intro j x y hy hx
    have := (hpat1 j).2.2
    rw [hx, hy, show (n₀ : ℤ) + 3 * j + 1 = k₁ + 3 * j + 2 by rw [hn0]; ring]
    exact this
  -- the two recurrences
  have rec0 := C.m1_next_centre n₀ hn1 (sR 0 _ _ (by ring) (by ring))
    (sR' 0 _ _ (by ring) (by ring)) (sF 0 _ _ (by ring) (by ring))
    (sR 1 _ _ (by ring) (by ring)) (sR' 1 _ _ (by ring) (by ring))
  have rec1 := C.m1_next_centre (n₀ + 3) (by omega) (sR 1 _ _ (by push_cast; ring) (by ring))
    (sR' 1 _ _ (by push_cast; ring) (by ring)) (sF 1 _ _ (by push_cast; ring) (by ring))
    (sR 2 _ _ (by push_cast; ring) (by ring)) (sR' 2 _ _ (by push_cast; ring) (by ring))
  -- signs
  have g0 : C.sgn ((n₀ : ℤ) - 1) = -1 := C.sgn_rev (sR 0 _ _ (by ring) (by ring))
  have g1 : C.sgn (n₀ : ℤ) = -1 := C.sgn_rev (sR' 0 _ _ (by ring) (by ring))
  have g2 : C.sgn ((n₀ : ℤ) + 1) = 1 := C.sgn_fwd (sF 0 _ _ (by ring) (by ring))
  have g3 : C.sgn ((n₀ : ℤ) + 2) = -1 := C.sgn_rev (sR 1 _ _ (by ring) (by ring))
  have g4 : C.sgn ((n₀ : ℤ) + 3) = -1 := C.sgn_rev (sR' 1 _ _ (by ring) (by ring))
  have g5 : C.sgn ((n₀ : ℤ) + 4) = 1 := C.sgn_fwd (sF 1 _ _ (by ring) (by ring))
  have g6 : C.sgn ((n₀ : ℤ) + 5) = -1 := C.sgn_rev (sR 2 _ _ (by ring) (by ring))
  -- the turns
  have t1 : C.yv (n₀ + 1) = -C.yv n₀ := C.m1_yv_turn n₀ (by push_cast; rw [add_sub_cancel_right, g1, g2])
  have t2 : C.yv (n₀ + 2) = -C.yv (n₀ + 1) := C.m1_yv_turn (n₀ + 1) (by
    push_cast; rw [show (n₀ : ℤ) + 1 + 1 - 1 = (n₀ : ℤ) + 1 by ring, g2,
      show (n₀ : ℤ) + 1 + 1 = (n₀ : ℤ) + 2 by ring, g3]; norm_num)
  have t4 : C.yv (n₀ + 4) = -C.yv (n₀ + 3) := C.m1_yv_turn (n₀ + 3) (by
    push_cast; rw [show (n₀ : ℤ) + 3 + 1 - 1 = (n₀ : ℤ) + 3 by ring, g4,
      show (n₀ : ℤ) + 3 + 1 = (n₀ : ℤ) + 4 by ring, g5])
  have t5 : C.yv (n₀ + 5) = -C.yv (n₀ + 4) := C.m1_yv_turn (n₀ + 4) (by
    push_cast; rw [show (n₀ : ℤ) + 4 + 1 - 1 = (n₀ : ℤ) + 4 by ring, g5,
      show (n₀ : ℤ) + 4 + 1 = (n₀ : ℤ) + 5 by ring, g6]; norm_num)
  have y2 : C.yv (n₀ + 2) = C.yv n₀ := by rw [t2, t1, neg_neg]
  have y5 : C.yv (n₀ + 5) = C.yv (n₀ + 3) := by rw [t5, t4, neg_neg]
  -- the monodromy
  have hp5 : C.yv (n₀ + 5) = C.pre P.N *ᵥ C.yv (n₀ - 1) := by
    rw [← C.yv_add_N]; congr 1; omega
  have hp6 : C.yv (n₀ + 6) = C.pre P.N *ᵥ C.yv n₀ := by
    rw [← C.yv_add_N]; congr 1; omega
  have hact6 : C.act ((n₀ : ℤ) + 6) = C.act n₀ := by
    have := C.act_add n₀; rwa [show ((n₀ : ℤ) + P.N) = (n₀ : ℤ) + 6 by rw [hN]; norm_num] at this
  -- the Wronskian `det(z₀, z₁) = -1/K₁` and the pairings
  have hc0in : C.lab (n₀ : ℤ) = C.lab ((n₀ : ℤ) - 1) - 1 := sR 0 _ _ (by ring) (by ring)
  have hc0out : C.lab ((n₀ : ℤ) + 1) = C.lab n₀ - 1 := sR' 0 _ _ (by ring) (by ring)
  have hc1in : C.lab ((n₀ : ℤ) + 3) = C.lab ((n₀ : ℤ) + 3 - 1) - 1 := sR 1 _ _ (by ring) (by ring)
  have hc1out : C.lab ((n₀ : ℤ) + 3 + 1) = C.lab ((n₀ : ℤ) + 3) - 1 :=
    sR' 1 _ _ (by ring) (by ring)
  obtain ⟨Q1, W1⟩ := C.yv_pair (n₀ + 2)
  obtain ⟨cq1, cw1⟩ := C.cross_mm hc1in hc1out
  rw [show ((n₀ + 2 + 1 : ℕ) : ℤ) = (n₀ : ℤ) + 3 by push_cast; ring, cq1] at Q1
  rw [show ((n₀ + 2 + 1 : ℕ) : ℤ) = (n₀ : ℤ) + 3 by push_cast; ring, cw1] at W1
  rw [y2, show n₀ + 2 + 1 = n₀ + 3 by ring] at Q1 W1
  obtain ⟨Q0, -⟩ := C.yv_pair (n₀ - 1)
  obtain ⟨cq0, -⟩ := C.cross_mm hc0in hc0out
  rw [show ((n₀ - 1 + 1 : ℕ) : ℤ) = (n₀ : ℤ) by push_cast [Nat.sub_add_cancel hn1]; ring, cq0,
    Nat.sub_add_cancel hn1] at Q0
  have hK0 : 0 < C.act n₀ ^ 2 + 4 := by positivity
  have hK1 : 0 < C.act ((n₀ : ℤ) + 3) ^ 2 + 4 := by positivity
  have hW : elDet (C.yv n₀) (C.yv (n₀ + 3)) ≠ 0 := by
    rw [W1]; exact neg_ne_zero.2 (by positivity)
  have hsym := C.Sloc_symm 0
  -- normalize the second recurrence
  rw [show ((n₀ + 3 : ℕ) : ℤ) + 3 = (n₀ : ℤ) + 6 by push_cast; ring, hact6,
    show n₀ + 3 + 3 = n₀ + 6 by ring, show n₀ + 3 - 1 = n₀ + 2 by omega, y2,
    show ((n₀ + 3 : ℕ) : ℤ) = (n₀ : ℤ) + 3 by push_cast; ring,
    show (n₀ : ℤ) + 3 + 2 = (n₀ : ℤ) + 5 by ring, show (n₀ : ℤ) + 3 + 1 = (n₀ : ℤ) + 4 by ring]
    at rec1
  set K0 := C.act (n₀ : ℤ) ^ 2 + 4 with hK0def
  set K1 := C.act ((n₀ : ℤ) + 3) ^ 2 + 4 with hK1def
  set Z0 := C.yv n₀
  set Z1 := C.yv (n₀ + 3)
  set D0 := C.sw (n₀ : ℤ) ^ 2 + C.sw ((n₀ : ℤ) + 2) ^ 2 - C.sw ((n₀ : ℤ) + 1) ^ 2 with hD0
  set D1 := C.sw ((n₀ : ℤ) + 3) ^ 2 + C.sw ((n₀ : ℤ) + 5) ^ 2 - C.sw ((n₀ : ℤ) + 4) ^ 2 with hD1
  -- the monodromy is `-1`, `K₀ = K₁`, `D₀ = D₁ = 0`, `e₀ = -e₁`
  have key : K0 = K1 ∧ D0 = 0 ∧ D1 = 0 ∧ C.cre n₀ = -C.cre ((n₀ : ℤ) + 3) := by
    rcases C.pre_N with hσ | hσ
    · exfalso
      rw [hσ, Matrix.one_mulVec, y5] at hp5
      rw [← hp5] at rec0
      have := congrArg (elDet Z0) rec0
      simp only [elDet_smul_right, elDet_add_right, elDet_self, mul_zero, add_zero] at this
      have : (K1 + K0) * elDet Z0 Z1 = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact hW h
    · rw [hσ, Matrix.neg_mulVec, Matrix.one_mulVec, y5] at hp5
      rw [hσ, Matrix.neg_mulVec, Matrix.one_mulVec] at hp6
      have hm1 : C.yv (n₀ - 1) = -Z1 := by rw [hp5, neg_neg]
      rw [hm1] at rec0 Q0
      rw [hp6] at rec1
      have d0 := congrArg (elDet Z0) rec0
      simp only [elDet_smul_right, elDet_add_right, elDet_self, elDet_neg_right, mul_zero,
        add_zero] at d0
      have hK : K0 = K1 := by
        have : (K1 - K0) * elDet Z0 Z1 = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact absurd h hW
      have d1 := congrArg (fun v ↦ elDet v Z1) rec0
      simp only [elDet_smul_left, elDet_add_left, elDet_self, mul_zero] at d1
      have dl : ∀ c : ℝ, ∀ v w : Fin 2 → ℝ, elDet (c • v) w = c * elDet v w :=
        fun c v w ↦ elDet_smul_left c v w
      have hD0z : D0 = 0 := by
        have e1 : elDet (-Z1) Z1 = 0 := by simp only [elDet, Pi.neg_apply]; ring
        rw [e1, mul_zero, zero_add] at d1
        rcases mul_eq_zero.1 d1.symm with h | h
        · exact h
        · exact absurd h hW
      have d2 := congrArg (elDet Z0) rec1
      simp only [elDet_smul_right, elDet_add_right, elDet_self, elDet_neg_right, mul_zero,
        neg_zero, zero_add] at d2
      have hD1z : D1 = 0 := by
        rcases mul_eq_zero.1 d2.symm with h | h
        · exact h
        · exact absurd h hW
      refine ⟨hK, hD0z, hD1z, ?_⟩
      rw [← Q0, ← Q1, elQ_neg_left, elQ_comm hsym]
  obtain ⟨hK, hD0z, hD1z, he⟩ := key
  -- the Euler identity over the window `n₀, …, n₀ + 5`
  have hr : Finset.range P.N = Finset.range 6 := by rw [hN]
  have cre_add : ∀ k, C.cre (k + P.N) = C.cre k := fun k ↦ by
    simp only [CostateCycle.cre, CostateCycle.wt, C.mu_add, C.lab_add, add_sub_cancel_right,
      C.act_add]
  have heul := C.euler_sum
  have hf := m1_sum_window (N := P.N)
    (fun k ↦ (C.sgn (k - 1) + C.sgn k) * C.cre k) (fun k ↦ by
      simp only [show k + P.N - 1 = k - 1 + P.N by ring, C.sgn_add, cre_add]) n₀
  have hg := m1_sum_window (N := P.N)
    (fun k ↦ (C.sgn (k - 1) + C.sgn k) / (C.act k ^ 2 + 4)) (fun k ↦ by
      simp only [show k + P.N - 1 = k - 1 + P.N by ring, C.sgn_add, C.act_add]) n₀
  have h6f := m1_sum_six (fun k ↦ (C.sgn (k - 1) + C.sgn k) * C.cre k) n₀
  have h6g := m1_sum_six (fun k ↦ (C.sgn (k - 1) + C.sgn k) / (C.act k ^ 2 + 4)) n₀
  rw [← hf, ← hg, hr, h6f, h6g] at heul
  simp only [add_sub_cancel_right, show (n₀ : ℤ) + 2 - 1 = (n₀ : ℤ) + 1 by ring,
    show (n₀ : ℤ) + 3 - 1 = (n₀ : ℤ) + 2 by ring, show (n₀ : ℤ) + 4 - 1 = (n₀ : ℤ) + 3 by ring,
    show (n₀ : ℤ) + 5 - 1 = (n₀ : ℤ) + 4 by ring, g0, g1, g2, g3, g4, g5, g6] at heul
  have hraw : C.rawCost = 32 / K0 := by
    have hK' : C.act ((n₀ : ℤ) + 3) ^ 2 + 4 = K0 := by rw [hK]
    have hK'' : C.act (n₀ : ℤ) ^ 2 + 4 = K0 := rfl
    rw [he, hK', hK''] at heul
    have : C.rawCost / 4 = 8 / K0 := by linear_combination -heul
    have hK0' : K0 ≠ 0 := hK0.ne'
    field_simp at this ⊢
    linarith
  have hcost : P.cost = 8 * √3 / K0 := by
    rw [P.cost_eq_rawCost, show P.termCycle.rawCost = C.rawCost from rfl, hraw]; ring
  -- the margins `a, b₀, c₀, b₁, c₁`
  set a := C.act (n₀ : ℤ) with ha_def
  have ha := C.act_pos (n₀ : ℤ)
  have ha3 : C.act ((n₀ : ℤ) + 3) = a := by
    have h3 := C.act_pos ((n₀ : ℤ) + 3)
    have : C.act ((n₀ : ℤ) + 3) ^ 2 = a ^ 2 := by
      have := hK; simp only [hK0def, hK1def] at this; linarith
    exact (pow_left_inj₀ h3.le ha.le two_ne_zero).1 this
  have ham1 : C.act ((n₀ : ℤ) - 1) = C.act ((n₀ : ℤ) + 5) := by
    have := C.act_add ((n₀ : ℤ) - 1)
    rw [show (n₀ : ℤ) - 1 + P.N = (n₀ : ℤ) + 5 by rw [hN]; push_cast; ring] at this
    exact this.symm
  set b₀ := C.act ((n₀ : ℤ) + 1)
  set c₀ := C.act ((n₀ : ℤ) + 2)
  set b₁ := C.act ((n₀ : ℤ) + 4)
  set c₁ := C.act ((n₀ : ℤ) + 5)
  -- `D₀ = D₁ = 0`
  have hD0' : (b₀ - a) * (c₀ - a) = 2 * a ^ 2 := by
    have := hD0z
    simp only [hD0, CostateCycle.sw, show (n₀ : ℤ) + 2 + 1 = (n₀ : ℤ) + 3 by ring,
      show (n₀ : ℤ) + 1 + 1 = (n₀ : ℤ) + 2 by ring, ha3] at this
    linear_combination (-1 / 2 : ℝ) * this
  have hD1' : (b₁ - a) * (c₁ - a) = 2 * a ^ 2 := by
    have := hD1z
    simp only [hD1, CostateCycle.sw, show (n₀ : ℤ) + 3 + 1 = (n₀ : ℤ) + 4 by ring,
      show (n₀ : ℤ) + 5 + 1 = (n₀ : ℤ) + 6 by ring, show (n₀ : ℤ) + 4 + 1 = (n₀ : ℤ) + 5 by ring,
      ha3, hact6] at this
    linear_combination (-1 / 2 : ℝ) * this
  -- the strict centre minima
  have hmix : P.rep.IsMixed := ⟨⟨_, (hpat1 0).2.2⟩, ⟨_, (hpat1 0).1⟩⟩
  have hrev : ∀ x : ℤ, ∀ j : ℤ, x = k₁ + 3 * j → P.rep.IsReverse x := fun x j h ↦ by
    rw [h]; exact (hpat1 j).1
  have hrev' : ∀ x : ℤ, ∀ j : ℤ, x = k₁ + 3 * j + 1 → P.rep.IsReverse x := fun x j h ↦ by
    rw [h]; exact (hpat1 j).2.1
  obtain ⟨m1, m2⟩ := P.centre_min hmix (k := (n₀ : ℤ)) (hrev _ 0 (by rw [hn0]; ring))
    (hrev' _ 0 (by rw [hn0]; ring))
  obtain ⟨m3, m4⟩ := P.centre_min hmix (k := (n₀ : ℤ) + 3) (hrev _ 1 (by rw [hn0]; ring))
    (hrev' _ 1 (by rw [hn0]; ring))
  rw [ham1] at m1
  rw [ha3, show (n₀ : ℤ) + 3 - 1 = (n₀ : ℤ) + 2 by ring] at m3
  rw [ha3, show (n₀ : ℤ) + 3 + 1 = (n₀ : ℤ) + 4 by ring] at m4
  -- the centre factors
  have f0 := C.centre_factor hc0in hc0out
  have f1 := C.centre_factor hc1in hc1out
  rw [ham1] at f0
  rw [ha3, show (n₀ : ℤ) + 3 - 1 = (n₀ : ℤ) + 2 by ring,
    show (n₀ : ℤ) + 3 + 1 = (n₀ : ℤ) + 4 by ring] at f1
  have hq0 := C.one_lt_q (n₀ : ℤ)
  have hq1 := C.one_lt_q ((n₀ : ℤ) + 3)
  have hK1a : K1 = a ^ 2 + 4 := by simp only [hK1def, ha3]
  have l0 : (a + c₁) * (a + b₀) < K0 := by
    have f0' : C.q (n₀ : ℤ) * ((a + c₁) * (a + b₀)) = K0 := f0
    have hp : 0 < (a + c₁) * (a + b₀) := mul_pos (by linarith) (by linarith)
    have : (a + c₁) * (a + b₀) < C.q (n₀ : ℤ) * ((a + c₁) * (a + b₀)) := by
      exact lt_mul_of_one_lt_left hp hq0
    linarith
  have l1 : (a + c₀) * (a + b₁) < K0 := by
    have hp : 0 < (a + c₀) * (a + b₁) := mul_pos (by linarith) (by linarith)
    have : (a + c₀) * (a + b₁) < C.q ((n₀ : ℤ) + 3) * ((a + c₀) * (a + b₁)) := by
      exact lt_mul_of_one_lt_left hp hq1
    have f1' : C.q ((n₀ : ℤ) + 3) * ((a + c₀) * (a + b₁)) = a ^ 2 + 4 := f1
    have hK0a : K0 = a ^ 2 + 4 := rfl
    linarith
  obtain ⟨-,hproductCost⟩ := m1_two_centre_bounds ha rfl m1 m2 m3 m4 hD0' hD1' l0 l1
  have hcostGap : octagonCost < P.cost := by
    rw [hcost]
    exact m1_octagonCost_lt_two_centre.trans hproductCost
  exact (not_lt_of_ge (show P.cost ≤ octagonCost from hc)) hcostGap

end SmoothedOctagon
