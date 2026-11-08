module

public import SmoothedOctagon.Exclusion.Forward.Core

/-!
# Case M2, small forward minimum: the scalar core without the cost and the cap

`fs_U_lt_three` (`Exclusion/Forward/Scalars/SmallMin.lean`) proves `U < 3` for a case-F window
`ff_Dim`, but uses only its rows `rowL`, `rowR`, its floors and its order conditions, not the
seven-entry cost bound or the Casimir cap (which a case-M2 window does not supply). This module
restates it on the window data of a case-M2 small forward minimum.

## Main API

* `sf_Dim`: the dimensionless window `(U, z, w, P, D, u, v)` with the order conditions, the left
  and right rows and the two exterior floors; `sf_Dim.swap`.
* `sf_Dim.U_lt_three`: `U < 3` (the proof of `fs_U_lt_three`, verbatim).
* `sf_Win`: the physical window `(p, b, a, c, d, u, v)` with `a ≤ p, b, c, d`, the strict stars,
  the three factors `> 1`, the rows and the floors; `sf_Win.toDim`.
* `sf_Win.a_sq_gt`: `4/3 < a²`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- **The dimensionless small-minimum window**: the fields of `ff_Dim` that the small forward
minimum (`fs_U_lt_three`) uses. -/
structure sf_Dim where
  U : ℝ
  z : ℝ
  w : ℝ
  P : ℝ
  D : ℝ
  u : ℝ
  v : ℝ
  one_le_z : 1 ≤ z
  one_le_w : 1 ≤ w
  one_le_P : 1 ≤ P
  one_le_D : 1 ≤ D
  Pz_lt : P * z < U
  z_lt : z < U
  w_lt : w < U
  wD_lt : w * D < U
  one_lt_h : 1 < ff_hd U z P
  one_lt_q : 1 < ff_q U z w
  one_lt_k : 1 < ff_hd U w D
  rowL : ff_n U z (ff_hd U z P) * u + ff_m U z w (ff_hd U z P) * v =
    ff_alpha U z (ff_hd U z P) * ff_A U z w - ff_B U z (ff_hd U z P)
  rowR : ff_m U w z (ff_hd U w D) * u + ff_n U w (ff_hd U w D) * v =
    ff_alpha U w (ff_hd U w D) * ff_A U z w - ff_B U w (ff_hd U w D)
  floorL : ff_F (z / (1 + z)) (ff_hd U z P) ≤ u
  floorR : ff_F (w / (1 + w)) (ff_hd U w D) ≤ v

namespace sf_Dim

variable (W : sf_Dim)

/-- The reflection `(z, P, u) ↔ (w, D, v)` of the window. -/
def swap : sf_Dim where
  U := W.U
  z := W.w
  w := W.z
  P := W.D
  D := W.P
  u := W.v
  v := W.u
  one_le_z := W.one_le_w
  one_le_w := W.one_le_z
  one_le_P := W.one_le_D
  one_le_D := W.one_le_P
  Pz_lt := by rw [mul_comm]; exact W.wD_lt
  z_lt := W.w_lt
  w_lt := W.z_lt
  wD_lt := by rw [mul_comm]; exact W.Pz_lt
  one_lt_h := W.one_lt_k
  one_lt_q := by rw [ff_Dim.ff_q_comm]; exact W.one_lt_q
  one_lt_k := W.one_lt_h
  rowL := by rw [ff_Dim.ff_A_comm]; linear_combination W.rowR
  rowR := by rw [ff_Dim.ff_A_comm]; linear_combination W.rowL
  floorL := W.floorR
  floorR := W.floorL

/-- The small forward minimum with `z ≤ w` (the proof of `fs_U_lt_three_le`). -/
theorem U_lt_three_le (hzw : W.z ≤ W.w) : W.U < 3 := by
  by_contra hU3
  push Not at hU3
  have hz := W.one_le_z
  have hw := W.one_le_w
  have hzU := W.z_lt
  have hwU := W.w_lt
  have hU0 : 0 < W.U := by linarith
  have hz0 : 0 < W.z := by linarith
  have hS : 0 < 1 + W.z := by linarith
  have hT : 0 < 1 + W.w := by linarith
  have hK : 0 < 1 + W.U := by linarith
  have hZ : 0 < W.z ^ 2 + W.U := by positivity
  have hWW : 0 < W.w ^ 2 + W.U := by positivity
  set h := ff_hd W.U W.z W.P with hhdef
  set k := ff_hd W.U W.w W.D with hkdef
  have hh1 : 1 < h := W.one_lt_h
  have hk1 : 1 < k := W.one_lt_k
  have hhl : (1 + W.z) ^ 2 / (W.z ^ 2 + W.U) ≤ h := by
    rw [hhdef]; unfold ff_hd
    apply div_le_div_of_nonneg_right _ hZ.le
    nlinarith [W.one_le_P]
  have hhu : h ≤ (1 + W.z) / W.z := by
    rw [hhdef]; unfold ff_hd
    rw [div_le_div_iff₀ hZ hz0]
    nlinarith [W.Pz_lt]
  have hkl : (1 + W.w) ^ 2 / (W.w ^ 2 + W.U) ≤ k := by
    rw [hkdef]; unfold ff_hd
    apply div_le_div_of_nonneg_right _ hWW.le
    nlinarith [W.one_le_D]
  have hq : 1 < ff_q W.U W.z W.w := W.one_lt_q
  have hn : 0 ≤ ff_n W.U W.z h := by
    unfold ff_n
    apply div_nonneg _ hZ.le
    apply mul_nonneg (mul_nonneg (by positivity) (by linarith)); linarith
  have hm : 0 ≤ ff_m W.U W.z W.w h := by
    unfold ff_m
    apply mul_nonneg (by positivity)
    have : 0 ≤ ff_q W.U W.z W.w * (1 + W.z) - 1 := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1) this]
  have hy : 1 / 2 ≤ W.w / (1 + W.w) := by rw [le_div_iff₀ hT]; linarith
  have hx : 1 / 2 ≤ W.z / (1 + W.z) := by rw [le_div_iff₀ hS]; linarith
  have hxy : W.z / (1 + W.z) ≤ W.w / (1 + W.w) := by
    rw [div_le_div_iff₀ hS hT]; nlinarith
  have hv := W.floorR
  -- the residual is nonnegative for every admissible opposite floor `V ≤ v`
  have hres : ∀ V, V ≤ W.v → 0 ≤ fs_res W.U W.z W.w h V := by
    intro V hV
    have hrow := W.rowL
    have hu := W.floorL
    unfold fs_res
    have := mul_le_mul_of_nonneg_left hu hn
    have := mul_le_mul_of_nonneg_left hV hm
    linarith
  have hBw : 1 - W.w / (1 + W.w) + (W.w / (1 + W.w)) ^ 2 ≤ W.v :=
    le_trans (fs_F_ge hy hk1) hv
  have hII : (1 + W.z) ^ 2 / (W.z ^ 2 + W.U) ≤ (1 + W.w) ^ 2 / (W.w ^ 2 + W.U) := by
    rw [div_le_div_iff₀ hZ hWW]
    have : (1 + W.w) ^ 2 * (W.z ^ 2 + W.U) - (1 + W.z) ^ 2 * (W.w ^ 2 + W.U) =
        (W.w - W.z) * (W.U * (W.w + W.z + 2) - 2 * W.w * W.z - W.w - W.z) := by ring
    have h2 : 0 ≤ W.U * (W.w + W.z + 2) - 2 * W.w * W.z - W.w - W.z := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hzw) h2]
  rcases lt_or_ge ((1 + W.z) ^ 2) (1 + W.U) with hSK | hSK
  · -- the zero-central-factor face
    set w' := (1 + W.U) / (1 + W.z) - 1 with hw'
    have hw'z : W.z ≤ w' := by
      rw [hw', le_sub_iff_add_le, le_div_iff₀ hS]; nlinarith
    have hw'w : w' ≤ W.w := by
      rw [hw', sub_le_iff_le_add, div_le_iff₀ hS]
      have := hq; unfold ff_q at this; rw [lt_div_iff₀ hK] at this; nlinarith
    have hq' : 1 ≤ ff_q W.U W.z w' := by
      rw [hw']; unfold ff_q; rw [le_div_iff₀ hK]; field_simp; linarith
    have hT' : 0 < 1 + w' := by linarith
    have hy' : 1 / 2 ≤ w' / (1 + w') := by rw [le_div_iff₀ hT']; linarith
    have hyy : w' / (1 + w') ≤ W.w / (1 + W.w) := by
      rw [div_le_div_iff₀ hT' hT]; nlinarith
    have h0 := hres _ hBw
    have hle := fs_res_le (V' := 1 - w' / (1 + w') + (w' / (1 + w')) ^ 2) hU0 hz0
      (by linarith) hw'w hq' hh1.le le_rfl (fs_B_mono hy' hyy)
    have hneg := fs_face_q1 hzU hz hSK.le hh1
    linarith
  · rcases le_or_gt (2 * W.z + 1) W.U with hlow | hhard
    · -- the low face
      have hqz : 1 ≤ ff_q W.U W.z W.z := by unfold ff_q; rw [le_div_iff₀ hK]; linarith only [hSK]
      have h0 := hres _ hBw
      have hle := fs_res_le (V' := 1 - W.z / (1 + W.z) + (W.z / (1 + W.z)) ^ 2) hU0 hz0 hz hzw hqz
        hh1.le le_rfl (fs_B_mono hx hxy)
      have hneg := fs_face_low hzU hz hSK hlow hh1
      linarith
    · -- the hard face
      have hqz : 1 ≤ ff_q W.U W.z W.z := by unfold ff_q; rw [le_div_iff₀ hK]; linarith only [hSK]
      have hIz : 1 < (1 + W.z) ^ 2 / (W.z ^ 2 + W.U) := by rw [lt_div_iff₀ hZ]; linarith only [hhard]
      have hIw : 1 < (1 + W.w) ^ 2 / (W.w ^ 2 + W.U) := lt_of_lt_of_le hIz hII
      have hV : ff_F (W.w / (1 + W.w)) ((1 + W.w) ^ 2 / (W.w ^ 2 + W.U)) ≤ W.v :=
        le_trans (fs_F_mono_r hy hIw hkl) hv
      have h0 := hres _ hV
      have hVV : ff_F (W.z / (1 + W.z)) ((1 + W.z) ^ 2 / (W.z ^ 2 + W.U)) ≤
          ff_F (W.w / (1 + W.w)) ((1 + W.w) ^ 2 / (W.w ^ 2 + W.U)) :=
        le_trans (fs_F_mono_r hx hIz hII) (fs_F_mono_x hx hxy hIw)
      have hle := fs_res_le hU0 hz0 hz hzw hqz hh1.le (fs_F_ge hy hIw) hVV
      have hneg := fs_face_hard hU3 hhard hzU hz hSK hhl hhu hh1
      linarith

/-- **The small forward minimum**: `U < 3`. -/
theorem U_lt_three : W.U < 3 := by
  rcases le_total W.z W.w with h | h
  · exact W.U_lt_three_le h
  · exact W.swap.U_lt_three_le h

end sf_Dim

/-- **The physical small-minimum window**: five consecutive active margins
`(p, b, a, c, d)` with `a` their minimum, the strict stars of the four switches, the three factors
`h, q, k > 1`, the left and right rows in the norms `u = 8 d_{-1}`, `v = 8 d_0`, and
the exterior floors. -/
structure sf_Win where
  a : ℝ
  p : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  u : ℝ
  v : ℝ
  a_pos : 0 < a
  a_le_p : a ≤ p
  a_le_b : a ≤ b
  a_le_c : a ≤ c
  a_le_d : a ≤ d
  pb_lt : p * b < 4
  ab_lt : a * b < 4
  ac_lt : a * c < 4
  cd_lt : c * d < 4
  one_lt_h : 1 < ff_fac p b a
  one_lt_q : 1 < ff_fac b a c
  one_lt_k : 1 < ff_fac a c d
  rowL : ff_Mn a b (ff_fac p b a) * u + ff_Mm a b (ff_fac b a c) (ff_fac p b a) * v =
    ff_Mal a b (ff_fac p b a) * ff_Cph b a c - ff_Cph p b a
  rowR : ff_Mm a c (ff_fac b a c) (ff_fac a c d) * u + ff_Mn a c (ff_fac a c d) * v =
    ff_Mal a c (ff_fac a c d) * ff_Cph b a c - ff_Cph a c d
  floorL : ff_F (b / (a + b)) (ff_fac p b a) ≤ u
  floorR : ff_F (c / (a + c)) (ff_fac a c d) ≤ v

namespace sf_Win

variable (W : sf_Win)

theorem b_pos : 0 < W.b := lt_of_lt_of_le W.a_pos W.a_le_b
theorem c_pos : 0 < W.c := lt_of_lt_of_le W.a_pos W.a_le_c
theorem p_pos : 0 < W.p := lt_of_lt_of_le W.a_pos W.a_le_p
theorem d_pos : 0 < W.d := lt_of_lt_of_le W.a_pos W.a_le_d

/-- The dimensionless form of the window: `U = 4/a²`, `z = b/a`, `w = c/a`, `P = p/a`, `D = d/a`
(the construction of `ff_Win.toDim`). -/
noncomputable def toDim : sf_Dim where
  U := 4 / W.a ^ 2
  z := W.b / W.a
  w := W.c / W.a
  P := W.p / W.a
  D := W.d / W.a
  u := W.u
  v := W.v
  one_le_z := (one_le_div W.a_pos).2 W.a_le_b
  one_le_w := (one_le_div W.a_pos).2 W.a_le_c
  one_le_P := (one_le_div W.a_pos).2 W.a_le_p
  one_le_D := (one_le_div W.a_pos).2 W.a_le_d
  Pz_lt := by
    have := W.a_pos
    rw [div_mul_div_comm, ← sq]; exact div_lt_div_of_pos_right W.pb_lt (by positivity)
  z_lt := by
    have := W.a_pos; have := W.ab_lt
    rw [div_lt_div_iff₀ W.a_pos (by positivity)]; nlinarith
  w_lt := by
    have := W.a_pos; have := W.ac_lt
    rw [div_lt_div_iff₀ W.a_pos (by positivity)]; nlinarith
  wD_lt := by
    have := W.a_pos
    rw [div_mul_div_comm, ← sq]; exact div_lt_div_of_pos_right W.cd_lt (by positivity)
  one_lt_h := by rw [ff_hd_eq W.a_pos]; exact W.one_lt_h
  one_lt_q := by rw [ff_q_eq_fac W.a_pos]; exact W.one_lt_q
  one_lt_k := by rw [ff_hd_eq W.a_pos, ff_fac_comm]; exact W.one_lt_k
  rowL := by
    have h := W.rowL
    rw [ff_hd_eq W.a_pos, ff_alpha_phys W.a_pos W.b_pos]
    rw [← ff_n_phys W.a_pos W.b_pos, ← ff_m_phys W.a_pos W.b_pos,
      ← ff_A_phys W.a_pos W.b_pos W.c_pos, ← ff_B_phys W.a_pos W.p_pos W.b_pos] at h
    refine mul_left_cancel₀ W.a_pos.ne' ?_
    linear_combination h
  rowR := by
    have h := W.rowR
    rw [ff_hd_eq W.a_pos, ff_alpha_phys W.a_pos W.c_pos]
    rw [ff_Cph_comm W.a W.c W.d, ff_fac_comm W.a W.c W.d, ff_fac_comm W.b W.a W.c,
      ← ff_n_phys W.a_pos W.c_pos, ← ff_m_phys W.a_pos W.c_pos,
      ← ff_A_phys W.a_pos W.b_pos W.c_pos, ← ff_B_phys W.a_pos W.d_pos W.c_pos] at h
    refine mul_left_cancel₀ W.a_pos.ne' ?_
    linear_combination h
  floorL := by
    have h := W.floorL
    rw [ff_hd_eq W.a_pos]
    have e : W.b / W.a / (1 + W.b / W.a) = W.b / (W.a + W.b) := by
      have := W.a_pos; have := W.b_pos; field_simp
    rw [e]; exact h
  floorR := by
    have h := W.floorR
    rw [ff_hd_eq W.a_pos, ff_fac_comm]
    have e : W.c / W.a / (1 + W.c / W.a) = W.c / (W.a + W.c) := by
      have := W.a_pos; have := W.c_pos; field_simp
    rw [e]; exact h

/-- **The small forward minimum, physical form**: `a² > 4/3`. -/
theorem a_sq_gt : 4 / 3 < W.a ^ 2 := by
  have h := W.toDim.U_lt_three
  have ha : 0 < W.a ^ 2 := by have := W.a_pos; positivity
  change 4 / W.a ^ 2 < 3 at h
  rw [div_lt_iff₀ ha] at h
  linarith

end sf_Win

end SmoothedOctagon
