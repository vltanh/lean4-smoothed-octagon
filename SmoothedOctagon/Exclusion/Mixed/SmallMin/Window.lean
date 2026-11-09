module

public import SmoothedOctagon.Exclusion.Forward.Interface
public import SmoothedOctagon.Exclusion.Mixed.Frames
public import SmoothedOctagon.Exclusion.Mixed.SmallMin.Scalar

/-!
# Case M2, small forward minimum: the window of five pieces with four forward switches

The case-F wiring (`CostateCycle.ff_rows`, `ff_floors`, `Exclusion/Forward/Interface`) assumes every
switch forward, but uses it only at the four switches `m - 2, m - 1, m, m + 1` between the pieces
`m - 2, …, m + 2`. This module restates it under these four local hypotheses and builds the
small-minimum window `sf_Win` of a costate cycle at such a run.

## Main API

* `CostateCycle.sf_rows`: the left and right rows at the piece `m`
  (from `wire_stat_w` at `m - 1, m, m + 1`, `wire_w_rel` at `m, m + 1`, `factor_pp`).
* `CostateCycle.sf_floors`: the exterior floors (`wire_floor_out` at `m - 1`,
  `wire_floor_in` at `m + 1`).
* `CostateCycle.sf_window`: the window `sf_Win` at `m` when `a_m` is the minimum of the five
  margins; `CostateCycle.sf_act_sq_gt`: then `a_m² > 4/3`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

/-- The four switches of a run of four forward switches, in the forms the wiring consumes. -/
private theorem sf_labs {m : ℤ} (hf2 : C.m2Fwd (m - 2)) (hf1 : C.m2Fwd (m - 1)) (hf0 : C.m2Fwd m) :
    C.lab (m - 1) = C.lab (m - 1 - 1) + 1 ∧ C.lab m = C.lab (m - 1) + 1 ∧
      C.lab (m + 1) = C.lab (m + 1 - 1) + 1 := by
  unfold m2Fwd at hf2 hf1 hf0
  refine ⟨?_, ?_, ?_⟩
  · rw [show m - 1 - 1 = m - 2 by ring, show m - 1 = m - 2 + 1 by ring]; exact hf2
  · rw [sub_add_cancel] at hf1; exact hf1
  · rw [add_sub_cancel_right]; exact hf0

/-- **The left and right rows at a run of four forward switches**: the case-F rows
`ff_rows` with the all-forward hypothesis replaced by the four switches `m - 2, …, m + 1`. -/
theorem sf_rows {m : ℤ} (hf2 : C.m2Fwd (m - 2)) (hf1 : C.m2Fwd (m - 1)) (hf0 : C.m2Fwd m)
    (hf3 : C.m2Fwd (m + 1)) :
    let p := C.act (m - 2); let b := C.act (m - 1); let a := C.act m; let c := C.act (m + 1)
    let d := C.act (m + 2)
    ff_Mn a b (ff_fac p b a) * C.ff_u m + ff_Mm a b (ff_fac b a c) (ff_fac p b a) * C.ff_v m =
        ff_Mal a b (ff_fac p b a) * ff_Cph b a c - ff_Cph p b a ∧
      ff_Mm a c (ff_fac b a c) (ff_fac a c d) * C.ff_u m + ff_Mn a c (ff_fac a c d) * C.ff_v m =
        ff_Mal a c (ff_fac a c d) * ff_Cph b a c - ff_Cph a c d := by
  intro p b a c d
  obtain ⟨i1, i0, i3⟩ := C.sf_labs hf2 hf1 hf0
  have hF1 : C.lab (m - 1 + 1) = C.lab (m - 1) + 1 := hf1
  have hF0 : C.lab (m + 1) = C.lab m + 1 := hf0
  have hF3 : C.lab (m + 1 + 1) = C.lab (m + 1) + 1 := hf3
  have sg : ∀ k, C.lab k = C.lab (k - 1) + 1 → C.lab (k + 1) = C.lab k + 1 →
      C.sgn (k - 1) = C.sgn k := fun k h1 h2 ↦ by
    rw [C.sgn_fwd (by rw [sub_add_cancel]; exact h1), C.sgn_fwd h2]
  have sL := C.wire_stat_w (sg _ i1 hF1)
  have s0 := C.wire_stat_w (sg _ i0 hF0)
  have sR := C.wire_stat_w (sg _ i3 hF3)
  rw [show m - 1 - 1 = m - 2 by ring, sub_add_cancel] at sL
  rw [add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring] at sR
  have rL := C.wire_w_rel (k := m) (by rw [show m - 2 = m - 1 - 1 by ring]; exact i1) i0 hF0
  have rR := C.wire_w_rel (k := m + 1) (by
      rw [show m + 1 - 2 = m - 1 by ring, add_sub_cancel_right]; exact i0) i3 hF3
  rw [show m + 1 - 2 = m - 1 by ring, add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring] at rR
  have fL := C.factor_pp i1 hF1
  have f0 := C.factor_pp i0 hF0
  have fR := C.factor_pp i3 hF3
  simp only [CostateCycle.sw, show m - 1 - 1 = m - 2 by ring, sub_add_cancel,
    add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring, show m - 2 + 1 = m - 1 by ring] at fL f0 fR
  have ew : ∀ k, C.ff_wt k = C.wt k := fun _ ↦ rfl
  simp only [ff_u, ff_v, ew]
  exact (wire_rows_alg (C.act_pos _) (C.act_pos _) (C.act_pos _) (C.act_pos _) (C.act_pos _) fL f0
    fR rL rR sL s0 sR).2

/-- **The two exterior floors at a run of four forward switches**: `ff_floors` with the
all-forward hypothesis replaced by the four switches `m - 2, …, m + 1`. -/
theorem sf_floors {m : ℤ} (hf2 : C.m2Fwd (m - 2)) (hf1 : C.m2Fwd (m - 1)) (hf0 : C.m2Fwd m)
    (hf3 : C.m2Fwd (m + 1)) :
    let p := C.act (m - 2); let b := C.act (m - 1); let a := C.act m; let c := C.act (m + 1)
    let d := C.act (m + 2)
    ff_F (b / (a + b)) (ff_fac p b a) ≤ C.ff_u m ∧ ff_F (c / (a + c)) (ff_fac a c d) ≤ C.ff_v m := by
  intro p b a c d
  obtain ⟨i1, -, i3⟩ := C.sf_labs hf2 hf1 hf0
  have hF1 : C.lab (m - 1 + 1) = C.lab (m - 1) + 1 := hf1
  have hF3 : C.lab (m + 1 + 1) = C.lab (m + 1) + 1 := hf3
  have fo := C.wire_floor_out i1 hF1
  have fi := C.wire_floor_in i3 hF3
  rw [sub_add_cancel] at fo
  rw [add_sub_cancel_right] at fi
  have fL := C.factor_pp i1 hF1
  have fR := C.factor_pp i3 hF3
  simp only [CostateCycle.sw, show m - 1 - 1 = m - 2 by ring, sub_add_cancel,
    add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring, show m - 2 + 1 = m - 1 by ring] at fL fR
  have hK1 : 0 < C.act (m - 1) ^ 2 + 4 := by positivity
  have hK2 : 0 < C.act (m + 1) ^ 2 + 4 := by positivity
  have hq1 : C.q (m - 1) = ff_fac p b a := by
    simp only [ff_fac, p, b, a]; field_simp; linarith
  have hq2 : C.q (m + 1) = ff_fac a c d := by
    simp only [ff_fac, a, c, d]; field_simp; linarith
  have h1 := C.act_pos (m - 1)
  have h2 := C.act_pos m
  have h3 := C.act_pos (m + 1)
  have ew : ∀ k, C.ff_wt k = C.wt k := fun _ ↦ rfl
  have eu : C.ff_u m = 8 * C.swd (m - 1) := by
    simp only [ff_u, ew, CostateCycle.swd, sub_add_cancel]; field_simp; ring
  have ev : C.ff_v m = 8 * C.swd m := by
    simp only [ff_v, ew, CostateCycle.swd]; field_simp; ring
  rw [eu, ev, ← hq1, ← hq2]
  refine ⟨?_, ?_⟩
  · rw [show a + b = b + a by ring]; exact fo
  · exact fi

/-- The factors of the three interior pieces of a run of four forward switches. -/
private theorem sf_factors {m : ℤ} (hf2 : C.m2Fwd (m - 2)) (hf1 : C.m2Fwd (m - 1))
    (hf0 : C.m2Fwd m) (hf3 : C.m2Fwd (m + 1)) :
    C.q (m - 1) = ff_fac (C.act (m - 2)) (C.act (m - 1)) (C.act m) ∧
      C.q m = ff_fac (C.act (m - 1)) (C.act m) (C.act (m + 1)) ∧
      C.q (m + 1) = ff_fac (C.act m) (C.act (m + 1)) (C.act (m + 2)) := by
  obtain ⟨i1, i0, i3⟩ := C.sf_labs hf2 hf1 hf0
  have hF1 : C.lab (m - 1 + 1) = C.lab (m - 1) + 1 := hf1
  have hF0 : C.lab (m + 1) = C.lab m + 1 := hf0
  have hF3 : C.lab (m + 1 + 1) = C.lab (m + 1) + 1 := hf3
  have fL := C.factor_pp i1 hF1
  have f0 := C.factor_pp i0 hF0
  have fR := C.factor_pp i3 hF3
  simp only [CostateCycle.sw, show m - 1 - 1 = m - 2 by ring, sub_add_cancel,
    add_sub_cancel_right, show m + 1 + 1 = m + 2 by ring, show m - 2 + 1 = m - 1 by ring] at fL f0 fR
  have hK1 : 0 < C.act (m - 1) ^ 2 + 4 := by positivity
  have hK0 : 0 < C.act m ^ 2 + 4 := by positivity
  have hK2 : 0 < C.act (m + 1) ^ 2 + 4 := by positivity
  refine ⟨?_, ?_, ?_⟩ <;> simp only [ff_fac] <;> field_simp <;> linarith

/-- **The small-minimum window of a costate cycle** at a run of four forward switches
`m - 2, …, m + 1` whose central margin `a_m` is the minimum of the five margins `a_{m-2}, …,
a_{m+2}`, with `u = 8 d_{m-1}`, `v = 8 d_m`. -/
noncomputable def sf_window {m : ℤ} (hf2 : C.m2Fwd (m - 2)) (hf1 : C.m2Fwd (m - 1))
    (hf0 : C.m2Fwd m) (hf3 : C.m2Fwd (m + 1))
    (hmin : ∀ j, m - 2 ≤ j → j ≤ m + 2 → C.act m ≤ C.act j) : sf_Win where
  a := C.act m
  p := C.act (m - 2)
  b := C.act (m - 1)
  c := C.act (m + 1)
  d := C.act (m + 2)
  u := C.ff_u m
  v := C.ff_v m
  a_pos := C.act_pos m
  a_le_p := hmin _ le_rfl (by omega)
  a_le_b := hmin _ (by omega) (by omega)
  a_le_c := hmin _ (by omega) (by omega)
  a_le_d := hmin _ (by omega) le_rfl
  pb_lt := by have := C.m2_star (m - 1); rwa [show m - 1 - 1 = m - 2 by ring] at this
  ab_lt := by rw [mul_comm]; exact C.m2_star m
  ac_lt := by have := C.m2_star (m + 1); rwa [add_sub_cancel_right] at this
  cd_lt := by
    have := C.m2_star (m + 2); rwa [show m + 2 - 1 = m + 1 by ring] at this
  one_lt_h := by rw [← (C.sf_factors hf2 hf1 hf0 hf3).1]; exact C.one_lt_q _
  one_lt_q := by rw [← (C.sf_factors hf2 hf1 hf0 hf3).2.1]; exact C.one_lt_q _
  one_lt_k := by rw [← (C.sf_factors hf2 hf1 hf0 hf3).2.2]; exact C.one_lt_q _
  rowL := (C.sf_rows hf2 hf1 hf0 hf3).1
  rowR := (C.sf_rows hf2 hf1 hf0 hf3).2
  floorL := (C.sf_floors hf2 hf1 hf0 hf3).1
  floorR := (C.sf_floors hf2 hf1 hf0 hf3).2

/-- **No small forward minimum on a costate cycle**: at a run of four forward switches
whose central margin is the minimum of the five margins, `a_m² > 4/3`. -/
theorem sf_act_sq_gt {m : ℤ} (hf2 : C.m2Fwd (m - 2)) (hf1 : C.m2Fwd (m - 1))
    (hf0 : C.m2Fwd m) (hf3 : C.m2Fwd (m + 1))
    (hmin : ∀ j, m - 2 ≤ j → j ≤ m + 2 → C.act m ≤ C.act j) : 4 / 3 < C.act m ^ 2 :=
  (C.sf_window hf2 hf1 hf0 hf3 hmin).a_sq_gt

end CostateCycle

end SmoothedOctagon
