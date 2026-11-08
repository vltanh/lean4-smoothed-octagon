module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOA2
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOA3
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1HandOB5

/-!
# Gate S1 by hand: the outer low-ratio face

`hs1_outer_face_proof` proves the leaf `hs1_outer_face`:
the duration reduction `hh1o_face_red` leaves the two tests `F₀`, `F₁`; with `β = x + C(α - 1)`,
`8x/(9x + 8) ≤ C ≤ x(7x + 1)/(4x² + 11x + 1)`, the three branches close them:

* S (`x ≤ 3/2`): `hl1o_S_main` (beta reduction, shape concavity at `C = 8/17`, two terminal
  faces);
* A (`x ≥ 3/2`, `α ≥ 6/5`): `hl1o_A_F1`, `hl1o_A_F0` (norm, beta and shape reductions, then the
  terminal curves);
* B (`x ≥ 3/2`, `α ≤ 6/5`): `hl1o_B_F1`, `hl1o_B_F0` (the same reductions on the small shapes,
  then the terminal curves), which use the actual cap `6α² ≥ x(x + 2)` and, for `F₀`, the incoming
  ceiling `u ≤ u_ℓ(x, β)`.

## Main API

* `hl1o_slope`, `hs1_outer_face_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-- The actual strip in slope form: `β = x + C(α - 1)` with `C` between the two order slopes. -/
theorem hl1o_slope {x al be : ℝ} (hx : 1 < x) (hal : 1 ≤ al) (hxb : x ≤ be)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) :
    ∃ C, 8 * x / (9 * x + 8) ≤ C ∧ C ≤ x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1) ∧
      be = x + C * (al - 1) := by
  have hd0 : 0 < 9 * x + 8 := by linarith
  have hd1 : 0 < 4 * x ^ 2 + 11 * x + 1 := by positivity
  rcases eq_or_lt_of_le hal with h | h
  · refine ⟨8 * x / (9 * x + 8), le_rfl, ?_, ?_⟩
    · rw [div_le_div_iff₀ hd0 hd1]; nlinarith
    · rw [← h] at hb' ⊢
      have : be ≤ x := by simpa using hb'
      have : be = x := le_antisymm this hxb
      rw [this]; ring
  · have hA : 0 < al - 1 := by linarith
    refine ⟨(be - x) / (al - 1), ?_, ?_, ?_⟩
    · rw [le_div_iff₀ hA]
      have : 8 * x / (9 * x + 8) * (al - 1) = 8 * x * (al - 1) / (9 * x + 8) := by ring
      linarith
    · rw [div_le_iff₀ hA]
      have : x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1) * (al - 1) =
          x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1) := by ring
      linarith
    · field_simp
      ring

/-- **The outer low-ratio face**: on the outer face `q = 1/7` with the order strip in `β`,
`u_f(x) ≤ u ≤ V̄(x)` (and `u ≤ u_ℓ(x, β)` when `x ≥ 3/2`, `α ≤ 6/5`) and `2 ≤ τ ≤ 7r_A`:
`Γ_*(1/7) - (7/96)R*_τ(1/7) > 9193/50000`. -/
theorem hs1_outer_face_proof {x al be u τ : ℝ} (hx : 1 < x) (hx2 : x ≤ 2) (hal : 1 ≤ al)
    (hax : al ≤ x) (hxb : x ≤ be) (hbx : be ≤ al * x) (hqc : x * (x + 2) ≤ 6 * al ^ 2)
    (hb : x + 8 * x * (al - 1) / (9 * x + 8) ≤ be)
    (hb' : be ≤ x + x * (7 * x + 1) * (al - 1) / (4 * x ^ 2 + 11 * x + 1)) (hu : hsUf x ≤ u)
    (huv : u ≤ hsVbar x) (hul : 3 / 2 ≤ x → al ≤ 6 / 5 → u ≤ hsUl x be) (hτ : 2 ≤ τ)
    (hτT : τ ≤ 7 * hsRA al be) :
    9193 / 50000 < hsGs x al u (1 / 7) - 7 / 96 * hsRs x be al u (1 / 7) τ := by
  have hred := hh1o_face_red (x := x) (u := u) (by linarith) hal (by linarith) hτ hτT
  obtain ⟨C, hC0, hC1, hbC⟩ := hl1o_slope hx hal hxb hb hb'
  have hA1 : 0 ≤ al - 1 := by linarith
  have hu0 : 3 / 4 ≤ u := by
    have : 0 ≤ (x - 1) ^ 2 / (28 * (x + 1) ^ 2) := by positivity
    unfold hsUf at hu; linarith
  have hu1 : u ≤ 19 / 25 := by have := (hh1_Vbar_bounds hx hx2).2; linarith
  have hCp : C ≤ 10 / 13 := by
    have : x * (7 * x + 1) / (4 * x ^ 2 + 11 * x + 1) ≤ 10 / 13 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hCm : ∀ x0 : ℝ, 0 < x0 → x0 ≤ x → 8 * x0 / (9 * x0 + 8) ≤ C := fun x0 h0 h =>
    le_trans (by rw [div_le_div_iff₀ (by positivity) (by linarith)]; nlinarith) hC0
  suffices h : 0 < hh1oF0 x al be u ∧ 0 < hh1oF1 x al be u by
    have := lt_min h.1 h.2
    linarith
  rcases le_total x (3 / 2) with hS | hS
  · have h817 := hCm 1 one_pos hx.le
    norm_num at h817
    obtain ⟨h1, h0⟩ := hl1o_S_main hal hax hS h817 hCp hbC hu0 hu1
    exact ⟨h0, h1⟩
  have h2443 := hCm (3 / 2) (by norm_num) hS
  norm_num at h2443
  rcases le_total (6 / 5) al with hA | hB
  · exact ⟨hl1o_A_F0 hS hx2 hA hax h2443 hCp hbC hu0 hu1,
      hl1o_A_F1 hS hx2 hA hax h2443 hCp hbC hu huv⟩
  · refine ⟨?_, hl1o_B_F1 hS hx2 hal hB hqc (by linarith) hCp hbC hu0 hu1⟩
    have hb10 : be ≤ x + 10 / 13 * (al - 1) := by
      rw [hbC]; nlinarith [mul_le_mul_of_nonneg_right hCp hA1]
    exact hl1o_B_F0 hS hx2 hal hB hqc hxb hb10 hu (hul hS hB)

end SmoothedOctagon
