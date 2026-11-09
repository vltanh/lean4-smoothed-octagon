module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Cost.Defs
public import Mathlib.Analysis.Convex.Jensen

/-!
# S6: closed ratio geometry and the exact shape chord
-/

@[expose] public section

namespace SmoothedOctagon
open Real Set MeasureTheory

private noncomputable def s6ChordDen (R d e : ℝ) : ℝ :=
  2+(e+1-(e-1)*R)*d

private theorem s6_chord_den_pos {R d e : ℝ} (hR : R < 1) (hd : 0 ≤ d)
    (he : 1 ≤ e) : 0 < s6ChordDen R d e := by
  have hg : e+1-(e-1)*R = 2+(e-1)*(1-R) := by ring
  unfold s6ChordDen
  rw [hg]
  positivity

/-- Derivative of the shape coordinate with respect to the shape slope. -/
theorem costT_shape_hasDerivAt {R d e : ℝ} (hR : R < 1) (hd : 0 ≤ d) (he : 1 ≤ e) :
    HasDerivAt (fun e => costT R d e)
      (-2*d*(1-R^2)*(1+d)/(2+(e+1-(e-1)*R)*d)^2) e := by
  have hden := s6_chord_den_pos hR hd he
  have hn := (((((hasDerivAt_id' e).const_add 1).mul_const R).sub
    ((hasDerivAt_id' e).sub_const 1)).mul_const d).const_add (2*R)
  have hdd := ((((hasDerivAt_id' e).const_add 1).sub
    (((hasDerivAt_id' e).sub_const 1).mul_const R)).mul_const d).const_add 2
  have h := hn.div hdd (by
    dsimp only [Pi.sub_apply]
    simpa only [s6ChordDen,add_comm] using hden.ne')
  convert h using 1
  · funext z
    unfold costT
    dsimp only [Pi.div_apply,Pi.sub_apply]
    ring
  · simp only [Pi.sub_apply]
    field_simp
    ring

/-- The shape ratio decreases with the shape slope, on the full
closed interval. The proof is an exact positive-product difference. -/
theorem costT_antitone_shape {R d e f : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hd : 0 ≤ d) (he : 1 ≤ e) (hef : e ≤ f) : costT R d f ≤ costT R d e := by
  have heD := s6_chord_den_pos hR1 hd he
  have hfD := s6_chord_den_pos hR1 hd (he.trans hef)
  have hprod : 0 ≤ 2*d*(1-R^2)*(1+d)*(f-e) := by
    have hR2 : 0 ≤ 1-R^2 := by nlinarith only [hR0,hR1]
    positivity
  unfold costT
  change _/s6ChordDen R d f ≤ _/s6ChordDen R d e
  rw [div_le_div_iff₀ hfD heD]
  dsimp [s6ChordDen] at *
  nlinarith only [hprod]

/-- At fixed shape slope the same ratio decreases with displacement. -/
theorem costT_antitone_displacement {R d v e : ℝ} (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hd : 0 ≤ d) (hdv : d ≤ v) (he : 1 ≤ e) : costT R v e ≤ costT R d e := by
  have hdD := s6_chord_den_pos hR1 hd he
  have hvD := s6_chord_den_pos hR1 (hd.trans hdv) he
  have hprod : 0 ≤ 2*(e-1)*(1-R^2)*(v-d) := by
    have hR2 : 0 ≤ 1-R^2 := by nlinarith only [hR0,hR1]
    positivity
  unfold costT
  change _/s6ChordDen R v e ≤ _/s6ChordDen R d e
  rw [div_le_div_iff₀ hvD hdD]
  dsimp [s6ChordDen] at *
  nlinarith only [hprod]

/-- Closed correlated ratio range, including zero displacement. -/
theorem costT_correlated_bounds {R d e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    27*R/31 ≤ costT R d e ∧ costT R d e ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hRlt : R < 1 := by linarith only [hR1]
  have he0 : 1 ≤ e := by linarith only [he]
  have hden := s6_chord_den_pos hRlt hd he0
  have hupper : costT R d e ≤ R := by
    unfold costT
    change _/s6ChordDen R d e ≤ R
    rw [div_le_iff₀ hden]
    have hp : 0 ≤ (e-1)*(1-R^2)*d := by
      have hq : 0 ≤ 1-R^2 := by nlinarith only [hR0,hRlt]
      positivity
    dsimp [s6ChordDen]
    nlinarith only [hp]
  have hcorner : 27*R/31 ≤ costT R (1/19) 3 := by
    have hc := s6_chord_den_pos (R := R) (d := 1/19) (e := 3) hRlt (by norm_num) (by norm_num)
    unfold costT
    change 27*R/31 ≤ _/s6ChordDen R (1/19) 3
    rw [le_div_iff₀ hc]
    have hp := mul_nonneg (show 0 ≤ 3*R-1 by linarith only [hR])
      (show 0 ≤ 18*R+62 by positivity)
    dsimp [s6ChordDen]
    nlinarith only [hp]
  have hdisp := costT_antitone_displacement hR0 hRlt hd hd1 (by norm_num : (1:ℝ) ≤ 3)
  have hshape := costT_antitone_shape hR0 hRlt hd he0 he1
  exact ⟨hcorner.trans (hdisp.trans hshape),hupper⟩

/-- Positivity of the actual envelope expressions on their full closed box. -/
theorem cost_shear_envelopes_pos {R d : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) : 0 < costZU R d ∧ 0 < costZL R d := by
  have hR0 : 0 < R := by linarith only [hR]
  have hRlt : R < 1 := by linarith only [hR1]
  have h3 : 0 < 3-R := by linarith only [hR1]
  have h1 : 0 < 1-R := by linarith only [hRlt]
  have hbase : 0 < 2*R^2*(1+R)/(3-R) := by positivity
  have hA : 1/3 < (1+2*R)/(3*(1-R)) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith only [hR0]
  have hrest : 0 ≤ d*((1+2*R)/(3*(1-R))-3*d/2) :=
    mul_nonneg hd (by linarith only [hA,hd1])
  constructor
  · unfold costZU
    nlinarith only [hbase,hrest]
  · unfold costZL
    exact mul_pos hbase (by linarith only [hd])

theorem costBExact_shape_min_of_floor {R d e u : ℝ} (hu : 3/4 ≤ u) (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    min (costBExact R (costT R d 3) u (costZU R d) (costZL R d))
      (costBExact R (costT R d (13/5)) u (costZU R d) (costZL R d)) ≤
      costBExact R (costT R d e) u (costZU R d) (costZL R d) := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hRlt : R < 1 := by linarith only [hR1]
  obtain ⟨hZU,hZL⟩ := cost_shear_envelopes_pos hR hR1 hd hd1
  have hc := (costBExact_strictConcaveOn hR hR1 hu hZU.le hZL).concaveOn
  have hleft := costT_correlated_bounds hR hR1 hd hd1 (by norm_num : (13/5:ℝ) ≤ 3) (le_refl 3)
  have hright := costT_correlated_bounds hR hR1 hd hd1 (le_refl (13/5)) (by norm_num : (13/5:ℝ) ≤ 3)
  have hlo := costT_antitone_shape hR0 hRlt hd (by linarith only [he] : 1 ≤ e) he1
  have hhi := costT_antitone_shape hR0 hRlt hd (by norm_num : (1:ℝ) ≤ 13/5) he
  exact hc.min_le_of_mem_Icc hleft hright ⟨hlo,hhi⟩


/-- Exact-score shape chord at the genuine variance floor, including d=0. -/
theorem costBExact_shape_min {R d e : ℝ} (hR : 1/3 ≤ R) (hR1 : R ≤ 7/19)
    (hd : 0 ≤ d) (hd1 : d ≤ 1/19) (he : 13/5 ≤ e) (he1 : e ≤ 3) :
    min (costBExact R (costT R d 3) (s6VarianceFloor R d) (costZU R d) (costZL R d))
      (costBExact R (costT R d (13/5)) (s6VarianceFloor R d) (costZU R d) (costZL R d)) ≤
      costBExact R (costT R d e) (s6VarianceFloor R d) (costZU R d) (costZL R d) := by
  exact costBExact_shape_min_of_floor
    (s6_variance_floor_ge_three_quarters (by linarith only [hR]) hd) hR hR1 hd hd1 he he1

/-- The displacement-zero endpoint is explicitly included in the chord. -/
theorem costT_zero_displacement (R e : ℝ) : costT R 0 e = R := by
  simp [costT]

end SmoothedOctagon
