module

public import SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Slope
public import SmoothedOctagon.Exclusion.Forward.Scalars.Neighbor.Asymmetric
public import SmoothedOctagon.Exclusion.Forward.Reduce

/-!
# Case F scalars: the neighbour residual

The neighbour residual `𝓔 = αA - B - nF_{z/S}(h) - mF_{w/T}(T²/W)` is negative on the comparison
domain with `w ≥ 4/3`. Lowering the larger neighbour reduces this to two faces, the symmetric face
`w = z ≥ 4/3` and the asymmetric face `w = 4/3 ≥ z`.

## Main API

* `fs_N0`, `fs_N1`, `fs_resN_canon`: `𝓔` is a canonical function of the exterior factor (`fs_cf`).
* `fs_P_nonneg'`, `fs_N_conc`: concavity in `h` for `1 ≤ z ≤ 5/3`.
* `fs_neighborValue_neg`: the symmetric value, by reciprocal moments and edge convexity.
* `fs_neighborSlope_neg`: the symmetric partial slope, by a derivative maximum principle.
* `asym_continuous_row_neg`: shape and scale convexity on the asymmetric comparison rectangle.
* `fs_tangent_comb`, `fs_NS_Eval`, `fs_NS_Dval`, `fs_NS_Tval`,
  `fs_resN_sym_of_floor`, `fs_resN_sym`,
  `fs_resN_asym`: the two faces.
* `fs_resN_le`: lowering the larger neighbour does not decrease `𝓔` (with `fs_A_sub_le`, `fs_m_sub`,
  `fs_F_ge`, `fs_F_mono_x`, `fs_F_mono_r`).
* `fs_resN_neg`: the sign.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-! ### The canonical form of the neighbour residual -/

/-- Constant coefficient of `𝓔` as a canonical function of `h`, with `A`, `q`, `V = F_{w/T}(T²/W)`
as atoms. -/
noncomputable def fs_N0 (U z A V q : ℝ) : ℝ :=
  -(1 + U) * z * A / (z ^ 2 + U) - 1 + z ^ 2 / (1 + z) - z ^ 3 / (z ^ 2 + U) +
    (1 + z) ^ 2 * (U - z) / (z ^ 2 + U) + (1 + U) ^ 2 * V / ((1 + z) * (z ^ 2 + U)) * q * z

/-- Linear coefficient of `𝓔`. -/
noncomputable def fs_N1 (U z A V q : ℝ) : ℝ :=
  (1 + U) * (1 + z) * A / (z ^ 2 + U) - (z ^ 2 + U) / (1 + z) -
    (1 + z) ^ 2 * (U - z) / (z ^ 2 + U) * (1 - (z / (1 + z)) ^ 2) -
    (1 + U) ^ 2 * V / ((1 + z) * (z ^ 2 + U)) * (q * (1 + z) - 1)

/-- The canonical form of the neighbour residual. -/
theorem fs_resN_canon {U z w h : ℝ} (hU : 0 < U) (hz : 0 < z) (hh : 0 < h) (hh1 : h ≠ 1) :
    ff_resN U z w h = fs_cf (fs_N0 U z (ff_A U z w) (ff_F (w / (1 + w)) ((1 + w) ^ 2 / (w ^ 2 + U)))
        (ff_q U z w))
      (fs_N1 U z (ff_A U z w) (ff_F (w / (1 + w)) ((1 + w) ^ 2 / (w ^ 2 + U))) (ff_q U z w))
      (-(z ^ 2 * (U - z) / (z ^ 2 + U))) (z ^ 2 * (1 + z) / (z ^ 2 + U)) z
      (z * (1 + z) * (U - z) / (z ^ 2 + U)) h := by
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  have hh1' : h - 1 ≠ 0 := sub_ne_zero.2 hh1
  unfold ff_resN ff_alpha ff_B ff_n ff_m fs_cf fs_N0 fs_N1
  unfold ff_F
  generalize ff_A U z w = A
  generalize ff_q U z w = q
  generalize (1 + w) ^ 2 / (w ^ 2 + U) = r
  generalize Real.log h = L
  generalize hV : 1 + (w / (1 + w)) ^ 2 * r - w / (1 + w) * r * Real.log r / (r - 1) = V
  field_simp
  ring

/-- The concavity polynomial `P(s) ≥ 0` for `s ≥ S²/Z`, `1 ≤ z ≤ 5/3`. -/
theorem fs_P_nonneg' {U z s : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 5 / 3) (hU : 1 + 6 * z / 5 ≤ U) (hU3 : U ≤ 3)
    (hs : (1 + z) ^ 2 / (z ^ 2 + U) ≤ s) :
    0 ≤ (U - z) * s ^ 2 * (2 * z * s - (1 + z)) + (z ^ 2 + U) * s - 2 * z * (1 + z) := by
  exact fs_factor_curvature_nonneg hz (by nlinarith only [hz, hz']) (by linarith only [hz, hU]) hU3 hs

/-- The concavity condition of the neighbour residual on `[S²/Z, h]`. -/
theorem fs_N_conc {U z s : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 5 / 3) (hU : 1 + 6 * z / 5 ≤ U) (hU3 : U ≤ 3)
    (hs : (1 + z) ^ 2 / (z ^ 2 + U) ≤ s) :
    2 * -(z ^ 2 * (U - z) / (z ^ 2 + U)) * s ^ 3 + 2 * (z ^ 2 * (1 + z) / (z ^ 2 + U)) +
      z * (1 + z) * (U - z) / (z ^ 2 + U) * s ^ 2 - z * s ≤ 0 := by
  have hP := fs_P_nonneg' hz hz' hU hU3 hs
  have hU0 : 0 < U := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have e : 2 * -(z ^ 2 * (U - z) / (z ^ 2 + U)) * s ^ 3 + 2 * (z ^ 2 * (1 + z) / (z ^ 2 + U)) +
      z * (1 + z) * (U - z) / (z ^ 2 + U) * s ^ 2 - z * s =
      -(z * ((U - z) * s ^ 2 * (2 * z * s - (1 + z)) + (z ^ 2 + U) * s - 2 * z * (1 + z)) /
        (z ^ 2 + U)) := by
    field_simp; ring
  rw [e]
  have : 0 ≤ z * ((U - z) * s ^ 2 * (2 * z * s - (1 + z)) + (z ^ 2 + U) * s - 2 * z * (1 + z)) /
      (z ^ 2 + U) := by
    have : 0 ≤ z := by linarith
    positivity
  linarith

/-! ### The two faces -/


/-- The tangent line over `[h₀, h_c]` is below the larger of its two end values. -/
theorem fs_tangent_comb {E D h0 h hc : ℝ} (hE : E < 0) (hT : E + (hc - h0) * D < 0) (h1 : h0 ≤ h)
    (h2 : h ≤ hc) : E + (h - h0) * D < 0 := by
  rcases le_total D 0 with hD | hD
  · nlinarith
  · nlinarith

theorem fs_NS_Eval {U z : ℝ} (hz : 4 / 3 ≤ z) (hU : 1 + 6 * z / 5 ≤ U) (hU3 : U < 3) :
    fs_cf (fs_N0 U z (ff_A U z z) (ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U)))
        (ff_q U z z))
      (fs_N1 U z (ff_A U z z) (ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U))) (ff_q U z z))
      (-(z ^ 2 * (U - z) / (z ^ 2 + U))) (z ^ 2 * (1 + z) / (z ^ 2 + U)) z
      (z * (1 + z) * (U - z) / (z ^ 2 + U)) ((1 + z) ^ 2 / (z ^ 2 + U)) < 0 := by
  have hz' : z ≤ 5 / 3 := by linarith
  have hU0 : 0 < U := by linarith
  have hz0 : 0 < z := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = (z - 1) / (z + 1) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (2 * z + 1 - U) / (z ^ 2 + U) := ⟨_, rfl⟩
  have hz1 : 0 < z + 1 := by linarith
  have ha0 : 1 / 7 ≤ a := by rw [ha, le_div_iff₀ hz1]; linarith
  have ha1 : a ≤ 1 / 4 := by rw [ha, div_le_iff₀ hz1]; linarith
  have ht0 : 1 / 8 ≤ t := by rw [ht, le_div_iff₀ hZ]; nlinarith
  have ht1 : t ≤ 1 / 4 := by rw [ht, div_le_iff₀ hZ]; nlinarith
  have hb : 1 - a = 2 / (z + 1) := by rw [ha]; field_simp; ring
  have hI : 1 + t = (1 + z) ^ 2 / (z ^ 2 + U) := by rw [ht]; field_simp; ring
  have hc : 1 - a * (1 + t) = (1 + U) / (z ^ 2 + U) := by rw [ha, ht]; field_simp; ring
  have hE := fs_neighborValue_neg ha0 ha1 ht0 ht1
  unfold fs_neighborValue fs_neighborR fs_neighborCL fs_neighborCM at hE
  dsimp only at hE
  rw [hc, hb, hI] at hE
  rw [ha, ht] at hE
  have hlq : Real.log ((1 + z) * (1 + z) / (1 + U)) =
      Real.log ((1 + z) ^ 2 / (z ^ 2 + U)) - Real.log ((1 + U) / (z ^ 2 + U)) := by
    rw [← Real.log_div (by positivity) (by positivity)]; congr 1; field_simp
  have hl3 : (1 + z) ^ 2 / (z ^ 2 + U) - 1 = (2 * z + 1 - U) / (z ^ 2 + U) := by field_simp; ring
  refine lt_of_eq_of_lt ?_ hE
  simp only [fs_cf, fs_N0, fs_N1]
  unfold ff_A ff_F ff_q
  rw [hlq, hl3]
  generalize Real.log ((1 + z) ^ 2 / (z ^ 2 + U)) = LI
  generalize Real.log ((1 + U) / (z ^ 2 + U)) = Lc
  generalize hd : 2 * z + 1 - U = d
  have hd0 : d ≠ 0 := by rw [← hd]; linarith
  field_simp
  subst hd
  ring

/-- The partial factor derivative at the symmetric least factor is negative. -/
theorem fs_NS_Dval {U z : ℝ} (hz : 4 / 3 ≤ z) (hU : 1 + 6 * z / 5 ≤ U) (hU3 : U < 3) :
    fs_cf' (fs_N1 U z (ff_A U z z) (ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U))) (ff_q U z z))
        (-(z ^ 2 * (U - z) / (z ^ 2 + U))) (z ^ 2 * (1 + z) / (z ^ 2 + U)) z
        (z * (1 + z) * (U - z) / (z ^ 2 + U)) ((1 + z) ^ 2 / (z ^ 2 + U)) < 0 := by
  have hz' : z ≤ 5 / 3 := by linarith
  have hU0 : 0 < U := by linarith
  have hz0 : 0 < z := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = (z - 1) / (z + 1) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t, t = (2 * z + 1 - U) / (z ^ 2 + U) := ⟨_, rfl⟩
  have hz1 : 0 < z + 1 := by linarith
  have ha0 : 1 / 7 ≤ a := by rw [ha, le_div_iff₀ hz1]; linarith
  have ha1 : a ≤ 1 / 4 := by rw [ha, div_le_iff₀ hz1]; linarith
  have ht0 : 1 / 8 ≤ t := by rw [ht, le_div_iff₀ hZ]; nlinarith
  have ht1 : t ≤ 48 / 197 := by
    rw [ht, div_le_iff₀ hZ]
    have hm := mul_nonneg (show 0 ≤ z - 4 / 3 by linarith) (show 0 ≤ z - 3 / 4 by linarith)
    nlinarith only [hU, hm]
  have hb : 1 - a = 2 / (z + 1) := by rw [ha]; field_simp; ring
  have hI : 1 + t = (1 + z) ^ 2 / (z ^ 2 + U) := by rw [ht]; field_simp; ring
  have hc : 1 - a * (1 + t) = (1 + U) / (z ^ 2 + U) := by rw [ha, ht]; field_simp; ring
  have hD := fs_neighborSlope_neg ha0 ha1 ht0 ht1
  unfold fs_neighborSlope fs_neighborSlopeR fs_neighborSlopeCL at hD
  dsimp only at hD
  rw [hc, hb, hI] at hD
  rw [ha, ht] at hD
  have hlq : Real.log ((1 + z) * (1 + z) / (1 + U)) =
      Real.log ((1 + z) ^ 2 / (z ^ 2 + U)) - Real.log ((1 + U) / (z ^ 2 + U)) := by
    rw [← Real.log_div (by positivity) (by positivity)]; congr 1; field_simp
  have hl3 : (1 + z) ^ 2 / (z ^ 2 + U) - 1 = (2 * z + 1 - U) / (z ^ 2 + U) := by field_simp; ring
  refine lt_of_eq_of_lt ?_ hD
  simp only [fs_cf', fs_N1]
  unfold ff_A ff_F ff_q
  rw [hlq, hl3]
  generalize Real.log ((1 + z) ^ 2 / (z ^ 2 + U)) = LI
  generalize Real.log ((1 + U) / (z ^ 2 + U)) = Lc
  generalize hd : 2 * z + 1 - U = d
  have hd0 : d ≠ 0 := by rw [← hd]; linarith
  field_simp
  subst hd
  ring

theorem fs_NS_Tval {U z : ℝ} (hz : 4 / 3 ≤ z) (hU : 1 + 6 * z / 5 ≤ U) (hU3 : U < 3) :
    fs_cf (fs_N0 U z (ff_A U z z) (ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U)))
        (ff_q U z z))
      (fs_N1 U z (ff_A U z z) (ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U))) (ff_q U z z))
      (-(z ^ 2 * (U - z) / (z ^ 2 + U))) (z ^ 2 * (1 + z) / (z ^ 2 + U)) z
      (z * (1 + z) * (U - z) / (z ^ 2 + U)) ((1 + z) ^ 2 / (z ^ 2 + U)) +
      ((1 + z) * (5 * U - 2 - 3 * z) / (3 * (z ^ 2 + U)) - (1 + z) ^ 2 / (z ^ 2 + U)) *
      fs_cf' (fs_N1 U z (ff_A U z z) (ff_F (z / (1 + z)) ((1 + z) ^ 2 / (z ^ 2 + U))) (ff_q U z z))
        (-(z ^ 2 * (U - z) / (z ^ 2 + U))) (z ^ 2 * (1 + z) / (z ^ 2 + U)) z
        (z * (1 + z) * (U - z) / (z ^ 2 + U)) ((1 + z) ^ 2 / (z ^ 2 + U)) < 0 := by
  have hE := fs_NS_Eval hz hU hU3
  have hD := fs_NS_Dval hz hU hU3
  have hU0 : 0 < U := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hbudget : 0 ≤ U - 1 - 6 * z / 5 := by linarith only [hU]
  have hgap : 0 ≤ (1 + z) * (5 * U - 2 - 3 * z) / (3 * (z ^ 2 + U)) -
      (1 + z) ^ 2 / (z ^ 2 + U) := by
    have he : (1 + z) * (5 * U - 2 - 3 * z) / (3 * (z ^ 2 + U)) -
        (1 + z) ^ 2 / (z ^ 2 + U) =
        5 * (1 + z) * (U - 1 - 6 * z / 5) / (3 * (z ^ 2 + U)) := by field_simp; ring
    rw [he]
    positivity
  have hm := mul_nonpos_of_nonneg_of_nonpos hgap hD.le
  linarith only [hE, hm]

/-- The symmetric neighbour residual is negative for every factor above its least value. -/
theorem fs_resN_sym_of_floor {U z h : ℝ} (hz : 4 / 3 ≤ z) (hU : 1 + 6 * z / 5 ≤ U) (hU3 : U < 3)
    (hhl : (1 + z) ^ 2 / (z ^ 2 + U) ≤ h) : ff_resN U z z h < 0 := by
  have hz' : z ≤ 5 / 3 := by linarith
  have hU0 : 0 < U := by linarith
  have hz0 : 0 < z := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  have hI1 : 1 < (1 + z) ^ 2 / (z ^ 2 + U) := by rw [lt_div_iff₀ hZ]; nlinarith
  have hh1 : 1 < h := lt_of_lt_of_le hI1 hhl
  rw [fs_resN_canon hU0 hz0 (by linarith) hh1.ne']
  refine lt_of_le_of_lt (fs_cf_tangent (by positivity) hhl
    (fun s hs ↦ fs_N_conc (by linarith) hz' hU hU3.le hs.1)) ?_
  have hE := fs_NS_Eval hz hU hU3
  have hD := fs_NS_Dval hz hU hU3
  have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hhl) hD.le
  linarith only [hE, hm]

/-- **The symmetric neighbour face** `w = z ≥ 4/3`: the residual is negative. -/
theorem fs_resN_sym {U z h : ℝ} (hz : 4 / 3 ≤ z) (hU : 1 + 6 * z / 5 ≤ U) (hU3 : U < 3)
    (hhl : (1 + z) ^ 2 / (z ^ 2 + U) ≤ h)
    (hhu : h ≤ (1 + z) * (5 * U - 2 - 3 * z) / (3 * (z ^ 2 + U))) : ff_resN U z z h < 0 := by
  have hz' : z ≤ 5 / 3 := by linarith
  have hU0 : 0 < U := by linarith
  have hz0 : 0 < z := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  have hI1 : 1 < (1 + z) ^ 2 / (z ^ 2 + U) := by rw [lt_div_iff₀ hZ]; nlinarith
  have hh1 : 1 < h := lt_of_lt_of_le hI1 hhl
  rw [fs_resN_canon hU0 hz0 (by linarith) hh1.ne']
  refine lt_of_le_of_lt (fs_cf_tangent (by positivity) hhl
    (fun s hs ↦ fs_N_conc (by linarith) hz' hU hU3.le hs.1)) ?_
  exact fs_tangent_comb (fs_NS_Eval hz hU hU3) (fs_NS_Tval hz hU hU3) hhl hhu

/-- **The asymmetric neighbour face** `w = 4/3 ≥ z`: the residual is negative. -/
theorem fs_resN_asym {U z h : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 4 / 3) (hU : 9 / 5 + 3 * z / 5 ≤ U)
    (hU3 : U < 3) (hhl : (1 + z) ^ 2 / (z ^ 2 + U) ≤ h)
    (hhu : h ≤ (1 + z) * (5 * U - 2 - 3 * (4 / 3)) / (3 * (z ^ 2 + U))) :
    ff_resN U z (4 / 3) h < 0 :=
  asym_physical_face_neg hz hz' hU hU3 hhl hhu


/-! ### Reduction of the larger neighbour -/

/-- `m(w) - m(w') = α(w - w')`. -/
theorem fs_m_sub {U z w w' h : ℝ} (hU : 0 < U) (hz : 0 < z) :
    ff_m U z w h - ff_m U z w' h = ff_alpha U z h * (w - w') := by
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  unfold ff_m ff_alpha ff_q
  field_simp
  ring

/-- `A(w) - A(w') ≤ (w - w')(1 - 1/T + 1/T²)` for `1 ≤ w' ≤ w`. -/
theorem fs_A_sub_le {U z w w' : ℝ} (hU : 0 < U) (hz : 0 < z) (hw' : 1 ≤ w') (hww : w' ≤ w) :
    ff_A U z w - ff_A U z w' ≤ (w - w') * (1 - 1 / (1 + w) + 1 / (1 + w) ^ 2) := by
  set B := 1 - 1 / (1 + w) + 1 / (1 + w) ^ 2 with hB
  have key := ff_le_of_deriv (f := fun s ↦ s * B - ff_A U z s)
    (f' := fun s ↦ B - (1 - 1 / (1 + s) + 1 / (1 + s) ^ 2)) hww (fun s hs ↦ ?_) (fun s hs ↦ ?_)
  · linarith
  · have hs1 : 0 < 1 + s := by linarith [hs.1]
    have hK : 0 < 1 + U := by linarith
    have hz0 : 0 < 1 + z := by linarith
    have hlog : HasDerivAt (fun s ↦ Real.log (ff_q U z s)) (1 / (1 + s)) s := by
      have hq : HasDerivAt (fun s ↦ (1 + z) * (1 + s) / (1 + U)) ((1 + z) * 1 / (1 + U)) s :=
        (((hasDerivAt_id' s).const_add 1).const_mul (1 + z)).div_const (1 + U)
      have hq0 : (1 + z) * (1 + s) / (1 + U) ≠ 0 := by positivity
      have := hq.log hq0
      show HasDerivAt (fun s ↦ Real.log ((1 + z) * (1 + s) / (1 + U))) _ s
      refine this.congr_deriv ?_
      field_simp
    have hinv : HasDerivAt (fun s : ℝ ↦ 1 / (1 + s)) (-1 / (1 + s) ^ 2) s := by
      have := ((hasDerivAt_id' s).const_add 1).inv hs1.ne'
      convert this using 1
      · ext y; simp
    have hA : HasDerivAt (fun s ↦ ff_A U z s) (1 - 1 / (1 + s) + 1 / (1 + s) ^ 2) s := by
      have := (((((hasDerivAt_id' s).const_add (1 + z)).sub_const (1 / (1 + z))).sub hinv).add_const
        (1 / (1 + U))).sub hlog
      have h2 : HasDerivAt (fun s ↦ ff_A U z s) (1 - -1 / (1 + s) ^ 2 - 1 / (1 + s)) s := this
      exact h2.congr_deriv (by ring)
    have := ((hasDerivAt_id' s).mul_const B).sub hA
    convert this using 1
    ring
  · have hs0 : 1 ≤ s := le_trans hw' hs.1
    have hs1 : 0 < 1 + s := by linarith
    have hw1 : 0 < 1 + w := by linarith [hs.2]
    have c1 : 1 / (1 + w) ≤ 1 / (1 + s) := one_div_le_one_div_of_le hs1 (by linarith [hs.2])
    have c2 : 1 / (1 + s) ≤ 1 / 2 := by rw [div_le_div_iff₀ hs1 (by norm_num)]; linarith
    have e1 : 1 / (1 + w) ^ 2 = (1 / (1 + w)) ^ 2 := (one_div_pow _ _).symm
    have e2 : 1 / (1 + s) ^ 2 = (1 / (1 + s)) ^ 2 := (one_div_pow _ _).symm
    rw [hB, e1, e2]
    nlinarith [mul_nonneg (sub_nonneg.2 c1) (by linarith : (0 : ℝ) ≤ 1 - 1 / (1 + s) - 1 / (1 + w))]

/-- `F_x(r) ≥ 1 - x + x²` for `x ≥ 1/2`, `r > 1`. -/
theorem fs_F_ge {x r : ℝ} (hx : 1 / 2 ≤ x) (hr : 1 < r) : 1 - x + x ^ 2 ≤ ff_F x r := by
  have hr1 : 0 < r - 1 := by linarith
  have hf := ff_f_nonneg hr.le
  unfold ff_f at hf
  have hq : r * Real.log r ≤ r - 1 + (r - 1) ^ 2 / 2 := by
    have : r * Real.log r ≤ r * ((r - r⁻¹) / 2) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have e : r * ((r - r⁻¹) / 2) = r - 1 + (r - 1) ^ 2 / 2 := by field_simp; ring
    linarith
  unfold ff_F
  have e : x * r * Real.log r / (r - 1) = x * (r * Real.log r) / (r - 1) := by ring
  rw [e]
  have : x * (r * Real.log r) / (r - 1) ≤ x * (r - 1 + (r - 1) ^ 2 / 2) / (r - 1) := by
    apply div_le_div_of_nonneg_right _ hr1.le
    exact mul_le_mul_of_nonneg_left hq (by linarith)
  have e2 : x * (r - 1 + (r - 1) ^ 2 / 2) / (r - 1) = x * (1 + (r - 1) / 2) := by
    field_simp
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ x) hr1.le) (by linarith : (0 : ℝ) ≤ x - 1 / 2)]

/-- The exterior floor increases in its factor for `x ≥ 1/2`. -/
theorem fs_F_mono_r {x r r' : ℝ} (hx : 1 / 2 ≤ x) (hr : 1 < r) (hrr : r ≤ r') :
    ff_F x r ≤ ff_F x r' :=
  ff_F_mono hx hr hrr

/-- `F_x(r)` increases in `x ≥ 1/2` for `r > 1`. -/
theorem fs_F_mono_x {x x' r : ℝ} (hx : 1 / 2 ≤ x) (hxx : x ≤ x') (hr : 1 < r) :
    ff_F x r ≤ ff_F x' r := by
  have hr1 : 0 < r - 1 := by linarith
  have hl : Real.log r / (r - 1) ≤ 1 := by
    rw [div_le_one hr1]; exact Real.log_le_sub_one_of_pos (by linarith)
  have e : ∀ y : ℝ, ff_F y r = 1 + y ^ 2 * r - y * r * (Real.log r / (r - 1)) := by
    intro y; unfold ff_F; ring
  rw [e, e]
  have : 0 ≤ (x' - x) * r * ((x' + x) - Real.log r / (r - 1)) := by
    apply mul_nonneg (mul_nonneg (by linarith) (by linarith)); linarith
  nlinarith

/-- **The reduction of the larger neighbour**, in difference form: `𝓔` does not decrease when `w` is
lowered to `w' ∈ [1, w]`, provided `w < U < 2w' + 1` and `q(w') ≥ 1`. -/
theorem fs_resN_le {U z w w' h : ℝ} (hU : 0 < U) (hz : 0 < z) (hw' : 1 ≤ w') (hww : w' ≤ w)
    (hwU : w < U) (hU2 : U < 2 * w' + 1) (hq : 1 ≤ ff_q U z w') (hh : 1 ≤ h) :
    ff_resN U z w h ≤ ff_resN U z w' h := by
  have hw : 1 ≤ w := le_trans hw' hww
  have hW' : 0 < w' ^ 2 + U := by positivity
  have hW : 0 < w ^ 2 + U := by positivity
  set V := ff_F (w / (1 + w)) ((1 + w) ^ 2 / (w ^ 2 + U)) with hV
  set V' := ff_F (w' / (1 + w')) ((1 + w') ^ 2 / (w' ^ 2 + U)) with hV'
  have hI' : 1 < (1 + w') ^ 2 / (w' ^ 2 + U) := by rw [lt_div_iff₀ hW']; nlinarith
  have hII : (1 + w') ^ 2 / (w' ^ 2 + U) ≤ (1 + w) ^ 2 / (w ^ 2 + U) := by
    rw [div_le_div_iff₀ hW' hW]
    have : (1 + w) ^ 2 * (w' ^ 2 + U) - (1 + w') ^ 2 * (w ^ 2 + U) =
        (w - w') * (U * (w + w' + 2) - 2 * w * w' - w - w') := by ring
    have h2 : 0 ≤ U * (w + w' + 2) - 2 * w * w' - w - w' := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hww) h2]
  have hI : 1 < (1 + w) ^ 2 / (w ^ 2 + U) := lt_of_lt_of_le hI' hII
  have hy' : 1 / 2 ≤ w' / (1 + w') := by rw [le_div_iff₀ (by linarith)]; linarith
  have hyy : w' / (1 + w') ≤ w / (1 + w) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]; nlinarith
  have hVV : V' ≤ V :=
    le_trans (fs_F_mono_r hy' hI' hII) (fs_F_mono_x hy' hyy hI)
  have hVB : 1 - 1 / (1 + w) + 1 / (1 + w) ^ 2 ≤ V := by
    have h1 := fs_F_ge (le_trans hy' hyy) hI
    have e : 1 - w / (1 + w) + (w / (1 + w)) ^ 2 = 1 - 1 / (1 + w) + 1 / (1 + w) ^ 2 := by
      field_simp; ring
    linarith
  have hA := fs_A_sub_le hU hz hw' hww
  have hms := fs_m_sub (w := w) (w' := w') (h := h) hU hz
  have hα : 0 ≤ ff_alpha U z h := (ff_alpha_pos hU hz hh).le
  have hm' : 0 ≤ ff_m U z w' h := by
    unfold ff_m
    apply mul_nonneg (by positivity)
    have : 0 ≤ ff_q U z w' * (1 + z) - 1 := by nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ h - 1) this]
  have key : ff_resN U z w h - ff_resN U z w' h =
      ff_alpha U z h * (ff_A U z w - ff_A U z w') - ff_alpha U z h * (w - w') * V -
        ff_m U z w' h * (V - V') := by
    unfold ff_resN
    rw [← hV, ← hV']
    have : ff_m U z w h = ff_m U z w' h + ff_alpha U z h * (w - w') := by linarith
    rw [this]; ring
  have t1 := mul_le_mul_of_nonneg_left hA hα
  have t2 : ff_alpha U z h * ((w - w') * (1 - 1 / (1 + w) + 1 / (1 + w) ^ 2)) ≤
      ff_alpha U z h * ((w - w') * V) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hVB (by linarith)) hα
  have t3 : 0 ≤ ff_m U z w' h * (V - V') := mul_nonneg hm' (by linarith)
  nlinarith

/-! ### The neighbour sign -/

/-- **The neighbour sign.** After lowering `w` to `max(z, 4/3)`, the residual is concave in `h` on
the symmetric face (`fs_N_conc`), where reciprocal moments control the value and slope.
On the asymmetric face, shape and scale convexity reduce the sign to reciprocal tangent bounds. -/
theorem fs_resN_neg {U z w h : ℝ} (hU : 11 / 5 ≤ U) (hU3 : U < 3) (hz : 1 ≤ z) (hzw : z ≤ w)
    (hw : 4 / 3 ≤ w) (hzw' : z + w ≤ 5 * (U - 1) / 3) (hh1 : 1 < h)
    (hhl : (1 + z) ^ 2 / (z ^ 2 + U) ≤ h) (_hhu : h ≤ (1 + z) / z)
    (hhc : h ≤ (1 + z) * (5 * U - 2 - 3 * w) / (3 * (z ^ 2 + U))) : ff_resN U z w h < 0 := by
  have hU0 : 0 < U := by linarith
  have hz0 : 0 < z := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hwU : w < U := by linarith
  have hS : 0 < 1 + z := by linarith
  rcases le_total z (4 / 3) with hz43 | hz43
  · have hq : 1 ≤ ff_q U z (4 / 3) := by
      unfold ff_q; rw [le_div_iff₀ (by linarith)]; nlinarith
    refine lt_of_le_of_lt (fs_resN_le hU0 hz0 (by norm_num) hw hwU (by linarith) hq hh1.le) ?_
    refine fs_resN_asym hz hz43 (by linarith) hU3 hhl (le_trans hhc ?_)
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hS.le
    linarith
  · have hq : 1 ≤ ff_q U z z := by
      unfold ff_q; rw [le_div_iff₀ (by linarith)]; nlinarith
    refine lt_of_le_of_lt (fs_resN_le hU0 hz0 hz hzw hwU (by linarith) hq hh1.le) ?_
    refine fs_resN_sym hz43 (by linarith) hU3 hhl (le_trans hhc ?_)
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hS.le
    linarith

end SmoothedOctagon
