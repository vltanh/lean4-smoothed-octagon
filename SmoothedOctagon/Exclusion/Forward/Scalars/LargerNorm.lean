module

public import SmoothedOctagon.Exclusion.Forward.Scalars.LargerNorm.Endpoints

/-!
# Case F scalars: the larger-norm residual

On the symmetric domain `1 ≤ z = w ≤ 4/3`, `1 + 6z/5 ≤ U < 3`, `S²/Z ≤ h ≤ S(5U - 2 - 3z)/(3Z)`, the
larger-norm residual `𝓔_v = r - nL(z, h) - m/64` is negative.

## Main API

* `fs_resV_canon`: `𝓔_v` is a canonical function of the exterior factor (`fs_cf`).
* `fs_P_nonneg`: the concavity polynomial is nonnegative.
* `fs_normValue_neg`, `fs_normTangent_neg`: the value and the other tangent endpoint in the coordinates
  `a = (z - 1)/(z + 1)`, `t = I - 1`.
* `fs_resV_neg`: the sign.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-! ### The canonical form -/

/-- Constant coefficient of `𝓔_v` as a canonical function of `h` (`Φ` an atom). -/
noncomputable def fs_V0 (U z Φ : ℝ) : ℝ :=
  -z * (1 + U) * Φ / (z ^ 2 + U) - z * (8 * U ^ 2 * (1 + z) - 17 * U * z ^ 2 - 210 * U * z - 129 * U +
    64 * z ^ 3 + 367 * z ^ 2 + 230 * z - 9) / (64 * (z ^ 2 + U) * (1 + z))

/-- Linear coefficient of `𝓔_v`. -/
noncomputable def fs_V1 (U z Φ : ℝ) : ℝ :=
  (1 + U) * (1 + z) * Φ / (z ^ 2 + U) + (8 * U ^ 2 * z ^ 2 + 16 * U ^ 2 * z - 7 * U ^ 2 +
    47 * U * z ^ 3 - 163 * U * z ^ 2 - 147 * U * z + 33 * U - 64 * z ^ 4 + 175 * z ^ 3 +
    213 * z ^ 2 - 35 * z - 24) / (64 * (z ^ 2 + U) * (1 + z))

/-- The canonical form of `𝓔_v` (`w = z`), with `Φ` kept as an atom. -/
theorem fs_resV_canon {U z h : ℝ} (hU : 0 < U) (hz : 0 < z) (hh : 0 < h) (hh1 : h ≠ 1) :
    ff_resV U z z h = fs_cf (fs_V0 U z (ff_Phi U z z)) (fs_V1 U z (ff_Phi U z z))
      (z ^ 2 * (z - U) / (z ^ 2 + U)) (z ^ 2 * (1 + z) / (z ^ 2 + U)) z
      (z * (U - z) * (1 + z) / (z ^ 2 + U)) h := by
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  have hh1' : h - 1 ≠ 0 := sub_ne_zero.2 hh1
  unfold ff_resV ff_r ff_n ff_L ff_m ff_q fs_cf fs_V0 fs_V1
  simp only [ff_f]
  generalize ff_Phi U z z = Φ
  generalize Real.log h = L
  field_simp
  ring

/-- The concavity polynomial `P(s) = (U - z)s²(2zs - S) + Zs - 2zS ≥ 0` for `s ≥ S²/Z`; it controls
the sign of the second derivative of `𝓔_v` in `h`. -/
theorem fs_P_nonneg {U z s : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 4 / 3) (hU : 1 + 6 * z / 5 ≤ U) (hU3 : U ≤ 3)
    (hs : (1 + z) ^ 2 / (z ^ 2 + U) ≤ s) :
    0 ≤ (U - z) * s ^ 2 * (2 * z * s - (1 + z)) + (z ^ 2 + U) * s - 2 * z * (1 + z) := by
  exact fs_factor_curvature_nonneg hz (by nlinarith only [hz, hz']) (by linarith only [hz, hU]) hU3 hs

/-- **The symmetric larger-norm sign**: `𝓔_v < 0` on the symmetric domain. Concavity in `h`
reduces the sign to the two endpoints of its affine tangent. Convexity controls the value;
concavity of the normalized tangent derivative makes the other endpoint increase to the
geometric boundary, where it equals that value. -/
theorem fs_resV_neg {U z h : ℝ} (hz : 1 ≤ z) (hz' : z ≤ 4 / 3) (hU : 1 + 6 * z / 5 ≤ U)
    (hU3 : U < 3) (hhl : (1 + z) ^ 2 / (z ^ 2 + U) ≤ h)
    (hhu : h ≤ (1 + z) * (5 * U - 2 - 3 * z) / (3 * (z ^ 2 + U))) : ff_resV U z z h < 0 := by
  have hU0 : 0 < U := by linarith
  have hz0 : 0 < z := by linarith
  have hZ : 0 < z ^ 2 + U := by positivity
  have hS : 0 < 1 + z := by linarith
  have hK : 0 < 1 + U := by linarith
  have hI1 : 1 < (1 + z) ^ 2 / (z ^ 2 + U) := by rw [lt_div_iff₀ hZ]; nlinarith
  have hh1 : 1 < h := lt_of_lt_of_le hI1 hhl
  rw [fs_resV_canon hU0 hz0 (by linarith) hh1.ne']
  refine lt_of_le_of_lt (fs_cf_tangent (by positivity) hhl ?_) ?_
  · intro s hs
    have hP := fs_P_nonneg hz hz' hU hU3.le hs.1
    have hs0 : 0 < s := by linarith [hs.1]
    have e : 2 * (z ^ 2 * (z - U) / (z ^ 2 + U)) * s ^ 3 + 2 * (z ^ 2 * (1 + z) / (z ^ 2 + U)) +
        z * (U - z) * (1 + z) / (z ^ 2 + U) * s ^ 2 - z * s =
        -(z * ((U - z) * s ^ 2 * (2 * z * s - (1 + z)) + (z ^ 2 + U) * s - 2 * z * (1 + z)) /
          (z ^ 2 + U)) := by
      field_simp; ring
    rw [e]
    have : 0 ≤ z * ((U - z) * s ^ 2 * (2 * z * s - (1 + z)) + (z ^ 2 + U) * s - 2 * z * (1 + z)) /
        (z ^ 2 + U) := by positivity
    linarith
  · obtain ⟨a, ha⟩ : ∃ a, a = (z - 1) / (z + 1) := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, t = (2 * z + 1 - U) / (z ^ 2 + U) := ⟨_, rfl⟩
    have hz1 : 0 < z + 1 := by linarith
    have ha0 : 0 ≤ a := by rw [ha]; apply div_nonneg <;> linarith
    have ha1 : a ≤ 1 / 7 := by rw [ha, div_le_iff₀ hz1]; linarith
    have ht0 : 0 < t := by rw [ht]; apply div_pos _ hZ; linarith
    have ht1 : t ≤ 1 / 4 := by rw [ht, div_le_iff₀ hZ]; nlinarith
    have hb : 1 - a = 2 / (z + 1) := by rw [ha]; field_simp; ring
    have hI : 1 + t = (1 + z) ^ 2 / (z ^ 2 + U) := by rw [ht]; field_simp; ring
    have hc : 1 - a * (1 + t) = (1 + U) / (z ^ 2 + U) := by rw [ha, ht]; field_simp; ring
    have htstar : t ≤ (1 - a ^ 2) / (4 + a ^ 2) := by
      have hslack : 1 - a ^ 2 - (4 + a ^ 2) * t = (5 * U - 5 - 6 * z) / (z ^ 2 + U) := by
        rw [ha, ht]
        field_simp
        ring
      have hnonneg : 0 ≤ (5 * U - 5 - 6 * z) / (z ^ 2 + U) :=
        div_nonneg (by linarith only [hU]) hZ.le
      rw [le_div_iff₀ (by positivity : 0 < 4 + a ^ 2)]
      nlinarith only [hslack, hnonneg]
    have hza : (1 + a) / (1 - a) = z := by rw [hb, ha]; field_simp; ring
    have hUrec : 4 / ((1 - a) ^ 2 * (1 + t)) - z ^ 2 = U := by rw [hb, hI]; field_simp; ring
    have hE := fs_normValue_neg ha0 ha1 ht0 ht1
    have hT := fs_normTangent_neg ha0 ha1 ht0 htstar
    have hEv : fs_cf (fs_V0 U z (ff_Phi U z z)) (fs_V1 U z (ff_Phi U z z))
        (z ^ 2 * (z - U) / (z ^ 2 + U)) (z ^ 2 * (1 + z) / (z ^ 2 + U)) z
        (z * (U - z) * (1 + z) / (z ^ 2 + U)) ((1 + z) ^ 2 / (z ^ 2 + U)) < 0 := by
      unfold fs_normValue fs_normValueRat at hE
      dsimp only at hE
      rw [hza, hUrec] at hE
      unfold fs_normRat at hE
      dsimp only at hE
      rw [hc, hb, hI] at hE
      rw [ha, ht] at hE
      convert hE using 1
      simp only [fs_cf, fs_V0, fs_V1]
      rw [fs_Phi_sym hU0 hz0]
      generalize Real.log ((1 + z) ^ 2 / (z ^ 2 + U)) = LI
      generalize Real.log ((1 + U) / (z ^ 2 + U)) = Lc
      field_simp
      ring
    have hTv : fs_cf (fs_V0 U z (ff_Phi U z z)) (fs_V1 U z (ff_Phi U z z))
        (z ^ 2 * (z - U) / (z ^ 2 + U)) (z ^ 2 * (1 + z) / (z ^ 2 + U)) z
        (z * (U - z) * (1 + z) / (z ^ 2 + U)) ((1 + z) ^ 2 / (z ^ 2 + U)) +
        ((1 + z) * (5 * U - 2 - 3 * z) / (3 * (z ^ 2 + U)) - (1 + z) ^ 2 / (z ^ 2 + U)) *
        fs_cf' (fs_V1 U z (ff_Phi U z z)) (z ^ 2 * (z - U) / (z ^ 2 + U))
          (z ^ 2 * (1 + z) / (z ^ 2 + U)) z (z * (U - z) * (1 + z) / (z ^ 2 + U))
          ((1 + z) ^ 2 / (z ^ 2 + U)) < 0 := by
      unfold fs_normTangent fs_normValue fs_normValueRat fs_normSlope at hT
      dsimp only at hT
      rw [hza, hUrec] at hT
      unfold fs_normRat fs_normSlopeRat fs_normSpan at hT
      dsimp only at hT
      rw [hc, hb, hI] at hT
      rw [ha, ht] at hT
      convert hT using 1
      simp only [fs_cf, fs_cf', fs_V0, fs_V1]
      rw [fs_Phi_sym hU0 hz0]
      generalize Real.log ((1 + z) ^ 2 / (z ^ 2 + U)) = LI
      generalize Real.log ((1 + U) / (z ^ 2 + U)) = Lc
      field_simp
      ring
    rcases le_total (fs_cf' (fs_V1 U z (ff_Phi U z z)) (z ^ 2 * (z - U) / (z ^ 2 + U))
          (z ^ 2 * (1 + z) / (z ^ 2 + U)) z (z * (U - z) * (1 + z) / (z ^ 2 + U))
          ((1 + z) ^ 2 / (z ^ 2 + U))) 0 with hD | hD
    · nlinarith
    · nlinarith

end SmoothedOctagon
