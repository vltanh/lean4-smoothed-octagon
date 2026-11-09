module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.EventFactor

/-!
# Case M2, forward successor: monotonicity of the envelope in the incoming norm

The transported norm at `v = 3/4` exceeds `2/3` by a curvature bound and AM--GM.
The ratios `η = p/W`, `β = pW/B` and `m = P_v/B²` then control the normalized derivative
of the envelope numerator. Lowering the transported norm to `2/3` leaves a negative bound.

## Main API

* `nsfPv`, `nsfK0`, `nsfDp`, `nsfD0`, `nsfg`, `nsfNen`, `nsfNd34`, `nsfh1`: the envelope data.
* `nsf_wU_floor`: the transported norm at `v = 3/4` exceeds `2/3`.
* `nsf_norm_derivative_neg`: the numerator's derivative at `v = 3/4` is negative.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `P_v = Y(k/t + Y)`, the `v`-slope of `B²w_U`. -/
noncomputable def nsfPv (t x k : ℝ) : ℝ := x * (x + 2) * (k / t + x * (x + 2))

/-- `K₀ = B²w_U` at `v = 0`. -/
noncomputable def nsfK0 (t x k : ℝ) : ℝ :=
  k ^ 2 - k * t + t ^ 2 + (k / t * (-1 + t ^ 2) + t * (2 - t)) * (x * (x + 2))

/-- `g = 1 - cp/W²`. -/
noncomputable def nsfg (t x : ℝ) : ℝ := 1 - (1 - t) * (t + x) / (1 + x) ^ 2

/-- `D' = B(1 + W/p) + P_v/(pW)`. -/
noncomputable def nsfDp (t x k : ℝ) : ℝ :=
  (k + 2 * t * x + x ^ 2) * (1 + (1 + x) / (t + x)) + nsfPv t x k / ((t + x) * (1 + x))

/-- `D₀ = B(h₁ + v - g)` at `v = 0`. -/
noncomputable def nsfD0 (t x k : ℝ) : ℝ :=
  (k + 2 * t * x + x ^ 2) * ((-(1 - t) + (t + x) ^ 2 / (1 + x)) / (t + x))
    + (nsfK0 t x k - (k + 2 * t * x + x ^ 2) ^ 2) / ((t + x) * (1 + x))
    + (t + x) * (1 + x) - (t + x) ^ 2 - (k + 2 * t * x + x ^ 2) * nsfg t x

/-- `N(v) = 4v(K₀ + vP_v) - (D₀ + D'v)²`. -/
noncomputable def nsfNen (t x k v : ℝ) : ℝ :=
  4 * v * (nsfK0 t x k + v * nsfPv t x k) - (nsfD0 t x k + nsfDp t x k * v) ^ 2

/-- `N'(3/4) = 4K₀ - 2D₀D' + (3/2)(4P_v - D'²)`. -/
noncomputable def nsfNd34 (t x k : ℝ) : ℝ :=
  4 * nsfK0 t x k - 2 * nsfD0 t x k * nsfDp t x k + 3 / 2 * (4 * nsfPv t x k - nsfDp t x k ^ 2)

/-- `h₁ = (Wv - c + p²/W)/p + α + β - p²/B`. -/
noncomputable def nsfh1 (t x k v : ℝ) : ℝ :=
  ((1 + x) * v - (1 - t) + (t + x) ^ 2 / (1 + x)) / (t + x) + nsfAq t x k v + nsfBq t x k
    - (t + x) ^ 2 / (k + 2 * t * x + x ^ 2)

private def nsfNormC (t k : ℝ) := 4 * t * (k ^ 2 - 3 * k * t + 3 * t ^ 2)
private def nsfNormD (t k : ℝ) := 4 * k * t ^ 2 + 3 * k + 12 * t ^ 3 - 24 * t ^ 2
private def nsfNormE (t k : ℝ) := k * (12 * t ^ 2 - 16 * t - 3) - 44 * t ^ 3 + 24 * t ^ 2 + 36 * t

private theorem nsf_norm_taylor_bounds {t k : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 31 / 30) :
    4 / 9 ≤ nsfNormC t k ∧ nsfNormD t k < 7 / 5 ∧ 5 < nsfNormE t k := by
  have ht : 0 < t := by linarith
  have hsum : 0 ≤ t + 1 / 3 := by linarith
  have hsum1 : t + 1 / 3 ≤ 1 := by linarith
  have hsum_sq := mul_nonneg hsum (sub_nonneg.mpr hsum1)
  have hts : 0 ≤ t * (1 / 3) := by positivity
  have hstep : 0 ≤ t - 1 / 3 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hkterm : 0 ≤ 4 * t * (k - 1) * (k + 1 - 3 * t) := by
      apply mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
    have htterm : 0 ≤ 12 * (t - 1 / 3) ^ 3 := by positivity
    dsimp [nsfNormC]
    nlinarith only [hkterm, htterm]
  · have hkterm : 0 ≤ (31 / 30 - k) * (4 * t ^ 2 + 3) := by
      apply mul_nonneg (by linarith) (by positivity)
    have hb : 4 * (31 / 30 : ℝ) * (t + 1 / 3) +
        12 * (t ^ 2 + t / 3 + (1 / 3) ^ 2) - 24 * (t + 1 / 3) ≤ 0 := by
      nlinarith only [hsum_sq, hts, hsum]
    have hdec := mul_nonpos_of_nonneg_of_nonpos hstep hb
    have e : nsfNormD t (31 / 30) - nsfNormD (1 / 3) (31 / 30) = (t - 1 / 3) *
        (4 * (31 / 30) * (t + 1 / 3) + 12 * (t ^ 2 + t / 3 + (1 / 3) ^ 2) - 24 * (t + 1 / 3)) := by
      dsimp [nsfNormD]; ring
    rw [← e] at hdec
    have hinc : nsfNormD t k ≤ nsfNormD t (31 / 30) := by dsimp [nsfNormD]; nlinarith only [hkterm]
    have hend : nsfNormD (1 / 3 : ℝ) (31 / 30) < 7 / 5 := by norm_num [nsfNormD]
    linarith
  · have htpoly : 12 * t ^ 2 - 16 * t - 3 < 0 := by
      have := mul_nonneg ht.le (show 0 ≤ 1 - t by linarith)
      nlinarith
    have hkterm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 31 / 30 - k by linarith) htpoly.le
    have hb : 0 ≤ (31 / 30 : ℝ) * (12 * (t + 1 / 3) - 16) -
        44 * (t ^ 2 + t / 3 + (1 / 3) ^ 2) + 24 * (t + 1 / 3) + 36 := by
      have h1 : 12 * (t + 1 / 3) - 16 ≤ 0 := by linarith
      have h2 := mul_le_mul_of_nonpos_right (show (31 / 30 : ℝ) ≤ 2 by norm_num) h1
      nlinarith only [h2, hsum_sq, hts, hsum]
    have hinc := mul_nonneg hstep hb
    have e : nsfNormE t (31 / 30) - nsfNormE (1 / 3) (31 / 30) = (t - 1 / 3) *
        ((31 / 30) * (12 * (t + 1 / 3) - 16) -
          44 * (t ^ 2 + t / 3 + (1 / 3) ^ 2) + 24 * (t + 1 / 3) + 36) := by
      dsimp [nsfNormE]; ring
    rw [← e] at hinc
    have hdec : nsfNormE t (31 / 30) ≤ nsfNormE t k := by dsimp [nsfNormE]; nlinarith only [hkterm]
    have hend : (5 : ℝ) < nsfNormE (1 / 3) (31 / 30) := by norm_num [nsfNormE]
    linarith

/-- The transported norm at the least incoming norm exceeds `2/3`. The Taylor remainder
is positive, and its quadratic part is positive by AM--GM. -/
theorem nsf_wU_floor {t x k : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hx : 0 ≤ x) (hk0 : 1 ≤ k) (hk1 : k ≤ 31 / 30) : 2 / 3 < nsfwU t x k (3 / 4) := by
  have ht : 0 < t := by linarith
  have hk : 0 < k := by linarith
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  obtain ⟨hC, hD, hE⟩ := nsf_norm_taylor_bounds ht0 ht1 hk0 hk1
  have e : 12 * t * (k + 2 * t * x + x ^ 2) ^ 2 * (nsfwU t x k (3 / 4) - 2 / 3) =
      nsfNormC t k - 2 * nsfNormD t k * x + nsfNormE t k * x ^ 2 + 4 * t * (9 - 8 * t) * x ^ 3 + t * x ^ 4 := by
    unfold nsfwU nsfNormC nsfNormD nsfNormE
    field_simp
    ring
  have hlin : 0 ≤ (7 / 5 - nsfNormD t k) * x := mul_nonneg (by linarith) hx
  have hquad : 0 ≤ (nsfNormE t k - 5) * x ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have htail : 0 ≤ 4 * t * (9 - 8 * t) * x ^ 3 + t * x ^ 4 := by
    have : 0 ≤ 9 - 8 * t := by linarith
    positivity
  have hmin : 0 < (4 / 9 : ℝ) - 14 / 5 * x + 5 * x ^ 2 := by
    nlinarith only [sq_nonneg (x - 7 / 25)]
  have hpos : 0 < 12 * t * (k + 2 * t * x + x ^ 2) ^ 2 * (nsfwU t x k (3 / 4) - 2 / 3) := by
    rw [e]
    nlinarith only [hC, hlin, hquad, htail, hmin]
  exact sub_pos.mp (pos_of_mul_pos_right hpos (by positivity))

private theorem nsf_envelope_ratio_bounds {t x k : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hj0 : 0 ≤ 2 * t + x - 1) (hj1 : 2 * t + x - 1 ≤ 1 / 30)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 31 / 30) :
    1 / 2 ≤ nsfEta t x ∧ nsfEta t x ≤ 19 / 37 ∧
      4 / 7 ≤ nsfBq t x k ∧ nsfBq t x k ≤ 3 / 4 ∧
      0 ≤ nsfPv t x k / (k + 2 * t * x + x ^ 2) ^ 2 ∧
      nsfPv t x k / (k + 2 * t * x + x ^ 2) ^ 2 ≤ 2 := by
  have ht : 0 < t := by linarith
  have hx : 0 < x := by linarith
  have hk : 0 < k := by linarith
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hW : 0 < 1 + x := by positivity
  have hx11 : x ≤ 11 / 30 := by linarith
  have hxSq : x ^ 2 ≤ (11 / 30 : ℝ) ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, by unfold nsfPv; positivity, ?_⟩
  · unfold nsfEta
    rw [le_div_iff₀ hW]
    linarith
  · unfold nsfEta
    rw [div_le_iff₀ hW]
    linarith
  · unfold nsfBq
    rw [le_div_iff₀ hB]
    have h1 : 0 ≤ (1 - t - 3 / 5) * (14 * (1 - t) + 2 / 5) := by
      apply mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (2 * t + x - 1) * (13 * (1 - t) + 3 * (2 * t + x - 1)) := by
      apply mul_nonneg hj0 (by linarith)
    nlinarith only [h1, h2, hk1]
  · unfold nsfBq
    rw [div_le_iff₀ hB]
    have h1 : (4 - 2 * t) * x ≤ (10 / 3 : ℝ) * (11 / 30) := by
      calc _ ≤ (10 / 3 : ℝ) * x := by nlinarith only [mul_nonneg hx.le (show 0 ≤ t - 1 / 3 by linarith)]
           _ ≤ _ := mul_le_mul_of_nonneg_left hx11 (by norm_num)
    nlinarith only [h1, hxSq, ht1, hk0]
  · let θ := x * (x + 2) / (k + 2 * t * x + x ^ 2)
    let κ := k / (t * (k + 2 * t * x + x ^ 2))
    have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
    have hθ : θ < 2 / 3 := by
      dsimp [θ]
      rw [div_lt_iff₀ hB]
      have h1 : (6 - 4 * t) * x ≤ (14 / 3 : ℝ) * (11 / 30) := by
        calc _ ≤ (14 / 3 : ℝ) * x := by nlinarith only [mul_nonneg hx.le (show 0 ≤ t - 1 / 3 by linarith)]
             _ ≤ _ := mul_le_mul_of_nonneg_left hx11 (by norm_num)
      nlinarith only [h1, hxSq, hk0]
    have hκ : κ < 7 / 3 := by
      dsimp [κ]
      rw [div_lt_iff₀ (mul_pos ht hB)]
      have h1 : t * (1 - 2 * t) ≤ t * x * (2 * t + x) := by
        have h2 := mul_le_mul_of_nonneg_left (show 1 - 2 * t ≤ x by linarith) ht.le
        have h3 := mul_le_mul_of_nonneg_left (show 1 ≤ 2 * t + x by linarith) (mul_nonneg ht.le hx.le)
        nlinarith only [h2, h3]
      have h2 := mul_le_mul_of_nonpos_right hk1 (show 7 * t - 3 ≤ 0 by linarith)
      have h3 := mul_nonneg (show 0 ≤ t - 1 / 3 by linarith) (show 0 ≤ 2 / 5 - t by linarith)
      nlinarith only [h1, h2, h3, ht0]
    have hκ0 : 0 ≤ κ := by dsimp [κ]; positivity
    have e : nsfPv t x k / (k + 2 * t * x + x ^ 2) ^ 2 = θ * (κ + θ) := by
      dsimp [θ, κ, nsfPv]
      field_simp
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left (show κ + θ ≤ 3 by linarith) hθ0
    nlinarith only [h1, hθ]

private noncomputable def nsfNormBalance (η β w : ℝ) : ℝ :=
  (w - 1) / β + β * (1 - η) - 1 / (4 * η) + 3 / 4 + 2 * η - η ^ 2

private noncomputable def nsfNormOmega (η β m w : ℝ) : ℝ :=
  4 * w + 3 * m - 2 * nsfNormBalance η β w * (1 + 1 / η + m / β)

private theorem nsf_envelope_omega_neg {η β m w : ℝ} (hη0 : 1 / 2 ≤ η) (hη1 : η ≤ 19 / 37)
    (hβ0 : 4 / 7 ≤ β) (hβ1 : β ≤ 3 / 4) (hm0 : 0 ≤ m) (hm1 : m ≤ 2)
    (hw : 2 / 3 ≤ w) : nsfNormOmega η β m w < -(2 / 19) := by
  have hη : 0 < η := by linarith
  have hβ : 0 < β := by linarith
  have hη2 : η ≤ 2 / 3 := by linarith
  have hηinv : 37 / 19 ≤ 1 / η := by rw [le_div_iff₀ hη]; linarith
  have hβinv : 1 / 3 ≤ 1 / (4 * β) := by rw [le_div_iff₀ (by positivity)]; linarith
  have hβinv2 : 1 / (4 * β) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hbaseline : 1 / 8 < nsfNormBalance η β (2 / 3) - β := by
    have hβstep : 0 ≤ 1 - β / 2 - 1 / (3 * β) - (11 / 84 : ℝ) := by
      have hpos : 0 ≤ (β - 4 / 7) * (7 / (12 * β) - 1 / 2) := by
        apply mul_nonneg (by linarith)
        have : 1 / 2 ≤ 7 / (12 * β) := by rw [le_div_iff₀ (by positivity)]; linarith
        linarith
      have e : (β - 4 / 7) * (7 / (12 * β) - 1 / 2) =
          1 - β / 2 - 1 / (3 * β) - 11 / 84 := by
        field_simp
        ring
      rwa [e] at hpos
    have hηstep : 0 ≤ nsfNormBalance η β (2 / 3) - β - (1 - β / 2 - 1 / (3 * β)) := by
      have hpos : 0 ≤ (η - 1 / 2) * (-β + 1 / (2 * η) + 3 / 2 - η) := by
        apply mul_nonneg (by linarith)
        have : 3 / 4 ≤ 1 / (2 * η) := by rw [le_div_iff₀ (by positivity)]; linarith
        linarith
      have e : (η - 1 / 2) * (-β + 1 / (2 * η) + 3 / 2 - η) =
          nsfNormBalance η β (2 / 3) - β - (1 - β / 2 - 1 / (3 * β)) := by
        unfold nsfNormBalance
        field_simp
        ring
      rwa [e] at hpos
    linarith
  let s := 1 + 1 / η + m / β
  have hs : 0 < s := by dsimp [s]; positivity
  have hsβ : 2 * β < s := by
    have : 0 ≤ m / β := by positivity
    dsimp [s]
    linarith
  have hwdec : nsfNormOmega η β m w ≤ nsfNormOmega η β m (2 / 3) := by
    have hslope : 4 - 2 * s / β < 0 := by rw [sub_neg, lt_div_iff₀ hβ]; linarith
    have hdec := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ w - 2 / 3 by linarith) hslope.le
    have e : nsfNormOmega η β m w - nsfNormOmega η β m (2 / 3) = (w - 2 / 3) * (4 - 2 * s / β) := by
      dsimp [nsfNormOmega, nsfNormBalance, s]
      ring
    rw [← e] at hdec
    linarith
  have hbase_lt : nsfNormOmega η β m (2 / 3) <
      8 / 3 - 2 * (β + 1 / 8) * (1 + 1 / η) + m * (1 - 1 / (4 * β)) := by
    have hprod := mul_lt_mul_of_pos_right (show β + 1 / 8 < nsfNormBalance η β (2 / 3) by linarith) hs
    have e : 8 / 3 - 2 * (β + 1 / 8) * s + 3 * m =
        8 / 3 - 2 * (β + 1 / 8) * (1 + 1 / η) + m * (1 - 1 / (4 * β)) := by
      dsimp [s]
      field_simp
      ring
    unfold nsfNormOmega
    change 4 * (2 / 3) + 3 * m - 2 * nsfNormBalance η β (2 / 3) * s < _
    rw [← e]
    linarith
  have hprod : (4 / 7 + 1 / 8 : ℝ) * (56 / 19) ≤ (β + 1 / 8) * (1 + 1 / η) := by
    exact mul_le_mul (by linarith) (by linarith) (by norm_num) (by linarith)
  have hm : m * (1 - 1 / (4 * β)) ≤ 4 / 3 := by
    have h1 := mul_le_mul_of_nonneg_left (show 1 - 1 / (4 * β) ≤ 2 / 3 by linarith) hm0
    nlinarith only [h1, hm1]
  linarith

/-- The envelope numerator decreases at `v = 3/4`: its normalized derivative is bounded
above by `-2/19` using the transported-norm floor and the geometric ratios. -/
theorem nsf_norm_derivative_neg {t x k : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5)
    (hj0 : 0 ≤ 2 * t + x - 1) (hj1 : 2 * t + x - 1 ≤ 1 / 30)
    (hk0 : 1 ≤ k) (hk1 : k ≤ 31 / 30) : nsfNd34 t x k < 0 := by
  have ht : 0 < t := by linarith
  have hx : 0 < x := by linarith
  have hk : 0 < k := by linarith
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hW : 0 < 1 + x := by positivity
  have hp : 0 < t + x := by positivity
  obtain ⟨hη0, hη1, hβ0, hβ1, hm0, hm1⟩ := nsf_envelope_ratio_bounds ht0 ht1 hj0 hj1 hk0 hk1
  have hw := nsf_wU_floor ht0 ht1 hx.le hk0 hk1
  have hω := nsf_envelope_omega_neg hη0 hη1 hβ0 hβ1 hm0 hm1 hw.le
  have e : nsfNd34 t x k / (k + 2 * t * x + x ^ 2) ^ 2 =
      nsfNormOmega (nsfEta t x) (nsfBq t x k)
        (nsfPv t x k / (k + 2 * t * x + x ^ 2) ^ 2) (nsfwU t x k (3 / 4)) := by
    unfold nsfNormOmega nsfNormBalance nsfEta nsfBq nsfNd34 nsfD0 nsfDp nsfK0 nsfPv nsfg nsfwU
    field_simp
    ring
  rw [← e] at hω
  have hneg : nsfNd34 t x k / (k + 2 * t * x + x ^ 2) ^ 2 < 0 := lt_trans hω (by norm_num)
  exact neg_of_div_neg_left hneg (sq_nonneg _)

end SmoothedOctagon
