module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.NormDerivative
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.EnvelopeBound

/-!
# Case M2, forward successor: the envelope Casimir sign

On `1/3 ≤ t ≤ 2/5`, `0 ≤ j ≤ 1/30`,
`1 ≤ k ≤ 31/30` and `3/4 ≤ v ≤ V`,
`𝒢 = B²{4vw_U - [h₁ + v - g]²}/(16s²) > 3/16 - (1 - 2t)²/32` (`nsf_envelope`).

`N(v) = B²{4vw_U - [h₁ + v - g]²} = 4v(K₀ + vP_v) - (D₀ + D'v)²` (`nsf_Nen_eq`) is a quadratic in `v`
with `N'' = 2(4P_v - D'²) < 0` (`nsf_Nen_concave`, arithmetic-geometric mean) and `N'(3/4) < 0`
(`nsf_norm_derivative_neg`, the transported-norm floor and geometric ratios), so `N(v) ≥ N(V)`.
At the endpoint, the order imbalance controls the loss from `3/16`
(`nsf_envelope_imbalance`).

## Main API

* `nsf_Nen_eq`, `nsf_Nen_concave`, `nsf_envelope`.
* The envelope data and derivative sign are in `SmallGap/NormDerivative`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `B²{4vw_U - [h₁ + v - g]²} = N(v)`. -/
theorem nsf_Nen_eq {t x k v : ℝ} (ht : 0 < t) (hx : 0 < x) (hk : 0 < k) :
    (k + 2 * t * x + x ^ 2) ^ 2 * (4 * v * nsfwU t x k v - (nsfh1 t x k v + v - nsfg t x) ^ 2) =
      nsfNen t x k v := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hW : (1 + x) ≠ 0 := by linarith
  have hp : t + x ≠ 0 := by linarith
  have ha : (k + 2 * t * x + x ^ 2) ^ 2 * nsfwU t x k v = nsfK0 t x k + v * nsfPv t x k := by
    unfold nsfwU nsfK0 nsfPv; field_simp; ring
  have hb : (k + 2 * t * x + x ^ 2) * (nsfh1 t x k v + v - nsfg t x) = nsfD0 t x k + nsfDp t x k * v := by
    have hA : nsfAq t x k v = ((k + 2 * t * x + x ^ 2) ^ 2 * nsfwU t x k v - (k + 2 * t * x + x ^ 2) ^ 2) /
        ((k + 2 * t * x + x ^ 2) * ((t + x) * (1 + x))) := by
      unfold nsfAq; field_simp
    rw [nsfh1, hA, ha]
    unfold nsfBq nsfD0 nsfDp
    field_simp
    ring
  have e : (k + 2 * t * x + x ^ 2) ^ 2 * (4 * v * nsfwU t x k v - (nsfh1 t x k v + v - nsfg t x) ^ 2) =
      4 * v * ((k + 2 * t * x + x ^ 2) ^ 2 * nsfwU t x k v) -
        ((k + 2 * t * x + x ^ 2) * (nsfh1 t x k v + v - nsfg t x)) ^ 2 := by ring
  rw [e, ha, hb]
  unfold nsfNen
  ring

/-- **Concavity in the incoming norm**: `4P_v < D'²` (arithmetic-geometric mean, `B > p²`). -/
theorem nsf_Nen_concave {t x k : ℝ} (ht : 0 < t) (hx : 0 < x) (hk : t ^ 2 < k) :
    4 * nsfPv t x k < nsfDp t x k ^ 2 := by
  have hp : 0 < t + x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hB : (t + x) ^ 2 < k + 2 * t * x + x ^ 2 := by nlinarith
  have hk0 : 0 < k := by nlinarith
  have hPv : 0 < nsfPv t x k := by unfold nsfPv; positivity
  set a := (k + 2 * t * x + x ^ 2) * (1 + (1 + x) / (t + x))
  set b := nsfPv t x k / ((t + x) * (1 + x))
  have hDp : nsfDp t x k = a + b := rfl
  have hab : (t + x) * (1 + x) < a := by
    have : (t + x) * (1 + x) < (t + x) ^ 2 * (1 + (1 + x) / (t + x)) := by
      have e : (t + x) ^ 2 * (1 + (1 + x) / (t + x)) = (t + x) ^ 2 + (t + x) * (1 + x) := by
        field_simp
      rw [e]; nlinarith
    have h2 : (t + x) ^ 2 * (1 + (1 + x) / (t + x)) ≤ a :=
      mul_le_mul_of_nonneg_right hB.le (by positivity)
    linarith
  have hb : b * ((t + x) * (1 + x)) = nsfPv t x k := by
    simp only [b]; field_simp
  rw [hDp]
  nlinarith [sq_nonneg (a - b), mul_lt_mul_of_pos_left hab (by positivity : (0 : ℝ) < b)]

/-- **The envelope Casimir bound**: `𝒢 > 3/16 - (1 - 2t)²/32` for `1/3 ≤ t ≤ 2/5`, `0 ≤ j ≤ 1/30`,
`1 ≤ k ≤ 31/30` and `3/4 ≤ v ≤ V`. -/
theorem nsf_envelope {t x k v : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj0 : 0 ≤ 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk0 : 1 ≤ k) (hk1 : k ≤ 31 / 30) (hv0 : 3 / 4 ≤ v)
    (hvV : v ≤ nsfVq t x) :
    3 / 16 - (1 - 2 * t) ^ 2 / 32 < (k + 2 * t * x + x ^ 2) ^ 2 *
      (4 * v * nsfwU t x k v - (nsfh1 t x k v + v - nsfg t x) ^ 2) / (16 * (k - t ^ 2) ^ 2) := by
  have ht : 0 < t := by linarith
  have hx : 0 < x := by linarith
  have hk : 0 < k := by linarith
  have hkt : t ^ 2 < k := by nlinarith
  rw [nsf_Nen_eq ht hx hk]
  have hE := nsf_norm_derivative_neg ht0 ht1 hj0 hj1 hk0 hk1
  have hP := nsf_envelope_imbalance ht0 ht1 hj0 hj1 hk0
    (show k ≤ 3 / 2 by linarith only [hk1])
  -- concavity: `N(v) ≥ N(V)`
  have hc := nsf_Nen_concave ht hx hkt
  have e : nsfNen t x k v - nsfNen t x k (nsfVq t x) = (nsfVq t x - v) *
      (-nsfNd34 t x k - (4 * nsfPv t x k - nsfDp t x k ^ 2) * (v + nsfVq t x - 3 / 2)) := by
    unfold nsfNen nsfNd34; ring
  have hN : nsfNen t x k (nsfVq t x) ≤ nsfNen t x k v := by
    have : 0 ≤ (nsfVq t x - v) * (-nsfNd34 t x k - (4 * nsfPv t x k - nsfDp t x k ^ 2) * (v + nsfVq t x - 3 / 2)) := by
      apply mul_nonneg (by linarith)
      have : 0 ≤ -(4 * nsfPv t x k - nsfDp t x k ^ 2) * (v + nsfVq t x - 3 / 2) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    linarith
  have hkt' : 0 < k - t ^ 2 := by linarith
  have hs : 0 < 16 * (k - t ^ 2) ^ 2 := by positivity
  exact hP.trans_le (div_le_div_of_nonneg_right hN hs.le)

end SmoothedOctagon
