module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.QElim
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.CertEn
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.CertPn

/-!
# Case M2, forward successor by hand: the envelope Casimir sign

On `1/3 ≤ t ≤ 2/5`, `0 ≤ j ≤ 1/30`,
`1 ≤ k ≤ 31/30` and `3/4 ≤ v ≤ V`,
`𝒢 = B²{4vw_U - [h₁ + v - g]²}/(16s²) > 9193/50000` (`fh_envelope`).

`N(v) = B²{4vw_U - [h₁ + v - g]²} = 4v(K₀ + vP_v) - (D₀ + D'v)²` (`fh_Nen_eq`) is a quadratic in `v`
with `N'' = 2(4P_v - D'²) < 0` (`fh_Nen_concave`, arithmetic-geometric mean) and `N'(3/4) < 0`
(certificate `CertEn`), so `N(v) ≥ N(V)`; and `N(V) > 16s²·9193/50000` (certificate `CertPn`).
These two coefficient-domination bounds are generated Bernstein certificates.

## Main API

* `fhPv`, `fhK0`, `fhDp`, `fhD0`, `fhg`, `fhNen`, `fhNd34`, `fhh1`; `fh_Nen_eq`; `fh_En_link`,
  `fh_Pn_link`; `fh_envelope`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `P_v = Y(k/t + Y)`, the `v`-slope of `B²w_U`. -/
noncomputable def fhPv (t x k : ℝ) : ℝ := x * (x + 2) * (k / t + x * (x + 2))

/-- `K₀ = B²w_U` at `v = 0`. -/
noncomputable def fhK0 (t x k : ℝ) : ℝ :=
  k ^ 2 - k * t + t ^ 2 + (k / t * (-1 + t ^ 2) + t * (2 - t)) * (x * (x + 2))

/-- `g = 1 - cp/W²`. -/
noncomputable def fhg (t x : ℝ) : ℝ := 1 - (1 - t) * (t + x) / (1 + x) ^ 2

/-- `D' = B(1 + W/p) + P_v/(pW)`. -/
noncomputable def fhDp (t x k : ℝ) : ℝ :=
  (k + 2 * t * x + x ^ 2) * (1 + (1 + x) / (t + x)) + fhPv t x k / ((t + x) * (1 + x))

/-- `D₀ = B(h₁ + v - g)` at `v = 0`. -/
noncomputable def fhD0 (t x k : ℝ) : ℝ :=
  (k + 2 * t * x + x ^ 2) * ((-(1 - t) + (t + x) ^ 2 / (1 + x)) / (t + x))
    + (fhK0 t x k - (k + 2 * t * x + x ^ 2) ^ 2) / ((t + x) * (1 + x))
    + (t + x) * (1 + x) - (t + x) ^ 2 - (k + 2 * t * x + x ^ 2) * fhg t x

/-- `N(v) = 4v(K₀ + vP_v) - (D₀ + D'v)²`. -/
noncomputable def fhNen (t x k v : ℝ) : ℝ :=
  4 * v * (fhK0 t x k + v * fhPv t x k) - (fhD0 t x k + fhDp t x k * v) ^ 2

/-- `N'(3/4) = 4K₀ - 2D₀D' + (3/2)(4P_v - D'²)`. -/
noncomputable def fhNd34 (t x k : ℝ) : ℝ :=
  4 * fhK0 t x k - 2 * fhD0 t x k * fhDp t x k + 3 / 2 * (4 * fhPv t x k - fhDp t x k ^ 2)

/-- `h₁ = (Wv - c + p²/W)/p + α + β - p²/B`. -/
noncomputable def fhh1 (t x k v : ℝ) : ℝ :=
  ((1 + x) * v - (1 - t) + (t + x) ^ 2 / (1 + x)) / (t + x) + fhAq t x k v + fhBq t x k
    - (t + x) ^ 2 / (k + 2 * t * x + x ^ 2)

/-- `B²{4vw_U - [h₁ + v - g]²} = N(v)`. -/
theorem fh_Nen_eq {t x k v : ℝ} (ht : 0 < t) (hx : 0 < x) (hk : 0 < k) :
    (k + 2 * t * x + x ^ 2) ^ 2 * (4 * v * fhwU t x k v - (fhh1 t x k v + v - fhg t x) ^ 2) =
      fhNen t x k v := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hW : (1 + x) ≠ 0 := by linarith
  have hp : t + x ≠ 0 := by linarith
  have ha : (k + 2 * t * x + x ^ 2) ^ 2 * fhwU t x k v = fhK0 t x k + v * fhPv t x k := by
    unfold fhwU fhK0 fhPv; field_simp; ring
  have hb : (k + 2 * t * x + x ^ 2) * (fhh1 t x k v + v - fhg t x) = fhD0 t x k + fhDp t x k * v := by
    have hA : fhAq t x k v = ((k + 2 * t * x + x ^ 2) ^ 2 * fhwU t x k v - (k + 2 * t * x + x ^ 2) ^ 2) /
        ((k + 2 * t * x + x ^ 2) * ((t + x) * (1 + x))) := by
      unfold fhAq; field_simp
    rw [fhh1, hA, ha]
    unfold fhBq fhD0 fhDp
    field_simp
    ring
  have e : (k + 2 * t * x + x ^ 2) ^ 2 * (4 * v * fhwU t x k v - (fhh1 t x k v + v - fhg t x) ^ 2) =
      4 * v * ((k + 2 * t * x + x ^ 2) ^ 2 * fhwU t x k v) -
        ((k + 2 * t * x + x ^ 2) * (fhh1 t x k v + v - fhg t x)) ^ 2 := by ring
  rw [e, ha, hb]
  unfold fhNen
  ring

/-- The cleared norm derivative `-2t²p²W³N'(3/4)` is the certificate polynomial `fhCEn`. -/
theorem fh_En_link (t x k : ℝ) (ht : 0 < t) (hx : 0 < x) :
    2 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 3 * (-fhNd34 t x k) =
      (fhCEnD0_0 (2 / 5 - t) + fhCEnD0_1 (2 / 5 - t) * (2 * t + x - 1) + fhCEnD0_2 (2 / 5 - t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCEnD0_3 (2 / 5 - t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCEnD0_4 (2 / 5 - t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCEnD0_5 (2 / 5 - t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCEnD0_6 (2 / 5 - t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCEnD0_7 (2 / 5 - t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCEnD0_8 (2 / 5 - t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCEnD0_9 (2 / 5 - t) * (2 * t + x - 1) ^ (9 : ℕ)) + (fhCEnD1_0 (2 / 5 - t) + fhCEnD1_1 (2 / 5 - t) * (2 * t + x - 1) + fhCEnD1_2 (2 / 5 - t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCEnD1_3 (2 / 5 - t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCEnD1_4 (2 / 5 - t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCEnD1_5 (2 / 5 - t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCEnD1_6 (2 / 5 - t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCEnD1_7 (2 / 5 - t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCEnD1_8 (2 / 5 - t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCEnD1_9 (2 / 5 - t) * (2 * t + x - 1) ^ (9 : ℕ)) * (k - 1) + (fhCEnD2_0 (2 / 5 - t) + fhCEnD2_1 (2 / 5 - t) * (2 * t + x - 1) + fhCEnD2_2 (2 / 5 - t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCEnD2_3 (2 / 5 - t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCEnD2_4 (2 / 5 - t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCEnD2_5 (2 / 5 - t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCEnD2_6 (2 / 5 - t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCEnD2_7 (2 / 5 - t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCEnD2_8 (2 / 5 - t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCEnD2_9 (2 / 5 - t) * (2 * t + x - 1) ^ (9 : ℕ)) * (k - 1) ^ (2 : ℕ) := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hp : t + x ≠ 0 := by linarith
  have ht' : t ≠ 0 := by linarith
  unfold fhCEnD0_0 fhCEnD0_1 fhCEnD0_2 fhCEnD0_3 fhCEnD0_4 fhCEnD0_5 fhCEnD0_6 fhCEnD0_7 fhCEnD0_8 fhCEnD0_9 fhCEnD1_0 fhCEnD1_1 fhCEnD1_2 fhCEnD1_3 fhCEnD1_4 fhCEnD1_5 fhCEnD1_6 fhCEnD1_7 fhCEnD1_8 fhCEnD1_9 fhCEnD2_0 fhCEnD2_1 fhCEnD2_2 fhCEnD2_3 fhCEnD2_4 fhCEnD2_5 fhCEnD2_6 fhCEnD2_7 fhCEnD2_8 fhCEnD2_9
  unfold fhNd34 fhD0 fhDp fhK0 fhPv fhg
  field_simp
  ring

/-- The cleared Casimir excess at `v = V` is the certificate polynomial `fhCPn`. -/
theorem fh_Pn_link (t x k : ℝ) (ht : 0 < t) (hx : 0 < x) :
    3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (fhNen t x k (fhVq t x) - 16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) =
      (fhCPnD0_0 (2 / 5 - t) + fhCPnD0_1 (2 / 5 - t) * (2 * t + x - 1) + fhCPnD0_2 (2 / 5 - t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCPnD0_3 (2 / 5 - t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCPnD0_4 (2 / 5 - t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCPnD0_5 (2 / 5 - t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCPnD0_6 (2 / 5 - t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCPnD0_7 (2 / 5 - t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCPnD0_8 (2 / 5 - t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCPnD0_9 (2 / 5 - t) * (2 * t + x - 1) ^ (9 : ℕ) + fhCPnD0_10 (2 / 5 - t) * (2 * t + x - 1) ^ (10 : ℕ) + fhCPnD0_11 (2 / 5 - t) * (2 * t + x - 1) ^ (11 : ℕ) + fhCPnD0_12 (2 / 5 - t) * (2 * t + x - 1) ^ (12 : ℕ) + fhCPnD0_13 (2 / 5 - t) * (2 * t + x - 1) ^ (13 : ℕ)) + (fhCPnD1_0 (2 / 5 - t) + fhCPnD1_1 (2 / 5 - t) * (2 * t + x - 1) + fhCPnD1_2 (2 / 5 - t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCPnD1_3 (2 / 5 - t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCPnD1_4 (2 / 5 - t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCPnD1_5 (2 / 5 - t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCPnD1_6 (2 / 5 - t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCPnD1_7 (2 / 5 - t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCPnD1_8 (2 / 5 - t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCPnD1_9 (2 / 5 - t) * (2 * t + x - 1) ^ (9 : ℕ) + fhCPnD1_10 (2 / 5 - t) * (2 * t + x - 1) ^ (10 : ℕ) + fhCPnD1_11 (2 / 5 - t) * (2 * t + x - 1) ^ (11 : ℕ) + fhCPnD1_12 (2 / 5 - t) * (2 * t + x - 1) ^ (12 : ℕ) + fhCPnD1_13 (2 / 5 - t) * (2 * t + x - 1) ^ (13 : ℕ)) * (k - 1) + (fhCPnD2_0 (2 / 5 - t) + fhCPnD2_1 (2 / 5 - t) * (2 * t + x - 1) + fhCPnD2_2 (2 / 5 - t) * (2 * t + x - 1) ^ (2 : ℕ) + fhCPnD2_3 (2 / 5 - t) * (2 * t + x - 1) ^ (3 : ℕ) + fhCPnD2_4 (2 / 5 - t) * (2 * t + x - 1) ^ (4 : ℕ) + fhCPnD2_5 (2 / 5 - t) * (2 * t + x - 1) ^ (5 : ℕ) + fhCPnD2_6 (2 / 5 - t) * (2 * t + x - 1) ^ (6 : ℕ) + fhCPnD2_7 (2 / 5 - t) * (2 * t + x - 1) ^ (7 : ℕ) + fhCPnD2_8 (2 / 5 - t) * (2 * t + x - 1) ^ (8 : ℕ) + fhCPnD2_9 (2 / 5 - t) * (2 * t + x - 1) ^ (9 : ℕ) + fhCPnD2_10 (2 / 5 - t) * (2 * t + x - 1) ^ (10 : ℕ) + fhCPnD2_11 (2 / 5 - t) * (2 * t + x - 1) ^ (11 : ℕ) + fhCPnD2_12 (2 / 5 - t) * (2 * t + x - 1) ^ (12 : ℕ) + fhCPnD2_13 (2 / 5 - t) * (2 * t + x - 1) ^ (13 : ℕ)) * (k - 1) ^ (2 : ℕ) := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hp : t + x ≠ 0 := by linarith
  have ht' : t ≠ 0 := by linarith
  have hQ : x ^ 2 + 6 * x + 6 ≠ 0 := by positivity
  have hNV : (1 + x) * (x ^ 2 + 6 * x + 6) * fhVq t x = 6 + 9 * x + 5 * x ^ (2 : ℕ) + x ^ (3 : ℕ) - 6 * t - 3 * t * x + t * x ^ (2 : ℕ) + 6 * t ^ (2 : ℕ) + 6 * t ^ (2 : ℕ) * x + t ^ (2 : ℕ) * x ^ (2 : ℕ) := by
    unfold fhVq; field_simp; ring
  have hNK : t * fhK0 t x k = -2 * x * k - x ^ (2 : ℕ) * k + t * k ^ (2 : ℕ) - t ^ (2 : ℕ) * k + 4 * t ^ (2 : ℕ) * x + 2 * t ^ (2 : ℕ) * x * k + 2 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + t ^ (2 : ℕ) * x ^ (2 : ℕ) * k + t ^ (3 : ℕ) - 2 * t ^ (3 : ℕ) * x - t ^ (3 : ℕ) * x ^ (2 : ℕ) := by
    unfold fhK0; field_simp; ring
  have hNP : t * fhPv t x k = 2 * x * k + x ^ (2 : ℕ) * k + 4 * t * x ^ (2 : ℕ) + 4 * t * x ^ (3 : ℕ) + t * x ^ (4 : ℕ) := by
    unfold fhPv; field_simp; ring
  have hND0 : t * (t + x) * (1 + x) ^ 2 * fhD0 t x k = -2 * x * k - 3 * x ^ (2 : ℕ) * k - x ^ (3 : ℕ) * k - t * k - 3 * t * x * k - 3 * t * x ^ (2 : ℕ) * k - t * x ^ (3 : ℕ) - 2 * t * x ^ (3 : ℕ) * k - t * x ^ (4 : ℕ) - t * x ^ (5 : ℕ) - t ^ (2 : ℕ) * k + 4 * t ^ (2 : ℕ) * x + t ^ (2 : ℕ) * x * k + 3 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + t ^ (2 : ℕ) * x ^ (3 : ℕ) * k - 4 * t ^ (2 : ℕ) * x ^ (4 : ℕ) + 2 * t ^ (3 : ℕ) + 2 * t ^ (3 : ℕ) * k - t ^ (3 : ℕ) * x - t ^ (3 : ℕ) * x * k - 6 * t ^ (3 : ℕ) * x ^ (3 : ℕ) - t ^ (4 : ℕ) - t ^ (4 : ℕ) * k + 2 * t ^ (4 : ℕ) * x - 4 * t ^ (4 : ℕ) * x ^ (2 : ℕ) - 2 * t ^ (5 : ℕ) * x := by
    unfold fhD0 fhK0 fhg; field_simp; ring
  have hNDp : t * (t + x) * (1 + x) * fhDp t x k = 2 * x * k + x ^ (2 : ℕ) * k + t * k + 3 * t * x * k + 5 * t * x ^ (2 : ℕ) + 2 * t * x ^ (2 : ℕ) * k + 7 * t * x ^ (3 : ℕ) + 3 * t * x ^ (4 : ℕ) + t ^ (2 : ℕ) * k + 2 * t ^ (2 : ℕ) * x + t ^ (2 : ℕ) * x * k + 7 * t ^ (2 : ℕ) * x ^ (2 : ℕ) + 5 * t ^ (2 : ℕ) * x ^ (3 : ℕ) + 2 * t ^ (3 : ℕ) * x + 2 * t ^ (3 : ℕ) * x ^ (2 : ℕ) := by
    unfold fhDp fhPv; field_simp; ring
  have e : 3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (fhNen t x k (fhVq t x) - 16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) =
      3125 * (4 * ((1 + x) * (x ^ 2 + 6 * x + 6) * fhVq t x) * (t * fhK0 t x k) * (t * (t + x) ^ 2 * (1 + x) ^ 3 * (x ^ 2 + 6 * x + 6))
        + 4 * ((1 + x) * (x ^ 2 + 6 * x + 6) * fhVq t x) ^ 2 * (t * fhPv t x k) * (t * (t + x) ^ 2 * (1 + x) ^ 2)
        - ((x ^ 2 + 6 * x + 6) * (t * (t + x) * (1 + x) ^ 2 * fhD0 t x k)
          + (t * (t + x) * (1 + x) * fhDp t x k) * ((1 + x) * (x ^ 2 + 6 * x + 6) * fhVq t x)) ^ 2)
      - 3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) := by
    unfold fhNen; ring
  rw [e, hNV, hNK, hNP, hND0, hNDp]
  unfold fhCPnD0_0 fhCPnD0_1 fhCPnD0_2 fhCPnD0_3 fhCPnD0_4 fhCPnD0_5 fhCPnD0_6 fhCPnD0_7 fhCPnD0_8 fhCPnD0_9 fhCPnD0_10 fhCPnD0_11 fhCPnD0_12 fhCPnD0_13 fhCPnD1_0 fhCPnD1_1 fhCPnD1_2 fhCPnD1_3 fhCPnD1_4 fhCPnD1_5 fhCPnD1_6 fhCPnD1_7 fhCPnD1_8 fhCPnD1_9 fhCPnD1_10 fhCPnD1_11 fhCPnD1_12 fhCPnD1_13 fhCPnD2_0 fhCPnD2_1 fhCPnD2_2 fhCPnD2_3 fhCPnD2_4 fhCPnD2_5 fhCPnD2_6 fhCPnD2_7 fhCPnD2_8 fhCPnD2_9 fhCPnD2_10 fhCPnD2_11 fhCPnD2_12 fhCPnD2_13
  ring

/-- **Concavity in the incoming norm**: `4P_v < D'²` (arithmetic-geometric mean, `B > p²`). -/
theorem fh_Nen_concave {t x k : ℝ} (ht : 0 < t) (hx : 0 < x) (hk : t ^ 2 < k) :
    4 * fhPv t x k < fhDp t x k ^ 2 := by
  have hp : 0 < t + x := by linarith
  have hW : 0 < 1 + x := by linarith
  have hB : (t + x) ^ 2 < k + 2 * t * x + x ^ 2 := by nlinarith
  have hk0 : 0 < k := by nlinarith
  have hPv : 0 < fhPv t x k := by unfold fhPv; positivity
  set a := (k + 2 * t * x + x ^ 2) * (1 + (1 + x) / (t + x))
  set b := fhPv t x k / ((t + x) * (1 + x))
  have hDp : fhDp t x k = a + b := rfl
  have hab : (t + x) * (1 + x) < a := by
    have : (t + x) * (1 + x) < (t + x) ^ 2 * (1 + (1 + x) / (t + x)) := by
      have e : (t + x) ^ 2 * (1 + (1 + x) / (t + x)) = (t + x) ^ 2 + (t + x) * (1 + x) := by
        field_simp
      rw [e]; nlinarith
    have h2 : (t + x) ^ 2 * (1 + (1 + x) / (t + x)) ≤ a :=
      mul_le_mul_of_nonneg_right hB.le (by positivity)
    linarith
  have hb : b * ((t + x) * (1 + x)) = fhPv t x k := by
    simp only [b]; field_simp
  rw [hDp]
  nlinarith [sq_nonneg (a - b), mul_lt_mul_of_pos_left hab (by positivity : (0 : ℝ) < b)]

/-- **The envelope Casimir sign**: `𝒢 > 9193/50000` for `1/3 ≤ t ≤ 2/5`, `0 ≤ j ≤ 1/30`,
`1 ≤ k ≤ 31/30` and `3/4 ≤ v ≤ V`. -/
theorem fh_envelope {t x k v : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj0 : 0 ≤ 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk0 : 1 ≤ k) (hk1 : k ≤ 31 / 30) (hv0 : 3 / 4 ≤ v)
    (hvV : v ≤ fhVq t x) :
    9193 / 50000 < (k + 2 * t * x + x ^ 2) ^ 2 *
      (4 * v * fhwU t x k v - (fhh1 t x k v + v - fhg t x) ^ 2) / (16 * (k - t ^ 2) ^ 2) := by
  have ht : 0 < t := by linarith
  have hx : 0 < x := by linarith
  have hk : 0 < k := by linarith
  have hkt : t ^ 2 < k := by nlinarith
  rw [fh_Nen_eq ht hx hk]
  -- `N'(3/4) < 0` and `N(V) > 16s² · cap`
  have hE : fhNd34 t x k < 0 := by
    have h := fhCEn_pos (2 / 5 - t) (2 * t + x - 1) (k - 1) (by linarith) (by linarith) hj0 hj1
      (by linarith) (by linarith)
    rw [← fh_En_link t x k ht hx] at h
    have : 0 < -fhNd34 t x k := pos_of_mul_pos_right h (by positivity)
    linarith
  have hP : 16 * (k - t ^ 2) ^ 2 * (9193 / 50000) < fhNen t x k (fhVq t x) := by
    have h := fhCPn_pos (2 / 5 - t) (2 * t + x - 1) (k - 1) (by linarith) (by linarith) hj0 hj1
      (by linarith) (by linarith)
    rw [← fh_Pn_link t x k ht hx] at h
    have : 0 < fhNen t x k (fhVq t x) - 16 * (k - t ^ 2) ^ 2 * (9193 / 50000) :=
      pos_of_mul_pos_right h (by positivity)
    linarith
  -- concavity: `N(v) ≥ N(V)`
  have hc := fh_Nen_concave ht hx hkt
  have e : fhNen t x k v - fhNen t x k (fhVq t x) = (fhVq t x - v) *
      (-fhNd34 t x k - (4 * fhPv t x k - fhDp t x k ^ 2) * (v + fhVq t x - 3 / 2)) := by
    unfold fhNen fhNd34; ring
  have hN : fhNen t x k (fhVq t x) ≤ fhNen t x k v := by
    have : 0 ≤ (fhVq t x - v) * (-fhNd34 t x k - (4 * fhPv t x k - fhDp t x k ^ 2) * (v + fhVq t x - 3 / 2)) := by
      apply mul_nonneg (by linarith)
      have : 0 ≤ -(4 * fhPv t x k - fhDp t x k ^ 2) * (v + fhVq t x - 3 / 2) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    linarith
  have hkt' : 0 < k - t ^ 2 := by linarith
  have hs : 0 < 16 * (k - t ^ 2) ^ 2 := by positivity
  rw [lt_div_iff₀ hs]
  linarith

end SmoothedOctagon
