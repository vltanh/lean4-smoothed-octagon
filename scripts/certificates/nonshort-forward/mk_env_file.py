from links import *
LEAN=__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '../../../SmoothedOctagon/Exclusion/Mixed/Nonshort/Forward/')
pre = "  have hW : (1 + x) ≠ 0 := by linarith\n  have hp : t + x ≠ 0 := by linarith\n  have ht' : t ≠ 0 := by linarith\n"
lE = link2('nsfCEn', 'nsf_En_link', '(t x k : ℝ)', '(ht : 0 < t) (hx : 0 < x)',
  "2 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 3 * (-nsfNd34 t x k)",
  yform_sub('nsfCEn', "(2 / 5 - t)", "(2 * t + x - 1)", "(k - 1)", var='z'),
  'nsfNd34 nsfD0 nsfDp nsfK0 nsfPv nsfg', 'The cleared norm derivative `-2t²p²W³N\'(3/4)` is the certificate polynomial `nsfCEn`.', pre=pre)
import json as _json
N2 = _json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'nums2.json')))
_rhsP = yform_sub('nsfCPn', "(2 / 5 - t)", "(2 * t + x - 1)", "(k - 1)", var='z')
_DP = " ".join(Dnames('nsfCPn'))
lP = f"""/-- The cleared Casimir excess at `v = V` is the certificate polynomial `nsfCPn`. -/
theorem nsf_Pn_link (t x k : ℝ) (ht : 0 < t) (hx : 0 < x) :
    3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (nsfNen t x k (nsfVq t x) - 16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) =
      {_rhsP} := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hp : t + x ≠ 0 := by linarith
  have ht' : t ≠ 0 := by linarith
  have hQ : x ^ 2 + 6 * x + 6 ≠ 0 := by positivity
  have hNV : (1 + x) * (x ^ 2 + 6 * x + 6) * nsfVq t x = {N2['NV']} := by
    unfold nsfVq; field_simp; ring
  have hNK : t * nsfK0 t x k = {N2['NK']} := by
    unfold nsfK0; field_simp; ring
  have hNP : t * nsfPv t x k = {N2['NP']} := by
    unfold nsfPv; field_simp; ring
  have hND0 : t * (t + x) * (1 + x) ^ 2 * nsfD0 t x k = {N2['ND0']} := by
    unfold nsfD0 nsfK0 nsfg; field_simp; ring
  have hNDp : t * (t + x) * (1 + x) * nsfDp t x k = {N2['NDp']} := by
    unfold nsfDp nsfPv; field_simp; ring
  have e : 3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (nsfNen t x k (nsfVq t x) - 16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) =
      3125 * (4 * ((1 + x) * (x ^ 2 + 6 * x + 6) * nsfVq t x) * (t * nsfK0 t x k) * (t * (t + x) ^ 2 * (1 + x) ^ 3 * (x ^ 2 + 6 * x + 6))
        + 4 * ((1 + x) * (x ^ 2 + 6 * x + 6) * nsfVq t x) ^ 2 * (t * nsfPv t x k) * (t * (t + x) ^ 2 * (1 + x) ^ 2)
        - ((x ^ 2 + 6 * x + 6) * (t * (t + x) * (1 + x) ^ 2 * nsfD0 t x k)
          + (t * (t + x) * (1 + x) * nsfDp t x k) * ((1 + x) * (x ^ 2 + 6 * x + 6) * nsfVq t x)) ^ 2)
      - 3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) := by
    unfold nsfNen; ring
  rw [e, hNV, hNK, hNP, hND0, hNDp]
  unfold {_DP}
  ring
"""
s = '''module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.EventFactor
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.NormDerivativeSigns
public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.SmallGap.CasimirExcessSigns

/-!
# Case M2, forward successor: the envelope Casimir sign

On `1/3 ≤ t ≤ 2/5`, `0 ≤ j ≤ 1/30`,
`1 ≤ k ≤ 31/30` and `3/4 ≤ v ≤ V`,
`𝒢 = B²{4vw_U - [h₁ + v - g]²}/(16s²) > 9193/50000` (`nsf_envelope`).

`N(v) = B²{4vw_U - [h₁ + v - g]²} = 4v(K₀ + vP_v) - (D₀ + D'v)²` (`nsf_Nen_eq`) is a quadratic in `v`
with `N'' = 2(4P_v - D'²) < 0` (`nsf_Nen_concave`, arithmetic-geometric mean) and `N'(3/4) < 0`
(certificate `nsfCEn_pos`), so `N(v) ≥ N(V)`; and `N(V) > 16s²·9193/50000` (certificate `nsfCPn_pos`).
Route: the two coefficient-domination bounds of §§2-4 are generated Bernstein certificates.

## Main API

* `nsfPv`, `nsfK0`, `nsfDp`, `nsfD0`, `nsfg`, `nsfNen`, `nsfNd34`, `nsfh1`; `nsf_Nen_eq`; `nsf_En_link`,
  `nsf_Pn_link`; `nsf_envelope`.
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

''' + lE + "\n" + lP + '''
/-- **Concavity in the incoming norm**):
`4P_v < D'²` (arithmetic-geometric mean, `B > p²`). -/
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

/-- **The envelope Casimir sign**). -/
theorem nsf_envelope {t x k v : ℝ} (ht0 : 1 / 3 ≤ t) (ht1 : t ≤ 2 / 5) (hj0 : 0 ≤ 2 * t + x - 1)
    (hj1 : 2 * t + x - 1 ≤ 1 / 30) (hk0 : 1 ≤ k) (hk1 : k ≤ 31 / 30) (hv0 : 3 / 4 ≤ v)
    (hvV : v ≤ nsfVq t x) :
    9193 / 50000 < (k + 2 * t * x + x ^ 2) ^ 2 *
      (4 * v * nsfwU t x k v - (nsfh1 t x k v + v - nsfg t x) ^ 2) / (16 * (k - t ^ 2) ^ 2) := by
  have ht : 0 < t := by linarith
  have hx : 0 < x := by linarith
  have hk : 0 < k := by linarith
  have hkt : t ^ 2 < k := by nlinarith
  rw [nsf_Nen_eq ht hx hk]
  -- `N'(3/4) < 0` and `N(V) > 16s² · cap`
  have hE : nsfNd34 t x k < 0 := by
    have h := nsfCEn_pos (2 / 5 - t) (2 * t + x - 1) (k - 1) (by linarith) (by linarith) hj0 hj1
      (by linarith) (by linarith)
    rw [← nsf_En_link t x k ht hx] at h
    have : 0 < -nsfNd34 t x k := pos_of_mul_pos_right h (by positivity)
    linarith
  have hP : 16 * (k - t ^ 2) ^ 2 * (9193 / 50000) < nsfNen t x k (nsfVq t x) := by
    have h := nsfCPn_pos (2 / 5 - t) (2 * t + x - 1) (k - 1) (by linarith) (by linarith) hj0 hj1
      (by linarith) (by linarith)
    rw [← nsf_Pn_link t x k ht hx] at h
    have : 0 < nsfNen t x k (nsfVq t x) - 16 * (k - t ^ 2) ^ 2 * (9193 / 50000) :=
      pos_of_mul_pos_right h (by positivity)
    linarith
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
  rw [lt_div_iff₀ hs]
  linarith

end SmoothedOctagon
'''
open(LEAN + 'SmallGap/EnvelopeCasimir.lean', 'w').write(s)
