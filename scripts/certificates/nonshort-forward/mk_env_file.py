from links import *
LEAN=__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '../../../SmoothedOctagon/Exclusion/Mixed/FwdHand/')
pre = "  have hW : (1 + x) ≠ 0 := by linarith\n  have hp : t + x ≠ 0 := by linarith\n  have ht' : t ≠ 0 := by linarith\n"
lE = link2('fhCEn', 'fh_En_link', '(t x k : ℝ)', '(ht : 0 < t) (hx : 0 < x)',
  "2 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 3 * (-fhNd34 t x k)",
  yform_sub('fhCEn', "(2 / 5 - t)", "(2 * t + x - 1)", "(k - 1)", var='z'),
  'fhNd34 fhD0 fhDp fhK0 fhPv fhg', 'The cleared norm derivative `-2t²p²W³N\'(3/4)` is the certificate polynomial `fhCEn`.', pre=pre)
import json as _json
N2 = _json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), 'nums2.json')))
_rhsP = yform_sub('fhCPn', "(2 / 5 - t)", "(2 * t + x - 1)", "(k - 1)", var='z')
_DP = " ".join(Dnames('fhCPn'))
lP = f"""/-- The cleared Casimir excess at `v = V` is the certificate polynomial `fhCPn`. -/
theorem fh_Pn_link (t x k : ℝ) (ht : 0 < t) (hx : 0 < x) :
    3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (fhNen t x k (fhVq t x) - 16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) =
      {_rhsP} := by
  have hW : (1 + x) ≠ 0 := by linarith
  have hp : t + x ≠ 0 := by linarith
  have ht' : t ≠ 0 := by linarith
  have hQ : x ^ 2 + 6 * x + 6 ≠ 0 := by positivity
  have hNV : (1 + x) * (x ^ 2 + 6 * x + 6) * fhVq t x = {N2['NV']} := by
    unfold fhVq; field_simp; ring
  have hNK : t * fhK0 t x k = {N2['NK']} := by
    unfold fhK0; field_simp; ring
  have hNP : t * fhPv t x k = {N2['NP']} := by
    unfold fhPv; field_simp; ring
  have hND0 : t * (t + x) * (1 + x) ^ 2 * fhD0 t x k = {N2['ND0']} := by
    unfold fhD0 fhK0 fhg; field_simp; ring
  have hNDp : t * (t + x) * (1 + x) * fhDp t x k = {N2['NDp']} := by
    unfold fhDp fhPv; field_simp; ring
  have e : 3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (fhNen t x k (fhVq t x) - 16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) =
      3125 * (4 * ((1 + x) * (x ^ 2 + 6 * x + 6) * fhVq t x) * (t * fhK0 t x k) * (t * (t + x) ^ 2 * (1 + x) ^ 3 * (x ^ 2 + 6 * x + 6))
        + 4 * ((1 + x) * (x ^ 2 + 6 * x + 6) * fhVq t x) ^ 2 * (t * fhPv t x k) * (t * (t + x) ^ 2 * (1 + x) ^ 2)
        - ((x ^ 2 + 6 * x + 6) * (t * (t + x) * (1 + x) ^ 2 * fhD0 t x k)
          + (t * (t + x) * (1 + x) * fhDp t x k) * ((1 + x) * (x ^ 2 + 6 * x + 6) * fhVq t x)) ^ 2)
      - 3125 * t ^ 2 * (t + x) ^ 2 * (1 + x) ^ 4 * (x ^ 2 + 6 * x + 6) ^ 2 * (16 * (k - t ^ 2) ^ 2 * (9193 / 50000)) := by
    unfold fhNen; ring
  rw [e, hNV, hNK, hNP, hND0, hNDp]
  unfold {_DP}
  ring
"""
s = '''module

public import SmoothedOctagon.Exclusion.Mixed.FwdHand.QElim
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.CertEn
public import SmoothedOctagon.Exclusion.Mixed.FwdHand.CertPn

/-!
# Case M2, forward successor by hand: the envelope Casimir sign

`MIXED_NONSHORT_FORWARD_ENVELOPE_CASIMIR_SIGN`: on `1/3 ≤ t ≤ 2/5`, `0 ≤ j ≤ 1/30`,
`1 ≤ k ≤ 31/30` and `3/4 ≤ v ≤ V`,
`𝒢 = B²{4vw_U - [h₁ + v - g]²}/(16s²) > 9193/50000` (`fh_envelope`).

`N(v) = B²{4vw_U - [h₁ + v - g]²} = 4v(K₀ + vP_v) - (D₀ + D'v)²` (`fh_Nen_eq`) is a quadratic in `v`
with `N'' = 2(4P_v - D'²) < 0` (`fh_Nen_concave`, arithmetic-geometric mean) and `N'(3/4) < 0`
(certificate `CertEn`), so `N(v) ≥ N(V)`; and `N(V) > 16s²·9193/50000` (certificate `CertPn`).
Route: the two coefficient-domination bounds of §§2-4 are generated Bernstein certificates.

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

''' + lE + "\n" + lP + '''
/-- **Concavity in the incoming norm** (`MIXED_NONSHORT_FORWARD_ENVELOPE_CASIMIR_SIGN` (6)):
`4P_v < D'²` (arithmetic-geometric mean, `B > p²`). -/
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

/-- **The envelope Casimir sign** (`MIXED_NONSHORT_FORWARD_ENVELOPE_CASIMIR_SIGN` (5)). -/
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
'''
open(LEAN + 'Envelope.lean', 'w').write(s)
