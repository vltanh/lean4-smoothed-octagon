module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.Basic

/-!
# The global upper bridge orders

The integral gap comparisons give the contact signs for the affine upper barriers
with slopes `5/4` and `9/8`. The first is a sum of positive products; the second
uses monotonicity of the normalized contact in `1/x` and completed squares on
the two ranges separated by `x = 3`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

private theorem upper54_normalized {a t : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (ht : 0 ≤ t) (ht4 : t < 4 / 9) :
    0 < 5 / 4 * ((3 - 2 * (1 - a + 5 / 4 * a * t) - (1 - a * t)) /
      (3 - (1 - a + 5 / 4 * a * t) - 2 * (1 - a * t))) *
      (1 - a * t) * (1 / (1 - a) - (1 - a * t)) -
      ((2 * (1 - a * t) - (1 - a + 5 / 4 * a * t)) / (1 - a) - (1 - a * t) ^ 2) := by
  have hden : 0 < 3 - (1 - a + 5 / 4 * a * t) - 2 * (1 - a * t) := by nlinarith
  have he : 5 / 4 * ((3 - 2 * (1 - a + 5 / 4 * a * t) - (1 - a * t)) /
      (3 - (1 - a + 5 / 4 * a * t) - 2 * (1 - a * t))) *
      (1 - a * t) * (1 / (1 - a) - (1 - a * t)) -
      ((2 * (1 - a * t) - (1 - a + 5 / 4 * a * t)) / (1 - a) - (1 - a * t) ^ 2) =
      a / (4 * (1 - a) * (4 + 3 * t)) *
      (1 + 6 * t ^ 2 + 7 * (3 * t - 1) ^ 2 +
       6 * (1 - a) * t * (2 * (4 - 9 * t) + 7 * t ^ 2) +
       6 * (1 - a) ^ 2 * t ^ 2 * (4 - 7 * t)) := by
    have hd : 3 - (1 - a + 5 / 4 * a * t) - 2 * (1 - a * t) = a * (4 + 3 * t) / 4 := by ring
    rw [hd]
    field_simp
    ring
  rw [he]
  have : 0 < 1 - a := by linarith
  have : 0 < 4 - 9 * t := by linarith
  have : 0 < 4 - 7 * t := by linarith
  positivity

/-- The global upper barrier has a positive contact expression under the linear-weight
gap comparison. Normalize by `a = 1-1/x`, `t = (1-z)/a` and use positive products. -/
theorem ss_upper_contact_54 {x z : ℝ} (hx : 1 < x) (hz : z ≤ 1)
    (hP : 1 / x + 5 / 4 * (1 - z) < z) :
    0 < 5 / 4 * ((3 - 2 * (1 / x + 5 / 4 * (1 - z)) - z) /
      (3 - (1 / x + 5 / 4 * (1 - z)) - 2 * z)) * z * (x - z) -
      ((2 * z - (1 / x + 5 / 4 * (1 - z))) * x - z ^ 2) := by
  have hx0 : 0 < x := by linarith
  let a := 1 - 1 / x
  let t := (1 - z) / a
  have hix : 0 < 1 / x := by positivity
  have hix1 : 1 / x < 1 := (div_lt_one hx0).mpr hx
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have ht : 0 ≤ t := div_nonneg (by linarith) ha.le
  have het : a * t = 1 - z := by dsimp [t]; field_simp
  have ht4 : t < 4 / 9 := by
    dsimp [a] at het
    nlinarith only [het, hP, ha]
  have hxp : x = 1 / (1 - a) := by dsimp [a]; field_simp; ring
  have hzp : z = 1 - a * t := by linarith only [het]
  have hpp : 1 / x + 5 / 4 * (1 - z) = 1 - a + 5 / 4 * a * t := by
    dsimp [a] at het ⊢
    nlinarith only [het]
  convert upper54_normalized ha ha1 ht ht4 using 1
  rw [hpp, hzp, hxp]
  ring

private noncomputable def upper98N (l t : ℝ) : ℝ :=
  1 / 4 - 73 * t / 32 + 265 * t ^ 2 / 64 +
    l * t * (73 * t ^ 2 - 186 * t + 80) / 32 + l ^ 2 * t ^ 2 * (40 - 73 * t) / 32

private theorem upper98N_mono {c l t : ℝ} (hc : 0 ≤ c) (hcl : c ≤ l)
    (ht : 0 ≤ t) (ht1 : t < 1 / 2) : upper98N c t ≤ upper98N l t := by
  have hq : 0 < 73 * t ^ 2 - 186 * t + 80 := by
    have hp := mul_nonneg (by linarith : 0 ≤ 1 / 2 - t)
      (by linarith : 0 ≤ 299 / 2 - 73 * t)
    nlinarith only [hp]
  have hq2 : 0 < 40 - 73 * t := by linarith
  have he : upper98N l t - upper98N c t =
      (l - c) * t / 32 *
      (73 * t ^ 2 - 186 * t + 80 + (l + c) * t * (40 - 73 * t)) := by
    unfold upper98N
    ring
  have hl : 0 ≤ l := hc.trans hcl
  have hb : 0 ≤ (l - c) * t / 32 *
      (73 * t ^ 2 - 186 * t + 80 + (l + c) * t * (40 - 73 * t)) := by
    have : 0 ≤ l - c := sub_nonneg.mpr hcl
    positivity
  linarith only [he, hb]

private theorem upper98_normalized {a t : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (ha5 : a ≤ 4 / 5) (ht : 0 ≤ t) (ht8 : t < 8 / 17) :
    0 < 9 / 8 * (((3 - 2 * (1 - a + 9 / 8 * a * t) - (1 - a * t)) /
      (3 - (1 - a + 9 / 8 * a * t) - 2 * (1 - a * t))) +
      ((1 - a * t) - (1 - a + 9 / 8 * a * t)) / 6) *
      (1 - a * t) * (1 / (1 - a) - (1 - a * t)) -
      ((2 * (1 - a * t) - (1 - a + 9 / 8 * a * t)) / (1 - a) - (1 - a * t) ^ 2) := by
  let E := 1 + 7 / 8 * t
  let D := 1 - 17 / 8 * t
  have hD : 0 < D := by dsimp [D]; linarith
  have hE : 1 ≤ E := by dsimp [E]; linarith
  have hE0 : 0 < E := by linarith
  have hl : 0 < 1 - a := by linarith
  have ht1 : t < 1 / 2 := by linarith
  have htone : 0 < 1 - t := by linarith
  have hden : 0 < 3 - (1 - a + 9 / 8 * a * t) - 2 * (1 - a * t) := by nlinarith
  have he : E * (1 - a) / a *
      (9 / 8 * (((3 - 2 * (1 - a + 9 / 8 * a * t) - (1 - a * t)) /
      (3 - (1 - a + 9 / 8 * a * t) - 2 * (1 - a * t))) +
      ((1 - a * t) - (1 - a + 9 / 8 * a * t)) / 6) *
      (1 - a * t) * (1 / (1 - a) - (1 - a * t)) -
      ((2 * (1 - a * t) - (1 - a + 9 / 8 * a * t)) / (1 - a) - (1 - a * t) ^ 2)) =
      upper98N (1 - a) t + 3 / 16 * a * D * E * (1 - a * t) * (1 + (1 - a) * t) := by
    dsimp [E, D, upper98N]
    have hd : 3 - (1 - a + 9 / 8 * a * t) - 2 * (1 - a * t) = a * (8 + 7 * t) / 8 := by ring
    rw [hd]
    field_simp
    ring
  have h1 : 1 - t ≤ 1 - a * t := by nlinarith only [ha1, ht]
  have h10 : 0 < 1 - a * t := by linarith
  have h2 : 1 ≤ 1 + (1 - a) * t := by nlinarith only [hl, ht]
  have hprod : 1 - t ≤ E * (1 - a * t) * (1 + (1 - a) * t) := by
    calc 1 - t ≤ 1 - a * t := h1
      _ ≤ E * (1 - a * t) := by nlinarith only [hE, h10]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) h2
  have hinc := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 3 / 16 * a * D)
  have hbase : 0 < upper98N (1 - a) t + 3 / 16 * a * D * (1 - t) := by
    by_cases ha3 : a ≤ 2 / 3
    · have hm := upper98N_mono (c := 1 / 3) (l := 1 - a) (by norm_num) (by linarith) ht ht1
      have hid : upper98N (1 / 3) t = 9 / 4 * (t - 1 / 3) ^ 2 +
          t * (30 + 53 * t + 292 * t ^ 2) / 576 := by dsimp [upper98N]; ring
      have hp : 0 < upper98N (1 / 3) t := by
        rw [hid]
        rcases ht.eq_or_lt with hzero | hpos
        · subst hzero; norm_num
        · positivity
      have hn : 0 ≤ 3 / 16 * a * D * (1 - t) := by positivity
      linarith only [hm, hp, hn]
    · have hm := upper98N_mono (c := 1 / 5) (l := 1 - a) (by norm_num) (by linarith) ht ht1
      have hi : 1 / 8 * D * (1 - t) ≤ 3 / 16 * a * D * (1 - t) := by
        have hh := mul_nonneg (by linarith : 0 ≤ 3 / 16 * a - 1 / 8)
          (by positivity : 0 ≤ D * (1 - t))
        nlinarith only [hh]
      have hid : upper98N (1 / 5) t + 1 / 8 * D * (1 - t) =
          27 / 8 * (t - 1 / 3) ^ 2 + t * (5 / 64 - 13 * t / 160) + 73 * t ^ 3 / 200 := by
        dsimp [upper98N, D]
        ring
      have hp : 0 < upper98N (1 / 5) t + 1 / 8 * D * (1 - t) := by
        rw [hid]
        have hlin : 0 < 5 / 64 - 13 * t / 160 := by linarith
        rcases ht.eq_or_lt with hzero | hpos
        · subst hzero; norm_num
        · positivity
      linarith only [hm, hi, hp]
  have hpos : 0 < E * (1 - a) / a := by positivity
  have hh : 0 < E * (1 - a) / a *
      (9 / 8 * (((3 - 2 * (1 - a + 9 / 8 * a * t) - (1 - a * t)) /
      (3 - (1 - a + 9 / 8 * a * t) - 2 * (1 - a * t))) +
      ((1 - a * t) - (1 - a + 9 / 8 * a * t)) / 6) *
      (1 - a * t) * (1 / (1 - a) - (1 - a * t)) -
      ((2 * (1 - a * t) - (1 - a + 9 / 8 * a * t)) / (1 - a) - (1 - a * t) ^ 2)) := by
    rw [he]
    nlinarith only [hbase, hinc]
  exact (mul_pos_iff_of_pos_left hpos).mp hh

/-- For `x ≤ 5`, the refined gap comparison makes the `9/8` barrier's contact
expression positive. Monotonicity in `1/x` and two completed squares give its sign. -/
theorem ss_upper_contact_98 {x z : ℝ} (hx : 1 < x) (hx5 : x ≤ 5) (hz : z ≤ 1)
    (hP : 1 / x + 9 / 8 * (1 - z) < z) :
    0 < 9 / 8 * (((3 - 2 * (1 / x + 9 / 8 * (1 - z)) - z) /
      (3 - (1 / x + 9 / 8 * (1 - z)) - 2 * z)) +
      (z - (1 / x + 9 / 8 * (1 - z))) / 6) * z * (x - z) -
      ((2 * z - (1 / x + 9 / 8 * (1 - z))) * x - z ^ 2) := by
  have hx0 : 0 < x := by linarith
  let a := 1 - 1 / x
  let t := (1 - z) / a
  have hix : 0 < 1 / x := by positivity
  have hix1 : 1 / x < 1 := (div_lt_one hx0).mpr hx
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have ht : 0 ≤ t := div_nonneg (by linarith) ha.le
  have het : a * t = 1 - z := by dsimp [t]; field_simp
  have ht8 : t < 8 / 17 := by
    dsimp [a] at het
    nlinarith only [het, hP, ha]
  have hxp : x = 1 / (1 - a) := by dsimp [a]; field_simp; ring
  have hzp : z = 1 - a * t := by linarith only [het]
  have hpp : 1 / x + 9 / 8 * (1 - z) = 1 - a + 9 / 8 * a * t := by
    dsimp [a] at het ⊢
    nlinarith only [het]
  have ha5 : a ≤ 4 / 5 := by
    have hix5 : 1 / 5 ≤ 1 / x := one_div_le_one_div_of_le hx0 hx5
    dsimp [a]
    linarith only [hix5]
  convert upper98_normalized ha ha1 ha5 ht ht8 using 1
  rw [hpp, hzp, hxp]
  ring

/-- A lower bound for the gap ratio gives the upper-barrier contact inequality. -/
theorem ord_upper_contact_of_ratio {p z x k R : ℝ} (hp : 0 < p)
    (hpz : p < z) (hz : z ≤ 1) (hk : 0 < k * z * (x - z))
    (hR : R < (ss_gB 1 p - m2Sec p 1 z) / (m2Sec p 1 z - ss_gB 1 z))
    (hcontact : 0 < k * R * z * (x - z) - ((2 * z - p) * x - z ^ 2)) :
    (m2Sec p 1 z - ss_gB 1 z) * ((2 * z - p) * x - z ^ 2) <
      k * (ss_gB 1 p - m2Sec p 1 z) * z * (x - z) := by
  have hη : 0 < m2Sec p 1 z - ss_gB 1 z := sub_pos.mpr (ss_sec_gt_right hp hpz hz)
  have hgap := (lt_div_iff₀ hη).mp hR
  have hgap' := mul_lt_mul_of_pos_left hgap hk
  have hcontact' := mul_pos hη hcontact
  nlinarith only [hgap', hcontact']

end SmoothedOctagon
