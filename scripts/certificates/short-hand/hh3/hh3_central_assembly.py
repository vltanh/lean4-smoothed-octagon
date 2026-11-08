"""Writes Heavy/S3Central.lean (assembly of `hs3_central_alpha_proof`)."""
import os
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../..'))
OUT = os.path.join(ROOT, 'SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy')
NS = {0: "2 + 4 * (4 - 3 * (2 * hsQc x {t} / hsRA {t} (hs3b x {t}))) / (5 * {t} - 1)",
      1: "hsRA {t} (hs3b x {t}) / hsQc x {t} + 4 / (5 * {t} - 1)"}


def part(i):
    fn = f"hs3F{i}"
    n_al = NS[i].format(t='al')
    n_t = NS[i].format(t='t')
    return f"""/-- The α-derivative of the central test `F_{i}` at frozen incoming norm `c`. -/
noncomputable def hh3CH{i} (x c t : ℝ) : ℝ :=
  (hh3HorD (hh3C{i}Ns x c) t * hh3Hor (hh3C{i}Ds x) t - hh3Hor (hh3C{i}Ns x c) t * hh3HorD (hh3C{i}Ds x) t) /
      hh3Hor (hh3C{i}Ds x) t ^ 2 +
    (hh3HorD (hh3CLs x) t * hh3Hor (hh3CLds x) t - hh3Hor (hh3CLs x) t * hh3HorD (hh3CLds x) t) /
      hh3Hor (hh3CLds x) t ^ 2 / (hh3Hor (hh3CLs x) t / hh3Hor (hh3CLds x) t)

theorem hh3_c{i}_D_pos {{x t : ℝ}} (hx : 0 < x) (ht : 1 < t) : 0 < hh3Hor (hh3C{i}Ds x) t := by
  rw [hh3_c{i}_D]
  have : 0 < 5 * t - 1 := by linarith
  positivity

theorem hh3_c{i}_hasDerivAt {{x c t : ℝ}} (hx : 1 < x) (ht : 1 < t) :
    HasDerivAt (fun s => {fn} x (hs3b x s) s c (hsQc x s)) (hh3CH{i} x c t) t := by
  have key : ∀ s, 1 < s → {fn} x (hs3b x s) s c (hsQc x s) =
      hh3Hor (hh3C{i}Ns x c) s / hh3Hor (hh3C{i}Ds x) s +
        log (hh3Hor (hh3CLs x) s / hh3Hor (hh3CLds x) s) := by
    intro s hs
    unfold {fn}
    rw [hh3_fn_split, hh3_c{i}_clear x s c hx hs, hh3_c_logarg x s (by linarith) (by linarith)]
  have h1 := (hh3_hor_hasDerivAt (hh3C{i}Ns x c) t).div (hh3_hor_hasDerivAt (hh3C{i}Ds x) t)
    (hh3_c{i}_D_pos (by linarith) ht).ne'
  have h2 := ((hh3_hor_hasDerivAt (hh3CLs x) t).div (hh3_hor_hasDerivAt (hh3CLds x) t)
    (hh3_c_Ld_pos (by linarith) (by linarith)).ne').log
    (div_pos (hh3_c_Ln_pos (by linarith) (by linarith)) (hh3_c_Ld_pos (by linarith) (by linarith))).ne'
  have hev : (fun s => {fn} x (hs3b x s) s c (hsQc x s)) =ᶠ[nhds t]
      (fun s => hh3Hor (hh3C{i}Ns x c) s / hh3Hor (hh3C{i}Ds x) s +
        log (hh3Hor (hh3CLs x) s / hh3Hor (hh3CLds x) s)) :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) (fun s hs => key s hs)
  exact (h1.add h2).congr_of_eventuallyEq hev

theorem hh3_c{i}_deriv_neg {{x c t : ℝ}} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hc : 3 / 4 ≤ c) (hc' : c ≤ 4 / 5)
    (ht : 108 / 95 ≤ t) (ht' : t ≤ 89 / 72) : hh3CH{i} x c t < 0 := by
  unfold hh3CH{i}
  have hE : 0 < hh3CE x t := by
    unfold hh3CE
    have : 0 < 5 * t - 1 := by linarith
    positivity
  apply hh3_deriv_neg (hh3_c{i}_D_pos (by linarith) (by linarith)) hE
    (hh3_c_Ln_pos (by linarith) (by linarith)) (hh3_c_Ld_pos (by linarith) (by linarith))
    (hh3_c{i}_h1 x t) (hh3_c_h2 x t)
  rw [hh3_c{i}_Q, hh3_c{i}_P_aff]
  have p1 := hh3_c{i}_Plo_pos hx hx2 ht ht'
  have p2 := hh3_c{i}_Phi_pos hx hx2 ht ht'
  rcases le_or_gt c (31 / 40) with hcc | hcc
  · nlinarith [mul_nonneg (sub_nonneg.2 hc) p2.le]
  · nlinarith [mul_nonneg (sub_nonneg.2 hc') p1.le]

theorem hh3_c{i}_mono {{x c al : ℝ}} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hc : 3 / 4 ≤ c) (hc' : c ≤ 4 / 5)
    (hal : hs3amin x ≤ al) (hal' : al ≤ 89 / 72) :
    {fn} x (hs3b x al) al c (hsQc x al) ≤
      {fn} x (hs3b x (hs3amin x)) (hs3amin x) c (hsQc x (hs3amin x)) := by
  have ham : 108 / 95 ≤ hs3amin x := by unfold hs3amin; linarith
  apply hh3_le_of_deriv_nonpos (f := fun s => {fn} x (hs3b x s) s c (hsQc x s)) (f' := hh3CH{i} x c) hal
  · intro s hs
    exact hh3_c{i}_hasDerivAt (by linarith) (by linarith [hs.1])
  · intro s hs
    exact (hh3_c{i}_deriv_neg hx hx2 hc hc' (by linarith [hs.1]) (by linarith [hs.2])).le

theorem hh3_c{i}_slope_pos {{x t : ℝ}} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (ht : 108 / 95 ≤ t)
    (ht' : t ≤ 89 / 72) :
    0 < hh3Slope x (hs3b x t) t (hsQc x t) ({n_t}) := by
  rw [hh3_c{i}_slope_eq x t (by linarith) (by linarith)]
  apply div_pos (hh3_c{i}_S_pos hx hx2 ht ht')
  have : 0 < 5 * t - 1 := by linarith
  positivity

/-- The central test `F_{i}` is negative along the central boundary. -/
theorem hh3_central_F{i} {{x al : ℝ}} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : hs3amin x ≤ al)
    (hal' : al ≤ 89 / 72) :
    {fn} x (hs3b x al) al (hsUCB x (hs3b x al)) (hsQc x al) < 0 := by
  have ham : 108 / 95 ≤ hs3amin x := by unfold hs3amin; linarith
  obtain ⟨hu0, hu1⟩ := hh3_c_u0 hx hx2
  have hu := hh3_c_umono hx hx2 hal
  have hs := hh3_c{i}_slope_pos hx hx2 (by linarith) hal'
  have hA : {fn} x (hs3b x al) al (hsUCB x (hs3b x al)) (hsQc x al) ≤
      {fn} x (hs3b x al) al (hsUCB x (20 * x / 19)) (hsQc x al) := by
    unfold {fn}
    have e := hh3_fn_u_affine x (hs3b x al) al (hsQc x al) ({n_al})
      (log (2 * hsQc x al / hsRA al (hs3b x al))) (hsUCB x (hs3b x al)) (hsUCB x (20 * x / 19))
    nlinarith [mul_nonneg (sub_nonneg.2 hu) hs.le]
  have hB := hh3_c{i}_mono hx hx2 hu0 hu1 hal hal'
  rw [hh3_c_b_amin x (by linarith)] at hB
  have hC := (hs3_central_endpoint hx hx2).{i + 1}
  linarith
"""


def main():
    s = f"""module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3CentralB0
public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S3CentralB1

/-!
# Heavy leaf `hs3_central_alpha` (`DISPLACEMENT_CENTRAL_FACE` §2 (4)-(10), inventory HS-S3 R34, R37)

For `2 ≤ x ≤ 13/6`, `a_min(x) ≤ α ≤ 89/72`, at `β = b(x, α)`, `q = q_c`, `u = ū(x, β)`:
`F₀ < 0` and `F₁ < 0`.

Route: the note differentiates `F_i(x, α, b(x, α), ū(x, b(x, α)))` in `α` (numerators `P_i` of 274 and
222 terms with the `u_b` term). Here the incoming norm is first raised to the endpoint value
`u₀ = ū(x, 20x/19)` (`hh3_c_umono`: `ū` decreases along the path; `hh3_c{{i}}_slope_pos`: the test
increases with `u`), then `α ↦ F_i(x, α, b(x, α), u₀, q_c(x, α))` is shown decreasing
(`hh3_c{{i}}_mono`: the cleared derivative is affine in `u₀ ∈ [3/4, 4/5]` and is certified at both ends)
and the endpoint sign is the stable leaf `hs3_central_endpoint`.

## Main API

* `hh3_central_F0`, `hh3_central_F1`.
* `hs3_central_alpha_proof`: the statement of `hs3_central_alpha`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

theorem hh3_fn_split (x be al u q n ℓ : ℝ) : hs3Fn x be al u q n ℓ = hs3Fn x be al u q n 0 + ℓ := by
  unfold hs3Fn
  ring

theorem hh3_le_of_deriv_nonpos {{f f' : ℝ → ℝ}} {{a b : ℝ}} (hab : a ≤ b)
    (hd : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z) (hn : ∀ z ∈ Ioo a b, f' z ≤ 0) : f b ≤ f a := by
  have := ss_le_of_deriv (f := fun t => -f t) (f' := fun t => -f' t) hab
    (fun z hz => (hd z hz).neg) (fun z hz => by linarith [hn z hz])
  linarith

/-- The sign of a derivative `(N/D)' + (log(Lₙ/L_d))'` from its cleared form. -/
theorem hh3_deriv_neg {{N N' D D' Ln Ln' Ld Ld' E ED EL : ℝ}} (hD : 0 < D) (hE : 0 < E) (hLn : 0 < Ln)
    (hLd : 0 < Ld) (h1 : D' * E = D * ED) (h2 : (Ln' * Ld - Ln * Ld') * E = Ln * Ld * EL)
    (hQ : N' * E - N * ED + D * EL < 0) :
    (N' * D - N * D') / D ^ 2 + (Ln' * Ld - Ln * Ld') / Ld ^ 2 / (Ln / Ld) < 0 := by
  have hD' : D' = D * ED / E := by
    field_simp
    linarith
  have hL' : Ln' * Ld - Ln * Ld' = Ln * Ld * EL / E := by
    field_simp
    linarith
  rw [hL', hD']
  have e : (N' * D - N * (D * ED / E)) / D ^ 2 + Ln * Ld * EL / E / Ld ^ 2 / (Ln / Ld) =
      (N' * E - N * ED + D * EL) / (D * E) := by
    field_simp
  rw [e]
  exact div_neg_of_neg_of_pos hQ (mul_pos hD hE)

theorem hh3_c_Ln_pos {{x t : ℝ}} (hx : 0 < x) (ht : 0 < t) : 0 < hh3Hor (hh3CLs x) t := by
  simp only [hh3CLs, hh3Hor]
  positivity

theorem hh3_c_Ld_pos {{x t : ℝ}} (hx : 0 < x) (ht : 0 < t) : 0 < hh3Hor (hh3CLds x) t := by
  simp only [hh3CLds, hh3Hor]
  positivity

/-- `1/5808 ≤ V_G(x) - 3/4 ≤ 1/50` on `[2, 13/6]`. -/
theorem hh3_VG_gap {{x : ℝ}} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) :
    1 / 5808 ≤ hsVG x - 3 / 4 ∧ hsVG x - 3 / 4 ≤ 1 / 50 := by
  unfold hsVG
  rw [add_sub_cancel_left]
  have hd : 0 < 96 * x * (x + 1) * (13 * x ^ 2 + 14 * x + 3) := by positivity
  have hA : 381 ≤ 71 * x ^ 2 + 48 * x + 1 := by nlinarith
  have hA' : 71 * x ^ 2 + 48 * x + 1 ≤ 440 := by nlinarith
  have h1 : 1 ≤ (x - 1) ^ 2 := by nlinarith
  have h1' : (x - 1) ^ 2 ≤ 2 := by nlinarith
  have hB : 96 * x * (x + 1) * (13 * x ^ 2 + 14 * x + 3) ≤ 63000 := by
    have : x * (x + 1) ≤ 247 / 36 := by nlinarith
    have : 13 * x ^ 2 + 14 * x + 3 ≤ 95 := by nlinarith
    have : 0 ≤ x * (x + 1) := by positivity
    nlinarith
  have hB' : 47808 ≤ 96 * x * (x + 1) * (13 * x ^ 2 + 14 * x + 3) := by
    have : 6 ≤ x * (x + 1) := by nlinarith
    have : 83 ≤ 13 * x ^ 2 + 14 * x + 3 := by nlinarith
    nlinarith
  constructor
  · rw [div_le_div_iff₀ (by norm_num) hd]
    nlinarith [mul_le_mul h1 hA (by norm_num) (by positivity)]
  · rw [div_le_div_iff₀ hd (by norm_num)]
    nlinarith [mul_le_mul h1' hA' (by positivity) (by norm_num)]

theorem hh3_c_ucb_eq {{x be : ℝ}} (hb : 1 < be) :
    hsUCB x be = 3 / 4 + 1 / 5808 + (x - 1) * (hsVG x - 3 / 4 - 1 / 5808) / (be - 1) := by
  unfold hsUCB
  have : be - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem hh3_c_b_ge {{x al : ℝ}} (hx : 0 < x) (hal : hs3amin x ≤ al) : 20 * x / 19 ≤ hs3b x al := by
  unfold hs3b
  unfold hs3amin at hal
  have h0 : 0 < 15 * x + 36 := by positivity
  have h2 : 25 * x / (15 * x + 36) * ((15 * x + 511) / 475 - 1) = x / 19 := by
    field_simp
    ring
  have h3 : 25 * x / (15 * x + 36) * ((15 * x + 511) / 475 - 1) ≤ 25 * x / (15 * x + 36) * (al - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

theorem hh3_c_b_amin (x : ℝ) (hx : 0 < x) : hs3b x (hs3amin x) = 20 * x / 19 := by
  unfold hs3b hs3amin
  have : 15 * x + 36 ≠ 0 := by positivity
  field_simp
  ring

theorem hh3_c_umono {{x al : ℝ}} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : hs3amin x ≤ al) :
    hsUCB x (hs3b x al) ≤ hsUCB x (20 * x / 19) := by
  have hb := hh3_c_b_ge (by linarith) hal
  have hb1 : 1 < 20 * x / 19 := by rw [lt_div_iff₀ (by norm_num)]; linarith
  rw [hh3_c_ucb_eq (by linarith), hh3_c_ucb_eq hb1]
  have hG := (hh3_VG_gap hx hx2).1
  have hnum : 0 ≤ (x - 1) * (hsVG x - 3 / 4 - 1 / 5808) := mul_nonneg (by linarith) (by linarith)
  have : (x - 1) * (hsVG x - 3 / 4 - 1 / 5808) / (hs3b x al - 1) ≤
      (x - 1) * (hsVG x - 3 / 4 - 1 / 5808) / (20 * x / 19 - 1) :=
    div_le_div_of_nonneg_left hnum (by linarith) (by linarith)
  linarith

theorem hh3_c_u0 {{x : ℝ}} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) :
    3 / 4 ≤ hsUCB x (20 * x / 19) ∧ hsUCB x (20 * x / 19) ≤ 4 / 5 := by
  obtain ⟨g1, g2⟩ := hh3_VG_gap hx hx2
  unfold hsUCB
  have hd : 0 < 20 * x / 19 - 1 := by
    have : 1 < 20 * x / 19 := by rw [lt_div_iff₀ (by norm_num)]; linarith
    linarith
  constructor
  · have : 0 ≤ ((x - 1) * (hsVG x - 3 / 4) + (20 * x / 19 - x) / 5808) / (20 * x / 19 - 1) := by
      apply div_nonneg _ hd.le
      nlinarith
    linarith
  · have : ((x - 1) * (hsVG x - 3 / 4) + (20 * x / 19 - x) / 5808) / (20 * x / 19 - 1) ≤ 1 / 20 := by
      rw [div_le_iff₀ hd]
      nlinarith
    linarith

{part(0)}
{part(1)}
/-- **`hs3_central_alpha`**, with the statement of the skeleton leaf. -/
theorem hs3_central_alpha_proof {{x al : ℝ}} (hx : 2 ≤ x) (hx2 : x ≤ 13 / 6) (hal : hs3amin x ≤ al)
    (hal' : al ≤ 89 / 72) :
    hs3F0 x (hs3b x al) al (hsUCB x (hs3b x al)) (hsQc x al) < 0 ∧
      hs3F1 x (hs3b x al) al (hsUCB x (hs3b x al)) (hsQc x al) < 0 :=
  ⟨hh3_central_F0 hx hx2 hal hal', hh3_central_F1 hx hx2 hal hal'⟩

end SmoothedOctagon
"""
    open(os.path.join(OUT, 'S3Central.lean'), 'w').write(s)


if __name__ == '__main__':
    main()
