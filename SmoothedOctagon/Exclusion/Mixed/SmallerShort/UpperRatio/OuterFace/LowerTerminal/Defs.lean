module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.Reductions

/-!
# Smaller-short window, upper ratio: the lower-shape terminal curve, definitions

The exact-log terminal function on the curve `α = a_f(x) = (36x + 25)/84`,
`c = c_+(x) = (24x + 51)/128`, `u = u_s`, in the coordinate `r = 1/a_f`: with a constant
multiplier `n ∈ {49/20, 63/25}`, the outer test is
`R_n = L_n + V A_n + Q_n + 1/Z + log(2Z/7)`, `V = u_s - 3/4 = 1/1200 + (2/75)F(85q² - 1)`,
`F = r(84 - 61r)/K`, `q = (84 - 61r)/(84 + 11r)`, `Z = J/(1152r)`,
`K = 504 + 2493r - 2261r²`, `J = 504 + 3645r - 1109r²`, where `A_n = A/(C_A r²)`,
`L_n = L/(C_L r²)` and `Q_n = Q/(q₀r + q₁)` have explicit polynomial numerators `A`, `L`, `Q`
in `r`. This file gives the definitions and the first two derivatives of every component and of
`R_n`.

## Main API

* The numerators `urAsl`, `urLsl`, `urQsl` (`n = 49/20`) and `urAsh`, `urLsh`, `urQsh`
  (`n = 63/25`), with derivatives (`…1`, `…2`).
* `ur_hd_quot`, `ur_hd_quot2`: first and second derivatives of a quotient.
* `urFc`, `urqc`, `urVc`, `urZi` (`1/Z`), `urLg` (`log(2Z/7)`) and their derivatives.
* `urRc` (`R_n`), `urRcd`, `urRcdd` and `ur_hd_Rc`, `ur_hd_Rcd`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- Derivative of a polynomial of degree at most six. -/
theorem ur_hd_poly6 (a0 a1 a2 a3 a4 a5 a6 r : ℝ) :
    HasDerivAt (fun s => a0 + a1 * s + a2 * s ^ 2 + a3 * s ^ 3 + a4 * s ^ 4 + a5 * s ^ 5 + a6 * s ^ 6)
      (a1 + 2 * a2 * r + 3 * a3 * r ^ 2 + 4 * a4 * r ^ 3 + 5 * a5 * r ^ 4 + 6 * a6 * r ^ 5) r := by
  have := ((((((hasDerivAt_id r).const_mul a1).add ((hasDerivAt_pow 2 r).const_mul a2)).add
    ((hasDerivAt_pow 3 r).const_mul a3)).add ((hasDerivAt_pow 4 r).const_mul a4)).add
    ((hasDerivAt_pow 5 r).const_mul a5)).add ((hasDerivAt_pow 6 r).const_mul a6)
  convert this.const_add a0 using 1
  · funext s; simp only [Pi.add_apply, id]; ring
  · norm_num
    ring

/-- First derivative of a quotient. -/
theorem ur_hd_quot {N D : ℝ → ℝ} {N1 D1 r : ℝ} (hN : HasDerivAt N N1 r) (hD : HasDerivAt D D1 r)
    (hD0 : D r ≠ 0) :
    HasDerivAt (fun s => N s / D s) ((N1 * D r - N r * D1) / D r ^ 2) r := hN.div hD hD0

/-- Second derivative of a quotient. -/
theorem ur_hd_quot2 {N D N1 D1 : ℝ → ℝ} {N2 D2 r : ℝ} (hN : HasDerivAt N (N1 r) r)
    (hD : HasDerivAt D (D1 r) r) (hN1 : HasDerivAt N1 N2 r) (hD1 : HasDerivAt D1 D2 r)
    (hD0 : D r ≠ 0) :
    HasDerivAt (fun s => (N1 s * D s - N s * D1 s) / D s ^ 2)
      (((N2 * D r - N r * D2) * D r - 2 * D1 r * (N1 r * D r - N r * D1 r)) / D r ^ 3) r := by
  have hnum := ((hN1.mul hD).sub (hN.mul hD1))
  have hden : HasDerivAt (fun s => D s ^ 2) (2 * D r * D1 r) r := by
    convert hD.pow 2 using 1; push_cast; ring
  convert hnum.div hden (pow_ne_zero 2 hD0) using 1
  simp only [Pi.mul_apply, Pi.sub_apply]
  field_simp
  ring

/-- A linear function. -/
theorem ur_hd_lin (p q r : ℝ) : HasDerivAt (fun s => p * s + q) p r := by
  simpa using ((hasDerivAt_id r).const_mul p).add_const q

/-- A quadratic function. -/
theorem ur_hd_quad (p q k r : ℝ) :
    HasDerivAt (fun s => p + q * s + k * s ^ 2) (q + 2 * k * r) r := by
  convert ur_hd_poly6 p q k 0 0 0 0 r using 1
  · funext s; ring
  · ring

/-- The numerator of `A_n`, `n = 49/20`. -/
noncomputable def urAsl (r : ℝ) : ℝ :=
  10553281375 * r ^ 6 - 103680325518 * r ^ 5 + 332580904767 * r ^ 4 - 411951691728 * r ^ 3 -
    142211039040 * r ^ 2 + 377902651392 * r + 53258010624

/-- The first derivative of the numerator of `A_n`, `n = 49/20`. -/
noncomputable def urAsl1 (r : ℝ) : ℝ :=
  63319688250 * r ^ 5 - 518401627590 * r ^ 4 + 1330323619068 * r ^ 3 - 1235855075184 * r ^ 2 -
    284422078080 * r + 377902651392

/-- The second derivative of the numerator of `A_n`, `n = 49/20`. -/
noncomputable def urAsl2 (r : ℝ) : ℝ :=
  316598441250 * r ^ 4 - 2073606510360 * r ^ 3 + 3990970857204 * r ^ 2 - 2471710150368 * r -
    284422078080

/-- The numerator of `L_n`, `n = 49/20`. -/
noncomputable def urLsl (r : ℝ) : ℝ :=
  8904843871 * r ^ 6 - 62623679118 * r ^ 5 + 267084640575 * r ^ 4 - 350015430096 * r ^ 3 +
    204186495168 * r ^ 2 - 60228790272 * r - 12290310144

/-- The first derivative of the numerator of `L_n`, `n = 49/20`. -/
noncomputable def urLsl1 (r : ℝ) : ℝ :=
  53429063226 * r ^ 5 - 313118395590 * r ^ 4 + 1068338562300 * r ^ 3 - 1050046290288 * r ^ 2 +
    408372990336 * r - 60228790272

/-- The second derivative of the numerator of `L_n`, `n = 49/20`. -/
noncomputable def urLsl2 (r : ℝ) : ℝ :=
  267145316130 * r ^ 4 - 1252473582360 * r ^ 3 + 3205015686900 * r ^ 2 - 2100092580576 * r +
    408372990336

/-- The numerator of `Q_n`, `n = 49/20`. -/
noncomputable def urQsl (r : ℝ) : ℝ :=
  250523 * r ^ 5 - 1486275 * r ^ 4 + 2522154 * r ^ 3 - 8748306 * r ^ 2 + 6114096 * r + 1016064

/-- The first derivative of the numerator of `Q_n`, `n = 49/20`. -/
noncomputable def urQsl1 (r : ℝ) : ℝ :=
  1252615 * r ^ 4 - 5945100 * r ^ 3 + 7566462 * r ^ 2 - 17496612 * r + 6114096

/-- The second derivative of the numerator of `Q_n`, `n = 49/20`. -/
noncomputable def urQsl2 (r : ℝ) : ℝ :=
  5010460 * r ^ 3 - 17835300 * r ^ 2 + 15132924 * r - 17496612

/-- The numerator of `A_n`, `n = 63/25`. -/
noncomputable def urAsh (r : ℝ) : ℝ :=
  1507611625 * r ^ 6 - 14811475074 * r ^ 5 + 47383333641 * r ^ 4 - 58001053104 * r ^ 3 -
    21418395840 * r ^ 2 + 53324199936 * r + 7608287232

/-- The first derivative of the numerator of `A_n`, `n = 63/25`. -/
noncomputable def urAsh1 (r : ℝ) : ℝ :=
  9045669750 * r ^ 5 - 74057375370 * r ^ 4 + 189533334564 * r ^ 3 - 174003159312 * r ^ 2 -
    42836791680 * r + 53324199936

/-- The second derivative of the numerator of `A_n`, `n = 63/25`. -/
noncomputable def urAsh2 (r : ℝ) : ℝ :=
  45228348750 * r ^ 4 - 296229501480 * r ^ 3 + 568600003692 * r ^ 2 - 348006318624 * r -
    42836791680

/-- The numerator of `L_n`, `n = 63/25`. -/
noncomputable def urLsh (r : ℝ) : ℝ :=
  1272120553 * r ^ 6 - 8946239874 * r ^ 5 + 38058322185 * r ^ 4 - 49565800368 * r ^ 3 +
    28885149504 * r ^ 2 - 8489650176 * r - 1755758592

/-- The first derivative of the numerator of `L_n`, `n = 63/25`. -/
noncomputable def urLsh1 (r : ℝ) : ℝ :=
  7632723318 * r ^ 5 - 44731199370 * r ^ 4 + 152233288740 * r ^ 3 - 148697401104 * r ^ 2 +
    57770299008 * r - 8489650176

/-- The second derivative of the numerator of `L_n`, `n = 63/25`. -/
noncomputable def urLsh2 (r : ℝ) : ℝ :=
  38163616590 * r ^ 4 - 178924797480 * r ^ 3 + 456699866220 * r ^ 2 - 297394802208 * r +
    57770299008

/-- The numerator of `Q_n`, `n = 63/25`. -/
noncomputable def urQsh (r : ℝ) : ℝ :=
  35789 * r ^ 5 - 212325 * r ^ 4 + 358662 * r ^ 3 - 1249758 * r ^ 2 + 863568 * r + 145152

/-- The first derivative of the numerator of `Q_n`, `n = 63/25`. -/
noncomputable def urQsh1 (r : ℝ) : ℝ :=
  178945 * r ^ 4 - 849300 * r ^ 3 + 1075986 * r ^ 2 - 2499516 * r + 863568

/-- The second derivative of the numerator of `Q_n`, `n = 63/25`. -/
noncomputable def urQsh2 (r : ℝ) : ℝ :=
  715780 * r ^ 3 - 2547900 * r ^ 2 + 2151972 * r - 2499516

theorem ur_hd_Asl (r : ℝ) : HasDerivAt urAsl (urAsl1 r) r := by
  convert ur_hd_poly6 53258010624 377902651392 (-142211039040) (-411951691728) 332580904767 (-103680325518) 10553281375 r using 1
  · funext s; unfold urAsl; ring
  · unfold urAsl1; ring

theorem ur_hd_Asl1 (r : ℝ) : HasDerivAt urAsl1 (urAsl2 r) r := by
  convert ur_hd_poly6 377902651392 (-284422078080) (-1235855075184) 1330323619068 (-518401627590) 63319688250 0 r using 1
  · funext s; unfold urAsl1; ring
  · unfold urAsl2; ring

theorem ur_hd_Lsl (r : ℝ) : HasDerivAt urLsl (urLsl1 r) r := by
  convert ur_hd_poly6 (-12290310144) (-60228790272) 204186495168 (-350015430096) 267084640575 (-62623679118) 8904843871 r using 1
  · funext s; unfold urLsl; ring
  · unfold urLsl1; ring

theorem ur_hd_Lsl1 (r : ℝ) : HasDerivAt urLsl1 (urLsl2 r) r := by
  convert ur_hd_poly6 (-60228790272) 408372990336 (-1050046290288) 1068338562300 (-313118395590) 53429063226 0 r using 1
  · funext s; unfold urLsl1; ring
  · unfold urLsl2; ring

theorem ur_hd_Qsl (r : ℝ) : HasDerivAt urQsl (urQsl1 r) r := by
  convert ur_hd_poly6 1016064 6114096 (-8748306) 2522154 (-1486275) 250523 0 r using 1
  · funext s; unfold urQsl; ring
  · unfold urQsl1; ring

theorem ur_hd_Qsl1 (r : ℝ) : HasDerivAt urQsl1 (urQsl2 r) r := by
  convert ur_hd_poly6 6114096 (-17496612) 7566462 (-5945100) 1252615 0 0 r using 1
  · funext s; unfold urQsl1; ring
  · unfold urQsl2; ring

theorem ur_hd_Ash (r : ℝ) : HasDerivAt urAsh (urAsh1 r) r := by
  convert ur_hd_poly6 7608287232 53324199936 (-21418395840) (-58001053104) 47383333641 (-14811475074) 1507611625 r using 1
  · funext s; unfold urAsh; ring
  · unfold urAsh1; ring

theorem ur_hd_Ash1 (r : ℝ) : HasDerivAt urAsh1 (urAsh2 r) r := by
  convert ur_hd_poly6 53324199936 (-42836791680) (-174003159312) 189533334564 (-74057375370) 9045669750 0 r using 1
  · funext s; unfold urAsh1; ring
  · unfold urAsh2; ring

theorem ur_hd_Lsh (r : ℝ) : HasDerivAt urLsh (urLsh1 r) r := by
  convert ur_hd_poly6 (-1755758592) (-8489650176) 28885149504 (-49565800368) 38058322185 (-8946239874) 1272120553 r using 1
  · funext s; unfold urLsh; ring
  · unfold urLsh1; ring

theorem ur_hd_Lsh1 (r : ℝ) : HasDerivAt urLsh1 (urLsh2 r) r := by
  convert ur_hd_poly6 (-8489650176) 57770299008 (-148697401104) 152233288740 (-44731199370) 7632723318 0 r using 1
  · funext s; unfold urLsh1; ring
  · unfold urLsh2; ring

theorem ur_hd_Qsh (r : ℝ) : HasDerivAt urQsh (urQsh1 r) r := by
  convert ur_hd_poly6 145152 863568 (-1249758) 358662 (-212325) 35789 0 r using 1
  · funext s; unfold urQsh; ring
  · unfold urQsh1; ring

theorem ur_hd_Qsh1 (r : ℝ) : HasDerivAt urQsh1 (urQsh2 r) r := by
  convert ur_hd_poly6 863568 (-2499516) 1075986 (-849300) 178945 0 0 r using 1
  · funext s; unfold urQsh1; ring
  · unfold urQsh2; ring

/-! ### The curve components -/

/-- `K = 504 + 2493r - 2261r²`. -/
noncomputable def urKc (r : ℝ) : ℝ := 504 + 2493 * r - 2261 * r ^ 2

/-- `J = 504 + 3645r - 1109r²`, `Z = J/(1152r)`. -/
noncomputable def urJc (r : ℝ) : ℝ := 504 + 3645 * r - 1109 * r ^ 2

/-- `F = r(84 - 61r)/K`. -/
noncomputable def urFc (r : ℝ) : ℝ := (84 * r - 61 * r ^ 2) / urKc r

noncomputable def urFcd (r : ℝ) : ℝ :=
  ((84 - 122 * r) * urKc r - (84 * r - 61 * r ^ 2) * (2493 - 4522 * r)) / urKc r ^ 2

noncomputable def urFcdd (r : ℝ) : ℝ :=
  ((-122 * urKc r - (84 * r - 61 * r ^ 2) * (-4522)) * urKc r -
    2 * (2493 - 4522 * r) * ((84 - 122 * r) * urKc r - (84 * r - 61 * r ^ 2) * (2493 - 4522 * r))) /
    urKc r ^ 3

/-- `q = (84 - 61r)/(84 + 11r)`. -/
noncomputable def urqc (r : ℝ) : ℝ := (84 - 61 * r) / (84 + 11 * r)

noncomputable def urqcd (r : ℝ) : ℝ := -6048 / (84 + 11 * r) ^ 2

noncomputable def urqcdd (r : ℝ) : ℝ := 133056 / (84 + 11 * r) ^ 3

/-- `V = u_s - 3/4 = 1/1200 + (2/75)F(85q² - 1)`. -/
noncomputable def urVc (r : ℝ) : ℝ := 1 / 1200 + 2 / 75 * urFc r * (85 * urqc r ^ 2 - 1)

noncomputable def urVcd (r : ℝ) : ℝ :=
  2 / 75 * (urFcd r * (85 * urqc r ^ 2 - 1) + 170 * urFc r * urqc r * urqcd r)

noncomputable def urVcdd (r : ℝ) : ℝ :=
  2 / 75 * (urFcdd r * (85 * urqc r ^ 2 - 1) + 340 * urFcd r * urqc r * urqcd r +
    170 * urFc r * (urqcd r ^ 2 + urqc r * urqcdd r))

/-- `1/Z = 1152r/J`. -/
noncomputable def urZi (r : ℝ) : ℝ := 1152 * r / urJc r

noncomputable def urZid (r : ℝ) : ℝ := (1152 * urJc r - 1152 * r * (3645 - 2218 * r)) / urJc r ^ 2

noncomputable def urZidd (r : ℝ) : ℝ :=
  ((0 * urJc r - 1152 * r * (-2218)) * urJc r -
    2 * (3645 - 2218 * r) * (1152 * urJc r - 1152 * r * (3645 - 2218 * r))) / urJc r ^ 3

/-- `log(2Z/7)`. -/
noncomputable def urLg (r : ℝ) : ℝ := log (2 * (urJc r / (1152 * r)) / 7)

noncomputable def urLgd (r : ℝ) : ℝ := (3645 - 2218 * r) / urJc r - 1 / r

noncomputable def urLgdd (r : ℝ) : ℝ :=
  (-2218 * urJc r - (3645 - 2218 * r) ^ 2) / urJc r ^ 2 + 1 / r ^ 2

/-- The terminal function `R_n` for numerators `As`, `Ls`, `Qs` with
denominators `CA r²`, `CL r²`, `q₀r + q₁`. -/
noncomputable def urRc (CA CL q0 q1 : ℝ) (As Ls Qs : ℝ → ℝ) (r : ℝ) : ℝ :=
  Ls r / (CL * r ^ 2) + urVc r * (As r / (CA * r ^ 2)) + Qs r / (q0 * r + q1) + urZi r + urLg r

/-- `R_n'`. -/
noncomputable def urRcd (CA CL q0 q1 : ℝ) (As Ls Qs As1 Ls1 Qs1 : ℝ → ℝ) (r : ℝ) : ℝ :=
  (Ls1 r * (CL * r ^ 2) - Ls r * (2 * CL * r)) / (CL * r ^ 2) ^ 2 +
    (urVcd r * (As r / (CA * r ^ 2)) +
      urVc r * ((As1 r * (CA * r ^ 2) - As r * (2 * CA * r)) / (CA * r ^ 2) ^ 2)) +
    (Qs1 r * (q0 * r + q1) - Qs r * q0) / (q0 * r + q1) ^ 2 + urZid r + urLgd r

/-- `R_n''`. -/
noncomputable def urRcdd (CA CL q0 q1 : ℝ) (As Ls Qs As1 Ls1 Qs1 As2 Ls2 Qs2 : ℝ → ℝ) (r : ℝ) :
    ℝ :=
  ((Ls2 r * (CL * r ^ 2) - Ls r * (2 * CL)) * (CL * r ^ 2) -
      2 * (2 * CL * r) * (Ls1 r * (CL * r ^ 2) - Ls r * (2 * CL * r))) / (CL * r ^ 2) ^ 3 +
    (urVcdd r * (As r / (CA * r ^ 2)) +
      2 * urVcd r * ((As1 r * (CA * r ^ 2) - As r * (2 * CA * r)) / (CA * r ^ 2) ^ 2) +
      urVc r * (((As2 r * (CA * r ^ 2) - As r * (2 * CA)) * (CA * r ^ 2) -
        2 * (2 * CA * r) * (As1 r * (CA * r ^ 2) - As r * (2 * CA * r))) / (CA * r ^ 2) ^ 3)) +
    ((Qs2 r * (q0 * r + q1) - Qs r * 0) * (q0 * r + q1) -
      2 * q0 * (Qs1 r * (q0 * r + q1) - Qs r * q0)) / (q0 * r + q1) ^ 3 +
    urZidd r + urLgdd r

/-! ### Derivatives of the components -/

theorem ur_hd_Kc (r : ℝ) : HasDerivAt urKc (2493 - 4522 * r) r := by
  convert ur_hd_quad 504 2493 (-2261) r using 1
  · funext s; unfold urKc; ring
  · ring

theorem ur_hd_Jc (r : ℝ) : HasDerivAt urJc (3645 - 2218 * r) r := by
  convert ur_hd_quad 504 3645 (-1109) r using 1
  · funext s; unfold urJc; ring
  · ring

theorem ur_hd_Fn (r : ℝ) : HasDerivAt (fun s => 84 * s - 61 * s ^ 2) (84 - 122 * r) r := by
  convert ur_hd_quad 0 84 (-61) r using 1
  · funext s; ring
  · ring

/-- `p - k s` has derivative `-k`. -/
theorem ur_hd_aff (p k r : ℝ) : HasDerivAt (fun s => p - k * s) (-k) r := by
  convert ur_hd_lin (-k) p r using 1
  · funext s; ring

theorem ur_hd_Fc {r : ℝ} (hK : urKc r ≠ 0) : HasDerivAt urFc (urFcd r) r :=
  ur_hd_quot (ur_hd_Fn r) (ur_hd_Kc r) hK

theorem ur_hd_Fcd {r : ℝ} (hK : urKc r ≠ 0) : HasDerivAt urFcd (urFcdd r) r := by
  have := ur_hd_quot2 (N := fun s => 84 * s - 61 * s ^ 2) (D := urKc)
    (N1 := fun s => 84 - 122 * s) (D1 := fun s => 2493 - 4522 * s) (ur_hd_Fn r) (ur_hd_Kc r)
    (ur_hd_aff 84 122 r) (ur_hd_aff 2493 4522 r) hK
  convert this using 1
  · rfl
  · rw [urFcdd]

theorem ur_hd_qc {r : ℝ} (hr : 0 < r) : HasDerivAt urqc (urqcd r) r := by
  have h := ur_hd_quot (ur_hd_aff 84 61 r) (ur_hd_lin 11 84 r) (by positivity)
  convert h using 1
  · funext s; unfold urqc; ring_nf
  · unfold urqcd; field_simp; ring

theorem ur_hd_qcd {r : ℝ} (hr : 0 < r) : HasDerivAt urqcd (urqcdd r) r := by
  have hD : HasDerivAt (fun s => (84 + 11 * s) ^ 2) (1848 + 242 * r) r := by
    convert ur_hd_quad 7056 1848 121 r using 1
    · funext s; ring
    · ring
  have h := ur_hd_quot (hasDerivAt_const r (-6048 : ℝ)) hD (by positivity)
  convert h using 1
  · rfl
  · rw [urqcdd]; field_simp; ring

theorem ur_hd_Vc {r : ℝ} (hr : 0 < r) (hK : urKc r ≠ 0) : HasDerivAt urVc (urVcd r) r := by
  have hq := ur_hd_qc hr
  have h := (((ur_hd_Fc hK).mul (((hq.mul hq).const_mul 85).sub_const 1)).const_mul
    (2 / 75)).const_add (1 / 1200)
  convert h using 1
  · funext s; unfold urVc; simp only [Pi.mul_apply]; ring
  · unfold urVcd; simp only [Pi.mul_apply]; ring

theorem ur_hd_Vcd {r : ℝ} (hr : 0 < r) (hK : urKc r ≠ 0) : HasDerivAt urVcd (urVcdd r) r := by
  have hq := ur_hd_qc hr
  have hqd := ur_hd_qcd hr
  have hF := ur_hd_Fc hK
  have hFd := ur_hd_Fcd hK
  have h := ((hFd.mul (((hq.mul hq).const_mul 85).sub_const 1)).add
    (((hF.const_mul 170).mul hq).mul hqd)).const_mul (2 / 75)
  convert h using 1
  · funext s; unfold urVcd; simp only [Pi.mul_apply, Pi.add_apply]; ring
  · unfold urVcdd; simp only [Pi.mul_apply]; ring

theorem ur_hd_Zi {r : ℝ} (hJ : urJc r ≠ 0) : HasDerivAt urZi (urZid r) r := by
  have hN : HasDerivAt (fun s => 1152 * s) 1152 r := by
    convert ur_hd_lin 1152 0 r using 1; funext s; ring
  have h := ur_hd_quot hN (ur_hd_Jc r) hJ
  convert h using 1
  · rfl
  · rw [urZid]

theorem ur_hd_Zid {r : ℝ} (hJ : urJc r ≠ 0) : HasDerivAt urZid (urZidd r) r := by
  have hN : HasDerivAt (fun s => 1152 * s) 1152 r := by
    convert ur_hd_lin 1152 0 r using 1; funext s; ring
  have := ur_hd_quot2 (N := fun s => 1152 * s) (D := urJc)
    (N1 := fun _ => 1152) (D1 := fun s => 3645 - 2218 * s) hN
    (ur_hd_Jc r) (hasDerivAt_const r 1152) (ur_hd_aff 3645 2218 r) hJ
  convert this using 1
  · funext s; unfold urZid; ring
  · unfold urZidd; ring

theorem ur_hd_Lg {r : ℝ} (hr : 0 < r) (hJ : 0 < urJc r) : HasDerivAt urLg (urLgd r) r := by
  have hN : HasDerivAt (fun s => 1152 * s) 1152 r := by
    convert ur_hd_lin 1152 0 r using 1; funext s; ring
  have hq := ur_hd_quot (ur_hd_Jc r) hN (by positivity)
  have h := ((hq.const_mul 2).div_const 7).log (by positivity)
  refine h.congr_deriv ?_
  unfold urLgd
  field_simp

theorem ur_hd_Lgd {r : ℝ} (hr : 0 < r) (hJ : 0 < urJc r) : HasDerivAt urLgd (urLgdd r) r := by
  have h1 := ur_hd_quot (ur_hd_aff 3645 2218 r) (ur_hd_Jc r) hJ.ne'
  have h2 := ur_hd_quot (hasDerivAt_const r (1 : ℝ)) (hasDerivAt_id r) hr.ne'
  convert h1.sub h2 using 1
  · funext s; unfold urLgd; simp only [Pi.sub_apply, id, one_div]
  · rw [urLgdd]; simp only [id]; field_simp; ring

/-- The first derivative of `R_n`. -/
theorem ur_hd_Rc {CA CL q0 q1 r : ℝ} {As Ls Qs As1 Ls1 Qs1 : ℝ → ℝ} (hr : 0 < r)
    (hCA : CA ≠ 0) (hCL : CL ≠ 0) (hq : q0 * r + q1 ≠ 0) (hK : urKc r ≠ 0) (hJ : 0 < urJc r)
    (hA : HasDerivAt As (As1 r) r) (hL : HasDerivAt Ls (Ls1 r) r) (hQ : HasDerivAt Qs (Qs1 r) r) :
    HasDerivAt (urRc CA CL q0 q1 As Ls Qs) (urRcd CA CL q0 q1 As Ls Qs As1 Ls1 Qs1 r) r := by
  have hD2 : ∀ C : ℝ, HasDerivAt (fun s => C * s ^ 2) (2 * C * r) r := fun C => by
    convert ur_hd_quad 0 0 C r using 1
    · funext s; ring
    · ring
  have hLa := ur_hd_quot hL (hD2 CL) (by positivity)
  have hAa := ur_hd_quot hA (hD2 CA) (by positivity)
  have hQa := ur_hd_quot hQ (ur_hd_lin q0 q1 r) hq
  have := (((hLa.add ((ur_hd_Vc hr hK).mul hAa)).add hQa).add (ur_hd_Zi hJ.ne')).add
    (ur_hd_Lg hr hJ)
  convert this using 1
  · funext s; unfold urRc; simp only [Pi.add_apply, Pi.mul_apply]
  · rw [urRcd]

/-- The second derivative of `R_n`. -/
theorem ur_hd_Rcd {CA CL q0 q1 r : ℝ} {As Ls Qs As1 Ls1 Qs1 As2 Ls2 Qs2 : ℝ → ℝ} (hr : 0 < r)
    (hCA : CA ≠ 0) (hCL : CL ≠ 0) (hq : q0 * r + q1 ≠ 0) (hK : urKc r ≠ 0) (hJ : 0 < urJc r)
    (hA : HasDerivAt As (As1 r) r) (hL : HasDerivAt Ls (Ls1 r) r) (hQ : HasDerivAt Qs (Qs1 r) r)
    (hA1 : HasDerivAt As1 (As2 r) r) (hL1 : HasDerivAt Ls1 (Ls2 r) r)
    (hQ1 : HasDerivAt Qs1 (Qs2 r) r) :
    HasDerivAt (urRcd CA CL q0 q1 As Ls Qs As1 Ls1 Qs1)
      (urRcdd CA CL q0 q1 As Ls Qs As1 Ls1 Qs1 As2 Ls2 Qs2 r) r := by
  have hD2 : ∀ C : ℝ, HasDerivAt (fun s => C * s ^ 2) (2 * C * r) r := fun C => by
    convert ur_hd_quad 0 0 C r using 1
    · funext s; ring
    · ring
  have hD1 : ∀ C : ℝ, HasDerivAt (fun s => 2 * C * s) (2 * C) r := fun C => by
    simpa using ur_hd_lin (2 * C) 0 r
  have hLa := ur_hd_quot2 (D := fun s => CL * s ^ 2) hL (hD2 CL) hL1 (hD1 CL) (by positivity)
  have hAa0 := ur_hd_quot hA (hD2 CA) (by positivity)
  have hAa := ur_hd_quot2 (D := fun s => CA * s ^ 2) hA (hD2 CA) hA1 (hD1 CA) (by positivity)
  have hQa := ur_hd_quot2 (D := fun s => q0 * s + q1) (D1 := fun _ => q0) hQ (ur_hd_lin q0 q1 r)
    hQ1 (hasDerivAt_const r q0) hq
  have := (((hLa.add (((ur_hd_Vcd hr hK).mul hAa0).add ((ur_hd_Vc hr hK).mul hAa))).add
    hQa).add (ur_hd_Zid hJ.ne')).add (ur_hd_Lgd hr hJ)
  convert this using 1
  · funext s; unfold urRcd; simp only [Pi.add_apply, Pi.mul_apply]
  · unfold urRcdd; ring

end SmoothedOctagon
