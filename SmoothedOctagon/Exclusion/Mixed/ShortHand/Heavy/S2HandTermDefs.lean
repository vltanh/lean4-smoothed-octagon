module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S2HandBase

/-!
# S2 hand signs: the lower-shape terminal curve, definitions

The exact-log terminal function of `archive/lighter-proofs/SHORT_RATIO_OUTER_TERMINAL_AF.md` on
the curve `α = a_f(x) = (36x + 25)/84`, `c = c_+(x) = (24x + 51)/128`, `u = u_s`, in the
coordinate `r = 1/a_f` (§2 (7)-(10)): with a constant multiplier `n ∈ {49/20, 63/25}`,
`R_n = L_n + V A_n + Q_n + 1/Z + log(2Z/7)`, `V = u_s - 3/4 = 1/1200 + (2/75)F(85q² - 1)`
(§3 (11)), `F = r(84 - 61r)/K`, `q = (84 - 61r)/(84 + 11r)`, `Z = J/(1152r)`,
`K = 504 + 2493r - 2261r²`, `J = 504 + 3645r - 1109r²`; the numerators of `A_n`, `L_n`, `Q_n`
are those of `SHORT_RATIO_OUTER_TERMINAL_ALGEBRA.md` §1. This file gives the definitions and
the first two derivatives of every component and of `R_n`.

## Main API

* The numerators `hl2Asl`, `hl2Lsl`, `hl2Qsl` (`n = 49/20`) and `hl2Ash`, `hl2Lsh`, `hl2Qsh`
  (`n = 63/25`), with derivatives (`…1`, `…2`).
* `hl2_hd_quot`, `hl2_hd_quot2`: first and second derivatives of a quotient.
* `hl2Fc`, `hl2qc`, `hl2Vc`, `hl2Zi` (`1/Z`), `hl2Lg` (`log(2Z/7)`) and their derivatives.
* `hl2Rc` (`R_n`), `hl2Rcd`, `hl2Rcdd` and `hl2_hd_Rc`, `hl2_hd_Rcd`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real Set

/-- Derivative of a polynomial of degree at most six. -/
theorem hl2_hd_poly6 (a0 a1 a2 a3 a4 a5 a6 r : ℝ) :
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
theorem hl2_hd_quot {N D : ℝ → ℝ} {N1 D1 r : ℝ} (hN : HasDerivAt N N1 r) (hD : HasDerivAt D D1 r)
    (hD0 : D r ≠ 0) :
    HasDerivAt (fun s => N s / D s) ((N1 * D r - N r * D1) / D r ^ 2) r := hN.div hD hD0

/-- Second derivative of a quotient. -/
theorem hl2_hd_quot2 {N D N1 D1 : ℝ → ℝ} {N2 D2 r : ℝ} (hN : HasDerivAt N (N1 r) r)
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
theorem hl2_hd_lin (p q r : ℝ) : HasDerivAt (fun s => p * s + q) p r := by
  simpa using ((hasDerivAt_id r).const_mul p).add_const q

/-- A quadratic function. -/
theorem hl2_hd_quad (p q k r : ℝ) :
    HasDerivAt (fun s => p + q * s + k * s ^ 2) (q + 2 * k * r) r := by
  convert hl2_hd_poly6 p q k 0 0 0 0 r using 1
  · funext s; ring
  · ring

/-- `Asl` numerator (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Asl (r : ℝ) : ℝ :=
  10553281375 * r ^ 6 - 103680325518 * r ^ 5 + 332580904767 * r ^ 4 - 411951691728 * r ^ 3 -
    142211039040 * r ^ 2 + 377902651392 * r + 53258010624

/-- `Asl` first derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Asl1 (r : ℝ) : ℝ :=
  63319688250 * r ^ 5 - 518401627590 * r ^ 4 + 1330323619068 * r ^ 3 - 1235855075184 * r ^ 2 -
    284422078080 * r + 377902651392

/-- `Asl` second derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Asl2 (r : ℝ) : ℝ :=
  316598441250 * r ^ 4 - 2073606510360 * r ^ 3 + 3990970857204 * r ^ 2 - 2471710150368 * r -
    284422078080

/-- `Lsl` numerator (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Lsl (r : ℝ) : ℝ :=
  8904843871 * r ^ 6 - 62623679118 * r ^ 5 + 267084640575 * r ^ 4 - 350015430096 * r ^ 3 +
    204186495168 * r ^ 2 - 60228790272 * r - 12290310144

/-- `Lsl` first derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Lsl1 (r : ℝ) : ℝ :=
  53429063226 * r ^ 5 - 313118395590 * r ^ 4 + 1068338562300 * r ^ 3 - 1050046290288 * r ^ 2 +
    408372990336 * r - 60228790272

/-- `Lsl` second derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Lsl2 (r : ℝ) : ℝ :=
  267145316130 * r ^ 4 - 1252473582360 * r ^ 3 + 3205015686900 * r ^ 2 - 2100092580576 * r +
    408372990336

/-- `Qsl` numerator (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Qsl (r : ℝ) : ℝ :=
  250523 * r ^ 5 - 1486275 * r ^ 4 + 2522154 * r ^ 3 - 8748306 * r ^ 2 + 6114096 * r + 1016064

/-- `Qsl` first derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Qsl1 (r : ℝ) : ℝ :=
  1252615 * r ^ 4 - 5945100 * r ^ 3 + 7566462 * r ^ 2 - 17496612 * r + 6114096

/-- `Qsl` second derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Qsl2 (r : ℝ) : ℝ :=
  5010460 * r ^ 3 - 17835300 * r ^ 2 + 15132924 * r - 17496612

/-- `Ash` numerator (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Ash (r : ℝ) : ℝ :=
  1507611625 * r ^ 6 - 14811475074 * r ^ 5 + 47383333641 * r ^ 4 - 58001053104 * r ^ 3 -
    21418395840 * r ^ 2 + 53324199936 * r + 7608287232

/-- `Ash` first derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Ash1 (r : ℝ) : ℝ :=
  9045669750 * r ^ 5 - 74057375370 * r ^ 4 + 189533334564 * r ^ 3 - 174003159312 * r ^ 2 -
    42836791680 * r + 53324199936

/-- `Ash` second derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Ash2 (r : ℝ) : ℝ :=
  45228348750 * r ^ 4 - 296229501480 * r ^ 3 + 568600003692 * r ^ 2 - 348006318624 * r -
    42836791680

/-- `Lsh` numerator (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Lsh (r : ℝ) : ℝ :=
  1272120553 * r ^ 6 - 8946239874 * r ^ 5 + 38058322185 * r ^ 4 - 49565800368 * r ^ 3 +
    28885149504 * r ^ 2 - 8489650176 * r - 1755758592

/-- `Lsh` first derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Lsh1 (r : ℝ) : ℝ :=
  7632723318 * r ^ 5 - 44731199370 * r ^ 4 + 152233288740 * r ^ 3 - 148697401104 * r ^ 2 +
    57770299008 * r - 8489650176

/-- `Lsh` second derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Lsh2 (r : ℝ) : ℝ :=
  38163616590 * r ^ 4 - 178924797480 * r ^ 3 + 456699866220 * r ^ 2 - 297394802208 * r +
    57770299008

/-- `Qsh` numerator (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Qsh (r : ℝ) : ℝ :=
  35789 * r ^ 5 - 212325 * r ^ 4 + 358662 * r ^ 3 - 1249758 * r ^ 2 + 863568 * r + 145152

/-- `Qsh` first derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Qsh1 (r : ℝ) : ℝ :=
  178945 * r ^ 4 - 849300 * r ^ 3 + 1075986 * r ^ 2 - 2499516 * r + 863568

/-- `Qsh` second derivative (`SHORT_RATIO_OUTER_TERMINAL_ALGEBRA` §1). -/
noncomputable def hl2Qsh2 (r : ℝ) : ℝ :=
  715780 * r ^ 3 - 2547900 * r ^ 2 + 2151972 * r - 2499516

theorem hl2_hd_Asl (r : ℝ) : HasDerivAt hl2Asl (hl2Asl1 r) r := by
  convert hl2_hd_poly6 53258010624 377902651392 (-142211039040) (-411951691728) 332580904767 (-103680325518) 10553281375 r using 1
  · funext s; unfold hl2Asl; ring
  · unfold hl2Asl1; ring

theorem hl2_hd_Asl1 (r : ℝ) : HasDerivAt hl2Asl1 (hl2Asl2 r) r := by
  convert hl2_hd_poly6 377902651392 (-284422078080) (-1235855075184) 1330323619068 (-518401627590) 63319688250 0 r using 1
  · funext s; unfold hl2Asl1; ring
  · unfold hl2Asl2; ring

theorem hl2_hd_Lsl (r : ℝ) : HasDerivAt hl2Lsl (hl2Lsl1 r) r := by
  convert hl2_hd_poly6 (-12290310144) (-60228790272) 204186495168 (-350015430096) 267084640575 (-62623679118) 8904843871 r using 1
  · funext s; unfold hl2Lsl; ring
  · unfold hl2Lsl1; ring

theorem hl2_hd_Lsl1 (r : ℝ) : HasDerivAt hl2Lsl1 (hl2Lsl2 r) r := by
  convert hl2_hd_poly6 (-60228790272) 408372990336 (-1050046290288) 1068338562300 (-313118395590) 53429063226 0 r using 1
  · funext s; unfold hl2Lsl1; ring
  · unfold hl2Lsl2; ring

theorem hl2_hd_Qsl (r : ℝ) : HasDerivAt hl2Qsl (hl2Qsl1 r) r := by
  convert hl2_hd_poly6 1016064 6114096 (-8748306) 2522154 (-1486275) 250523 0 r using 1
  · funext s; unfold hl2Qsl; ring
  · unfold hl2Qsl1; ring

theorem hl2_hd_Qsl1 (r : ℝ) : HasDerivAt hl2Qsl1 (hl2Qsl2 r) r := by
  convert hl2_hd_poly6 6114096 (-17496612) 7566462 (-5945100) 1252615 0 0 r using 1
  · funext s; unfold hl2Qsl1; ring
  · unfold hl2Qsl2; ring

theorem hl2_hd_Ash (r : ℝ) : HasDerivAt hl2Ash (hl2Ash1 r) r := by
  convert hl2_hd_poly6 7608287232 53324199936 (-21418395840) (-58001053104) 47383333641 (-14811475074) 1507611625 r using 1
  · funext s; unfold hl2Ash; ring
  · unfold hl2Ash1; ring

theorem hl2_hd_Ash1 (r : ℝ) : HasDerivAt hl2Ash1 (hl2Ash2 r) r := by
  convert hl2_hd_poly6 53324199936 (-42836791680) (-174003159312) 189533334564 (-74057375370) 9045669750 0 r using 1
  · funext s; unfold hl2Ash1; ring
  · unfold hl2Ash2; ring

theorem hl2_hd_Lsh (r : ℝ) : HasDerivAt hl2Lsh (hl2Lsh1 r) r := by
  convert hl2_hd_poly6 (-1755758592) (-8489650176) 28885149504 (-49565800368) 38058322185 (-8946239874) 1272120553 r using 1
  · funext s; unfold hl2Lsh; ring
  · unfold hl2Lsh1; ring

theorem hl2_hd_Lsh1 (r : ℝ) : HasDerivAt hl2Lsh1 (hl2Lsh2 r) r := by
  convert hl2_hd_poly6 (-8489650176) 57770299008 (-148697401104) 152233288740 (-44731199370) 7632723318 0 r using 1
  · funext s; unfold hl2Lsh1; ring
  · unfold hl2Lsh2; ring

theorem hl2_hd_Qsh (r : ℝ) : HasDerivAt hl2Qsh (hl2Qsh1 r) r := by
  convert hl2_hd_poly6 145152 863568 (-1249758) 358662 (-212325) 35789 0 r using 1
  · funext s; unfold hl2Qsh; ring
  · unfold hl2Qsh1; ring

theorem hl2_hd_Qsh1 (r : ℝ) : HasDerivAt hl2Qsh1 (hl2Qsh2 r) r := by
  convert hl2_hd_poly6 863568 (-2499516) 1075986 (-849300) 178945 0 0 r using 1
  · funext s; unfold hl2Qsh1; ring
  · unfold hl2Qsh2; ring

/-! ### The curve components -/

/-- `K = 504 + 2493r - 2261r²`. -/
noncomputable def hl2Kc (r : ℝ) : ℝ := 504 + 2493 * r - 2261 * r ^ 2

/-- `J = 504 + 3645r - 1109r²`, `Z = J/(1152r)`. -/
noncomputable def hl2Jc (r : ℝ) : ℝ := 504 + 3645 * r - 1109 * r ^ 2

/-- `F = r(84 - 61r)/K` (`TERMINAL_AF` (11)). -/
noncomputable def hl2Fc (r : ℝ) : ℝ := (84 * r - 61 * r ^ 2) / hl2Kc r

noncomputable def hl2Fcd (r : ℝ) : ℝ :=
  ((84 - 122 * r) * hl2Kc r - (84 * r - 61 * r ^ 2) * (2493 - 4522 * r)) / hl2Kc r ^ 2

noncomputable def hl2Fcdd (r : ℝ) : ℝ :=
  ((-122 * hl2Kc r - (84 * r - 61 * r ^ 2) * (-4522)) * hl2Kc r -
    2 * (2493 - 4522 * r) * ((84 - 122 * r) * hl2Kc r - (84 * r - 61 * r ^ 2) * (2493 - 4522 * r))) /
    hl2Kc r ^ 3

/-- `q = (84 - 61r)/(84 + 11r)` (`TERMINAL_AF` (11)). -/
noncomputable def hl2qc (r : ℝ) : ℝ := (84 - 61 * r) / (84 + 11 * r)

noncomputable def hl2qcd (r : ℝ) : ℝ := -6048 / (84 + 11 * r) ^ 2

noncomputable def hl2qcdd (r : ℝ) : ℝ := 133056 / (84 + 11 * r) ^ 3

/-- `V = u_s - 3/4 = 1/1200 + (2/75)F(85q² - 1)` (`TERMINAL_AF` (11)). -/
noncomputable def hl2Vc (r : ℝ) : ℝ := 1 / 1200 + 2 / 75 * hl2Fc r * (85 * hl2qc r ^ 2 - 1)

noncomputable def hl2Vcd (r : ℝ) : ℝ :=
  2 / 75 * (hl2Fcd r * (85 * hl2qc r ^ 2 - 1) + 170 * hl2Fc r * hl2qc r * hl2qcd r)

noncomputable def hl2Vcdd (r : ℝ) : ℝ :=
  2 / 75 * (hl2Fcdd r * (85 * hl2qc r ^ 2 - 1) + 340 * hl2Fcd r * hl2qc r * hl2qcd r +
    170 * hl2Fc r * (hl2qcd r ^ 2 + hl2qc r * hl2qcdd r))

/-- `1/Z = 1152r/J`. -/
noncomputable def hl2Zi (r : ℝ) : ℝ := 1152 * r / hl2Jc r

noncomputable def hl2Zid (r : ℝ) : ℝ := (1152 * hl2Jc r - 1152 * r * (3645 - 2218 * r)) / hl2Jc r ^ 2

noncomputable def hl2Zidd (r : ℝ) : ℝ :=
  ((0 * hl2Jc r - 1152 * r * (-2218)) * hl2Jc r -
    2 * (3645 - 2218 * r) * (1152 * hl2Jc r - 1152 * r * (3645 - 2218 * r))) / hl2Jc r ^ 3

/-- `log(2Z/7)`. -/
noncomputable def hl2Lg (r : ℝ) : ℝ := log (2 * (hl2Jc r / (1152 * r)) / 7)

noncomputable def hl2Lgd (r : ℝ) : ℝ := (3645 - 2218 * r) / hl2Jc r - 1 / r

noncomputable def hl2Lgdd (r : ℝ) : ℝ :=
  (-2218 * hl2Jc r - (3645 - 2218 * r) ^ 2) / hl2Jc r ^ 2 + 1 / r ^ 2

/-- The terminal function `R_n` (`TERMINAL_AF` (9)) for numerators `As`, `Ls`, `Qs` with
denominators `CA r²`, `CL r²`, `q₀r + q₁`. -/
noncomputable def hl2Rc (CA CL q0 q1 : ℝ) (As Ls Qs : ℝ → ℝ) (r : ℝ) : ℝ :=
  Ls r / (CL * r ^ 2) + hl2Vc r * (As r / (CA * r ^ 2)) + Qs r / (q0 * r + q1) + hl2Zi r + hl2Lg r

/-- `R_n'`. -/
noncomputable def hl2Rcd (CA CL q0 q1 : ℝ) (As Ls Qs As1 Ls1 Qs1 : ℝ → ℝ) (r : ℝ) : ℝ :=
  (Ls1 r * (CL * r ^ 2) - Ls r * (2 * CL * r)) / (CL * r ^ 2) ^ 2 +
    (hl2Vcd r * (As r / (CA * r ^ 2)) +
      hl2Vc r * ((As1 r * (CA * r ^ 2) - As r * (2 * CA * r)) / (CA * r ^ 2) ^ 2)) +
    (Qs1 r * (q0 * r + q1) - Qs r * q0) / (q0 * r + q1) ^ 2 + hl2Zid r + hl2Lgd r

/-- `R_n''`. -/
noncomputable def hl2Rcdd (CA CL q0 q1 : ℝ) (As Ls Qs As1 Ls1 Qs1 As2 Ls2 Qs2 : ℝ → ℝ) (r : ℝ) :
    ℝ :=
  ((Ls2 r * (CL * r ^ 2) - Ls r * (2 * CL)) * (CL * r ^ 2) -
      2 * (2 * CL * r) * (Ls1 r * (CL * r ^ 2) - Ls r * (2 * CL * r))) / (CL * r ^ 2) ^ 3 +
    (hl2Vcdd r * (As r / (CA * r ^ 2)) +
      2 * hl2Vcd r * ((As1 r * (CA * r ^ 2) - As r * (2 * CA * r)) / (CA * r ^ 2) ^ 2) +
      hl2Vc r * (((As2 r * (CA * r ^ 2) - As r * (2 * CA)) * (CA * r ^ 2) -
        2 * (2 * CA * r) * (As1 r * (CA * r ^ 2) - As r * (2 * CA * r))) / (CA * r ^ 2) ^ 3)) +
    ((Qs2 r * (q0 * r + q1) - Qs r * 0) * (q0 * r + q1) -
      2 * q0 * (Qs1 r * (q0 * r + q1) - Qs r * q0)) / (q0 * r + q1) ^ 3 +
    hl2Zidd r + hl2Lgdd r

/-! ### Derivatives of the components -/

theorem hl2_hd_Kc (r : ℝ) : HasDerivAt hl2Kc (2493 - 4522 * r) r := by
  convert hl2_hd_quad 504 2493 (-2261) r using 1
  · funext s; unfold hl2Kc; ring
  · ring

theorem hl2_hd_Jc (r : ℝ) : HasDerivAt hl2Jc (3645 - 2218 * r) r := by
  convert hl2_hd_quad 504 3645 (-1109) r using 1
  · funext s; unfold hl2Jc; ring
  · ring

theorem hl2_hd_Fn (r : ℝ) : HasDerivAt (fun s => 84 * s - 61 * s ^ 2) (84 - 122 * r) r := by
  convert hl2_hd_quad 0 84 (-61) r using 1
  · funext s; ring
  · ring

/-- `p - k s` has derivative `-k`. -/
theorem hl2_hd_aff (p k r : ℝ) : HasDerivAt (fun s => p - k * s) (-k) r := by
  convert hl2_hd_lin (-k) p r using 1
  · funext s; ring

theorem hl2_hd_Fc {r : ℝ} (hK : hl2Kc r ≠ 0) : HasDerivAt hl2Fc (hl2Fcd r) r :=
  hl2_hd_quot (hl2_hd_Fn r) (hl2_hd_Kc r) hK

theorem hl2_hd_Fcd {r : ℝ} (hK : hl2Kc r ≠ 0) : HasDerivAt hl2Fcd (hl2Fcdd r) r := by
  have := hl2_hd_quot2 (N := fun s => 84 * s - 61 * s ^ 2) (D := hl2Kc)
    (N1 := fun s => 84 - 122 * s) (D1 := fun s => 2493 - 4522 * s) (hl2_hd_Fn r) (hl2_hd_Kc r)
    (hl2_hd_aff 84 122 r) (hl2_hd_aff 2493 4522 r) hK
  convert this using 1
  · rfl
  · rw [hl2Fcdd]

theorem hl2_hd_qc {r : ℝ} (hr : 0 < r) : HasDerivAt hl2qc (hl2qcd r) r := by
  have h := hl2_hd_quot (hl2_hd_aff 84 61 r) (hl2_hd_lin 11 84 r) (by positivity)
  convert h using 1
  · funext s; unfold hl2qc; ring_nf
  · unfold hl2qcd; field_simp; ring

theorem hl2_hd_qcd {r : ℝ} (hr : 0 < r) : HasDerivAt hl2qcd (hl2qcdd r) r := by
  have hD : HasDerivAt (fun s => (84 + 11 * s) ^ 2) (1848 + 242 * r) r := by
    convert hl2_hd_quad 7056 1848 121 r using 1
    · funext s; ring
    · ring
  have h := hl2_hd_quot (hasDerivAt_const r (-6048 : ℝ)) hD (by positivity)
  convert h using 1
  · rfl
  · rw [hl2qcdd]; field_simp; ring

theorem hl2_hd_Vc {r : ℝ} (hr : 0 < r) (hK : hl2Kc r ≠ 0) : HasDerivAt hl2Vc (hl2Vcd r) r := by
  have hq := hl2_hd_qc hr
  have h := (((hl2_hd_Fc hK).mul (((hq.mul hq).const_mul 85).sub_const 1)).const_mul
    (2 / 75)).const_add (1 / 1200)
  convert h using 1
  · funext s; unfold hl2Vc; simp only [Pi.mul_apply]; ring
  · unfold hl2Vcd; simp only [Pi.mul_apply]; ring

theorem hl2_hd_Vcd {r : ℝ} (hr : 0 < r) (hK : hl2Kc r ≠ 0) : HasDerivAt hl2Vcd (hl2Vcdd r) r := by
  have hq := hl2_hd_qc hr
  have hqd := hl2_hd_qcd hr
  have hF := hl2_hd_Fc hK
  have hFd := hl2_hd_Fcd hK
  have h := ((hFd.mul (((hq.mul hq).const_mul 85).sub_const 1)).add
    (((hF.const_mul 170).mul hq).mul hqd)).const_mul (2 / 75)
  convert h using 1
  · funext s; unfold hl2Vcd; simp only [Pi.mul_apply, Pi.add_apply]; ring
  · unfold hl2Vcdd; simp only [Pi.mul_apply]; ring

theorem hl2_hd_Zi {r : ℝ} (hJ : hl2Jc r ≠ 0) : HasDerivAt hl2Zi (hl2Zid r) r := by
  have hN : HasDerivAt (fun s => 1152 * s) 1152 r := by
    convert hl2_hd_lin 1152 0 r using 1; funext s; ring
  have h := hl2_hd_quot hN (hl2_hd_Jc r) hJ
  convert h using 1
  · rfl
  · rw [hl2Zid]

theorem hl2_hd_Zid {r : ℝ} (hJ : hl2Jc r ≠ 0) : HasDerivAt hl2Zid (hl2Zidd r) r := by
  have hN : HasDerivAt (fun s => 1152 * s) 1152 r := by
    convert hl2_hd_lin 1152 0 r using 1; funext s; ring
  have := hl2_hd_quot2 (N := fun s => 1152 * s) (D := hl2Jc)
    (N1 := fun _ => 1152) (D1 := fun s => 3645 - 2218 * s) hN
    (hl2_hd_Jc r) (hasDerivAt_const r 1152) (hl2_hd_aff 3645 2218 r) hJ
  convert this using 1
  · funext s; unfold hl2Zid; ring
  · unfold hl2Zidd; ring

theorem hl2_hd_Lg {r : ℝ} (hr : 0 < r) (hJ : 0 < hl2Jc r) : HasDerivAt hl2Lg (hl2Lgd r) r := by
  have hN : HasDerivAt (fun s => 1152 * s) 1152 r := by
    convert hl2_hd_lin 1152 0 r using 1; funext s; ring
  have hq := hl2_hd_quot (hl2_hd_Jc r) hN (by positivity)
  have h := ((hq.const_mul 2).div_const 7).log (by positivity)
  refine h.congr_deriv ?_
  unfold hl2Lgd
  field_simp

theorem hl2_hd_Lgd {r : ℝ} (hr : 0 < r) (hJ : 0 < hl2Jc r) : HasDerivAt hl2Lgd (hl2Lgdd r) r := by
  have h1 := hl2_hd_quot (hl2_hd_aff 3645 2218 r) (hl2_hd_Jc r) hJ.ne'
  have h2 := hl2_hd_quot (hasDerivAt_const r (1 : ℝ)) (hasDerivAt_id r) hr.ne'
  convert h1.sub h2 using 1
  · funext s; unfold hl2Lgd; simp only [Pi.sub_apply, id, one_div]
  · rw [hl2Lgdd]; simp only [id]; field_simp; ring

/-- The first derivative of `R_n`. -/
theorem hl2_hd_Rc {CA CL q0 q1 r : ℝ} {As Ls Qs As1 Ls1 Qs1 : ℝ → ℝ} (hr : 0 < r)
    (hCA : CA ≠ 0) (hCL : CL ≠ 0) (hq : q0 * r + q1 ≠ 0) (hK : hl2Kc r ≠ 0) (hJ : 0 < hl2Jc r)
    (hA : HasDerivAt As (As1 r) r) (hL : HasDerivAt Ls (Ls1 r) r) (hQ : HasDerivAt Qs (Qs1 r) r) :
    HasDerivAt (hl2Rc CA CL q0 q1 As Ls Qs) (hl2Rcd CA CL q0 q1 As Ls Qs As1 Ls1 Qs1 r) r := by
  have hD2 : ∀ C : ℝ, HasDerivAt (fun s => C * s ^ 2) (2 * C * r) r := fun C => by
    convert hl2_hd_quad 0 0 C r using 1
    · funext s; ring
    · ring
  have hLa := hl2_hd_quot hL (hD2 CL) (by positivity)
  have hAa := hl2_hd_quot hA (hD2 CA) (by positivity)
  have hQa := hl2_hd_quot hQ (hl2_hd_lin q0 q1 r) hq
  have := (((hLa.add ((hl2_hd_Vc hr hK).mul hAa)).add hQa).add (hl2_hd_Zi hJ.ne')).add
    (hl2_hd_Lg hr hJ)
  convert this using 1
  · funext s; unfold hl2Rc; simp only [Pi.add_apply, Pi.mul_apply]
  · rw [hl2Rcd]

/-- The second derivative of `R_n`. -/
theorem hl2_hd_Rcd {CA CL q0 q1 r : ℝ} {As Ls Qs As1 Ls1 Qs1 As2 Ls2 Qs2 : ℝ → ℝ} (hr : 0 < r)
    (hCA : CA ≠ 0) (hCL : CL ≠ 0) (hq : q0 * r + q1 ≠ 0) (hK : hl2Kc r ≠ 0) (hJ : 0 < hl2Jc r)
    (hA : HasDerivAt As (As1 r) r) (hL : HasDerivAt Ls (Ls1 r) r) (hQ : HasDerivAt Qs (Qs1 r) r)
    (hA1 : HasDerivAt As1 (As2 r) r) (hL1 : HasDerivAt Ls1 (Ls2 r) r)
    (hQ1 : HasDerivAt Qs1 (Qs2 r) r) :
    HasDerivAt (hl2Rcd CA CL q0 q1 As Ls Qs As1 Ls1 Qs1)
      (hl2Rcdd CA CL q0 q1 As Ls Qs As1 Ls1 Qs1 As2 Ls2 Qs2 r) r := by
  have hD2 : ∀ C : ℝ, HasDerivAt (fun s => C * s ^ 2) (2 * C * r) r := fun C => by
    convert hl2_hd_quad 0 0 C r using 1
    · funext s; ring
    · ring
  have hD1 : ∀ C : ℝ, HasDerivAt (fun s => 2 * C * s) (2 * C) r := fun C => by
    simpa using hl2_hd_lin (2 * C) 0 r
  have hLa := hl2_hd_quot2 (D := fun s => CL * s ^ 2) hL (hD2 CL) hL1 (hD1 CL) (by positivity)
  have hAa0 := hl2_hd_quot hA (hD2 CA) (by positivity)
  have hAa := hl2_hd_quot2 (D := fun s => CA * s ^ 2) hA (hD2 CA) hA1 (hD1 CA) (by positivity)
  have hQa := hl2_hd_quot2 (D := fun s => q0 * s + q1) (D1 := fun _ => q0) hQ (hl2_hd_lin q0 q1 r)
    hQ1 (hasDerivAt_const r q0) hq
  have := (((hLa.add (((hl2_hd_Vcd hr hK).mul hAa0).add ((hl2_hd_Vc hr hK).mul hAa))).add
    hQa).add (hl2_hd_Zid hJ.ne')).add (hl2_hd_Lgd hr hJ)
  convert this using 1
  · funext s; unfold hl2Rcd; simp only [Pi.add_apply, Pi.mul_apply]
  · unfold hl2Rcdd; ring

end SmoothedOctagon
