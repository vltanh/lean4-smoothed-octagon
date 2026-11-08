module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandDefs

/-!
# Gate S4, hand proof W4: the separately concave numerator `N`

`archive/lighter-proofs/SHORT_CASIMIR_BOUNDARY_DERIVATIVES.md` §3. On the boundary `d = 1/19`
(`b = 20x/19`, `a` fixed) with the affine lower incoming curve `v = 757/1000 + 9(x - 2)/1000`,
the numerator of `f + 9/200` is the eight-term product source (5)

`N = 90250aC*²(W'K - 2WK') + 45125C*²K³(v'B + (v - 1)B') - 45125·361a²B'K³ + 45125a³C*²K'K -
  45125aC*²(Q'K - QK')K + 45125·19aC*B'K³ - 45125aC*²K'K² + (9/200)45125aC*²K³`,

`C* = 19a + 20x`, `B = C*/19`, `W = M + vD² - DE`, `Q = 2vD - E`, primes = `x`-derivatives.
Its two second derivatives are computed by composing second-order jets (`HL46J`) of the
factors before any expansion: `-N_aa = P_A(c, h)`, `-N_xx = P_X(c, h)` (`c = a - 1`, `h = x - 2`,
the note's printed polynomials). On `1/8 ≤ c ≤ 1/6`, `0 ≤ h ≤ 1/6` both are positive by the
note's monomial rule (`c = 1/8` in positive, `c = 1/6` in negative terms, then `h = 1/6` in the
negative terms of the resulting lower polynomial `L_A`, `L_X`). With the four positive corner values
this gives `N > 0` on `[2, 13/6] × [108/95, 22/19]` (concave minimum in `a`, then in `x` at the two
end values of `a`).

## Main API

* Building blocks `hl46W4v`, `hl46W4M`, `hl46W4Mx`, `hl46W4E`, `hl46W4Ex`, `hl46W4K`, `hl46W4Cs`,
  `hl46W4D`, `hl46W4Dx`, `hl46W4W`, `hl46W4Wx`, `hl46W4Q`, `hl46W4Qx`; the source `hl46W4N`;
  `hl46W4PA`, `hl46W4PX`.
* `hl46W4_N_jet_a`, `hl46W4_N_jet_x`: `N_aa = -P_A`, `N_xx = -P_X`.
* `hl46W4_mlo`, `hl46W4_mhi` (monomial rule), `hl46W4_PA_pos`, `hl46W4_PX_pos`,
  `hl46W4_N_corners`, `hl46W4_N_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set

/-- The affine lower incoming curve `v(x) = 757/1000 + 9(x - 2)/1000` (note (2)). -/
noncomputable def hl46W4v (x : ℝ) : ℝ := 757 / 1000 + 9 / 1000 * (x - 2)

/-- `M = S²(S² - S + 1)`, `S = 1 + x`. -/
noncomputable def hl46W4M (x : ℝ) : ℝ := (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1)

/-- `M' = 4S³ - 3S² + 2S`. -/
noncomputable def hl46W4Mx (x : ℝ) : ℝ := 4 * (1 + x) ^ 3 - 3 * (1 + x) ^ 2 + 2 * (1 + x)

/-- `E = S³(v - 1) + 3S - 1` on the lower curve `u = v(x)`. -/
noncomputable def hl46W4E (x : ℝ) : ℝ := hh46S4P x (hl46W4v x)

/-- `E' = 3S²(v - 1) + S³v' + 3`, `v' = 9/1000`. -/
noncomputable def hl46W4Ex (x : ℝ) : ℝ :=
  3 * (1 + x) ^ 2 * (hl46W4v x - 1) + (1 + x) ^ 3 * (9 / 1000) + 3

/-- `K = x(x + 2) + a²`. -/
noncomputable def hl46W4K (x a : ℝ) : ℝ := x * (x + 2) + a ^ 2

/-- `C* = 19a + 20x = 19B`. -/
noncomputable def hl46W4Cs (x a : ℝ) : ℝ := 19 * a + 20 * x

/-- `D = a² + 2ab + 1 + 2x - 2bx` at `b = 20x/19`. -/
noncomputable def hl46W4D (x a : ℝ) : ℝ := hsDg x (x * (1 + 1 / 19)) a

/-- `D' = 40a/19 + 2 - 80x/19`. -/
noncomputable def hl46W4Dx (x a : ℝ) : ℝ := 2 * a * (1 + 1 / 19) + 2 - 4 * x * (1 + 1 / 19)

/-- `W = M + vD² - DE` (so `w = W/K²` at `u = v`). -/
noncomputable def hl46W4W (x a : ℝ) : ℝ :=
  hl46W4M x + hl46W4D x a ^ 2 * hl46W4v x - hl46W4D x a * hl46W4E x

/-- `W' = M' + 2vDD' + v'D² - D'E - DE'`. -/
noncomputable def hl46W4Wx (x a : ℝ) : ℝ :=
  hl46W4Mx x + 2 * hl46W4D x a * hl46W4Dx x a * hl46W4v x + hl46W4D x a ^ 2 * (9 / 1000) -
    hl46W4Dx x a * hl46W4E x - hl46W4D x a * hl46W4Ex x

/-- `Q = 2vD - E` (so `E_L = Q/K` at `u = v`). -/
noncomputable def hl46W4Q (x a : ℝ) : ℝ := 2 * hl46W4D x a * hl46W4v x - hl46W4E x

/-- `Q' = 2vD' + 2v'D - E'`. -/
noncomputable def hl46W4Qx (x a : ℝ) : ℝ :=
  2 * hl46W4Dx x a * hl46W4v x + 2 * hl46W4D x a * (9 / 1000) - hl46W4Ex x

/-- The eight-term product source (5): `N = 45125aC*²K³(f + 9/200)`. -/
noncomputable def hl46W4N (x a : ℝ) : ℝ :=
  90250 * a * hl46W4Cs x a ^ 2 * (hl46W4Wx x a * hl46W4K x a - 2 * hl46W4W x a * (2 * x + 2)) +
  45125 * hl46W4Cs x a ^ 2 * hl46W4K x a ^ 3 *
    (9 / 1000 * (hl46W4Cs x a / 19) + (hl46W4v x - 1) * (20 / 19)) -
  45125 * 361 * a ^ 2 * (20 / 19) * hl46W4K x a ^ 3 +
  45125 * a ^ 3 * hl46W4Cs x a ^ 2 * (2 * x + 2) * hl46W4K x a -
  45125 * a * hl46W4Cs x a ^ 2 * (hl46W4Qx x a * hl46W4K x a - hl46W4Q x a * (2 * x + 2)) *
    hl46W4K x a +
  45125 * 19 * a * hl46W4Cs x a * (20 / 19) * hl46W4K x a ^ 3 -
  45125 * a * hl46W4Cs x a ^ 2 * (2 * x + 2) * hl46W4K x a ^ 2 +
  9 / 200 * 45125 * a * hl46W4Cs x a ^ 2 * hl46W4K x a ^ 3

/-- The note's `P_A(c, h) = -N_aa`. -/
noncomputable def hl46W4PA (c h : ℝ) : ℝ :=
  -63336006 * c ^ 7 - 190131480 * c ^ 6 * h - 3411515702 * c ^ 6 + 24630669 * c ^ 5 * h ^ 3 -
    (1339539957 / 2) * c ^ 5 * h ^ 2 - 12899389902 * c ^ 5 * h - 38269433832 * c ^ 5 +
    129635100 * c ^ 4 * h ^ 4 - 1384476705 * c ^ 4 * h ^ 3 + (1869625365 / 2) * c ^ 4 * h ^ 2 -
    13147630260 * c ^ 4 * h - 76129292340 * c ^ 4 + 51285465 * c ^ 3 * h ^ 5 +
    411975225 * c ^ 3 * h ^ 4 + 13232985800 * c ^ 3 * h ^ 3 + 128959957955 * c ^ 3 * h ^ 2 +
    307044832385 * c ^ 3 * h + 161763249920 * c ^ 3 - 67346640 * c ^ 2 * h ^ 6 +
    1058631255 * c ^ 2 * h ^ 5 + 10418692425 * c ^ 2 * h ^ 4 + 75222577320 * c ^ 2 * h ^ 3 +
    380210764425 * c ^ 2 * h ^ 2 + 804919769895 * c ^ 2 * h + 538404182004 * c ^ 2 -
    (63683307 / 2) * c * h ^ 7 + (285274251 / 2) * c * h ^ 6 + 2457318186 * c * h ^ 5 -
    1814606481 * c * h ^ 4 - (60062007819 / 2) * c * h ^ 3 + (96658382163 / 2) * c * h ^ 2 +
    317958337773 * c * h + 288505318770 * c - 5065020 * h ^ 8 - (119973087 / 2) * h ^ 7 +
    (808687201 / 2) * h ^ 6 + 3884414146 * h ^ 5 - 833702501 * h ^ 4 - (121026207631 / 2) * h ^ 3 -
    (304669396099 / 2) * h ^ 2 - 126156559259 * h - 22982058630

/-- The note's `P_X(c, h) = -N_xx`. -/
noncomputable def hl46W4PX (c h : ℝ) : ℝ :=
  3518667 * c ^ 7 * h - (63787617 / 2) * c ^ 7 + 51854040 * c ^ 6 * h ^ 2 - 276895341 * c ^ 6 * h +
    (124641691 / 2) * c ^ 6 + 51285465 * c ^ 5 * h ^ 3 + 247185135 * c ^ 5 * h ^ 2 +
    3969895740 * c ^ 5 * h + (25791991591 / 2) * c ^ 5 - 168366600 * c ^ 4 * h ^ 4 +
    1764385425 * c ^ 4 * h ^ 3 + 10418692425 * c ^ 4 * h ^ 2 + 37611288660 * c ^ 4 * h +
    (126736921475 / 2) * c ^ 4 - (445783149 / 2) * c ^ 3 * h ^ 5 +
    (1426371255 / 2) * c ^ 3 * h ^ 4 + 8191060620 * c ^ 3 * h ^ 3 - 3629212962 * c ^ 3 * h ^ 2 -
    (60062007819 / 2) * c ^ 3 * h + (32219460721 / 2) * c ^ 3 - 141820560 * c ^ 2 * h ^ 6 -
    (2519434827 / 2) * c ^ 2 * h ^ 5 + (12130308015 / 2) * c ^ 2 * h ^ 4 +
    38844141460 * c ^ 2 * h ^ 3 - 5002215006 * c ^ 2 * h ^ 2 - (363078622893 / 2) * c ^ 2 * h -
    (304669396099 / 2) * c ^ 2 - 121888800 * c * h ^ 7 - 1328584320 * c * h ^ 6 +
    (3371204193 / 2) * c * h ^ 5 + (129290985465 / 2) * c * h ^ 4 + 262820081435 * c * h ^ 3 +
    384548364339 * c * h ^ 2 + (269070634521 / 2) * c * h - (150855982151 / 2) * c -
    146512800 * h ^ 7 - 1368707760 * h ^ 6 + (7369631871 / 2) * h ^ 5 + (149621701905 / 2) * h ^ 4 +
    300221900635 * h ^ 3 + 530041237053 * h ^ 2 + (846227115771 / 2) * h + (235576507477 / 2)

/-! ### Second-order jets of `N` -/

/-- Jet of a constant. -/
private theorem jc (c y : ℝ) : HL46J (fun _ => c) (fun _ => 0) (fun _ => 0) y :=
  ⟨hasDerivAt_const y c, hasDerivAt_const y 0⟩

/-- Jet of the identity. -/
private theorem jid (y : ℝ) : HL46J (fun y => y) (fun _ => 1) (fun _ => 0) y :=
  ⟨hasDerivAt_id' y, hasDerivAt_const y 1⟩

/-- Jet of a quadratic. -/
private theorem jquad (p q r y : ℝ) :
    HL46J (fun y => p + q * y + r * y ^ 2) (fun y => q + 2 * r * y) (fun _ => 2 * r) y := by
  constructor
  · refine (((hasDerivAt_id' y).const_mul q).const_add p |>.fun_add
      ((hasDerivAt_pow 2 y).const_mul r)).congr_deriv ?_
    push_cast; ring
  · refine (((hasDerivAt_id' y).const_mul (2 * r)).const_add q).congr_deriv ?_
    ring

/-- Replace the function of a jet by an equal one. -/
private theorem jfun {f g f₁ f₂ : ℝ → ℝ} {y : ℝ} (h : HL46J f f₁ f₂ y) (hf : ∀ z, f z = g z) :
    HL46J g f₁ f₂ y := by
  have e : f = g := funext hf
  subst e; exact h

/-- Replace the second derivative at the point. -/
private theorem jsnd {f f₁ f₂ g₂ : ℝ → ℝ} {y : ℝ} (h : HL46J f f₁ f₂ y) (e : f₂ y = g₂ y) :
    HL46J f f₁ g₂ y := ⟨h.1, e ▸ h.2⟩

/-- `N_aa = -P_A(a - 1, x - 2)` at fixed `x` (jets of the factors composed before expansion). -/
theorem hl46W4_N_jet_a (x : ℝ) : ∃ F₁ : ℝ → ℝ, ∀ a : ℝ,
    HL46J (fun a => hl46W4N x a) F₁ (fun a => -hl46W4PA (a - 1) (x - 2)) a := by
  exact ⟨_, fun a => by
    have jK : HL46J (fun a => hl46W4K x a) _ _ a :=
      jfun (jquad (x * (x + 2)) 0 1 a) (fun z => by unfold hl46W4K; ring)
    have jC : HL46J (fun a => hl46W4Cs x a) _ _ a :=
      jfun (jquad (20 * x) 19 0 a) (fun z => by unfold hl46W4Cs; ring)
    have jD : HL46J (fun a => hl46W4D x a) _ _ a :=
      jfun (jquad (1 + 2 * x - 2 * (x * (1 + 1 / 19)) * x) (2 * (x * (1 + 1 / 19))) 1 a)
        (fun z => by unfold hl46W4D hsDg; ring)
    have jDx : HL46J (fun a => hl46W4Dx x a) _ _ a :=
      jfun (jquad (2 - 4 * x * (1 + 1 / 19)) (2 * (1 + 1 / 19)) 0 a)
        (fun z => by unfold hl46W4Dx; ring)
    have jW : HL46J (fun a => hl46W4W x a) _ _ a :=
      jfun (((jc (hl46W4M x) a).add ((jD.mul jD).mul (jc (hl46W4v x) a))).sub
        (jD.mul (jc (hl46W4E x) a))) (fun z => by unfold hl46W4W; ring)
    have jWx : HL46J (fun a => hl46W4Wx x a) _ _ a :=
      jfun (((((jc (hl46W4Mx x) a).add
        (((jc 2 a).mul jD).mul (jDx.mul (jc (hl46W4v x) a)))).add
        ((jD.mul jD).mul (jc (9 / 1000) a))).sub (jDx.mul (jc (hl46W4E x) a))).sub
        (jD.mul (jc (hl46W4Ex x) a))) (fun z => by unfold hl46W4Wx; ring)
    have jQ : HL46J (fun a => hl46W4Q x a) _ _ a :=
      jfun ((((jc 2 a).mul jD).mul (jc (hl46W4v x) a)).sub (jc (hl46W4E x) a))
        (fun z => by unfold hl46W4Q; ring)
    have jQx : HL46J (fun a => hl46W4Qx x a) _ _ a :=
      jfun (((((jc 2 a).mul jDx).mul (jc (hl46W4v x) a)).add
        (((jc 2 a).mul jD).mul (jc (9 / 1000) a))).sub (jc (hl46W4Ex x) a))
        (fun z => by unfold hl46W4Qx; ring)
    have jA := jid a
    have jKp := jc (2 * x + 2) a
    have jCC := jC.mul jC
    have jK3 := (jK.mul jK).mul jK
    have t1 := ((jc 90250 a).mul jA).mul (jCC.mul ((jWx.mul jK).sub (((jc 2 a).mul jW).mul jKp)))
    have t2 := ((jc 45125 a).mul (jCC.mul jK3)).mul
      (((jc (9 / 1000 / 19) a).mul jC).add (jc ((hl46W4v x - 1) * (20 / 19)) a))
    have t3 := ((jc (45125 * 361 * (20 / 19)) a).mul (jA.mul jA)).mul jK3
    have t4 := ((jc 45125 a).mul ((jA.mul jA).mul jA)).mul ((jCC.mul jKp).mul jK)
    have t5 := (((jc 45125 a).mul jA).mul jCC).mul (((jQx.mul jK).sub (jQ.mul jKp)).mul jK)
    have t6 := ((jc (45125 * 20) a).mul jA).mul (jC.mul jK3)
    have t7 := (((jc 45125 a).mul jA).mul jCC).mul (jKp.mul (jK.mul jK))
    have t8 := (((jc (9 / 200 * 45125) a).mul jA).mul jCC).mul jK3
    have jN := ((((((t1.add t2).sub t3).add t4).sub t5).add t6).sub t7).add t8
    refine jsnd (jfun (g := fun a => hl46W4N x a) jN (fun z => by unfold hl46W4N; ring)) ?_
    unfold hl46W4PA hl46W4W hl46W4Wx hl46W4Q hl46W4Qx
    unfold hl46W4K hl46W4Cs hl46W4D hsDg hl46W4Dx hl46W4M hl46W4Mx hl46W4E hl46W4Ex hh46S4P hl46W4v
    ring⟩

/-- `N_xx = -P_X(a - 1, x - 2)` at fixed `a`. -/
theorem hl46W4_N_jet_x (a : ℝ) : ∃ F₁ : ℝ → ℝ, ∀ x : ℝ,
    HL46J (fun x => hl46W4N x a) F₁ (fun x => -hl46W4PX (a - 1) (x - 2)) x := by
  exact ⟨_, fun x => by
    have jX := jid x
    have jS : HL46J (fun x => 1 + x) _ _ x := jfun (jquad 1 1 0 x) (fun z => by ring)
    have jv : HL46J (fun x => hl46W4v x) _ _ x :=
      jfun (jquad (757 / 1000 - 18 / 1000) (9 / 1000) 0 x) (fun z => by unfold hl46W4v; ring)
    have jK : HL46J (fun x => hl46W4K x a) _ _ x :=
      jfun (jquad (a ^ 2) 2 1 x) (fun z => by unfold hl46W4K; ring)
    have jC : HL46J (fun x => hl46W4Cs x a) _ _ x :=
      jfun (jquad (19 * a) 20 0 x) (fun z => by unfold hl46W4Cs; ring)
    have jKp : HL46J (fun x => 2 * x + 2) _ _ x :=
      jfun (jquad 2 2 0 x) (fun z => by ring)
    have jD : HL46J (fun x => hl46W4D x a) _ _ x :=
      jfun (jquad (a ^ 2 + 1) (2 * a * (1 + 1 / 19) + 2) (-(2 * (1 + 1 / 19))) x)
        (fun z => by unfold hl46W4D hsDg; ring)
    have jDx : HL46J (fun x => hl46W4Dx x a) _ _ x :=
      jfun (jquad (2 * a * (1 + 1 / 19) + 2) (-(4 * (1 + 1 / 19))) 0 x)
        (fun z => by unfold hl46W4Dx; ring)
    have jM : HL46J (fun x => hl46W4M x) _ _ x :=
      jfun ((jS.mul jS).mul (((jS.mul jS).sub jS).add (jc 1 x))) (fun z => by unfold hl46W4M; ring)
    have jMx : HL46J (fun x => hl46W4Mx x) _ _ x :=
      jfun ((((jc 4 x).mul ((jS.mul jS).mul jS)).sub ((jc 3 x).mul (jS.mul jS))).add
        ((jc 2 x).mul jS)) (fun z => by unfold hl46W4Mx; ring)
    have jE : HL46J (fun x => hl46W4E x) _ _ x :=
      jfun (((((jS.mul jS).mul jS).mul (jv.sub (jc 1 x))).add ((jc 3 x).mul jS)).sub (jc 1 x))
        (fun z => by unfold hl46W4E hh46S4P; ring)
    have jEx : HL46J (fun x => hl46W4Ex x) _ _ x :=
      jfun (((((jc 3 x).mul (jS.mul jS)).mul (jv.sub (jc 1 x))).add
        (((jS.mul jS).mul jS).mul (jc (9 / 1000) x))).add (jc 3 x))
        (fun z => by unfold hl46W4Ex; ring)
    have jW : HL46J (fun x => hl46W4W x a) _ _ x :=
      jfun ((jM.add ((jD.mul jD).mul jv)).sub (jD.mul jE)) (fun z => by unfold hl46W4W; ring)
    have jWx : HL46J (fun x => hl46W4Wx x a) _ _ x :=
      jfun ((((jMx.add (((jc 2 x).mul jD).mul (jDx.mul jv))).add
        ((jD.mul jD).mul (jc (9 / 1000) x))).sub (jDx.mul jE)).sub
        (jD.mul jEx)) (fun z => by unfold hl46W4Wx; ring)
    have jQ : HL46J (fun x => hl46W4Q x a) _ _ x :=
      jfun ((((jc 2 x).mul jD).mul jv).sub jE) (fun z => by unfold hl46W4Q; ring)
    have jQx : HL46J (fun x => hl46W4Qx x a) _ _ x :=
      jfun (((((jc 2 x).mul jDx).mul jv).add (((jc 2 x).mul jD).mul (jc (9 / 1000) x))).sub jEx)
        (fun z => by unfold hl46W4Qx; ring)
    have jA := jc a x
    have jCC := jC.mul jC
    have jK3 := (jK.mul jK).mul jK
    have t1 := ((jc 90250 x).mul jA).mul (jCC.mul ((jWx.mul jK).sub (((jc 2 x).mul jW).mul jKp)))
    have t2 := ((jc 45125 x).mul (jCC.mul jK3)).mul
      (((jc (9 / 1000 / 19) x).mul jC).add ((jv.sub (jc 1 x)).mul (jc (20 / 19) x)))
    have t3 := ((jc (45125 * 361 * (20 / 19)) x).mul (jA.mul jA)).mul jK3
    have t4 := ((jc 45125 x).mul ((jA.mul jA).mul jA)).mul ((jCC.mul jKp).mul jK)
    have t5 := (((jc 45125 x).mul jA).mul jCC).mul (((jQx.mul jK).sub (jQ.mul jKp)).mul jK)
    have t6 := ((jc (45125 * 20) x).mul jA).mul (jC.mul jK3)
    have t7 := (((jc 45125 x).mul jA).mul jCC).mul (jKp.mul (jK.mul jK))
    have t8 := (((jc (9 / 200 * 45125) x).mul jA).mul jCC).mul jK3
    have jN := ((((((t1.add t2).sub t3).add t4).sub t5).add t6).sub t7).add t8
    refine jsnd (jfun (g := fun x => hl46W4N x a) jN (fun z => by unfold hl46W4N; ring)) ?_
    unfold hl46W4PX hl46W4W hl46W4Wx hl46W4Q hl46W4Qx
    unfold hl46W4K hl46W4Cs hl46W4D hsDg hl46W4Dx hl46W4M hl46W4Mx hl46W4E hl46W4Ex hh46S4P hl46W4v
    ring⟩

/-! ### Positivity of `P_A`, `P_X` (monomial rule) -/

/-- Monomial rule, positive terms: `c ≥ 1/8`. -/
theorem hl46W4_mlo {c h : ℝ} (hc : 1 / 8 ≤ c) (hh : 0 ≤ h) (i j : ℕ) :
    (1 / 8 : ℝ) ^ i * h ^ j ≤ c ^ i * h ^ j :=
  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hc i) (pow_nonneg hh j)

/-- Monomial rule, negative terms: `c ≤ 1/6`. -/
theorem hl46W4_mhi {c h : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1 / 6) (hh : 0 ≤ h) (i j : ℕ) :
    c ^ i * h ^ j ≤ (1 / 6 : ℝ) ^ i * h ^ j :=
  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hc i) (pow_nonneg hh j)

/-- `P_A > 0` (the note: `P_A ≥ L_A > 5·10⁹`). -/
theorem hl46W4_PA_pos {c h : ℝ} (hc : 1 / 8 ≤ c) (hc' : c ≤ 1 / 6) (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) :
    0 < hl46W4PA c h := by
  have hc0 : 0 ≤ c := by linarith
  unfold hl46W4PA
  linarith [hl46W4_mlo hc hh 5 3, hl46W4_mlo hc hh 4 4, hl46W4_mlo hc hh 4 2, hl46W4_mlo hc hh 3 5,
    hl46W4_mlo hc hh 3 4, hl46W4_mlo hc hh 3 3, hl46W4_mlo hc hh 3 2, hl46W4_mlo hc hh 3 1,
    hl46W4_mlo hc hh 3 0, hl46W4_mlo hc hh 2 5, hl46W4_mlo hc hh 2 4, hl46W4_mlo hc hh 2 3,
    hl46W4_mlo hc hh 2 2, hl46W4_mlo hc hh 2 1, hl46W4_mlo hc hh 2 0, hl46W4_mlo hc hh 1 6,
    hl46W4_mlo hc hh 1 5, hl46W4_mlo hc hh 1 2, hl46W4_mlo hc hh 1 1, hl46W4_mlo hc hh 1 0,
    hl46W4_mhi hc0 hc' hh 7 0, hl46W4_mhi hc0 hc' hh 6 1, hl46W4_mhi hc0 hc' hh 6 0,
    hl46W4_mhi hc0 hc' hh 5 2, hl46W4_mhi hc0 hc' hh 5 1, hl46W4_mhi hc0 hc' hh 5 0,
    hl46W4_mhi hc0 hc' hh 4 3, hl46W4_mhi hc0 hc' hh 4 1, hl46W4_mhi hc0 hc' hh 4 0,
    hl46W4_mhi hc0 hc' hh 2 6, hl46W4_mhi hc0 hc' hh 1 7, hl46W4_mhi hc0 hc' hh 1 4,
    hl46W4_mhi hc0 hc' hh 1 3, pow_nonneg hh 1, pow_nonneg hh 2, pow_nonneg hh 3, pow_nonneg hh 4,
    pow_nonneg hh 5, pow_nonneg hh 6, pow_nonneg hh 7, pow_nonneg hh 8, pow_le_pow_left₀ hh hh' 1,
    pow_le_pow_left₀ hh hh' 2, pow_le_pow_left₀ hh hh' 3, pow_le_pow_left₀ hh hh' 4,
    pow_le_pow_left₀ hh hh' 5, pow_le_pow_left₀ hh hh' 6, pow_le_pow_left₀ hh hh' 7,
    pow_le_pow_left₀ hh hh' 8]

/-- `P_X > 0` (the note: `P_X ≥ L_X > 10¹¹`). -/
theorem hl46W4_PX_pos {c h : ℝ} (hc : 1 / 8 ≤ c) (hc' : c ≤ 1 / 6) (hh : 0 ≤ h) (hh' : h ≤ 1 / 6) :
    0 < hl46W4PX c h := by
  have hc0 : 0 ≤ c := by linarith
  unfold hl46W4PX
  linarith [hl46W4_mlo hc hh 7 1, hl46W4_mlo hc hh 6 2, hl46W4_mlo hc hh 6 0, hl46W4_mlo hc hh 5 3,
    hl46W4_mlo hc hh 5 2, hl46W4_mlo hc hh 5 1, hl46W4_mlo hc hh 5 0, hl46W4_mlo hc hh 4 3,
    hl46W4_mlo hc hh 4 2, hl46W4_mlo hc hh 4 1, hl46W4_mlo hc hh 4 0, hl46W4_mlo hc hh 3 4,
    hl46W4_mlo hc hh 3 3, hl46W4_mlo hc hh 3 0, hl46W4_mlo hc hh 2 4, hl46W4_mlo hc hh 2 3,
    hl46W4_mlo hc hh 1 5, hl46W4_mlo hc hh 1 4, hl46W4_mlo hc hh 1 3, hl46W4_mlo hc hh 1 2,
    hl46W4_mlo hc hh 1 1, hl46W4_mhi hc0 hc' hh 7 0, hl46W4_mhi hc0 hc' hh 6 1,
    hl46W4_mhi hc0 hc' hh 4 4, hl46W4_mhi hc0 hc' hh 3 5, hl46W4_mhi hc0 hc' hh 3 2,
    hl46W4_mhi hc0 hc' hh 3 1, hl46W4_mhi hc0 hc' hh 2 6, hl46W4_mhi hc0 hc' hh 2 5,
    hl46W4_mhi hc0 hc' hh 2 2, hl46W4_mhi hc0 hc' hh 2 1, hl46W4_mhi hc0 hc' hh 2 0,
    hl46W4_mhi hc0 hc' hh 1 7, hl46W4_mhi hc0 hc' hh 1 6, hl46W4_mhi hc0 hc' hh 1 0,
    pow_nonneg hh 1,
    pow_nonneg hh 2, pow_nonneg hh 3, pow_nonneg hh 4, pow_nonneg hh 5, pow_nonneg hh 6,
    pow_nonneg hh 7, pow_nonneg hh 8, pow_le_pow_left₀ hh hh' 1, pow_le_pow_left₀ hh hh' 2,
    pow_le_pow_left₀ hh hh' 3, pow_le_pow_left₀ hh hh' 4, pow_le_pow_left₀ hh hh' 5,
    pow_le_pow_left₀ hh hh' 6, pow_le_pow_left₀ hh hh' 7, pow_le_pow_left₀ hh hh' 8]


/-- The four corner values of `N` (the note's table). -/
theorem hl46W4_N_corners : 0 < hl46W4N 2 (108 / 95) ∧ 0 < hl46W4N 2 (22 / 19) ∧
    0 < hl46W4N (13 / 6) (108 / 95) ∧ 0 < hl46W4N (13 / 6) (22 / 19) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [hl46W4N, hl46W4W, hl46W4Wx, hl46W4Q, hl46W4Qx, hl46W4K, hl46W4Cs, hl46W4D, hsDg,
      hl46W4Dx, hl46W4M, hl46W4Mx, hl46W4E, hl46W4Ex, hh46S4P, hl46W4v]

/-- `N > 0` on `[2, 13/6] × [108/95, 22/19]`: concave in `a`, and in `x` at the end values. -/
theorem hl46W4_N_pos {x a : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (ha : 108 / 95 ≤ a)
    (ha' : a ≤ 22 / 19) : 0 < hl46W4N x a := by
  obtain ⟨c1, c2, c3, c4⟩ := hl46W4_N_corners
  have edge : ∀ a0 : ℝ, 1 / 8 ≤ a0 - 1 → a0 - 1 ≤ 1 / 6 → 0 < hl46W4N 2 a0 →
      0 < hl46W4N (13 / 6) a0 → 0 < hl46W4N x a0 := by
    intro a0 h1 h2 e0 e1
    obtain ⟨F₁, hF⟩ := hl46W4_N_jet_x a0
    exact hl46_concave_lt (f := fun x => hl46W4N x a0) (fun y _ => hF y)
      (fun y hy => by
        have := hl46W4_PX_pos (h := y - 2) h1 h2 (by linarith [hy.1]) (by linarith [hy.2])
        linarith) e0 e1 ⟨hx, hx'⟩
  obtain ⟨F₁, hF⟩ := hl46W4_N_jet_a x
  exact hl46_concave_lt (f := fun a => hl46W4N x a) (fun y _ => hF y)
    (fun y hy => by
      have := hl46W4_PA_pos (c := y - 1) (h := x - 2) (by linarith [hy.1]) (by linarith [hy.2])
        (by linarith) (by linarith)
      linarith)
    (edge _ (by norm_num) (by norm_num) c1 c3) (edge _ (by norm_num) (by norm_num) c2 c4) ⟨ha, ha'⟩

end SmoothedOctagon
