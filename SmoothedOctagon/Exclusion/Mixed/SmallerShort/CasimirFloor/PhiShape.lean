module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.PhiDisplacement.OtherPartials

/-!
# Smaller-short window, Casimir floor: at `x = 13/6`, `d = 1/19`, `Φ` decreases in `e`

At `x = 13/6`, `d = 1/19` only `a = 1 + e/19` depends on `e`, and `b = 20x/19`,
`u = ū(13/6, 130/57) ≤ 19/25`. The reductions of W1 (monotonicity of `Φ_a` in `u` and in `b`)
give `Φ_a ≤ Φ_a(13/6, a, 130/57, 19/25) = N₀(13/6, a)/(3325a²(19a + 130/3)²K³)`,
and `N₀(13/6, a) < 0` on the shape interval (`cas_w1_Pa_end_neg`, `PhiDisplacement/ShapeDerivative`). Since
`Φ_e = Φ_a/19`, `Φ` decreases in `e`.

The negativity of `N₀(13/6, a) = V + W/6 - Q(c, 1/6)/36` uses `V ≤ V(22/19)`, the bound on
`-W(1 + c)` and the twice-integrated `P_N` bound (`PhiDisplacement/ShapeSource`).

## Main API

* `cas_W5`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **W5**: at `x = 13/6`, `d = 1/19`, `Φ` decreases
in `e`. -/
theorem cas_W5 {e₁ e₂ : ℝ} (h1 : 13 / 5 ≤ e₁) (h12 : e₁ ≤ e₂) (h2 : e₂ ≤ 3) :
    casPhiC (13 / 6) (1 / 19) e₂ ≤ casPhiC (13 / 6) (1 / 19) e₁ := by
  have hu := (cas_w1_ubar (x := 13 / 6) (d₁ := 1 / 19) (d₂ := 1 / 19) (by norm_num) le_rfl
    (by norm_num) le_rfl le_rfl).2.2.2
  have hb : (13 / 6 : ℝ) * (1 + 1 / 19) = 20 * (13 / 6) / 19 := by norm_num
  unfold casPhiC
  rw [hb] at hu ⊢
  refine jet_anti_of
    (f := fun e => casClosedPhiC (13 / 6) (20 * (13 / 6) / 19) (1 + e * (1 / 19))
      (ssUbar (13 / 6) (20 * (13 / 6) / 19)))
    (f₁ := fun e => casW1Pa (13 / 6) (20 * (13 / 6) / 19) (1 + e * (1 / 19))
      (ssUbar (13 / 6) (20 * (13 / 6) / 19)) * (1 / 19))
    (a := 13 / 5) (b := 3) (fun z hz => ?_) (fun z hz => ?_) h1 h12 h2
  · have hl : HasDerivAt (fun e : ℝ => 1 + e * (1 / 19)) (1 / 19) z := by
      have := ((hasDerivAt_id' z).mul_const (1 / 19)).const_add 1
      refine this.congr_deriv ?_
      ring
    exact (cas_w1_hasDerivAt_al (x := 13 / 6) (be := 20 * (13 / 6) / 19)
      (u := ssUbar (13 / 6) (20 * (13 / 6) / 19)) (by norm_num) (by linarith [hz.1])
      (by norm_num)).comp z hl
  · have := cas_w1_Pa_end_neg (al := 1 + z * (1 / 19)) (u := ssUbar (13 / 6) (20 * (13 / 6) / 19))
      (by linarith [hz.1]) (by linarith [hz.2]) hu
    have : casW1Pa (13 / 6) (20 * (13 / 6) / 19) (1 + z * (1 / 19))
        (ssUbar (13 / 6) (20 * (13 / 6) / 19)) * (1 / 19) < 0 := by linarith
    exact this.le

end SmoothedOctagon
