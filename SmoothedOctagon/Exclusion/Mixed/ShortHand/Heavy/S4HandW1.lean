module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW1d

/-!
# W1: `Φ` decreases in `d` along the actual shape curve

`archive/lighter-proofs/SHORT_CASIMIR_FIRST_DERIVATIVES.md` §§1-3 (`-Φ_d > 27/5000`). On the
curve `a = 1 + ed`, `b = x(1 + d)`, `u = ū(x, b)` the point stays in the containing rectangle (2),
where `Φ_u ≥ -7/10` (9), `Φ_b ≤ -9/500` (6), (10), `Φ_a ≤ 3/500` (11), and
`0 ≤ ū(d₁) - ū(d₂) ≤ (9/500)(d₂ - d₁)` (4), (5). Route: instead of the chain rule along the curve,
the difference `Φ(d₂) - Φ(d₁)` is split into a `u`-step, a `b`-step and an `a`-step, each a
one-variable monotonicity on the rectangle (`S4HandW1d`, `S4HandW1c`), with total at most
`(d₂ - d₁)(7/10 · 9/500 - 9x/500 + 3e/500) ≤ -(27/5000)(d₂ - d₁)`.

## Main API

* `hl46_W1`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **W1** (`SHORT_CASIMIR_FIRST_DERIVATIVES` §§1-3): `Φ` decreases in `d` on the curve. -/
theorem hl46_W1 {x e d₁ d₂ : ℝ} (hx : 2 ≤ x) (hx' : x ≤ 13 / 6) (he : 13 / 5 ≤ e) (he' : e ≤ 3)
    (h0 : 0 ≤ d₁) (h12 : d₁ ≤ d₂) (h2 : d₂ ≤ 1 / 19) : hl46PhiC x d₂ e ≤ hl46PhiC x d₁ e := by
  obtain ⟨hu12, hud, hu2, hu1⟩ := hl46_w1_ubar hx hx' h0 h12 h2
  have ha1 : 1 ≤ 1 + e * d₁ := by nlinarith
  have ha12 : 1 + e * d₁ ≤ 1 + e * d₂ := by nlinarith
  have ha2 : 1 + e * d₂ ≤ 22 / 19 := by nlinarith
  have hb1 : x ≤ x * (1 + d₁) := by nlinarith
  have hb12 : x * (1 + d₁) ≤ x * (1 + d₂) := by nlinarith
  have hb2 : x * (1 + d₂) ≤ 20 * x / 19 := by nlinarith
  -- the `u`-step at `(b₂, a₂)`
  have su := hl46_mono_of
    (f := fun u => hh46S4PhiC x (x * (1 + d₂)) (1 + e * d₂) u + 7 / 10 * u)
    (f₁ := fun u => hl46W1Pu x (x * (1 + d₂)) (1 + e * d₂) u + 7 / 10) (a := 3 / 4) (b := 19 / 25)
    (fun z _ => (hl46_w1_hasDerivAt_u (by linarith) (by linarith)).add
      ((hasDerivAt_id' z).const_mul (7 / 10)) |>.congr_deriv (by ring))
    (fun z hz => by
      linarith [hl46_w1_Pu_ge hx hx' (ha1.trans ha12) ha2 (hb1.trans hb12) hb2 hz.2]) hu2 hu12 hu1
  -- the `b`-step at `(a₂, u₁)`
  have sb := hl46_anti_of
    (f := fun b => hh46S4PhiC x b (1 + e * d₂) (hsUbar x (x * (1 + d₁))) + 9 / 500 * b)
    (f₁ := fun b => hl46W1Pb x b (1 + e * d₂) (hsUbar x (x * (1 + d₁))) + 9 / 500)
    (a := x) (b := 20 * x / 19)
    (fun z hz => (hl46_w1_hasDerivAt_be (by linarith) (by linarith) (by linarith [hz.1])).add
      ((hasDerivAt_id' z).const_mul (9 / 500)) |>.congr_deriv (by ring))
    (fun z hz => by
      linarith [hl46_w1_Pb_le hx hx' (ha1.trans ha12) ha2 hz.1 hz.2 (hu2.trans hu12)])
    hb1 hb12 hb2
  -- the `a`-step at `(b₁, u₁)`
  have sa := hl46_anti_of
    (f := fun a => hh46S4PhiC x (x * (1 + d₁)) a (hsUbar x (x * (1 + d₁))) - 3 / 500 * a)
    (f₁ := fun a => hl46W1Pa x (x * (1 + d₁)) a (hsUbar x (x * (1 + d₁))) - 3 / 500)
    (a := 1) (b := 22 / 19)
    (fun z hz => (hl46_w1_hasDerivAt_al (by linarith) (by linarith [hz.1]) (by linarith)).sub
      ((hasDerivAt_id' z).const_mul (3 / 500)) |>.congr_deriv (by ring))
    (fun z hz => by linarith [hl46_w1_Pa_le hx hx' hz.1 hz.2 hb1 (hb12.trans hb2) hu1])
    ha1 ha12 ha2
  unfold hl46PhiC
  have k1 : 0 ≤ (d₂ - d₁) * (x - 2) := mul_nonneg (by linarith) (by linarith)
  have k2 : 0 ≤ (d₂ - d₁) * (3 - e) := mul_nonneg (by linarith) (by linarith)
  nlinarith

end SmoothedOctagon
