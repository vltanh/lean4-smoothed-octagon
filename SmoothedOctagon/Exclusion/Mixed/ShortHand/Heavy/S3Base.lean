module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.S3Leaves

/-!
# Heavy leaves of gate S3: shared lemmas

Generic tools for the certificates of `hs3_central_alpha` and `hs3_outer_face` (prefix `hh3`):
polynomials in Horner form with their derivative, Bernstein positivity of degree 5 and 6 on
`[0, 1]` with abstract coefficients, and the two elementary facts about the duration test
`hs3Fn` (it is increasing in the logarithm and affine in the incoming norm).

## Main API

* `hh3Hor`, `hh3HorD`, `hh3_hor_hasDerivAt`: `c₀ + t(c₁ + t(⋯))` and its derivative.
* `hh3_bern5`, `hh3_bern6`: a polynomial `∑ cᵢ yⁱ` of degree 5 (6) is positive on `[0, 1]` when
  its Bernstein coefficients `∑_{i ≤ j} C(n - i, j - i) cᵢ` are positive.
* `hh3_fn_log_mono`: `hs3Fn` is increasing in `ℓ`.
* `hh3_fn_u_affine`: `hs3Fn(u₂) - hs3Fn(u₁) = (u₂ - u₁) · hh3Slope`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- Horner evaluation `c₀ + t(c₁ + t(c₂ + ⋯))`. -/
noncomputable def hh3Hor : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, t => c + t * hh3Hor cs t

/-- The derivative of `hh3Hor cs` at `t`. -/
noncomputable def hh3HorD : List ℝ → ℝ → ℝ
  | [], _ => 0
  | _ :: cs, t => hh3Hor cs t + t * hh3HorD cs t

theorem hh3_hor_hasDerivAt (cs : List ℝ) (t : ℝ) :
    HasDerivAt (fun s => hh3Hor cs s) (hh3HorD cs t) t := by
  induction cs with
  | nil => simpa [hh3Hor, hh3HorD] using hasDerivAt_const t (0 : ℝ)
  | cons c cs ih =>
    have h1 : HasDerivAt (fun s : ℝ => s * hh3Hor cs s) (1 * hh3Hor cs t + t * hh3HorD cs t) t :=
      (hasDerivAt_id' t).mul ih
    have h2 := h1.const_add c
    simp only [hh3Hor, hh3HorD]
    convert h2 using 1
    ring

/-- Bernstein positivity of degree 5 on `[0, 1]` with abstract coefficients. -/
theorem hh3_bern5 {y c0 c1 c2 c3 c4 c5 : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1)
    (b0 : 0 < c0) (b1 : 0 < 5 * c0 + c1) (b2 : 0 < 10 * c0 + 4 * c1 + c2)
    (b3 : 0 < 10 * c0 + 6 * c1 + 3 * c2 + c3)
    (b4 : 0 < 5 * c0 + 4 * c1 + 3 * c2 + 2 * c3 + c4)
    (b5 : 0 < c0 + c1 + c2 + c3 + c4 + c5) :
    0 < c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4 + c5 * y ^ 5 := by
  have e : c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4 + c5 * y ^ 5 =
      c0 * (1 - y) ^ 5 + (5 * c0 + c1) * y * (1 - y) ^ 4 + (10 * c0 + 4 * c1 + c2) * y ^ 2 * (1 - y) ^ 3
      + (10 * c0 + 6 * c1 + 3 * c2 + c3) * y ^ 3 * (1 - y) ^ 2
      + (5 * c0 + 4 * c1 + 3 * c2 + 2 * c3 + c4) * y ^ 4 * (1 - y)
      + (c0 + c1 + c2 + c3 + c4 + c5) * y ^ 5 := by ring
  rw [e]
  have hb : 0 ≤ 1 - y := by linarith
  rcases lt_or_ge 0 y with hy | hy
  · have : 0 < (c0 + c1 + c2 + c3 + c4 + c5) * y ^ 5 := by positivity
    have : 0 ≤ c0 * (1 - y) ^ 5 + (5 * c0 + c1) * y * (1 - y) ^ 4
        + (10 * c0 + 4 * c1 + c2) * y ^ 2 * (1 - y) ^ 3
        + (10 * c0 + 6 * c1 + 3 * c2 + c3) * y ^ 3 * (1 - y) ^ 2
        + (5 * c0 + 4 * c1 + 3 * c2 + 2 * c3 + c4) * y ^ 4 * (1 - y) := by positivity
    linarith
  · have hy0 : y = 0 := le_antisymm hy h0
    subst hy0
    norm_num
    exact b0

/-- Bernstein positivity of degree 6 on `[0, 1]` with abstract coefficients. -/
theorem hh3_bern6 {y c0 c1 c2 c3 c4 c5 c6 : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1)
    (b0 : 0 < c0) (b1 : 0 < 6 * c0 + c1) (b2 : 0 < 15 * c0 + 5 * c1 + c2)
    (b3 : 0 < 20 * c0 + 10 * c1 + 4 * c2 + c3)
    (b4 : 0 < 15 * c0 + 10 * c1 + 6 * c2 + 3 * c3 + c4)
    (b5 : 0 < 6 * c0 + 5 * c1 + 4 * c2 + 3 * c3 + 2 * c4 + c5)
    (b6 : 0 < c0 + c1 + c2 + c3 + c4 + c5 + c6) :
    0 < c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4 + c5 * y ^ 5 + c6 * y ^ 6 := by
  have e : c0 + c1 * y + c2 * y ^ 2 + c3 * y ^ 3 + c4 * y ^ 4 + c5 * y ^ 5 + c6 * y ^ 6 =
      c0 * (1 - y) ^ 6 + (6 * c0 + c1) * y * (1 - y) ^ 5 + (15 * c0 + 5 * c1 + c2) * y ^ 2 * (1 - y) ^ 4
      + (20 * c0 + 10 * c1 + 4 * c2 + c3) * y ^ 3 * (1 - y) ^ 3
      + (15 * c0 + 10 * c1 + 6 * c2 + 3 * c3 + c4) * y ^ 4 * (1 - y) ^ 2
      + (6 * c0 + 5 * c1 + 4 * c2 + 3 * c3 + 2 * c4 + c5) * y ^ 5 * (1 - y)
      + (c0 + c1 + c2 + c3 + c4 + c5 + c6) * y ^ 6 := by ring
  rw [e]
  have hb : 0 ≤ 1 - y := by linarith
  rcases lt_or_ge 0 y with hy | hy
  · have : 0 < (c0 + c1 + c2 + c3 + c4 + c5 + c6) * y ^ 6 := by positivity
    have : 0 ≤ c0 * (1 - y) ^ 6 + (6 * c0 + c1) * y * (1 - y) ^ 5
        + (15 * c0 + 5 * c1 + c2) * y ^ 2 * (1 - y) ^ 4
        + (20 * c0 + 10 * c1 + 4 * c2 + c3) * y ^ 3 * (1 - y) ^ 3
        + (15 * c0 + 10 * c1 + 6 * c2 + 3 * c3 + c4) * y ^ 4 * (1 - y) ^ 2
        + (6 * c0 + 5 * c1 + 4 * c2 + 3 * c3 + 2 * c4 + c5) * y ^ 5 * (1 - y) := by positivity
    linarith
  · have hy0 : y = 0 := le_antisymm hy h0
    subst hy0
    norm_num
    exact b0

/-- `hs3Fn` is increasing in the logarithm value. -/
theorem hh3_fn_log_mono (x be al u q n : ℝ) {ℓ ℓ' : ℝ} (h : ℓ ≤ ℓ') :
    hs3Fn x be al u q n ℓ ≤ hs3Fn x be al u q n ℓ' := by
  unfold hs3Fn
  linarith

/-- The incoming-norm slope of `hs3Fn`:
`1/r_A + S - q(2Δ + εS) + n(-qΔS + q²(Δ² + ΔεS))`, `ε = 1 - α⁻²`, `Δ = D/α²`, `S = 1 + x`. -/
noncomputable def hh3Slope (x be al q n : ℝ) : ℝ :=
  1 / hsRA al be + (1 + x) - q * (2 * (hsDg x be al / al ^ 2) + (1 - 1 / al ^ 2) * (1 + x)) +
    n * (-q * (hsDg x be al / al ^ 2) * (1 + x) +
      q ^ 2 * ((hsDg x be al / al ^ 2) ^ 2 + hsDg x be al / al ^ 2 * (1 - 1 / al ^ 2) * (1 + x)))

/-- `hs3Fn` is affine in the incoming norm `u`. -/
theorem hh3_fn_u_affine (x be al q n ℓ u₁ u₂ : ℝ) :
    hs3Fn x be al u₂ q n ℓ - hs3Fn x be al u₁ q n ℓ = (u₂ - u₁) * hh3Slope x be al q n := by
  unfold hs3Fn hh3Slope hsELs hsWs hsA1 hsA2 hsA3 hsE0
  ring

end SmoothedOctagon
