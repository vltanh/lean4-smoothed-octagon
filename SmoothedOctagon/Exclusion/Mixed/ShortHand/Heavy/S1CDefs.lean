module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S1Base

/-!
# Gate S1, central face: partial derivatives in transport form

The partial derivatives of the central tests `hh1cF0`, `hh1cF1` (with the logarithm in place of
the cubic ceiling `ℓ`; the difference `ℓ - log` is handled separately), written in the transport
atoms `S = 1 + x`, `K`, `λ = hh1cL`, `d = hh1cd`, `v`, `E`, `w`, `q`, `T`, `B = α + β`.
They are the quantities whose signs control the central face; each is a small rational
function.

## Main API

* `u`: `hh1cGu` (`∂_uΓ_*`), `hh1cR2u`, `hh1cwu`;
* `β`: `hh1cdb`, `hh1cwb`, `hh1cR2b`, `hh1cTb`, `hh1cR1b`;
* `α`: `hh1cLa`, `hh1cda`, `hh1cqa`, `hh1cwa`, `hh1cELa`, `hh1cR2a`;
* `x`: `hh1cLx`, `hh1cdx`, `hh1cvx`, `hh1cEx`, `hh1cwx`, `hh1cELx`, `hh1cR2x`, `hh1cR1x`, `hh1cGx`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `∂_uΓ_* = (4v - 2SE)S⁴/(16X²)`. -/
noncomputable def hh1cGu (x u : ℝ) : ℝ :=
  (4 * hh1cv x - 2 * (1 + x) * hh1cE x u) * (1 + x) ^ 4 / (16 * (x * (x + 2)) ^ 2)

/-- `∂_u w = d² - dλS`. -/
noncomputable def hh1cwu (x a b : ℝ) : ℝ := hh1cd x a b ^ 2 - hh1cd x a b * hh1cL x a * (1 + x)

/-- `∂_u R̄₂ = 2∂_u w + (α + β)/α - (2d - λS)`. -/
noncomputable def hh1cR2u (x a b : ℝ) : ℝ :=
  2 * hh1cwu x a b + (a + b) / a - (2 * hh1cd x a b - hh1cL x a * (1 + x))

/-- `∂_β d = 2(α - x)/K`. -/
noncomputable def hh1cdb (x a : ℝ) : ℝ := 2 * (a - x) / hh1cK x a

/-- `∂_β w = 2d(∂_β d)u - (∂_β d)λE`. -/
noncomputable def hh1cwb (x a b u : ℝ) : ℝ :=
  2 * hh1cd x a b * hh1cdb x a * u - hh1cdb x a * hh1cL x a * hh1cE x u

/-- `∂_β R̄₂` with `∂_β log y = 1/(α + β)`. -/
noncomputable def hh1cR2b (x a b u : ℝ) : ℝ :=
  2 * hh1cwb x a b u - 2 * hh1cdb x a * u + (u - 1) / a - a / (a + b) ^ 2 + 1 / (a + b)

/-- `∂_β T = -K/(α(α + β)²)`. -/
noncomputable def hh1cTb (x a b : ℝ) : ℝ := -hh1cK x a / (a * (a + b) ^ 2)

/-- `∂_β R̄₁`, `R̄₁ = R̄₂ + (T - 2)(w - 3/4)`. -/
noncomputable def hh1cR1b (x a b u : ℝ) : ℝ :=
  hh1cR2b x a b u + hh1cTb x a b * (hh1cw x a b u - 3 / 4) + (hh1cT x a b - 2) * hh1cwb x a b u

/-- `∂_α λ = -2αλ/K`. -/
noncomputable def hh1cLa (x a : ℝ) : ℝ := -2 * a * hh1cL x a / hh1cK x a

/-- `∂_α d = 2(α + β)/K - 2αd/K` (at fixed `β`). -/
noncomputable def hh1cda (x a b : ℝ) : ℝ := 2 * (a + b) / hh1cK x a - 2 * a * hh1cd x a b / hh1cK x a

/-- `∂_α q_c = 2α/K - 2αq_c/K`. -/
noncomputable def hh1cqa (x a : ℝ) : ℝ := 2 * a / hh1cK x a - 2 * a * hh1cq x a / hh1cK x a

/-- `∂_α w`. -/
noncomputable def hh1cwa (x a b u : ℝ) : ℝ :=
  2 * hh1cL x a * hh1cLa x a * hh1cv x + 2 * hh1cd x a b * hh1cda x a b * u -
    (hh1cda x a b * hh1cL x a + hh1cd x a b * hh1cLa x a) * hh1cE x u

/-- `∂_α E_L`. -/
noncomputable def hh1cELa (x a b u : ℝ) : ℝ :=
  2 * hh1cda x a b * u - hh1cLa x a * hh1cE x u

/-- `∂_α R̄₂` (fixed `β`, `u`) with `∂_α log y = 1/α + 1/(α + β) - 2α/K`. -/
noncomputable def hh1cR2a (x a b u : ℝ) : ℝ :=
  2 * hh1cwa x a b u - hh1cELa x a b u - (u - 1) * b / a ^ 2 + b / (a + b) ^ 2 - hh1cqa x a +
    (1 / a + 1 / (a + b) - 2 * a / hh1cK x a)

/-- `∂_x λ = 2S/K - 2Sλ/K`. -/
noncomputable def hh1cLx (x a : ℝ) : ℝ := 2 * (1 + x) / hh1cK x a - 2 * (1 + x) * hh1cL x a / hh1cK x a

/-- `∂_x d = (2 - 2β)/K - 2Sd/K` (at fixed `α`, `β`). -/
noncomputable def hh1cdx (x a b : ℝ) : ℝ :=
  (2 - 2 * b) / hh1cK x a - 2 * (1 + x) * hh1cd x a b / hh1cK x a

/-- `∂_x v = 1/S² - 2/S³`. -/
noncomputable def hh1cvx (x : ℝ) : ℝ := 1 / (1 + x) ^ 2 - 2 / (1 + x) ^ 3

/-- `∂_x E = (u - 1) + 1/S² - 2(2S - 1)/S³` (at fixed `u`). -/
noncomputable def hh1cEx (x u : ℝ) : ℝ :=
  (u - 1) + 1 / (1 + x) ^ 2 - 2 * (2 * (1 + x) - 1) / (1 + x) ^ 3

/-- `∂_x w`. -/
noncomputable def hh1cwx (x a b u : ℝ) : ℝ :=
  2 * hh1cL x a * hh1cLx x a * hh1cv x + hh1cL x a ^ 2 * hh1cvx x +
    2 * hh1cd x a b * hh1cdx x a b * u -
    (hh1cdx x a b * hh1cL x a + hh1cd x a b * hh1cLx x a) * hh1cE x u -
    hh1cd x a b * hh1cL x a * hh1cEx x u

/-- `∂_x E_L`. -/
noncomputable def hh1cELx (x a b u : ℝ) : ℝ :=
  2 * hh1cdx x a b * u - hh1cLx x a * hh1cE x u - hh1cL x a * hh1cEx x u

/-- `∂_x R̄₂` (fixed `α`, `β`, `u`) with `∂_x log y = -2S/K`, `∂_x q_c = -2Sq_c/K`. -/
noncomputable def hh1cR2x (x a b u : ℝ) : ℝ :=
  2 * hh1cwx x a b u - hh1cELx x a b u + 2 * (1 + x) * hh1cq x a / hh1cK x a -
    2 * (1 + x) / hh1cK x a

/-- `∂_x R̄₁`, with `∂_x T = 2S/(α(α + β))`. -/
noncomputable def hh1cR1x (x a b u : ℝ) : ℝ :=
  hh1cR2x x a b u + 2 * (1 + x) / (a * (a + b)) * (hh1cw x a b u - 3 / 4) +
    (hh1cT x a b - 2) * hh1cwx x a b u

/-- `∂_xΓ_*` (fixed `u`). -/
noncomputable def hh1cGx (x u : ℝ) : ℝ :=
  (4 * u * hh1cvx x - 2 * hh1cE x u * hh1cEx x u) * (1 + x) ^ 4 / (16 * (x * (x + 2)) ^ 2) +
    (4 * u * hh1cv x - hh1cE x u ^ 2) *
      (4 * (1 + x) ^ 3 / (16 * (x * (x + 2)) ^ 2) - 4 * (1 + x) ^ 5 / (16 * (x * (x + 2)) ^ 3))

end SmoothedOctagon
