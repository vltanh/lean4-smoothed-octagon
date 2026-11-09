module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.FaceFunctions

/-!
# Smaller-short window, lower ratio, central face: partial derivatives in transport form

The partial derivatives of the central tests `lrcF0`, `lrcF1` (with the logarithm in place of
the cubic ceiling `ℓ`; the difference `ℓ - log` is handled separately), written in the transport
atoms `S = 1 + x`, `K`, `λ = lrcL`, `d = lrcd`, `v`, `E`, `w`, `q`, `T`, `B = α + β`.
They are the quantities whose signs control the central face; each is a small rational
function.

## Main API

* `u`: `lrcGu` (`∂_uΓ_*`), `lrcR2u`, `lrcwu`;
* `β`: `lrcdb`, `lrcwb`, `lrcR2b`, `lrcTb`, `lrcR1b`;
* `α`: `lrcLa`, `lrcda`, `lrcqa`, `lrcwa`, `lrcELa`, `lrcR2a`;
* `x`: `lrcLx`, `lrcdx`, `lrcvx`, `lrcEx`, `lrcwx`, `lrcELx`, `lrcR2x`, `lrcR1x`, `lrcGx`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- `∂_uΓ_* = (4v - 2SE)S⁴/(16X²)`. -/
noncomputable def lrcGu (x u : ℝ) : ℝ :=
  (4 * lrcv x - 2 * (1 + x) * lrcE x u) * (1 + x) ^ 4 / (16 * (x * (x + 2)) ^ 2)

/-- `∂_u w = d² - dλS`. -/
noncomputable def lrcwu (x a b : ℝ) : ℝ := lrcd x a b ^ 2 - lrcd x a b * lrcL x a * (1 + x)

/-- `∂_u R̄₂ = 2∂_u w + (α + β)/α - (2d - λS)`. -/
noncomputable def lrcR2u (x a b : ℝ) : ℝ :=
  2 * lrcwu x a b + (a + b) / a - (2 * lrcd x a b - lrcL x a * (1 + x))

/-- `∂_β d = 2(α - x)/K`. -/
noncomputable def lrcdb (x a : ℝ) : ℝ := 2 * (a - x) / lrcK x a

/-- `∂_β w = 2d(∂_β d)u - (∂_β d)λE`. -/
noncomputable def lrcwb (x a b u : ℝ) : ℝ :=
  2 * lrcd x a b * lrcdb x a * u - lrcdb x a * lrcL x a * lrcE x u

/-- `∂_β R̄₂` with `∂_β log y = 1/(α + β)`. -/
noncomputable def lrcR2b (x a b u : ℝ) : ℝ :=
  2 * lrcwb x a b u - 2 * lrcdb x a * u + (u - 1) / a - a / (a + b) ^ 2 + 1 / (a + b)

/-- `∂_β T = -K/(α(α + β)²)`. -/
noncomputable def lrcTb (x a b : ℝ) : ℝ := -lrcK x a / (a * (a + b) ^ 2)

/-- `∂_β R̄₁`, `R̄₁ = R̄₂ + (T - 2)(w - 3/4)`. -/
noncomputable def lrcR1b (x a b u : ℝ) : ℝ :=
  lrcR2b x a b u + lrcTb x a b * (lrcw x a b u - 3 / 4) + (lrcT x a b - 2) * lrcwb x a b u

/-- `∂_α λ = -2αλ/K`. -/
noncomputable def lrcLa (x a : ℝ) : ℝ := -2 * a * lrcL x a / lrcK x a

/-- `∂_α d = 2(α + β)/K - 2αd/K` (at fixed `β`). -/
noncomputable def lrcda (x a b : ℝ) : ℝ := 2 * (a + b) / lrcK x a - 2 * a * lrcd x a b / lrcK x a

/-- `∂_α q_c = 2α/K - 2αq_c/K`. -/
noncomputable def lrcqa (x a : ℝ) : ℝ := 2 * a / lrcK x a - 2 * a * lrcq x a / lrcK x a

/-- `∂_α w`. -/
noncomputable def lrcwa (x a b u : ℝ) : ℝ :=
  2 * lrcL x a * lrcLa x a * lrcv x + 2 * lrcd x a b * lrcda x a b * u -
    (lrcda x a b * lrcL x a + lrcd x a b * lrcLa x a) * lrcE x u

/-- `∂_α E_L`. -/
noncomputable def lrcELa (x a b u : ℝ) : ℝ :=
  2 * lrcda x a b * u - lrcLa x a * lrcE x u

/-- `∂_α R̄₂` (fixed `β`, `u`) with `∂_α log y = 1/α + 1/(α + β) - 2α/K`. -/
noncomputable def lrcR2a (x a b u : ℝ) : ℝ :=
  2 * lrcwa x a b u - lrcELa x a b u - (u - 1) * b / a ^ 2 + b / (a + b) ^ 2 - lrcqa x a +
    (1 / a + 1 / (a + b) - 2 * a / lrcK x a)

/-- `∂_x λ = 2S/K - 2Sλ/K`. -/
noncomputable def lrcLx (x a : ℝ) : ℝ := 2 * (1 + x) / lrcK x a - 2 * (1 + x) * lrcL x a / lrcK x a

/-- `∂_x d = (2 - 2β)/K - 2Sd/K` (at fixed `α`, `β`). -/
noncomputable def lrcdx (x a b : ℝ) : ℝ :=
  (2 - 2 * b) / lrcK x a - 2 * (1 + x) * lrcd x a b / lrcK x a

/-- `∂_x v = 1/S² - 2/S³`. -/
noncomputable def lrcvx (x : ℝ) : ℝ := 1 / (1 + x) ^ 2 - 2 / (1 + x) ^ 3

/-- `∂_x E = (u - 1) + 1/S² - 2(2S - 1)/S³` (at fixed `u`). -/
noncomputable def lrcEx (x u : ℝ) : ℝ :=
  (u - 1) + 1 / (1 + x) ^ 2 - 2 * (2 * (1 + x) - 1) / (1 + x) ^ 3

/-- `∂_x w`. -/
noncomputable def lrcwx (x a b u : ℝ) : ℝ :=
  2 * lrcL x a * lrcLx x a * lrcv x + lrcL x a ^ 2 * lrcvx x +
    2 * lrcd x a b * lrcdx x a b * u -
    (lrcdx x a b * lrcL x a + lrcd x a b * lrcLx x a) * lrcE x u -
    lrcd x a b * lrcL x a * lrcEx x u

/-- `∂_x E_L`. -/
noncomputable def lrcELx (x a b u : ℝ) : ℝ :=
  2 * lrcdx x a b * u - lrcLx x a * lrcE x u - lrcL x a * lrcEx x u

/-- `∂_x R̄₂` (fixed `α`, `β`, `u`) with `∂_x log y = -2S/K`, `∂_x q_c = -2Sq_c/K`. -/
noncomputable def lrcR2x (x a b u : ℝ) : ℝ :=
  2 * lrcwx x a b u - lrcELx x a b u + 2 * (1 + x) * lrcq x a / lrcK x a -
    2 * (1 + x) / lrcK x a

/-- `∂_x R̄₁`, with `∂_x T = 2S/(α(α + β))`. -/
noncomputable def lrcR1x (x a b u : ℝ) : ℝ :=
  lrcR2x x a b u + 2 * (1 + x) / (a * (a + b)) * (lrcw x a b u - 3 / 4) +
    (lrcT x a b - 2) * lrcwx x a b u

/-- `∂_xΓ_*` (fixed `u`). -/
noncomputable def lrcGx (x u : ℝ) : ℝ :=
  (4 * u * lrcvx x - 2 * lrcE x u * lrcEx x u) * (1 + x) ^ 4 / (16 * (x * (x + 2)) ^ 2) +
    (4 * u * lrcv x - lrcE x u ^ 2) *
      (4 * (1 + x) ^ 3 / (16 * (x * (x + 2)) ^ 2) - 4 * (1 + x) ^ 5 / (16 * (x * (x + 2)) ^ 3))

end SmoothedOctagon
