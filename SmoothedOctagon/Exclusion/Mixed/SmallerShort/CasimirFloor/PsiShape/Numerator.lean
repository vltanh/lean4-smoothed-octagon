module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.CasimirFloor.ShapeCurve

/-!
# Smaller-short window, Casimir floor: the shape derivative `Ψ_a` with a cleared numerator

In the variables `x, a = α, b = β, u` (Lean order `x be al u`), with `K = x(x + 2) + a²`,
`B = a + b`, `D = ssDg`, `E = casClosedP`, the closed form `Ψ = Γ - R₁/7` of `CasimirFloor/ClosedForms` has
`w = N/K²`, `N = M + uD² - DE` (`casW2N`) and `E_L = Q/K`, `Q = 2uD - E` (`casW2Q`).
Since `D_a = 2B`, `N_a = 2BQ`, `Q_a = 4Bu` and `K_a = 2a`, differentiating the nine pieces of
`R₁` (`K(w - 3/4)/(aB)`, `(u - 1)B/a`, `a/B`, `-a²/K`, `-E_L`, `log(2aB/K)`) and multiplying by
`a²B²K²` gives the term-by-term numerator `casW2Va` (the logarithm piece in the combined form
`(2a + b)K - 2a²B = X(2a + b) - a²b`), so that

`Ψ_a = -V/(7a²B²K²)`, `V = casW2V x b a u` (`cas_w2_deriv`).

The identity is checked in the abstract atoms `a, b, K, N, Q, u`; no polynomial in `x, a, b` is
expanded here.

## Main API

* `casW2N`, `casW2Q`, `casW2Va`, `casW2V`.
* `cas_w2_deriv`: `HasDerivAt (fun a => casClosedPsiC x b a u) (-V/(7a²B²K²)) a`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- `N = M + uD² - DE`, the numerator of `w = N/K²`. -/
noncomputable def casW2N (x be al u : ℝ) : ℝ :=
  (1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) + ssDg x be al ^ 2 * u - ssDg x be al * casClosedP x u

/-- `Q = 2uD - E`, the numerator of `E_L = Q/K`. -/
noncomputable def casW2Q (x be al u : ℝ) : ℝ := 2 * ssDg x be al * u - casClosedP x u

/-- The cleared numerator `-7a²B²K²Ψ_a`, term by term in the atoms `a, b, K, N, Q, u`
(`B = a + b`): the pieces of `R₁` in the order `K(w - 3/4)/(aB)` (two terms), `(u - 1)B/a`, `a/B`,
`-a²/K`, `-E_L` (two terms), `log(2aB/K)`. -/
noncomputable def casW2Va (a b K N Q u : ℝ) : ℝ :=
  2 * Q * a * (a + b) ^ 2 * K - N * ((a + b) * K + a * K + 2 * a ^ 2 * (a + b)) -
    3 / 4 * (2 * a ^ 2 * (a + b) - K * (2 * a + b)) * K ^ 2 - (u - 1) * b * (a + b) ^ 2 * K ^ 2 +
    a ^ 2 * b * K ^ 2 - a ^ 2 * (a + b) ^ 2 * (2 * a * K - 2 * a ^ 3) -
    4 * u * a ^ 2 * (a + b) ^ 3 * K + 2 * a ^ 3 * (a + b) ^ 2 * Q +
    a * (a + b) * K * ((2 * a + b) * K - 2 * a ^ 2 * (a + b))

/-- `V = -7a²B²K²Ψ_a` in the variables `x, b, a, u` (Lean order `x be al u`). -/
noncomputable def casW2V (x be al u : ℝ) : ℝ :=
  casW2Va al be (x * (x + 2) + al ^ 2) (casW2N x be al u) (casW2Q x be al u) u

/-- The derivative of the closed form `Ψ` in the shape variable `a`:
`Ψ_a = -V/(7a²B²K²)`. -/
theorem cas_w2_deriv {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    HasDerivAt (fun y => casClosedPsiC x be y u)
      (-casW2V x be al u / (7 * al ^ 2 * (al + be) ^ 2 * (x * (x + 2) + al ^ 2) ^ 2)) al := by
  have hK0 : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hB0 : 0 < al + be := by linarith
  have hK : HasDerivAt (fun y => x * (x + 2) + y ^ 2) (2 * al) al := by
    refine ((hasDerivAt_pow 2 al).const_add (x * (x + 2))).congr_deriv ?_
    norm_num
  have hD : HasDerivAt (fun y => ssDg x be y) (2 * al + 2 * be) al := by
    have := ((((hasDerivAt_pow 2 al).fun_add
      (((hasDerivAt_id' al).const_mul 2).mul_const be)).add_const 1).add_const (2 * x)).sub_const
      (2 * be * x)
    refine this.congr_deriv ?_
    norm_num
  have hN : HasDerivAt (fun y => casW2N x be y u) (2 * (al + be) * casW2Q x be al u) al := by
    have := (((hD.fun_pow 2).mul_const u).const_add
      ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1))).fun_sub (hD.mul_const (casClosedP x u))
    refine this.congr_deriv ?_
    unfold casW2Q
    norm_num
    ring
  have hQ : HasDerivAt (fun y => casW2Q x be y u) (4 * (al + be) * u) al := by
    refine (((hD.const_mul 2).mul_const u).sub_const (casClosedP x u)).congr_deriv ?_
    ring
  have hA : HasDerivAt (fun y => (x * (x + 2) + y ^ 2) / (y * (y + be)))
      ((2 * al * (al * (al + be)) - (x * (x + 2) + al ^ 2) * (2 * al + be)) /
        (al * (al + be)) ^ 2) al := by
    refine (hK.fun_div ((hasDerivAt_id' al).fun_mul ((hasDerivAt_id' al).add_const be))
      (by positivity)).congr_deriv ?_
    ring
  have hW : HasDerivAt (fun y => casClosedWc x be y u)
      ((2 * (al + be) * casW2Q x be al u * (x * (x + 2) + al ^ 2) ^ 2 -
        casW2N x be al u * (2 * (x * (x + 2) + al ^ 2) * (2 * al))) /
        ((x * (x + 2) + al ^ 2) ^ 2) ^ 2) al := by
    refine (hN.fun_div (hK.fun_pow 2) (by positivity)).congr_deriv ?_
    norm_num
  have hR : HasDerivAt (fun y => casClosedRest x be y u)
      (-((u - 1) * be) / al ^ 2 + be / (al + be) ^ 2 -
        (2 * al * (x * (x + 2) + al ^ 2) - al ^ 2 * (2 * al)) / (x * (x + 2) + al ^ 2) ^ 2 -
        (4 * (al + be) * u * (x * (x + 2) + al ^ 2) - casW2Q x be al u * (2 * al)) /
          (x * (x + 2) + al ^ 2) ^ 2) al := by
    have := (((((hasDerivAt_id' al).add_const be).const_mul (u - 1)).fun_div (hasDerivAt_id' al)
      hal.ne').fun_add ((hasDerivAt_id' al).fun_div ((hasDerivAt_id' al).add_const be)
      hB0.ne')).fun_sub ((hasDerivAt_pow 2 al).fun_div hK hK0.ne') |>.fun_sub
      (hQ.fun_div hK hK0.ne')
    refine this.congr_deriv ?_
    field_simp
    ring
  have hL : HasDerivAt (fun y => log (2 * y * (y + be) / (x * (x + 2) + y ^ 2)))
      (((2 * (al + be) + 2 * al) * (x * (x + 2) + al ^ 2) - 2 * al * (al + be) * (2 * al)) /
        (x * (x + 2) + al ^ 2) ^ 2 / (2 * al * (al + be) / (x * (x + 2) + al ^ 2))) al := by
    have := (((hasDerivAt_id' al).const_mul 2).fun_mul ((hasDerivAt_id' al).add_const be)).fun_div
      hK hK0.ne'
    refine (this.log (by positivity)).congr_deriv ?_
    ring
  have hall := (hasDerivAt_const al (casClosedG x u)).fun_sub
    (((((hA.fun_mul (hW.sub_const (3 / 4))).add_const 1).fun_add hR).fun_add hL).div_const 7)
  refine hall.congr_deriv ?_
  rw [show casClosedWc x be al u = casW2N x be al u / (x * (x + 2) + al ^ 2) ^ 2 from rfl]
  unfold casW2V
  generalize casW2N x be al u = N
  generalize casW2Q x be al u = Q
  generalize x * (x + 2) + al ^ 2 = K at hK0 ⊢
  have h1 : K ≠ 0 := hK0.ne'
  have h2 : al ≠ 0 := hal.ne'
  have h3 : al + be ≠ 0 := hB0.ne'
  unfold casW2Va
  field_simp
  ring

end SmoothedOctagon
