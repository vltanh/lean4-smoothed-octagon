module

public import SmoothedOctagon.Exclusion.MinimumStructure
public import SmoothedOctagon.Reduction.Clearance.Budget

/-!
# The normal multiplier of a costate cycle: switch norms, stationarity, ellipticity, Casimir

The normal multiplier `U` of a `CostateCycle` (`Period/Costate.lean`) and of a `NormalPeriod`, in
the margin coordinates of the library: switch norms and stationarity at the switches, the signed
action and its Euler identity, the global frame, ellipticity of mixed periods, and the
cost–Casimir inequality. Shared by cases M1, M2 and F.

## Conventions

* Triangular coordinates are `X ↦ C X C⁻¹`, `C = Term.triC = [[√3, 1], [√3, -1]]`
  (`det C = -2√3 < 0`: orientation reversing). Margins: `p_j(X) = tr(D_j (C X C⁻¹))`,
  `D_j = R^{-j} D₀ R^j`, `D₀ = diag(-1, 1)`, `R = Term.triR = [[0, 1], [-1, 1]]`; a traceless matrix
  is `triY p = ½ [[-p₀, p₀ + p₂], [-p₀ - p₁, p₀]]` of its margins (`el_triY_margin`).
* The margins `p_j` are `margin j` (= `2 ρ_{2-j}` of SmoothedPolygons). `λ = -1`.
* `J = C/√12 = rawCost/8` (`cost = (√3/4) rawCost`); `8J = ∑ ε_k G(a_k, a_{k+1})`.
* `γ² = det U = det Λ₁ / 12` (`NormalPeriod.det_Λ₁_zero`), `κ = √(12 γ²)`; the rescaled variables
  `u = 8d`, `E = 16e` are used only in `Exclusion/ShortRuns`.

## The local normal multiplier

`U = (1/√12) Ad_{X₀⁻¹} Λ₁(0)` in triangular coordinates; `𝒰(t) = (1/√12) X(t)⁻¹ Λ₁(t) X(t)` has
margins `μ_j = -α_j/(2√3) - (p₀ + p₁ + p₂) p_j / 4 + 1/2` at a switch (`CostateCycle.mu`;
`NormalPeriod.mu_zero` identifies it at the switch `0`). Along piece `k` (label `i`, factor `q`):
`μ_i` constant, `μ_i + μ_{i±1}` multiplied by `q^{±2}` (`mu_act`, `mu_grow`, `mu_decr`);
`γ² = (μ₀μ₁ + μ₁μ₂ + μ₂μ₀)/4` is constant (`gam2`, `gam2_succ`, `gam2_eq`).

* `wt k = -μ_{i_k}` (`tr(U Z_k)`), `swd k = d_k = (w_k + w_{k+1})/(2 s_k²)` (switch after piece
  `k`), `cre k = e_k = w_k/(2 K_k)`, `sgn k = ε_k = ±1`, `sw k = s_k = a_k + a_{k+1}`.

## Local identities (all proved from the costate transport, no first variation)

* `stationarity`: `J_{a_k} = tr(U V_k)` in the form
  `2(ε_{k-1} s_{k-1} d_{k-1} + ε_k s_k d_k - (ε_{k-1}+ε_k) a_k e_k) = (ε_{k-1} G_a(a_k,a_{k-1})
  + ε_k G_a(a_k,a_{k+1}))/8`. Proof: the vanishing new Hamiltonian at the end of piece `k` equals
  `4√3 ε_k (a_k + a_{k+1}) (tr(U V_k) - J_{a_k})` exactly (`el_stat_pp/mm/mp/pm`).
* `swd_fwd`, `swd_rev`: `ε = +1 ⇒ d ≥ j/2`, `ε = -1 ⇒ d ≤ j/2` (`elJ`).
* `turn_secant`, `turn_swd_ge` (`d ≥ 3/32` at a turn); `gram_pp`, `gram_mm` (Gram identities);
  `centre_stat` (stationarity at a centre); `centre_factor`, `factor_pp/mp/pm`; `cre_pos_pp`,
  `cre_neg_mm` (signs of the cross pairings when `γ² ≤ 0`).
* `arc_eq`, `rawCost_eq` (`elG`, `elF1`, `elF2`: the signed action), `euler_sum` (its Euler
  identity), `next_centre_local` (the three-factor recurrence).

## The global frame

`Amat k = T₀(q_k) R^{-ε_k}`, `pre n = A₀ ⋯ A_{n-1}` (`pre_preInv`, `det_pre`),
`Mloc k = P_k⁻¹ U P_k` (`Mloc_succ`, `Mloc_pre`), **`pre_N`: `P_N = ±1`** (from the
tangent closure), switch vectors `yv n = P_n (outgoing vector)` with `yv_norm` (`yᵀSy = d`),
`yv_pair` (pairing and Wronskian with the next one), `cross_pp`, `cross_mm`, `outv_turn`,
`yv_add_N` (`y_{N+n} = P_N y_n`), `S = Sloc 0 = -J₀ U` (`Sloc_symm`).

## Ellipticity and the cost–Casimir inequality

* `NormalPeriod.rev_run`, `swd_ge_of_mixed`, `centre_min`: run structure of a mixed period.
* **`NormalPeriod.gam2_pos_of_mixed`**: `γ² > 0` for every mixed normal period (the projective
  argument uses `el_three_gram`).
* `NormalPeriod.Λ₁_zero_neg`: `γ² > 0`, `S₀₀ > 0` ⇒ `Λ₁(0)₁₀ < 0` (negative elliptic; the
  triangular change reverses orientation, `el_ell_sign`).
* **`NormalPeriod.cost_casimir`**: `C ≥ 4πκ/(2κ + 3)` for negative elliptic `Λ₁(0)`
  (`el_winding`, `el_negEll_repr`).
* **`NormalPeriod.gam2_le_cap`**: competitive, `γ² > 0`, `d₀ > 0` ⇒ `γ² ≤ 97969/529200`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Set
open scoped Matrix

private lemma el_s3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
private lemma el_s3pos : (0 : ℝ) < √3 := by positivity

/-- Normalize a polynomial identity in `√3`, using `√3² = 3`. -/
local macro "el_ring" : tactic =>
  `(tactic| ((try ring_nf); (try simp only [el_s3]); (try ring_nf)))

/-- `f₀ + f₁ + f₂ = f i + f (i + 1) + f (i - 1)`. -/
theorem el_sum_rot (f : Fin 3 → ℝ) (i : Fin 3) : f 0 + f 1 + f 2 = f i + f (i + 1) + f (i - 1) := by
  fin_cases i
  · simp only [Fin.zero_eta, zero_add, show (0 : Fin 3) - 1 = 2 from rfl]
  · simp only [Fin.mk_one, show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) - 1 = 0 from rfl]
    ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      show (2 : Fin 3) - 1 = 1 from rfl]
    ring

/-- The quadric in the label order `i, i + 1, i - 1`. -/
theorem el_quad_rot (f : Fin 3 → ℝ) (i : Fin 3) :
    f 0 * f 1 + f 1 * f 2 + f 2 * f 0 = f i * f (i + 1) + f (i + 1) * f (i - 1) + f (i - 1) * f i := by
  fin_cases i
  · simp only [Fin.zero_eta, zero_add, show (0 : Fin 3) - 1 = 2 from rfl]
  · simp only [Fin.mk_one, show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) - 1 = 0 from rfl]
    ring
  · simp only [show (⟨2, by norm_num⟩ : Fin 3) = 2 from rfl, show (2 : Fin 3) + 1 = 0 from rfl,
      show (2 : Fin 3) - 1 = 1 from rfl]
    ring

/-- `∂G/∂a` of the signed action `G(a, b) = 3ab - 4 - (a² + b²) log(a + b) + ½ a² log(a² + 4)
+ ½ b² log(b² + 4)`; equivalently `a (2 f(1 + b/a) + h(1 + 4/a²))`. -/
noncomputable def elGa (a b : ℝ) : ℝ :=
  3 * b - 2 * a * Real.log (a + b) - (a ^ 2 + b ^ 2) / (a + b) + a * Real.log (a ^ 2 + 4) +
    a ^ 3 / (a ^ 2 + 4)

/-- `f(t) = t - 1/t - log t`. -/
noncomputable def elF (t : ℝ) : ℝ := t - t⁻¹ - Real.log t

/-- The switching threshold `j = (a² + ab + b²) / (4 (a + b)²)` of a switch between active margins
`a, b`. -/
noncomputable def elJ (a b : ℝ) : ℝ := (a ^ 2 + a * b + b ^ 2) / (4 * (a + b) ^ 2)

/-! ### The stationarity identities (in local form) -/

theorem el_stat_pp {a b c q n x0 x1 x2 y0 y1 y2 : ℝ} (ha : 0 < a) (hc : 0 < c) (hq : 0 < q)
    (hb : b = (a ^ 2 + 4) / (a + c) - a) (hn : n = (a + b) * q - a)
    (h0 : 2 * x0 + y0 = 0) (h2 : 2 * x2 + y2 = 0)
    (hperp : y0 * (b + c) + y1 * (a + c) + y2 * (a + b) = 0)
    (hL : Real.log q = Real.log (a + c) + Real.log (a + n) - Real.log (a ^ 2 + 4))
    (hnext : 2 * (q ^ 2 * (x0 + x1) + costateAGrow a b q) +
      (q * (y0 + y1) + costateBGrow a b q) = 0) :
    -((-(x0 / (2 * √3)) - (a + b + c) * a / 4 + 1 / 2) +
        (-(x2 / (2 * √3)) - (a + b + c) * c / 4 + 1 / 2)) / (a + c) -
      q ^ 2 * ((-(x0 / (2 * √3)) - (a + b + c) * a / 4 + 1 / 2) +
        (-(x1 / (2 * √3)) - (a + b + c) * b / 4 + 1 / 2)) / (a + n) +
      2 * a * (-(x0 / (2 * √3)) - (a + b + c) * a / 4 + 1 / 2) / (a ^ 2 + 4) =
    (elGa a c + elGa a n) / 8 := by
  have h3 := el_s3pos
  have hac : 0 < a + c := by linarith
  have hD : a + n = (a ^ 2 + 4) * q / (a + c) := by rw [hn, hb]; field_simp; ring
  have hy0 : y0 = -2 * x0 := by linarith
  have hy2 : y2 = -2 * x2 := by linarith
  have hy1 : y1 = -(y0 * (b + c) + y2 * (a + b)) / (a + c) := by field_simp; linarith
  simp only [elGa, costateAGrow, costateBGrow] at hnext ⊢
  rw [hL] at hnext
  generalize Real.log (a + n) = Ln at hnext ⊢
  generalize Real.log (a + c) = Lp at hnext ⊢
  generalize Real.log (a ^ 2 + 4) = LK at hnext ⊢
  rw [hD]
  linear_combination (norm := skip) ((a + c) / (4 * √3 * (a ^ 2 + 4) * q)) * hnext
  subst hy1
  subst hy0 hy2 hn
  subst hb
  field_simp
  el_ring

theorem el_stat_mm {a b c q n x0 x1 x2 y0 y1 y2 : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (hc : c = (a ^ 2 + 4) / (a + b) - a) (hn : n = (a + c) / q - a)
    (h0 : 2 * x0 + y0 = 0) (h1 : 2 * x1 + y1 = 0)
    (hperp : y0 * (b + c) + y1 * (a + c) + y2 * (a + b) = 0)
    (hL : Real.log q = -Real.log (a + b) - Real.log (a + n) + Real.log (a ^ 2 + 4))
    (hnext : 2 * ((q)⁻¹ ^ 2 * (x0 + x2) + costateADecr a c q) +
      ((q)⁻¹ * (y0 + y2) + costateBDecr a c q) = 0) :
    ((-(x0 / (2 * √3)) - (a + b + c) * a / 4 + 1 / 2) +
        (-(x1 / (2 * √3)) - (a + b + c) * b / 4 + 1 / 2)) / (a + b) +
      (q)⁻¹ ^ 2 * ((-(x0 / (2 * √3)) - (a + b + c) * a / 4 + 1 / 2) +
        (-(x2 / (2 * √3)) - (a + b + c) * c / 4 + 1 / 2)) / (a + n) -
      2 * a * (-(x0 / (2 * √3)) - (a + b + c) * a / 4 + 1 / 2) / (a ^ 2 + 4) =
    -(elGa a b + elGa a n) / 8 := by
  have h3 := el_s3pos
  have hab : 0 < a + b := by linarith
  have hD : a + n = (a ^ 2 + 4) / ((a + b) * q) := by rw [hn, hc]; field_simp; ring
  have hy0 : y0 = -2 * x0 := by linarith
  have hy1 : y1 = -2 * x1 := by linarith
  have hy2 : y2 = -(y0 * (b + c) + y1 * (a + c)) / (a + b) := by field_simp; linarith
  simp only [elGa, costateADecr, costateBDecr] at hnext ⊢
  rw [hL] at hnext
  generalize Real.log (a + n) = Ln at hnext ⊢
  generalize Real.log (a + b) = Lp at hnext ⊢
  generalize Real.log (a ^ 2 + 4) = LK at hnext ⊢
  rw [hD]
  linear_combination (norm := skip) (-((a + b) * q / (4 * √3 * (a ^ 2 + 4)))) * hnext
  subst hy2
  subst hy0 hy1 hn
  subst hc
  field_simp
  el_ring

theorem el_stat_mp {a b c q n x0 x1 y0 y1 y2 : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (hc : c = (a ^ 2 + 4) / (a + b) - a) (hn : n = (a + b) * q - a)
    (h0 : 2 * x0 + y0 = 0) (h1 : 2 * x1 + y1 = 0)
    (hperp : y0 * (b + c) + y1 * (a + c) + y2 * (a + b) = 0)
    (hL : Real.log q = -Real.log (a + b) + Real.log (a + n))
    (hnext : 2 * (q ^ 2 * (x0 + x1) + costateAGrow a b q) +
      (q * (y0 + y1) + costateBGrow a b q) = 0) :
    ((-(x0 / (2 * √3)) - (a + b + c) * a / 4 + 1 / 2) +
        (-(x1 / (2 * √3)) - (a + b + c) * b / 4 + 1 / 2)) / (a + b) -
      q ^ 2 * ((-(x0 / (2 * √3)) - (a + b + c) * a / 4 + 1 / 2) +
        (-(x1 / (2 * √3)) - (a + b + c) * b / 4 + 1 / 2)) / (a + n) =
    (-elGa a b + elGa a n) / 8 := by
  have h3 := el_s3pos
  have hab : 0 < a + b := by linarith
  have hD : a + n = (a + b) * q := by rw [hn]; ring
  have hy0 : y0 = -2 * x0 := by linarith
  have hy1 : y1 = -2 * x1 := by linarith
  have hy2 : y2 = -(y0 * (b + c) + y1 * (a + c)) / (a + b) := by field_simp; linarith
  simp only [elGa, costateAGrow, costateBGrow] at hnext ⊢
  rw [hL] at hnext
  generalize Real.log (a + n) = Ln at hnext ⊢
  generalize Real.log (a + b) = Lp at hnext ⊢
  generalize Real.log (a ^ 2 + 4) = LK at hnext ⊢
  rw [hD]
  linear_combination (norm := skip) (1 / (4 * √3 * ((a + b) * q))) * hnext
  subst hy2
  subst hy0 hy1 hn
  subst hc
  field_simp
  el_ring

theorem el_stat_pm {a b c q n x0 x2 y0 y1 y2 : ℝ} (ha : 0 < a) (hc : 0 < c) (hq : 0 < q)
    (hb : b = (a ^ 2 + 4) / (a + c) - a) (hn : n = (a + c) / q - a)
    (h0 : 2 * x0 + y0 = 0) (h2 : 2 * x2 + y2 = 0)
    (hperp : y0 * (b + c) + y1 * (a + c) + y2 * (a + b) = 0)
    (hL : Real.log q = Real.log (a + c) - Real.log (a + n))
    (hnext : 2 * ((q)⁻¹ ^ 2 * (x0 + x2) + costateADecr a c q) +
      ((q)⁻¹ * (y0 + y2) + costateBDecr a c q) = 0) :
    -((-(x0 / (2 * √3)) - (a + b + c) * a / 4 + 1 / 2) +
        (-(x2 / (2 * √3)) - (a + b + c) * c / 4 + 1 / 2)) / (a + c) +
      (q)⁻¹ ^ 2 * ((-(x0 / (2 * √3)) - (a + b + c) * a / 4 + 1 / 2) +
        (-(x2 / (2 * √3)) - (a + b + c) * c / 4 + 1 / 2)) / (a + n) =
    (elGa a c - elGa a n) / 8 := by
  have h3 := el_s3pos
  have hac : 0 < a + c := by linarith
  have hD : a + n = (a + c) / q := by rw [hn]; ring
  have hy0 : y0 = -2 * x0 := by linarith
  have hy2 : y2 = -2 * x2 := by linarith
  have hy1 : y1 = -(y0 * (b + c) + y2 * (a + b)) / (a + c) := by field_simp; linarith
  simp only [elGa, costateADecr, costateBDecr] at hnext ⊢
  rw [hL] at hnext
  generalize Real.log (a + n) = Ln at hnext ⊢
  generalize Real.log (a + c) = Lp at hnext ⊢
  generalize Real.log (a ^ 2 + 4) = LK at hnext ⊢
  rw [hD]
  linear_combination (norm := skip) (-(q / (4 * √3 * (a + c)))) * hnext
  subst hy1
  subst hy0 hy2 hn
  subst hb
  field_simp
  el_ring



/-! ### The signed action -/

/-- The signed action `G(a, b) = 3ab - 4 - (a² + b²) log(a + b) + ½ a² log(a² + 4)
+ ½ b² log(b² + 4)`. -/
noncomputable def elG (a b : ℝ) : ℝ :=
  3 * a * b - 4 - (a ^ 2 + b ^ 2) * Real.log (a + b) + a ^ 2 / 2 * Real.log (a ^ 2 + 4) +
    b ^ 2 / 2 * Real.log (b ^ 2 + 4)

/-- The outgoing half of the cost of a piece with active margin `a` and next active margin `n`. -/
noncomputable def elF1 (a n : ℝ) : ℝ :=
  a * (n - (4 - a * n) / (a + n)) - a ^ 2 * Real.log (a + n) + a ^ 2 / 2 * Real.log (a ^ 2 + 4)

/-- The incoming half of the cost of a piece with active margin `a` and previous active margin
`p`. -/
noncomputable def elF2 (p a : ℝ) : ℝ :=
  a * (p - (4 - a * p) / (a + p)) - a ^ 2 * Real.log (a + p) + a ^ 2 / 2 * Real.log (a ^ 2 + 4)

theorem elF1_add_elF2 {a b : ℝ} (hab : a + b ≠ 0) : elF1 a b + elF2 a b = elG a b := by
  simp only [elF1, elF2, elG, show b + a = a + b by ring]
  field_simp
  ring

/-- The Euler identity of the signed action:
`(a ∂_a + b ∂_b) G = 2G + 16/(a² + 4) + 16/(b² + 4)`. -/
theorem elGa_euler {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a * elGa a b + b * elGa b a = 2 * elG a b + 16 / (a ^ 2 + 4) + 16 / (b ^ 2 + 4) := by
  simp only [elGa, elG, show b + a = a + b by ring]
  field_simp
  ring

theorem el_arc_pp {a b c q n : ℝ} (ha : 0 < a) (hc : 0 < c) (hq : 0 < q)
    (hb : b = (a ^ 2 + 4) / (a + c) - a) (hn : n = (a + b) * q - a)
    (hL : Real.log q = Real.log (a + c) + Real.log (a + n) - Real.log (a ^ 2 + 4)) :
    Term.rawArc a b c q = elF1 a n + elF2 c a := by
  have hac : 0 < a + c := by linarith
  have hD : a + n = (a ^ 2 + 4) * q / (a + c) := by rw [hn, hb]; field_simp; ring
  simp only [Term.rawArc, elF1, elF2, hL]
  generalize Real.log (a + n) = Ln
  generalize Real.log (a + c) = Lp
  generalize Real.log (a ^ 2 + 4) = LK
  rw [hD]
  subst hn
  subst hb
  field_simp
  ring

theorem el_arc_mm {a b c q n : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (hc : c = (a ^ 2 + 4) / (a + b) - a) (hn : n = (a + c) / q - a)
    (hL : Real.log q = -Real.log (a + b) - Real.log (a + n) + Real.log (a ^ 2 + 4)) :
    Term.rawArc a b c q = -elF1 a n - elF2 b a := by
  have hab : 0 < a + b := by linarith
  have hD : a + n = (a ^ 2 + 4) / ((a + b) * q) := by rw [hn, hc]; field_simp; ring
  simp only [Term.rawArc, elF1, elF2, hL]
  generalize Real.log (a + n) = Ln
  generalize Real.log (a + b) = Lp
  generalize Real.log (a ^ 2 + 4) = LK
  rw [hD]
  subst hn
  subst hc
  field_simp
  ring

theorem el_arc_mp {a b c q n : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : 0 < q)
    (hc : c = (a ^ 2 + 4) / (a + b) - a) (hn : n = (a + b) * q - a)
    (hL : Real.log q = -Real.log (a + b) + Real.log (a + n)) :
    Term.rawArc a b c q = elF1 a n - elF2 b a := by
  have hab : 0 < a + b := by linarith
  have hD : a + n = (a + b) * q := by rw [hn]; ring
  simp only [Term.rawArc, elF1, elF2, hL]
  generalize Real.log (a + n) = Ln
  generalize Real.log (a + b) = Lp
  generalize Real.log (a ^ 2 + 4) = LK
  rw [hD]
  subst hn
  subst hc
  field_simp
  ring

theorem el_arc_pm {a b c q n : ℝ} (ha : 0 < a) (hc : 0 < c) (hq : 0 < q)
    (hb : b = (a ^ 2 + 4) / (a + c) - a) (hn : n = (a + c) / q - a)
    (hL : Real.log q = Real.log (a + c) - Real.log (a + n)) :
    Term.rawArc a b c q = -elF1 a n + elF2 c a := by
  have hac : 0 < a + c := by linarith
  have hD : a + n = (a + c) / q := by rw [hn]; ring
  simp only [Term.rawArc, elF1, elF2, hL]
  generalize Real.log (a + n) = Ln
  generalize Real.log (a + c) = Lp
  generalize Real.log (a ^ 2 + 4) = LK
  rw [hD]
  subst hn
  subst hb
  field_simp
  ring

/-! ### One-sided derivatives at the start of a piece -/

/-- If the Hamiltonian of the growing label along a piece, `2 (s² Y + costateAGrow a b s) +
(s B + costateBGrow a b s)` (`2Y + B = 0`), is `≤ 0` on `[1, q]`, then `Y ≤ 0`. -/
theorem el_grow_start {a b q Y B : ℝ} (hq : 1 < q) (hYB : 2 * Y + B = 0)
    (hle : ∀ s ∈ Icc 1 q,
      2 * (s ^ 2 * Y + costateAGrow a b s) + (s * B + costateBGrow a b s) ≤ 0) : Y ≤ 0 := by
  set F : ℝ → ℝ := fun s ↦
    (a + b) * Real.log s - (a + b) * (s - 1) + a * ((s - 1) ^ 2 / s) with hF
  set g : ℝ → ℝ := fun s ↦ Y * (s - 1) + √3 * a / 2 * F s with hg
  have hσ : ∀ s, 0 < s → 2 * (s ^ 2 * Y + costateAGrow a b s) + (s * B + costateBGrow a b s) =
      2 * s * g s := by
    intro s hs
    have hB : B = -2 * Y := by linarith
    simp only [hg, hF, costateAGrow, costateBGrow, hB]
    field_simp
    ring
  have hFd : HasDerivAt F 0 1 := by
    have hlog : HasDerivAt Real.log (1 : ℝ)⁻¹ 1 := Real.hasDerivAt_log one_ne_zero
    have h1 : HasDerivAt (fun s : ℝ ↦ (s - 1) ^ 2) (2 * (1 - 1)) 1 := by
      simpa using ((hasDerivAt_id' (1 : ℝ)).sub_const 1).fun_pow 2
    have hsq : HasDerivAt (fun s : ℝ ↦ (s - 1) ^ 2 / s)
        ((2 * (1 - 1) * 1 - (1 - 1) ^ 2 * 1) / 1 ^ 2) 1 := h1.div (hasDerivAt_id' 1) one_ne_zero
    have := ((hlog.const_mul (a + b)).sub
      (((hasDerivAt_id' (1 : ℝ)).sub_const 1).const_mul (a + b))).add (hsq.const_mul a)
    exact this.congr_deriv (by ring)
  have hgd : HasDerivAt g Y 1 := by
    have := (((hasDerivAt_id' (1 : ℝ)).sub_const 1).const_mul Y).add (hFd.const_mul (√3 * a / 2))
    exact this.congr_deriv (by ring)
  have hg1 : g 1 = 0 := by simp [hg, hF]
  exact cst_deriv_nonpos_of_right hgd hq hg1 (fun s hs ↦ by
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs.1
    have h1 := hle s hs
    rw [hσ s hs0] at h1
    by_contra hpos
    push Not at hpos
    have : 0 < 2 * s * g s := by positivity
    linarith)

/-- If the Hamiltonian of the decreasing label along a piece, `2 (s⁻² Y + costateADecr a c s) +
(s⁻¹ B + costateBDecr a c s)` (`2Y + B = 0`), is `≤ 0` on `[1, q]`, then `0 ≤ Y`. -/
theorem el_decr_start {a c q Y B : ℝ} (hq : 1 < q) (hYB : 2 * Y + B = 0)
    (hle : ∀ s ∈ Icc 1 q,
      2 * (s⁻¹ ^ 2 * Y + costateADecr a c s) + (s⁻¹ * B + costateBDecr a c s) ≤ 0) :
    0 ≤ Y := by
  set h : ℝ → ℝ := fun s ↦ (a + c) * Real.log s - a * (s - 1) - c * (1 - s⁻¹) with hh
  set g : ℝ → ℝ := fun s ↦ Y * (1 - s⁻¹) + √3 * a / 2 * h s with hg
  have hσ : ∀ s, 0 < s → 2 * (s⁻¹ ^ 2 * Y + costateADecr a c s) + (s⁻¹ * B + costateBDecr a c s) =
      -(2 / s) * g s := by
    intro s hs
    have hB : B = -2 * Y := by linarith
    simp only [hg, hh, costateADecr, costateBDecr, hB]
    field_simp
    ring
  have hinv : HasDerivAt (fun s : ℝ ↦ s⁻¹) (-((1 : ℝ) ^ 2)⁻¹) 1 := hasDerivAt_inv one_ne_zero
  have hhd : HasDerivAt h 0 1 := by
    have hlog : HasDerivAt Real.log (1 : ℝ)⁻¹ 1 := Real.hasDerivAt_log one_ne_zero
    have := ((hlog.const_mul (a + c)).sub
      (((hasDerivAt_id' (1 : ℝ)).sub_const 1).const_mul a)).sub ((hinv.const_sub 1).const_mul c)
    exact this.congr_deriv (by ring)
  have hgd : HasDerivAt g Y 1 := by
    have := ((hinv.const_sub 1).const_mul Y).add (hhd.const_mul (√3 * a / 2))
    exact this.congr_deriv (by ring)
  have hg1 : g 1 = 0 := by simp [hg, hh]
  have := cst_deriv_nonpos_of_right (f := fun s ↦ -g s) hgd.neg hq (by simp [hg1]) (fun s hs ↦ by
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs.1
    have h1 := hle s hs
    rw [hσ s hs0] at h1
    by_contra hpos
    push Not at hpos
    have : 0 < 2 / s * -g s := by positivity
    linarith)
  linarith


/-! ### The turn secant bound -/

/-- `G_a(a, b) - G_a(a, c) = 2a (f(1 + b/a) - f(1 + c/a))`. -/
theorem elGa_sub {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    elGa a b - elGa a c = 2 * a * (elF (1 + b / a) - elF (1 + c / a)) := by
  have e1 : 1 + b / a = (a + b) / a := by field_simp
  have e2 : 1 + c / a = (a + c) / a := by field_simp
  simp only [elGa, elF, e1, e2]
  rw [Real.log_div (by positivity) ha.ne', Real.log_div (by positivity) ha.ne']
  field_simp
  ring

/-- `t ↦ f(t) - 3t/4` is monotone on `t > 0`: `f'(t) - 3/4 = (t - 2)²/(4t²)`. -/
theorem elF_sub_monotone : MonotoneOn (fun t ↦ elF t - 3 / 4 * t) (Ioi 0) := by
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t ↦ elF t - 3 / 4 * t)
      (1 - (-(t ^ 2)⁻¹) - t⁻¹ - 3 / 4 * 1) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have := (((hasDerivAt_id' t).sub (hasDerivAt_inv ht0)).sub (Real.hasDerivAt_log ht0)).sub
      ((hasDerivAt_id' t).const_mul (3 / 4))
    exact this
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt) ?_
  intro t ht
  rw [interior_Ioi] at ht
  rw [(hd t ht).deriv]
  have ht0 : 0 < t := ht
  have : 1 - (-(t ^ 2)⁻¹) - t⁻¹ - 3 / 4 * 1 = (t - 2) ^ 2 / (4 * t ^ 2) := by
    field_simp; ring
  rw [this]; positivity

/-- The secant of `f` on `(1, ∞)` is at least `3/4`. -/
theorem elF_secant {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) : 3 / 4 * (x - y) ≤ elF x - elF y := by
  have := elF_sub_monotone (show y ∈ Ioi (0 : ℝ) from hy) (show x ∈ Ioi (0 : ℝ) from by
    simp only [mem_Ioi]; linarith) hxy
  simp only at this
  linarith


/-! ### Triangular matrices from margins, quadratic forms -/

/-- The traceless matrix with margins `p` in the triangular coordinates of `Term.triC`:
`Y(p) = ½ [[-p₀, p₀ + p₂], [-p₀ - p₁, p₀]]`, so `p_j = tr(D_j Y)`. -/
noncomputable def triY (p : Fin 3 → ℝ) : Mat2 :=
  !![-(p 0) / 2, (p 0 + p 2) / 2; -(p 0 + p 1) / 2, p 0 / 2]

theorem triY_rot_succ (p : Fin 3 → ℝ) :
    triY (fun j ↦ p (j + 1)) = Term.triR * triY p * Term.triRinv := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [triY, Term.triR, Term.triRinv, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem triY_rot_pred (p : Fin 3 → ℝ) :
    triY (fun j ↦ p (j - 1)) = Term.triRinv * triY p * Term.triR := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [triY, Term.triR, Term.triRinv, Matrix.mul_apply, Fin.sum_univ_two,
      show (-1 : Fin 3) = 2 from rfl] <;> ring

theorem det_triY (p : Fin 3 → ℝ) : (triY p).det = (p 0 * p 1 + p 1 * p 2 + p 2 * p 0) / 4 := by
  rw [Matrix.det_fin_two]; simp [triY]; ring

/-- `J₀ = [[0, -1], [1, 0]]`, the triangular copy of `J`. -/
def elJ0 : Mat2 := !![0, -1; 1, 0]

/-- The bilinear form `xᵀ M y`. -/
def elQ (M : Mat2) (x y : Fin 2 → ℝ) : ℝ :=
  x 0 * (M 0 0 * y 0 + M 0 1 * y 1) + x 1 * (M 1 0 * y 0 + M 1 1 * y 1)

/-- `det(x, y) = x₀ y₁ - x₁ y₀`. -/
def elDet (x y : Fin 2 → ℝ) : ℝ := x 0 * y 1 - x 1 * y 0


theorem elQ_11 (M : Mat2) (x y : ℝ) : elQ M ![x, 0] ![y, 0] = x * y * M 0 0 := by
  simp [elQ]; ring
theorem elQ_22 (M : Mat2) (x y : ℝ) : elQ M ![0, x] ![0, y] = x * y * M 1 1 := by
  simp [elQ]; ring
theorem elQ_21 (M : Mat2) (x y : ℝ) : elQ M ![0, x] ![y, 0] = x * y * M 1 0 := by
  simp [elQ]; ring
theorem elQ_12 (M : Mat2) (x y : ℝ) : elQ M ![x, 0] ![0, y] = x * y * M 0 1 := by
  simp [elQ]; ring


theorem elQ_comm {S : Mat2} (hS : S 0 1 = S 1 0) (x y : Fin 2 → ℝ) : elQ S x y = elQ S y x := by
  simp only [elQ, hS]; ring

theorem elQ_neg_left (S : Mat2) (x y : Fin 2 → ℝ) : elQ S (-x) y = -elQ S x y := by
  simp only [elQ, Pi.neg_apply]; ring

theorem elDet_self (x : Fin 2 → ℝ) : elDet x x = 0 := by simp only [elDet]; ring

theorem elDet_add_right (x y z : Fin 2 → ℝ) : elDet x (y + z) = elDet x y + elDet x z := by
  simp only [elDet, Pi.add_apply]; ring

theorem elDet_add_left (x y z : Fin 2 → ℝ) : elDet (x + y) z = elDet x z + elDet y z := by
  simp only [elDet, Pi.add_apply]; ring

theorem elDet_neg_right (x y : Fin 2 → ℝ) : elDet x (-y) = -elDet x y := by
  simp only [elDet, Pi.neg_apply]; ring

theorem elQ_mulVec (M P : Mat2) (x y : Fin 2 → ℝ) :
    elQ M (P *ᵥ x) (P *ᵥ y) = elQ (P.transpose * M * P) x y := by
  simp [elQ, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]; ring

theorem elDet_mulVec (P : Mat2) (x y : Fin 2 → ℝ) :
    elDet (P *ᵥ x) (P *ᵥ y) = P.det * elDet x y := by
  simp [elDet, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.det_fin_two]; ring

theorem el_transpose_J0 (P : Mat2) : P.transpose * elJ0 * P = P.det • elJ0 := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [elJ0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

theorem elQ_smul_left (M : Mat2) (c : ℝ) (x y : Fin 2 → ℝ) : elQ M (c • x) y = c * elQ M x y := by
  simp [elQ]; ring

theorem elQ_smul_right (M : Mat2) (c : ℝ) (x y : Fin 2 → ℝ) : elQ M x (c • y) = c * elQ M x y := by
  simp [elQ]; ring

theorem elDet_smul_left (c : ℝ) (x y : Fin 2 → ℝ) : elDet (c • x) y = c * elDet x y := by
  simp [elDet]; ring

theorem elDet_smul_right (c : ℝ) (x y : Fin 2 → ℝ) : elDet x (c • y) = c * elDet x y := by
  simp [elDet]; ring

/-- `R^i` and `R^{-i}` for a label `i`. -/
noncomputable def elRp (i : Fin 3) : Mat2 := Term.triR ^ i.val
noncomputable def elRm (i : Fin 3) : Mat2 := Term.triRinv ^ i.val

theorem elRp_mul_elRm (i : Fin 3) : elRp i * elRm i = 1 := by
  fin_cases i <;> simp [elRp, elRm, pow_succ, Term.triR, Term.triRinv, Matrix.mul_fin_two,
    Matrix.one_fin_two]

theorem elRm_mul_elRp (i : Fin 3) : elRm i * elRp i = 1 := by
  fin_cases i <;> simp [elRp, elRm, pow_succ, Term.triR, Term.triRinv, Matrix.mul_fin_two,
    Matrix.one_fin_two]

theorem triFactor_eq_conj (i : Fin 3) (q : ℝ) :
    Term.triFactor i q = elRm i * Term.triFactor 0 q * elRp i := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [elRp, elRm, pow_succ, Term.triR, Term.triRinv, Term.triFactor, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

theorem elRp_fwd (i : Fin 3) :
    elRp i = Term.triRinv * elRp (i + 1) ∨ elRp i = -(Term.triRinv * elRp (i + 1)) := by
  fin_cases i
  · left; simp [elRp, Term.triR, Term.triRinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  · left; simp [elRp, pow_succ, Term.triR, Term.triRinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  · right
    simp [elRp, pow_succ, Term.triR, Term.triRinv, Matrix.mul_fin_two, Matrix.one_fin_two]

theorem elRp_rev (i : Fin 3) :
    elRp i = Term.triR * elRp (i - 1) ∨ elRp i = -(Term.triR * elRp (i - 1)) := by
  fin_cases i
  · right
    simp [elRp, pow_succ, Term.triR, Term.triRinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  · left; simp [elRp, pow_succ, Term.triR, Term.triRinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  · left; simp [elRp, pow_succ, Term.triR, Term.triRinv, Matrix.mul_fin_two, Matrix.one_fin_two]

theorem elRp_R_elRm (i : Fin 3) :
    elRp i * Term.triR * elRm (i + 1) = 1 ∨ elRp i * Term.triR * elRm (i + 1) = -1 := by
  fin_cases i
  · left; simp [elRp, elRm, Term.triR, Term.triRinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  · left; simp [elRp, elRm, pow_succ, Term.triR, Term.triRinv, Matrix.mul_fin_two,
      Matrix.one_fin_two]
  · right; simp [elRp, elRm, pow_succ, Term.triR, Term.triRinv, Matrix.mul_fin_two,
      Matrix.one_fin_two]


/-! ### The projective lemma for a nonelliptic form -/

/-- For a symmetric `S` with `det S ≤ 0` and three vectors of positive `S`-norm, the product of
the three pairings is positive (the Gram determinant of three plane vectors vanishes). -/
theorem el_three_gram {S : Mat2} (hsym : S 0 1 = S 1 0) (hdet : S.det ≤ 0)
    {y0 y y' : Fin 2 → ℝ} (h0 : 0 < elQ S y0 y0) (h1 : 0 < elQ S y y) (h2 : 0 < elQ S y' y') :
    0 < elQ S y0 y * elQ S y0 y' * elQ S y y' := by
  set a := elQ S y0 y
  set b := elQ S y0 y'
  set c := elQ S y y'
  set d0 := elQ S y0 y0
  set d := elQ S y y
  set d' := elQ S y' y'
  have hdet' : S 0 0 * S 1 1 - S 0 1 * S 1 0 ≤ 0 := by rwa [Matrix.det_fin_two] at hdet
  have g1 : d0 * d - a ^ 2 = (S 0 0 * S 1 1 - S 0 1 * S 1 0) * elDet y0 y ^ 2 := by
    simp only [a, d0, d, elQ, elDet, hsym]; ring
  have g2 : d0 * d' - b ^ 2 = (S 0 0 * S 1 1 - S 0 1 * S 1 0) * elDet y0 y' ^ 2 := by
    simp only [b, d0, d', elQ, elDet, hsym]; ring
  have g3 : d * d' - c ^ 2 = (S 0 0 * S 1 1 - S 0 1 * S 1 0) * elDet y y' ^ 2 := by
    simp only [c, d, d', elQ, elDet, hsym]; ring
  have g : d0 * d * d' - d0 * c ^ 2 - a ^ 2 * d' - b ^ 2 * d + 2 * a * b * c = 0 := by
    simp only [a, b, c, d0, d, d', elQ, hsym]; ring
  have e1 : d0 * d ≤ a ^ 2 := by nlinarith [sq_nonneg (elDet y0 y)]
  have e2 : d0 * d' ≤ b ^ 2 := by nlinarith [sq_nonneg (elDet y0 y')]
  have e3 : d * d' ≤ c ^ 2 := by nlinarith [sq_nonneg (elDet y y')]
  have f1 : d0 * (d * d') ≤ d0 * c ^ 2 := mul_le_mul_of_nonneg_left e3 h0.le
  have f2 : d' * (d0 * d) ≤ d' * a ^ 2 := mul_le_mul_of_nonneg_left e1 h2.le
  have f3 : d * (d0 * d') ≤ d * b ^ 2 := mul_le_mul_of_nonneg_left e2 h1.le
  have hp : 0 < d0 * d * d' := by positivity
  nlinarith

/-- The local lower bound `X` of the cross pairing:
`(s_- j_- + s_+ j_+ - 𝒞)/(4a) = (-1 + 2a(1/s_- + 1/s_+) - a²/K + log(s_- s_+/K))/16`. -/
theorem el_cross_bound {a p n : ℝ} (ha : 0 < a) (hp : 0 < p) (hn : 0 < n) :
    ((a + p) * (elJ p a / 2) + (a + n) * (elJ a n / 2) - (elGa a p + elGa a n) / 16) / (2 * a) =
      (-1 + 2 * a * (1 / (a + p) + 1 / (a + n)) - a ^ 2 / (a ^ 2 + 4) +
        Real.log ((a + p) * (a + n) / (a ^ 2 + 4))) / 16 := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  simp only [elJ, elGa]
  field_simp
  ring

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

/-! ### The local normal multiplier -/

/-- The margins `μ_j = p_j(𝒰)` of the local normal multiplier `𝒰 = (1/√12) X⁻¹ Λ₁ X` at the
switch `k` (the start of piece `k`). -/
noncomputable def mu (k : ℤ) (j : Fin 3) : ℝ :=
  -(C.α k j / (2 * √3)) - (C.m k 0 + C.m k 1 + C.m k 2) * C.m k j / 4 + 1 / 2

/-- `γ² = det 𝒰 = (μ₀μ₁ + μ₁μ₂ + μ₂μ₀)/4 = det Λ₁ / 12` at the switch `k`. -/
noncomputable def gam2 (k : ℤ) : ℝ :=
  (C.mu k 0 * C.mu k 1 + C.mu k 1 * C.mu k 2 + C.mu k 2 * C.mu k 0) / 4

/-- The quadric of the switch margins in the label order of piece `k`. -/
theorem quad_rot (k : ℤ) (i : Fin 3) :
    C.m k i * C.m k (i + 1) + C.m k (i + 1) * C.m k (i - 1) + C.m k (i - 1) * C.m k i = 4 := by
  rw [← el_quad_rot (C.m k) i]; exact C.m_quad k

/-- The active coordinate `μ_{i_k}` is constant along piece `k`. -/
theorem mu_act (k : ℤ) : C.mu (k + 1) (C.lab k) = C.mu k (C.lab k) := by
  obtain ⟨M0, M1, M2, A0, -, -, -, -, -⟩ := C.transport k (i := C.lab k) rfl
  have hq := C.q_pos k
  simp only [mu]
  rw [el_sum_rot (C.m (k + 1)) (C.lab k), el_sum_rot (C.m k) (C.lab k), M0, M1, M2, A0]
  simp only [costateAct]
  field_simp
  ring

/-- `μ_i + μ_{i+1}` is multiplied by `q²` along piece `k` (label `i`). -/
theorem mu_grow (k : ℤ) : C.mu (k + 1) (C.lab k) + C.mu (k + 1) (C.lab k + 1) =
    C.q k ^ 2 * (C.mu k (C.lab k) + C.mu k (C.lab k + 1)) := by
  obtain ⟨M0, M1, M2, A0, A1, -, -, -, -⟩ := C.transport k (i := C.lab k) rfl
  have hq := C.q_pos k
  have hQ := C.quad_rot k (C.lab k)
  simp only [mu]
  rw [el_sum_rot (C.m (k + 1)) (C.lab k), el_sum_rot (C.m k) (C.lab k), M0, M1, M2]
  have e : C.α (k + 1) (C.lab k + 1) =
      C.q k ^ 2 * (C.α k (C.lab k) + C.α k (C.lab k + 1)) +
        costateAGrow (C.m k (C.lab k)) (C.m k (C.lab k + 1)) (C.q k) - C.α (k + 1) (C.lab k) := by
    linarith
  rw [e, A0]
  simp only [costateAct, costateAGrow]
  have h3 := el_s3pos
  field_simp
  linear_combination (4 * √3 * (C.q k ^ 3 - C.q k)) * hQ

/-- `μ_i + μ_{i-1}` is multiplied by `q⁻²` along piece `k` (label `i`). -/
theorem mu_decr (k : ℤ) : C.mu (k + 1) (C.lab k) + C.mu (k + 1) (C.lab k - 1) =
    (C.q k)⁻¹ ^ 2 * (C.mu k (C.lab k) + C.mu k (C.lab k - 1)) := by
  obtain ⟨M0, M1, M2, A0, -, A2, -, -, -⟩ := C.transport k (i := C.lab k) rfl
  have hq := C.q_pos k
  have hQ := C.quad_rot k (C.lab k)
  simp only [mu]
  rw [el_sum_rot (C.m (k + 1)) (C.lab k), el_sum_rot (C.m k) (C.lab k), M0, M1, M2]
  have e : C.α (k + 1) (C.lab k - 1) =
      (C.q k)⁻¹ ^ 2 * (C.α k (C.lab k) + C.α k (C.lab k - 1)) +
        costateADecr (C.m k (C.lab k)) (C.m k (C.lab k - 1)) (C.q k) - C.α (k + 1) (C.lab k) := by
    linarith
  rw [e, A0]
  simp only [costateAct, costateADecr]
  have h3 := el_s3pos
  field_simp
  linear_combination (4 * √3 * (1 - C.q k ^ 2)) * hQ

/-- `γ²` in the label order `i, i + 1, i - 1`. -/
theorem gam2_rot (k : ℤ) (i : Fin 3) : C.gam2 k =
    (C.mu k i * C.mu k (i + 1) + C.mu k (i + 1) * C.mu k (i - 1) + C.mu k (i - 1) * C.mu k i) / 4 := by
  rw [gam2, el_quad_rot (C.mu k) i]

/-- `γ² = det 𝒰` is constant along the cycle. -/
theorem gam2_succ (k : ℤ) : C.gam2 (k + 1) = C.gam2 k := by
  rw [C.gam2_rot (k + 1) (C.lab k), C.gam2_rot k (C.lab k)]
  have h1 := C.mu_act k
  have h2 := C.mu_grow k
  have h3 := C.mu_decr k
  have hq := C.q_pos k
  have e2 : C.mu (k + 1) (C.lab k + 1) = C.q k ^ 2 * (C.mu k (C.lab k) + C.mu k (C.lab k + 1)) -
      C.mu k (C.lab k) := by linarith
  have e3 : C.mu (k + 1) (C.lab k - 1) =
      (C.q k)⁻¹ ^ 2 * (C.mu k (C.lab k) + C.mu k (C.lab k - 1)) - C.mu k (C.lab k) := by linarith
  rw [e2, e3, h1]
  field_simp
  ring

theorem gam2_eq (k : ℤ) : C.gam2 k = C.gam2 0 := by
  induction k using Int.induction_on with
  | zero => rfl
  | succ j ih => rw [C.gam2_succ, ih]
  | pred j ih => rw [← ih, ← C.gam2_succ (-(j : ℤ) - 1), sub_add_cancel]

theorem mu_add (k : ℤ) (j : Fin 3) : C.mu (k + N) j = C.mu k (j - 1) := by
  simp only [mu, C.α_add, C.m_add]
  congr 3
  rw [el_sum_rot (fun l ↦ C.m k (l - 1)) 0]
  simp only [zero_add, show (1 : Fin 3) - 1 = 0 from rfl, show (0 : Fin 3) - 1 = 2 from rfl,
    show (2 : Fin 3) - 1 = 1 from rfl]
  ring

/-! ### Signs, switch norms, cross pairings -/

/-- The sign `ε_k = ±1` of the switch from piece `k` to piece `k + 1`. -/
noncomputable def sgn (k : ℤ) : ℝ := if C.lab (k + 1) = C.lab k + 1 then 1 else -1

/-- `w_k = -μ_{i_k}` on piece `k` (`tr(U Z_k)`, which is `2 (Mloc k)₀₀`). -/
noncomputable def wt (k : ℤ) : ℝ := -C.mu k (C.lab k)

/-- The switch norm `d_k = y_kᵀ S y_k` of the switch after piece `k`. -/
noncomputable def swd (k : ℤ) : ℝ :=
  (C.wt k + C.wt (k + 1)) / (2 * (C.act k + C.act (k + 1)) ^ 2)

/-- The cross pairing `e_k = y_{k-1}ᵀ S y_k` on piece `k`. -/
noncomputable def cre (k : ℤ) : ℝ := C.wt k / (2 * (C.act k ^ 2 + 4))

theorem lab_cases (k : ℤ) : C.lab (k + 1) = C.lab k + 1 ∨ C.lab (k + 1) = C.lab k - 1 :=
  cst_fin_ne_cases (C.lab_ne k)

theorem sgn_fwd {k : ℤ} (h : C.lab (k + 1) = C.lab k + 1) : C.sgn k = 1 := by simp [sgn, h]

theorem sgn_rev {k : ℤ} (h : C.lab (k + 1) = C.lab k - 1) : C.sgn k = -1 := by
  have : C.lab k - 1 ≠ C.lab k + 1 := by generalize C.lab k = i; revert i; decide
  simp [sgn, h, this]

/-- The active margin of piece `k + 1` is the margin of its label at the switch `k + 1`. -/
theorem act_succ (k : ℤ) : C.act (k + 1) = C.m (k + 1) (C.lab (k + 1)) := rfl

/-- The active margin of piece `k - 1` is the margin of its label at the switch `k`. -/
theorem act_pred (k : ℤ) : C.act (k - 1) = C.m k (C.lab (k - 1)) := by
  have := C.m_act (k - 1); rw [sub_add_cancel] at this; exact this.symm

theorem wt_pred (k : ℤ) : C.wt (k - 1) = -C.mu k (C.lab (k - 1)) := by
  have := C.mu_act (k - 1); rw [sub_add_cancel] at this; simp only [wt, this]

/-- **The boundary identity `J_{a_k} = tr(U V_k)`**, in local form: on every piece `k`,
`2 (ε_{k-1} s_{k-1} d_{k-1} + ε_k s_k d_k - (ε_{k-1} + ε_k) a_k e_k)
  = (ε_{k-1} G_a(a_k, a_{k-1}) + ε_k G_a(a_k, a_{k+1})) / 8`. -/
theorem stationarity (k : ℤ) :
    2 * (C.sgn (k - 1) * (C.act (k - 1) + C.act k) * C.swd (k - 1) +
      C.sgn k * (C.act k + C.act (k + 1)) * C.swd k -
      (C.sgn (k - 1) + C.sgn k) * C.act k * C.cre k) =
    (C.sgn (k - 1) * elGa (C.act k) (C.act (k - 1)) +
      C.sgn k * elGa (C.act k) (C.act (k + 1))) / 8 := by
  have ek : k - 1 + 1 = k := by ring
  have hσprev : 2 * C.α k (C.lab (k - 1)) + C.β k (C.lab (k - 1)) = 0 := by
    have := C.sig_act_succ (k - 1); rw [ek] at this; exact this
  have hσ0 := C.sig_act k
  have hσ0' : 2 * C.α (k + 1) (C.lab k) + C.β (k + 1) (C.lab k) = 0 := C.sig_act_succ k
  have hσnext := C.sig_act (k + 1)
  have hperp := C.perp_rot k (C.lab k)
  have hquad := C.quad_rot k (C.lab k)
  obtain ⟨M0, M1, M2, A0, A1, A2, B0, B1, B2⟩ := C.transport k (i := C.lab k) rfl
  have hmg := C.mu_grow k
  have hmd := C.mu_decr k
  have hma := C.mu_act k
  have hq := C.q_pos k
  have hapos : 0 < C.m k (C.lab k) := C.m_pos k _
  have hbpos : 0 < C.m k (C.lab k + 1) := C.m_pos k _
  have hcpos : 0 < C.m k (C.lab k - 1) := C.m_pos k _
  have hn0 : 0 < C.act (k + 1) := C.act_pos _
  have ewk : C.wt k + C.wt (k + 1) = -(C.mu (k + 1) (C.lab k) + C.mu (k + 1) (C.lab (k + 1))) := by
    simp only [wt]; rw [hma]; ring
  have hsum := el_sum_rot (C.m k) (C.lab k)
  have hK : 0 < C.m k (C.lab k) ^ 2 + 4 := by positivity
  simp only [swd, cre, ek, ewk]
  rw [C.wt_pred, C.act_pred]
  simp only [act]
  rcases C.lab_cases (k - 1) with hin | hin <;> rcases C.lab_cases k with hout | hout
  · -- `++`
    rw [ek] at hin
    have hp : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
    rw [C.sgn_fwd (by rw [ek]; exact hin), C.sgn_fwd hout, hp, hout, hmg]
    rw [hp] at hσprev
    rw [hout] at hσnext
    have hb : C.m k (C.lab k + 1) =
        (C.m k (C.lab k) ^ 2 + 4) / (C.m k (C.lab k) + C.m k (C.lab k - 1)) - C.m k (C.lab k) := by
      field_simp; linarith
    have hn : C.m (k + 1) (C.lab k + 1) = (C.m k (C.lab k) + C.m k (C.lab k + 1)) * C.q k -
        C.m k (C.lab k) := M1
    have hnext : 2 * (C.q k ^ 2 * (C.α k (C.lab k) + C.α k (C.lab k + 1)) +
        costateAGrow (C.m k (C.lab k)) (C.m k (C.lab k + 1)) (C.q k)) +
        (C.q k * (C.β k (C.lab k) + C.β k (C.lab k + 1)) +
          costateBGrow (C.m k (C.lab k)) (C.m k (C.lab k + 1)) (C.q k)) = 0 := by
      rw [← A1, ← B1]; linarith
    have hL : Real.log (C.q k) = Real.log (C.m k (C.lab k) + C.m k (C.lab k - 1)) +
        Real.log (C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1)) -
        Real.log (C.m k (C.lab k) ^ 2 + 4) := by
      have e : C.q k = (C.m k (C.lab k) + C.m k (C.lab k - 1)) *
          (C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1)) / (C.m k (C.lab k) ^ 2 + 4) := by
        rw [hn, hb]; field_simp; ring
      have h1 : 0 < C.m k (C.lab k) + C.m k (C.lab k - 1) := by linarith
      have h2 : 0 < C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1) := by
        linarith [C.m_pos (k + 1) (C.lab k + 1)]
      rw [e, Real.log_div (mul_pos h1 h2).ne' hK.ne', Real.log_mul h1.ne' h2.ne']
    have key := el_stat_pp hapos hcpos hq hb hn hσ0 hσprev hperp hL hnext
    simp only [wt, mu, hsum]
    linear_combination (norm := skip) key
    field_simp
    el_ring
  · -- `+-`
    rw [ek] at hin
    have hp : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
    rw [C.sgn_fwd (by rw [ek]; exact hin), C.sgn_rev hout, hp, hout, hmd]
    rw [hp] at hσprev
    rw [hout] at hσnext
    have hb : C.m k (C.lab k + 1) =
        (C.m k (C.lab k) ^ 2 + 4) / (C.m k (C.lab k) + C.m k (C.lab k - 1)) - C.m k (C.lab k) := by
      field_simp; linarith
    have hn : C.m (k + 1) (C.lab k - 1) = (C.m k (C.lab k) + C.m k (C.lab k - 1)) / C.q k -
        C.m k (C.lab k) := M2
    have hnext : 2 * ((C.q k)⁻¹ ^ 2 * (C.α k (C.lab k) + C.α k (C.lab k - 1)) +
        costateADecr (C.m k (C.lab k)) (C.m k (C.lab k - 1)) (C.q k)) +
        ((C.q k)⁻¹ * (C.β k (C.lab k) + C.β k (C.lab k - 1)) +
          costateBDecr (C.m k (C.lab k)) (C.m k (C.lab k - 1)) (C.q k)) = 0 := by
      rw [← A2, ← B2]; linarith
    have hL : Real.log (C.q k) = Real.log (C.m k (C.lab k) + C.m k (C.lab k - 1)) -
        Real.log (C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1)) := by
      have h1 : 0 < C.m k (C.lab k) + C.m k (C.lab k - 1) := by linarith
      have h2 : 0 < C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1) := by
        linarith [C.m_pos (k + 1) (C.lab k - 1)]
      have e : C.q k = (C.m k (C.lab k) + C.m k (C.lab k - 1)) /
          (C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1)) := by
        rw [hn, show ∀ x y z : ℝ, x + (y / z - x) = y / z from fun x y z ↦ by ring]
        field_simp
      rw [e, Real.log_div h1.ne' h2.ne']
    have key := el_stat_pm hapos hcpos hq hb hn hσ0 hσprev hperp hL hnext
    simp only [wt, mu, hsum]
    linear_combination (norm := skip) key
    field_simp
    el_ring
  · -- `-+`
    rw [ek] at hin
    have hp : C.lab (k - 1) = C.lab k + 1 := by rw [hin, sub_add_cancel]
    rw [C.sgn_rev (by rw [ek]; exact hin), C.sgn_fwd hout, hp, hout, hmg]
    rw [hp] at hσprev
    rw [hout] at hσnext
    have hc : C.m k (C.lab k - 1) =
        (C.m k (C.lab k) ^ 2 + 4) / (C.m k (C.lab k) + C.m k (C.lab k + 1)) - C.m k (C.lab k) := by
      field_simp; linarith
    have hn : C.m (k + 1) (C.lab k + 1) = (C.m k (C.lab k) + C.m k (C.lab k + 1)) * C.q k -
        C.m k (C.lab k) := M1
    have hnext : 2 * (C.q k ^ 2 * (C.α k (C.lab k) + C.α k (C.lab k + 1)) +
        costateAGrow (C.m k (C.lab k)) (C.m k (C.lab k + 1)) (C.q k)) +
        (C.q k * (C.β k (C.lab k) + C.β k (C.lab k + 1)) +
          costateBGrow (C.m k (C.lab k)) (C.m k (C.lab k + 1)) (C.q k)) = 0 := by
      rw [← A1, ← B1]; linarith
    have hL : Real.log (C.q k) = -Real.log (C.m k (C.lab k) + C.m k (C.lab k + 1)) +
        Real.log (C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1)) := by
      have h1 : 0 < C.m k (C.lab k) + C.m k (C.lab k + 1) := by linarith
      have h2 : 0 < C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1) := by
        linarith [C.m_pos (k + 1) (C.lab k + 1)]
      have e : C.q k = (C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1)) /
          (C.m k (C.lab k) + C.m k (C.lab k + 1)) := by
        rw [hn]; field_simp; ring
      rw [e, Real.log_div h2.ne' h1.ne']; ring
    have key := el_stat_mp hapos hbpos hq hc hn hσ0 hσprev hperp hL hnext
    simp only [wt, mu, hsum]
    linear_combination (norm := skip) key
    field_simp
    el_ring
  · -- `--`
    rw [ek] at hin
    have hp : C.lab (k - 1) = C.lab k + 1 := by rw [hin, sub_add_cancel]
    rw [C.sgn_rev (by rw [ek]; exact hin), C.sgn_rev hout, hp, hout, hmd]
    rw [hp] at hσprev
    rw [hout] at hσnext
    have hc : C.m k (C.lab k - 1) =
        (C.m k (C.lab k) ^ 2 + 4) / (C.m k (C.lab k) + C.m k (C.lab k + 1)) - C.m k (C.lab k) := by
      field_simp; linarith
    have hn : C.m (k + 1) (C.lab k - 1) = (C.m k (C.lab k) + C.m k (C.lab k - 1)) / C.q k -
        C.m k (C.lab k) := M2
    have hnext : 2 * ((C.q k)⁻¹ ^ 2 * (C.α k (C.lab k) + C.α k (C.lab k - 1)) +
        costateADecr (C.m k (C.lab k)) (C.m k (C.lab k - 1)) (C.q k)) +
        ((C.q k)⁻¹ * (C.β k (C.lab k) + C.β k (C.lab k - 1)) +
          costateBDecr (C.m k (C.lab k)) (C.m k (C.lab k - 1)) (C.q k)) = 0 := by
      rw [← A2, ← B2]; linarith
    have hL : Real.log (C.q k) = -Real.log (C.m k (C.lab k) + C.m k (C.lab k + 1)) -
        Real.log (C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1)) +
        Real.log (C.m k (C.lab k) ^ 2 + 4) := by
      have h1 : 0 < C.m k (C.lab k) + C.m k (C.lab k + 1) := by linarith
      have h2 : 0 < C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1) := by
        linarith [C.m_pos (k + 1) (C.lab k - 1)]
      have e : C.q k = (C.m k (C.lab k) ^ 2 + 4) / ((C.m k (C.lab k) + C.m k (C.lab k + 1)) *
          (C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1))) := by
        rw [hn, show ∀ x y z : ℝ, x + (y / z - x) = y / z from fun x y z ↦ by ring, hc,
          show ∀ x y z : ℝ, x + (y / z - x) = y / z from fun x y z ↦ by ring]
        field_simp
      rw [e, Real.log_div hK.ne' (mul_pos h1 h2).ne', Real.log_mul h1.ne' h2.ne']; ring
    have key := el_stat_mm hapos hbpos hq hc hn hσ0 hσprev hperp hL hnext
    simp only [wt, mu, hsum]
    linear_combination (norm := skip) key
    field_simp
    el_ring

/-- `d_k - j_k/2 = (α_i + α_{i+1})/(4√3 s_k²)` at a reverse switch (`i = i_{k+1}`). -/
theorem swd_sub_rev {k : ℤ} (h : C.lab (k + 1) = C.lab k - 1) :
    C.swd k - elJ (C.act k) (C.act (k + 1)) / 2 =
      (C.α (k + 1) (C.lab (k + 1)) + C.α (k + 1) (C.lab (k + 1) + 1)) /
        (4 * √3 * (C.act k + C.act (k + 1)) ^ 2) := by
  have hk : C.lab k = C.lab (k + 1) + 1 := by rw [h, sub_add_cancel]
  have hquad := C.quad_rot (k + 1) (C.lab (k + 1))
  have hsum := el_sum_rot (C.m (k + 1)) (C.lab (k + 1))
  have hma := C.mu_act k
  have ha0 : C.act k = C.m (k + 1) (C.lab (k + 1) + 1) := by rw [← hk]; exact (C.m_act k).symm
  have hp1 := C.m_pos (k + 1) (C.lab (k + 1))
  have hp2 := C.m_pos (k + 1) (C.lab (k + 1) + 1)
  have h3 := el_s3pos
  simp only [swd, elJ, wt]
  rw [← hma, ha0, act_succ, hk]
  have hc : C.m (k + 1) (C.lab (k + 1) - 1) =
      (4 - C.m (k + 1) (C.lab (k + 1)) * C.m (k + 1) (C.lab (k + 1) + 1)) /
        (C.m (k + 1) (C.lab (k + 1)) + C.m (k + 1) (C.lab (k + 1) + 1)) := by
    field_simp; linarith
  simp only [mu, hsum, hc]
  field_simp
  el_ring

/-- `d_k - j_k/2 = (α_i + α_{i-1})/(4√3 s_k²)` at a forward switch (`i = i_{k+1}`). -/
theorem swd_sub_fwd {k : ℤ} (h : C.lab (k + 1) = C.lab k + 1) :
    C.swd k - elJ (C.act k) (C.act (k + 1)) / 2 =
      (C.α (k + 1) (C.lab (k + 1)) + C.α (k + 1) (C.lab (k + 1) - 1)) /
        (4 * √3 * (C.act k + C.act (k + 1)) ^ 2) := by
  have hk : C.lab k = C.lab (k + 1) - 1 := by rw [h, add_sub_cancel_right]
  have hquad := C.quad_rot (k + 1) (C.lab (k + 1))
  have hsum := el_sum_rot (C.m (k + 1)) (C.lab (k + 1))
  have hma := C.mu_act k
  have ha0 : C.act k = C.m (k + 1) (C.lab (k + 1) - 1) := by rw [← hk]; exact (C.m_act k).symm
  have hp1 := C.m_pos (k + 1) (C.lab (k + 1))
  have hp2 := C.m_pos (k + 1) (C.lab (k + 1) - 1)
  have h3 := el_s3pos
  simp only [swd, elJ, wt]
  rw [← hma, ha0, act_succ, hk]
  have hb : C.m (k + 1) (C.lab (k + 1) + 1) =
      (4 - C.m (k + 1) (C.lab (k + 1)) * C.m (k + 1) (C.lab (k + 1) - 1)) /
        (C.m (k + 1) (C.lab (k + 1)) + C.m (k + 1) (C.lab (k + 1) - 1)) := by
    field_simp; linarith
  simp only [mu, hsum, hb]
  field_simp
  el_ring

/-- **The weak switching inequality at a reverse switch**: `d_k ≤ j_k/2`. -/
theorem swd_rev {k : ℤ} (h : C.lab (k + 1) = C.lab k - 1) :
    C.swd k ≤ elJ (C.act k) (C.act (k + 1)) / 2 := by
  have hk : C.lab k = C.lab (k + 1) + 1 := by rw [h, sub_add_cancel]
  have hY : C.α (k + 1) (C.lab (k + 1)) + C.α (k + 1) (C.lab (k + 1) + 1) ≤ 0 := by
    refine el_grow_start (C.one_lt_q (k + 1)) ?_ (C.sig_grow_le (k + 1))
    have h1 := C.sig_act (k + 1)
    have h2 := C.sig_act_succ k
    rw [hk] at h2
    simp only [sig] at h2
    linarith
  have e := C.swd_sub_rev h
  have hd : 0 < 4 * √3 * (C.act k + C.act (k + 1)) ^ 2 := by
    have := C.act_pos k; have := C.act_pos (k + 1); have := el_s3pos; positivity
  have : (C.α (k + 1) (C.lab (k + 1)) + C.α (k + 1) (C.lab (k + 1) + 1)) /
      (4 * √3 * (C.act k + C.act (k + 1)) ^ 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hY hd.le
  linarith

/-- **The weak switching inequality at a forward switch**: `d_k ≥ j_k/2`. -/
theorem swd_fwd {k : ℤ} (h : C.lab (k + 1) = C.lab k + 1) :
    elJ (C.act k) (C.act (k + 1)) / 2 ≤ C.swd k := by
  have hk : C.lab k = C.lab (k + 1) - 1 := by rw [h, add_sub_cancel_right]
  have hY : 0 ≤ C.α (k + 1) (C.lab (k + 1)) + C.α (k + 1) (C.lab (k + 1) - 1) := by
    refine el_decr_start (C.one_lt_q (k + 1)) ?_ (C.sig_decr_le (k + 1))
    have h1 := C.sig_act (k + 1)
    have h2 := C.sig_act_succ k
    rw [hk] at h2
    simp only [sig] at h2
    linarith
  have e := C.swd_sub_fwd h
  have hd : 0 < 4 * √3 * (C.act k + C.act (k + 1)) ^ 2 := by
    have := C.act_pos k; have := C.act_pos (k + 1); have := el_s3pos; positivity
  have : 0 ≤ (C.α (k + 1) (C.lab (k + 1)) + C.α (k + 1) (C.lab (k + 1) - 1)) /
      (4 * √3 * (C.act k + C.act (k + 1)) ^ 2) := div_nonneg hY hd.le
  linarith

/-! ### Turns, Gram identities, centres -/

/-- The data on piece `k` in the label order of piece `k` (`i = i_k`): the margins and `μ`
at its start, the factor relation of the margin `n = a_{k+1}`, and the transport of `μ`. -/
private theorem wt_succ_grow {k : ℤ} (hout : C.lab (k + 1) = C.lab k + 1) :
    C.wt k + C.wt (k + 1) = -(C.q k ^ 2 * (C.mu k (C.lab k) + C.mu k (C.lab k + 1))) := by
  simp only [wt]; rw [hout, ← C.mu_grow k, C.mu_act k]; ring

private theorem wt_succ_decr {k : ℤ} (hout : C.lab (k + 1) = C.lab k - 1) :
    C.wt k + C.wt (k + 1) = -((C.q k)⁻¹ ^ 2 * (C.mu k (C.lab k) + C.mu k (C.lab k - 1))) := by
  simp only [wt]; rw [hout, ← C.mu_decr k, C.mu_act k]; ring

private theorem act_succ_grow {k : ℤ} (hout : C.lab (k + 1) = C.lab k + 1) :
    C.act k + C.act (k + 1) = (C.m k (C.lab k) + C.m k (C.lab k + 1)) * C.q k := by
  rw [act_succ, hout, C.m_grow k]; simp only [act]; ring

private theorem act_succ_decr {k : ℤ} (hout : C.lab (k + 1) = C.lab k - 1) :
    C.act k + C.act (k + 1) = (C.m k (C.lab k) + C.m k (C.lab k - 1)) / C.q k := by
  rw [act_succ, hout, C.m_decr k]; simp only [act]; ring

private theorem wt_pred_eq (k : ℤ) :
    C.wt (k - 1) + C.wt k = -(C.mu k (C.lab (k - 1)) + C.mu k (C.lab k)) := by
  rw [C.wt_pred]; simp only [wt]; ring

private theorem act_pred_eq (k : ℤ) :
    C.act (k - 1) + C.act k = C.m k (C.lab (k - 1)) + C.m k (C.lab k) := by
  rw [C.act_pred]; rfl

/-- At a turn `- +` the two switch vectors are opposite: `d_{k-1} = d_k`. -/
theorem turn_swd_mp {k : ℤ} (hin : C.lab k = C.lab (k - 1) - 1)
    (hout : C.lab (k + 1) = C.lab k + 1) : C.swd (k - 1) = C.swd k := by
  have hp : C.lab (k - 1) = C.lab k + 1 := by rw [hin, sub_add_cancel]
  have hq := C.q_pos k
  have h1 := C.m_pos k (C.lab k)
  have h2 := C.m_pos k (C.lab k + 1)
  simp only [swd]
  rw [sub_add_cancel, C.wt_succ_grow hout, C.act_succ_grow hout, C.wt_pred_eq, C.act_pred_eq, hp]
  field_simp
  ring

/-- At a turn `+ -` the two switch vectors are opposite: `d_{k-1} = d_k`. -/
theorem turn_swd_pm {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1)
    (hout : C.lab (k + 1) = C.lab k - 1) : C.swd (k - 1) = C.swd k := by
  have hp : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
  have hq := C.q_pos k
  have h1 := C.m_pos k (C.lab k)
  have h2 := C.m_pos k (C.lab k - 1)
  simp only [swd]
  rw [sub_add_cancel, C.wt_succ_decr hout, C.act_succ_decr hout, C.wt_pred_eq, C.act_pred_eq, hp]
  field_simp
  ring

/-- **The turn secant**: at a turn `k`, with `p = a_{k-1}`, `n = a_{k+1}`,
`16 (n - p) d_k = G_a(a_k, n) - G_a(a_k, p)` and `d_{k-1} = d_k`. -/
theorem turn_secant {k : ℤ} (hturn : C.sgn (k - 1) = -C.sgn k) :
    C.swd (k - 1) = C.swd k ∧
      16 * (C.act (k + 1) - C.act (k - 1)) * C.swd k =
        elGa (C.act k) (C.act (k + 1)) - elGa (C.act k) (C.act (k - 1)) := by
  have hst := C.stationarity k
  have ek : k - 1 + 1 = k := by ring
  have hpm : C.swd (k - 1) = C.swd k := by
    rcases C.lab_cases (k - 1) with hin | hin <;> rw [ek] at hin <;>
      rcases C.lab_cases k with hout | hout
    · rw [C.sgn_fwd (by rw [ek]; exact hin), C.sgn_fwd hout] at hturn; norm_num at hturn
    · exact C.turn_swd_pm hin hout
    · exact C.turn_swd_mp hin hout
    · rw [C.sgn_rev (by rw [ek]; exact hin), C.sgn_rev hout] at hturn; norm_num at hturn
  refine ⟨hpm, ?_⟩
  rw [hturn, hpm] at hst
  have hs : C.sgn k = 1 ∨ C.sgn k = -1 := by
    unfold sgn; split_ifs <;> simp
  rcases hs with hs | hs <;> rw [hs] at hst <;> linarith

/-- **Gram identity at a centre `- -`**: `d_{k-1} d_k - e_k² = γ²/K_k²`. -/
theorem gram_mm {k : ℤ} (hin : C.lab k = C.lab (k - 1) - 1)
    (hout : C.lab (k + 1) = C.lab k - 1) :
    C.swd (k - 1) * C.swd k - C.cre k ^ 2 = C.gam2 k / (C.act k ^ 2 + 4) ^ 2 := by
  have hp : C.lab (k - 1) = C.lab k + 1 := by rw [hin, sub_add_cancel]
  have hq := C.q_pos k
  have h1 := C.m_pos k (C.lab k)
  have h2 := C.m_pos k (C.lab k + 1)
  have h3 := C.m_pos k (C.lab k - 1)
  have hquad := C.quad_rot k (C.lab k)
  have hqe : C.q k = (C.m k (C.lab k) ^ 2 + 4) /
      ((C.m k (C.lab k) + C.m k (C.lab k + 1)) * (C.act k + C.act (k + 1))) := by
    rw [C.act_succ_decr hout]
    have hc : C.m k (C.lab k - 1) = (C.m k (C.lab k) ^ 2 + 4) /
        (C.m k (C.lab k) + C.m k (C.lab k + 1)) - C.m k (C.lab k) := by field_simp; linarith
    rw [hc, show ∀ x y z : ℝ, x + (y / z - x) = y / z from fun x y z ↦ by ring]; field_simp
  simp only [swd, cre]
  rw [sub_add_cancel, C.wt_succ_decr hout, C.wt_pred_eq, C.act_pred_eq, hp, C.gam2_rot k (C.lab k)]
  have hs : 0 < C.act k + C.act (k + 1) := by linarith [C.act_pos k, C.act_pos (k + 1)]
  rw [hqe]
  simp only [wt, act] at hs ⊢
  field_simp
  ring

/-- **Gram identity at a forward same-sign piece `+ +`**: `d_{k-1} d_k - e_k² = γ²/K_k²`. -/
theorem gram_pp {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1)
    (hout : C.lab (k + 1) = C.lab k + 1) :
    C.swd (k - 1) * C.swd k - C.cre k ^ 2 = C.gam2 k / (C.act k ^ 2 + 4) ^ 2 := by
  have hp : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
  have hq := C.q_pos k
  have h1 := C.m_pos k (C.lab k)
  have h2 := C.m_pos k (C.lab k + 1)
  have h3 := C.m_pos k (C.lab k - 1)
  have hquad := C.quad_rot k (C.lab k)
  have hqe : C.q k = (C.m k (C.lab k) + C.m k (C.lab k - 1)) * (C.act k + C.act (k + 1)) /
      (C.m k (C.lab k) ^ 2 + 4) := by
    rw [C.act_succ_grow hout]
    have hb : C.m k (C.lab k + 1) = (C.m k (C.lab k) ^ 2 + 4) /
        (C.m k (C.lab k) + C.m k (C.lab k - 1)) - C.m k (C.lab k) := by field_simp; linarith
    rw [hb, show ∀ x y z : ℝ, x + (y / z - x) = y / z from fun x y z ↦ by ring]; field_simp
  simp only [swd, cre]
  rw [sub_add_cancel, C.wt_succ_grow hout, C.wt_pred_eq, C.act_pred_eq, hp, C.gam2_rot k (C.lab k)]
  have hs : 0 < C.act k + C.act (k + 1) := by linarith [C.act_pos k, C.act_pos (k + 1)]
  rw [hqe]
  simp only [wt, act] at hs ⊢
  field_simp
  ring

/-- **The turn bound**: at a turn the switch norm is at least `3/32`. -/
theorem turn_swd_ge {k : ℤ} (hturn : C.sgn (k - 1) = -C.sgn k) : 3 / 32 ≤ C.swd k := by
  obtain ⟨-, hsec⟩ := C.turn_secant hturn
  have ek : k - 1 + 1 = k := by ring
  have ha := C.act_pos k
  have hp := C.act_pos (k - 1)
  have hn := C.act_pos (k + 1)
  rw [elGa_sub ha hn hp] at hsec
  -- the outer active margins differ
  have hne : C.act (k + 1) ≠ C.act (k - 1) := by
    rcases C.lab_cases (k - 1) with hin | hin <;> rw [ek] at hin <;>
      rcases C.lab_cases k with hout | hout
    · rw [C.sgn_fwd (by rw [ek]; exact hin), C.sgn_fwd hout] at hturn; norm_num at hturn
    · have := C.turn_down (k - 1) (by rw [ek]; exact hin)
        (by rw [ek, show k - 1 + 2 = k + 1 by ring]; exact hout)
      rw [show k - 1 + 2 = k + 1 by ring] at this; exact this.ne
    · have := C.turn_up (k - 1) (by rw [ek]; exact hin)
        (by rw [ek, show k - 1 + 2 = k + 1 by ring]; exact hout)
      rw [show k - 1 + 2 = k + 1 by ring] at this; exact this.ne'
    · rw [C.sgn_rev (by rw [ek]; exact hin), C.sgn_rev hout] at hturn; norm_num at hturn
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs := elF_secant (x := 1 + C.act (k - 1) / C.act k) (y := 1 + C.act (k + 1) / C.act k)
      (by positivity) (by have := div_le_div_of_nonneg_right hlt.le ha.le; linarith)
    have e : (1 + C.act (k - 1) / C.act k) - (1 + C.act (k + 1) / C.act k) =
        (C.act (k - 1) - C.act (k + 1)) / C.act k := by field_simp; ring
    rw [e] at hs
    have h1 : 0 < C.act (k - 1) - C.act (k + 1) := by linarith
    have h2 : 3 / 2 * (C.act (k - 1) - C.act (k + 1)) ≤
        2 * C.act k * (elF (1 + C.act (k - 1) / C.act k) - elF (1 + C.act (k + 1) / C.act k)) := by
      have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * C.act k)
      have e2 : 2 * C.act k * (3 / 4 * ((C.act (k - 1) - C.act (k + 1)) / C.act k)) =
          3 / 2 * (C.act (k - 1) - C.act (k + 1)) := by field_simp; ring
      linarith
    nlinarith
  · have hs := elF_secant (x := 1 + C.act (k + 1) / C.act k) (y := 1 + C.act (k - 1) / C.act k)
      (by positivity) (by have := div_le_div_of_nonneg_right hgt.le ha.le; linarith)
    have e : (1 + C.act (k + 1) / C.act k) - (1 + C.act (k - 1) / C.act k) =
        (C.act (k + 1) - C.act (k - 1)) / C.act k := by field_simp; ring
    rw [e] at hs
    have h1 : 0 < C.act (k + 1) - C.act (k - 1) := by linarith
    have h2 : 3 / 2 * (C.act (k + 1) - C.act (k - 1)) ≤
        2 * C.act k * (elF (1 + C.act (k + 1) / C.act k) - elF (1 + C.act (k - 1) / C.act k)) := by
      have := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 2 * C.act k)
      have e2 : 2 * C.act k * (3 / 4 * ((C.act (k + 1) - C.act (k - 1)) / C.act k)) =
          3 / 2 * (C.act (k + 1) - C.act (k - 1)) := by field_simp; ring
      linarith
    nlinarith

/-- **Centre stationarity**. At a centre `k` (both incident switches reverse), with `a = a_k`,
`p = a_{k-1}`, `n = a_{k+1}`, `r = a/(a + p)`, `t = a/(a + n)`, `ρ = a²/(a² + 4)`, `u = 8 d_{k-1}`,
`v = 8 d_k`, `E = 16 e_k`: `E = 1 + r + t - ρ + log(ρ/(r t)) - (1 - u)/r - (1 - v)/t`. -/
theorem centre_stat {k : ℤ} (hin : C.lab k = C.lab (k - 1) - 1)
    (hout : C.lab (k + 1) = C.lab k - 1) :
    16 * C.cre k = 1 + C.act k / (C.act k + C.act (k - 1)) + C.act k / (C.act k + C.act (k + 1)) -
      C.act k ^ 2 / (C.act k ^ 2 + 4) +
      Real.log (C.act k ^ 2 / (C.act k ^ 2 + 4) /
        (C.act k / (C.act k + C.act (k - 1)) * (C.act k / (C.act k + C.act (k + 1))))) -
      (1 - 8 * C.swd (k - 1)) / (C.act k / (C.act k + C.act (k - 1))) -
      (1 - 8 * C.swd k) / (C.act k / (C.act k + C.act (k + 1))) := by
  have hst := C.stationarity k
  rw [C.sgn_rev (by rw [sub_add_cancel]; exact hin), C.sgn_rev hout] at hst
  have ha := C.act_pos k
  have hp := C.act_pos (k - 1)
  have hn := C.act_pos (k + 1)
  have hlog : Real.log (C.act k ^ 2 / (C.act k ^ 2 + 4) /
      (C.act k / (C.act k + C.act (k - 1)) * (C.act k / (C.act k + C.act (k + 1))))) =
      Real.log (C.act k + C.act (k - 1)) + Real.log (C.act k + C.act (k + 1)) -
        Real.log (C.act k ^ 2 + 4) := by
    have e : C.act k ^ 2 / (C.act k ^ 2 + 4) /
        (C.act k / (C.act k + C.act (k - 1)) * (C.act k / (C.act k + C.act (k + 1)))) =
        (C.act k + C.act (k - 1)) * (C.act k + C.act (k + 1)) / (C.act k ^ 2 + 4) := by
      field_simp
    rw [e, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity)]
  have he : C.cre k = ((C.act k + C.act (k - 1)) * C.swd (k - 1) +
      (C.act k + C.act (k + 1)) * C.swd k) / (2 * C.act k) -
      (elGa (C.act k) (C.act (k - 1)) + elGa (C.act k) (C.act (k + 1))) / (32 * C.act k) := by
    linear_combination (norm := skip) (1 / (4 * C.act k)) * hst
    field_simp
    ring
  rw [hlog, he]
  simp only [elGa]
  field_simp
  ring

/-- The factor of a centre `- -`: `q_k (a_k + a_{k-1}) (a_k + a_{k+1}) = a_k² + 4`. -/
theorem centre_factor {k : ℤ} (hin : C.lab k = C.lab (k - 1) - 1)
    (hout : C.lab (k + 1) = C.lab k - 1) :
    C.q k * ((C.act k + C.act (k - 1)) * (C.act k + C.act (k + 1))) = C.act k ^ 2 + 4 := by
  have hp : C.lab (k - 1) = C.lab k + 1 := by rw [hin, sub_add_cancel]
  have hq := C.q_pos k
  have h1 := C.m_pos k (C.lab k)
  have h2 := C.m_pos k (C.lab k + 1)
  have hquad := C.quad_rot k (C.lab k)
  have e := C.act_succ_decr hout
  rw [show C.act k + C.act (k + 1) = C.act k + C.act (k + 1) from rfl, e, C.act_pred, hp]
  have hc : C.m k (C.lab k - 1) = (C.m k (C.lab k) ^ 2 + 4) /
      (C.m k (C.lab k) + C.m k (C.lab k + 1)) - C.m k (C.lab k) := by field_simp; linarith
  rw [hc, show ∀ x y z : ℝ, x + (y / z - x) = y / z from fun x y z ↦ by ring]
  simp only [act]
  field_simp

/-! ### The frame of piece `k` and the global prefix frame -/

/-- `A_k = T₀(q_k) R^{-ε_k}`. -/
noncomputable def Amat (k : ℤ) : Mat2 :=
  Term.triFactor 0 (C.q k) * (if C.lab (k + 1) = C.lab k + 1 then Term.triRinv else Term.triR)

/-- `A_k⁻¹ = R^{ε_k} T₀(q_k)⁻¹`. -/
noncomputable def Ainv (k : ℤ) : Mat2 :=
  (if C.lab (k + 1) = C.lab k + 1 then Term.triR else Term.triRinv) * Term.triFactor 0 (C.q k)⁻¹

theorem Amat_Ainv (k : ℤ) : C.Amat k * C.Ainv k = 1 := by
  have hq := (C.q_pos k).ne'
  simp only [Amat, Ainv]
  split_ifs
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Term.triRinv, Term.triRinv_mul_triR, Matrix.one_mul,
      Term.triFactor_mul_inv 0 hq]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Term.triR, Term.triR_mul_triRinv, Matrix.one_mul,
      Term.triFactor_mul_inv 0 hq]

theorem Ainv_Amat (k : ℤ) : C.Ainv k * C.Amat k = 1 := by
  have hq := (C.q_pos k).ne'
  simp only [Amat, Ainv]
  split_ifs
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Term.triFactor 0 _), Term.triFactor_inv_mul 0 hq,
      Matrix.one_mul, Term.triR_mul_triRinv]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Term.triFactor 0 _), Term.triFactor_inv_mul 0 hq,
      Matrix.one_mul, Term.triRinv_mul_triR]

theorem det_Amat (k : ℤ) : (C.Amat k).det = 1 := by
  have hq := (C.q_pos k).ne'
  simp only [Amat]
  split_ifs <;> simp [Term.triFactor, Term.triR, Term.triRinv, Matrix.det_fin_two, hq]

theorem Amat_add (k : ℤ) : C.Amat (k + N) = C.Amat k := by
  simp only [Amat, show k + N + 1 = k + 1 + N by ring, C.lab_add, C.q_add, add_left_inj]

/-- The prefix `P_n = A_0 ⋯ A_{n-1}`. -/
noncomputable def pre : ℕ → Mat2
  | 0 => 1
  | n + 1 => pre n * C.Amat n

/-- `P_n⁻¹`. -/
noncomputable def preInv : ℕ → Mat2
  | 0 => 1
  | n + 1 => C.Ainv n * preInv n

theorem pre_preInv (n : ℕ) : C.pre n * C.preInv n = 1 := by
  induction n with
  | zero => simp [pre, preInv]
  | succ n ih =>
    simp only [pre, preInv]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C.Amat n), C.Amat_Ainv, Matrix.one_mul, ih]

theorem preInv_pre (n : ℕ) : C.preInv n * C.pre n = 1 := by
  induction n with
  | zero => simp [pre, preInv]
  | succ n ih =>
    simp only [pre, preInv]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C.preInv n), ih, Matrix.one_mul, C.Ainv_Amat]

theorem det_pre (n : ℕ) : (C.pre n).det = 1 := by
  induction n with
  | zero => simp [pre]
  | succ n ih => simp only [pre, Matrix.det_mul, ih, C.det_Amat, mul_one]

/-- The local normal multiplier `M_k = P_k⁻¹ U P_k` in the frame of piece `k` (label `i_k` rotated
to `0`). -/
noncomputable def Mloc (k : ℤ) : Mat2 := triY (fun j ↦ C.mu k (j + C.lab k))

theorem det_Mloc (k : ℤ) : (C.Mloc k).det = C.gam2 k := by
  rw [Mloc, det_triY, C.gam2_rot k (C.lab k)]
  simp only [zero_add, show (1 : Fin 3) + C.lab k = C.lab k + 1 by abel,
    show (2 : Fin 3) + C.lab k = C.lab k - 1 by
      generalize C.lab k = i; revert i; decide]

/-- Along piece `k`, `𝒰` is conjugated by the tangent factor. -/
private theorem Mloc_conj (k : ℤ) :
    triY (fun j ↦ C.mu (k + 1) (j + C.lab k)) =
      Term.triFactor 0 (C.q k)⁻¹ * C.Mloc k * Term.triFactor 0 (C.q k) := by
  have hq := (C.q_pos k).ne'
  have h1 := C.mu_act k
  have h2 := C.mu_grow k
  have h3 := C.mu_decr k
  have e1 : (1 : Fin 3) + C.lab k = C.lab k + 1 := by abel
  have e2 : (2 : Fin 3) + C.lab k = C.lab k - 1 := by generalize C.lab k = i; revert i; decide
  have e3 : C.mu (k + 1) (C.lab k - 1) =
      (C.q k)⁻¹ ^ 2 * (C.mu k (C.lab k) + C.mu k (C.lab k - 1)) - C.mu k (C.lab k) := by
    linarith
  have e4 : C.mu (k + 1) (C.lab k + 1) =
      C.q k ^ 2 * (C.mu k (C.lab k) + C.mu k (C.lab k + 1)) - C.mu k (C.lab k) := by linarith
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [triY, Mloc, Term.triFactor, Matrix.mul_apply, Fin.sum_univ_two, e1, e2, h1, e3, e4] <;>
    field_simp <;> ring

/-- `M_{k+1} = A_k⁻¹ M_k A_k`. -/
theorem Mloc_succ (k : ℤ) : C.Mloc (k + 1) = C.Ainv k * C.Mloc k * C.Amat k := by
  have hc := C.Mloc_conj k
  rcases C.lab_cases k with h | h
  · have e : C.Mloc (k + 1) = triY (fun j ↦ C.mu (k + 1) (j + 1 + C.lab k)) := by
      simp only [Mloc, h]; congr 1; funext j; congr 1; abel
    rw [e, triY_rot_succ (fun j ↦ C.mu (k + 1) (j + C.lab k)), hc]
    simp only [Amat, Ainv, h, ↓reduceIte, Matrix.mul_assoc]
  · have e : C.Mloc (k + 1) = triY (fun j ↦ C.mu (k + 1) (j - 1 + C.lab k)) := by
      simp only [Mloc, h]; congr 1; funext j; congr 1; abel
    have hne : ¬ (C.lab k - 1 = C.lab k + 1) := by generalize C.lab k = i; revert i; decide
    rw [e, triY_rot_pred (fun j ↦ C.mu (k + 1) (j + C.lab k)), hc]
    simp only [Amat, Ainv, h, hne, ↓reduceIte, Matrix.mul_assoc]

/-- `M_n = P_n⁻¹ M_0 P_n`. -/
theorem Mloc_pre (n : ℕ) : C.Mloc n = C.preInv n * C.Mloc 0 * C.pre n := by
  induction n with
  | zero => simp [pre, preInv]
  | succ n ih =>
    rw [Nat.cast_succ, C.Mloc_succ, ih]
    simp only [pre, preInv, Matrix.mul_assoc]

/-- **The full frame monodromy**: `P_N = σ I`, `σ = ±1`. -/
theorem pre_N : C.pre N = 1 ∨ C.pre N = -1 := by
  have hpm : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ s' : ℝ, (s' = 1 ∨ s' = -1) → (s * s' = 1 ∨ s * s' = -1) := by
    rintro s (rfl | rfl) s' (rfl | rfl) <;> norm_num
  -- one factor
  have hstep : ∀ n : ℕ, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      C.pre n * Term.triFactor 0 (C.q n) * elRp (C.lab n) =
        s • (C.pre (n + 1) * elRp (C.lab ((n + 1 : ℕ) : ℤ))) := by
    intro n
    simp only [pre, Amat, Nat.cast_succ]
    rcases C.lab_cases n with h | h
    · simp only [h, ↓reduceIte]
      rcases elRp_fwd (C.lab n) with h' | h'
      · exact ⟨1, Or.inl rfl, by rw [h', one_smul]; simp only [Matrix.mul_assoc]⟩
      · exact ⟨-1, Or.inr rfl, by rw [h', neg_smul, one_smul]; simp only [Matrix.mul_assoc,
          Matrix.mul_neg]⟩
    · have hne : ¬ (C.lab n - 1 = C.lab n + 1) := by
        generalize C.lab n = i; revert i; decide
      simp only [h, hne, ↓reduceIte]
      rcases elRp_rev (C.lab n) with h' | h'
      · exact ⟨1, Or.inl rfl, by rw [h', one_smul]; simp only [Matrix.mul_assoc]⟩
      · exact ⟨-1, Or.inr rfl, by rw [h', neg_smul, one_smul]; simp only [Matrix.mul_assoc,
          Matrix.mul_neg]⟩
  -- the tangent products from `0`
  have key : ∀ n : ℕ, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ((List.range n).map fun j : ℕ ↦ Term.triFactor (C.lab j) (C.q j)).prod =
        s • (elRm (C.lab 0) * C.pre n * elRp (C.lab n)) := by
    intro n
    induction n with
    | zero => exact ⟨1, Or.inl rfl, by simp [pre, elRm_mul_elRp]⟩
    | succ n ih =>
      obtain ⟨s, hs, hF⟩ := ih
      obtain ⟨s', hs', hP⟩ := hstep n
      refine ⟨s * s', hpm s hs s' hs', ?_⟩
      rw [List.prod_range_succ, hF, triFactor_eq_conj]
      have e : elRm (C.lab 0) * C.pre n * elRp (C.lab n) *
          (elRm (C.lab n) * Term.triFactor 0 (C.q n) * elRp (C.lab n)) =
          elRm (C.lab 0) * (C.pre n * Term.triFactor 0 (C.q n) * elRp (C.lab n)) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (elRp (C.lab n)), elRp_mul_elRm, Matrix.one_mul]
      rw [Matrix.smul_mul, e, hP, Matrix.mul_smul, smul_smul]
      simp only [Matrix.mul_assoc]
  obtain ⟨s, hs, hF⟩ := key N
  have hcl := C.closure 0
  simp only [zero_add] at hcl
  rw [hcl, show C.lab (N : ℤ) = C.lab 0 + 1 by simpa using C.lab_add 0] at hF
  have hfin : elRp (C.lab 0) * Term.triR * elRm (C.lab 0 + 1) = s • C.pre N := by
    rw [hF, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    simp only [← Matrix.mul_assoc]
    rw [elRp_mul_elRm, Matrix.one_mul, Matrix.mul_assoc, elRp_mul_elRm, Matrix.mul_one]
  rcases hs with rfl | rfl <;> rcases elRp_R_elRm (C.lab 0) with h | h <;> rw [h] at hfin
  · left; simpa using hfin.symm
  · right; rw [one_smul] at hfin; exact hfin.symm
  · right; rw [neg_smul, one_smul] at hfin; rw [← neg_neg (C.pre N), ← hfin]
  · left; rw [neg_smul, one_smul, neg_inj] at hfin; exact hfin.symm

/-! ### The switch vectors -/

/-- `s_k = a_k + a_{k+1}`. -/
noncomputable def sw (k : ℤ) : ℝ := C.act k + C.act (k + 1)

theorem sw_pos (k : ℤ) : 0 < C.sw k := add_pos (C.act_pos k) (C.act_pos (k + 1))

/-- The switch vector after piece `k`, in the frame of piece `k`. -/
noncomputable def outv (k : ℤ) : Fin 2 → ℝ :=
  if C.lab (k + 1) = C.lab k + 1 then ![C.q k / C.sw k, 0] else ![0, 1 / (C.q k * C.sw k)]

/-- The switch vector before piece `k`, in the frame of piece `k`. -/
noncomputable def inc (k : ℤ) : Fin 2 → ℝ :=
  if C.lab k = C.lab (k - 1) + 1 then ![0, -(1 / C.sw (k - 1))] else ![-(1 / C.sw (k - 1)), 0]

theorem Amat_inc (k : ℤ) : C.Amat k *ᵥ C.inc (k + 1) = C.outv k := by
  have hq := (C.q_pos k).ne'
  have hs := (C.sw_pos k).ne'
  simp only [Amat, inc, outv, add_sub_cancel_right]
  rcases C.lab_cases k with h | h
  · simp only [h, ↓reduceIte]
    ext i; fin_cases i <;>
      simp [Term.triFactor, Term.triRinv, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  · have hne : ¬ (C.lab k - 1 = C.lab k + 1) := by generalize C.lab k = i; revert i; decide
    simp only [h, hne, ↓reduceIte]
    ext i; fin_cases i <;>
      simp [Term.triFactor, Term.triR, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      field_simp

/-- The local form `S_k = -J₀ M_k` (`P_kᵀ S P_k`). -/
noncomputable def Sloc (k : ℤ) : Mat2 := -(elJ0 * C.Mloc k)

private theorem Sloc_apply (k : ℤ) :
    C.Sloc k 0 0 = -(C.mu k (C.lab k) + C.mu k (C.lab k + 1)) / 2 ∧
      C.Sloc k 0 1 = C.mu k (C.lab k) / 2 ∧
      C.Sloc k 1 0 = C.mu k (C.lab k) / 2 ∧
      C.Sloc k 1 1 = -(C.mu k (C.lab k) + C.mu k (C.lab k - 1)) / 2 := by
  have e1 : (1 : Fin 3) + C.lab k = C.lab k + 1 := by abel
  have e2 : (2 : Fin 3) + C.lab k = C.lab k - 1 := by generalize C.lab k = i; revert i; decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Sloc, Mloc, triY, elJ0, Matrix.mul_apply, Fin.sum_univ_two, e1, e2] <;> ring

theorem Sloc_out (k : ℤ) : elQ (C.Sloc k) (C.outv k) (C.outv k) = C.swd k := by
  obtain ⟨s00, s01, s10, s11⟩ := C.Sloc_apply k
  have hq := (C.q_pos k).ne'
  have hs := (C.sw_pos k).ne'
  simp only [swd, outv]
  rcases C.lab_cases k with h | h
  · rw [C.wt_succ_grow h]
    simp only [h, ↓reduceIte, elQ_11, s00]
    simp only [sw] at hs ⊢
    field_simp
  · have hne : ¬ (C.lab k - 1 = C.lab k + 1) := by generalize C.lab k = i; revert i; decide
    rw [C.wt_succ_decr h]
    simp only [hne, h, ↓reduceIte, elQ_22, s11]
    simp only [sw] at hs ⊢
    field_simp

theorem Sloc_in (k : ℤ) : elQ (C.Sloc k) (C.inc k) (C.inc k) = C.swd (k - 1) := by
  obtain ⟨s00, s01, s10, s11⟩ := C.Sloc_apply k
  have hs := (C.sw_pos (k - 1)).ne'
  simp only [swd, inc, sub_add_cancel, C.wt_pred_eq]
  rcases C.lab_cases (k - 1) with h | h <;> rw [sub_add_cancel] at h
  · have hp : C.lab (k - 1) = C.lab k - 1 := by rw [h, add_sub_cancel_right]
    rw [ite_eq_left h, hp, elQ_22, s11]
    simp only [sw, sub_add_cancel] at hs ⊢
    field_simp; ring
  · have hp : C.lab (k - 1) = C.lab k + 1 := by rw [h, sub_add_cancel]
    have hne : ¬ (C.lab (k - 1) - 1 = C.lab (k - 1) + 1) := by
      generalize C.lab (k - 1) = i; revert i; decide
    have hne' : ¬ (C.lab k = C.lab (k - 1) + 1) := by rw [h]; exact hne
    rw [ite_eq_right hne', hp, elQ_11, s00]
    simp only [sw, sub_add_cancel] at hs ⊢
    field_simp; ring

/-- The factor of a forward same-sign piece: `q_k K_k = s_{k-1} s_k`. -/
theorem factor_pp {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1)
    (hout : C.lab (k + 1) = C.lab k + 1) :
    C.q k * (C.act k ^ 2 + 4) = C.sw (k - 1) * C.sw k := by
  have hp : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
  have h1 := C.m_pos k (C.lab k)
  have h3 := C.m_pos k (C.lab k - 1)
  have hquad := C.quad_rot k (C.lab k)
  have e := C.act_succ_grow hout
  simp only [sw, sub_add_cancel]
  rw [e, C.act_pred, hp]
  have hb : C.m k (C.lab k + 1) = (C.m k (C.lab k) ^ 2 + 4) /
      (C.m k (C.lab k) + C.m k (C.lab k - 1)) - C.m k (C.lab k) := by field_simp; linarith
  rw [hb, show ∀ x y z : ℝ, x + (y / z - x) = y / z from fun x y z ↦ by ring]
  simp only [act]
  field_simp
  ring

/-- The factor of a turn `- +`: `q_k s_{k-1} = s_k`. -/
theorem factor_mp {k : ℤ} (hin : C.lab k = C.lab (k - 1) - 1)
    (hout : C.lab (k + 1) = C.lab k + 1) : C.q k * C.sw (k - 1) = C.sw k := by
  have hp : C.lab (k - 1) = C.lab k + 1 := by rw [hin, sub_add_cancel]
  simp only [sw, sub_add_cancel]
  rw [C.act_succ_grow hout, C.act_pred, hp]
  simp only [act]; ring

/-- The factor of a turn `+ -`: `q_k s_k = s_{k-1}`. -/
theorem factor_pm {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1)
    (hout : C.lab (k + 1) = C.lab k - 1) : C.q k * C.sw k = C.sw (k - 1) := by
  have hp : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
  have hq := (C.q_pos k).ne'
  simp only [sw, sub_add_cancel]
  rw [C.act_succ_decr hout, C.act_pred, hp]
  simp only [act]; field_simp; ring

theorem inc_fwd {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1) :
    C.inc k = ![0, -(1 / C.sw (k - 1))] := by
  simp only [inc]; exact ite_eq_left hin

theorem inc_rev {k : ℤ} (hin : C.lab k = C.lab (k - 1) - 1) :
    C.inc k = ![-(1 / C.sw (k - 1)), 0] := by
  have hne : ¬ (C.lab k = C.lab (k - 1) + 1) := by
    rw [hin]; generalize C.lab (k - 1) = i; revert i; decide
  simp only [inc]; exact ite_eq_right hne

theorem outv_fwd {k : ℤ} (hout : C.lab (k + 1) = C.lab k + 1) :
    C.outv k = ![C.q k / C.sw k, 0] := by
  simp only [outv]; exact ite_eq_left hout

theorem outv_rev {k : ℤ} (hout : C.lab (k + 1) = C.lab k - 1) :
    C.outv k = ![0, 1 / (C.q k * C.sw k)] := by
  have hne : ¬ (C.lab (k + 1) = C.lab k + 1) := by
    rw [hout]; generalize C.lab k = i; revert i; decide
  simp only [outv]; exact ite_eq_right hne

/-- **The cross pairing at a same-sign piece**: `y_{k-1}ᵀ S y_k = e_k`, and the Wronskian
`det(y_{k-1}, y_k) = ε/K_k`. -/
theorem cross_pp {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1)
    (hout : C.lab (k + 1) = C.lab k + 1) :
    elQ (C.Sloc k) (C.inc k) (C.outv k) = C.cre k ∧
      elDet (C.inc k) (C.outv k) = 1 / (C.act k ^ 2 + 4) := by
  obtain ⟨-, -, s10, -⟩ := C.Sloc_apply k
  have hf := C.factor_pp hin hout
  have h1 := (C.sw_pos (k - 1)).ne'
  have h2 := (C.sw_pos k).ne'
  have hK : C.act k ^ 2 + 4 ≠ 0 := by positivity
  rw [C.inc_fwd hin, C.outv_fwd hout, elQ_21, s10]
  refine ⟨?_, ?_⟩
  · simp only [cre, wt]
    field_simp
    simp only [act] at hf ⊢
    linear_combination (-(C.mu k (C.lab k))) * hf
  · simp only [elDet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    field_simp
    linear_combination hf

theorem cross_mm {k : ℤ} (hin : C.lab k = C.lab (k - 1) - 1)
    (hout : C.lab (k + 1) = C.lab k - 1) :
    elQ (C.Sloc k) (C.inc k) (C.outv k) = C.cre k ∧
      elDet (C.inc k) (C.outv k) = -(1 / (C.act k ^ 2 + 4)) := by
  obtain ⟨-, s01, -, -⟩ := C.Sloc_apply k
  have hf := C.centre_factor hin hout
  have h1 := (C.sw_pos (k - 1)).ne'
  have h2 := (C.sw_pos k).ne'
  have hq := (C.q_pos k).ne'
  have hK : C.act k ^ 2 + 4 ≠ 0 := by positivity
  rw [C.inc_rev hin, C.outv_rev hout, elQ_12, s01]
  have hf' : C.q k * C.sw (k - 1) * C.sw k = C.act k ^ 2 + 4 := by
    simp only [sw, sub_add_cancel]; rw [← hf]; ring
  refine ⟨?_, ?_⟩
  · simp only [cre, wt]
    field_simp
    simp only [act] at hf' ⊢
    linear_combination (C.mu k (C.lab k)) * hf'
  · simp only [elDet, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    field_simp
    linear_combination hf'

/-- At a turn the two switch vectors are opposite. -/
theorem outv_turn {k : ℤ} (hturn : C.sgn (k - 1) = -C.sgn k) : C.outv k = -C.inc k := by
  have ek : k - 1 + 1 = k := by ring
  rcases C.lab_cases (k - 1) with hin | hin <;> rw [ek] at hin <;>
    rcases C.lab_cases k with hout | hout
  · rw [C.sgn_fwd (by rw [ek]; exact hin), C.sgn_fwd hout] at hturn; norm_num at hturn
  · have hf := C.factor_pm hin hout
    have h2 := (C.sw_pos k).ne'
    have hq := (C.q_pos k).ne'
    rw [C.inc_fwd hin, C.outv_rev hout, ← hf]
    ext i; fin_cases i <;> simp <;> field_simp
  · have hf := C.factor_mp hin hout
    have h2 := (C.sw_pos (k - 1)).ne'
    have hq := (C.q_pos k).ne'
    rw [C.inc_rev hin, C.outv_fwd hout, ← hf]
    ext i; fin_cases i <;> simp <;> field_simp
  · rw [C.sgn_rev (by rw [ek]; exact hin), C.sgn_rev hout] at hturn; norm_num at hturn

/-! ### The global switch vectors -/

/-- The switch vector `y_n = P_n (outgoing vector of piece n)` after piece `n` in the global
frame. -/
noncomputable def yv (n : ℕ) : Fin 2 → ℝ := C.pre n *ᵥ C.outv n

theorem yv_eq_inc (n : ℕ) : C.pre (n + 1) *ᵥ C.inc ((n + 1 : ℕ) : ℤ) = C.yv n := by
  simp only [pre, yv, Nat.cast_succ, ← Matrix.mulVec_mulVec, C.Amat_inc]

theorem transpose_pre_J0 (n : ℕ) : (C.pre n).transpose * elJ0 = elJ0 * C.preInv n := by
  have h := el_transpose_J0 (C.pre n)
  rw [C.det_pre, one_smul] at h
  calc (C.pre n).transpose * elJ0 = (C.pre n).transpose * elJ0 * (C.pre n * C.preInv n) := by
        rw [C.pre_preInv, Matrix.mul_one]
    _ = elJ0 * C.preInv n := by rw [← Matrix.mul_assoc, h]

/-- The global form `S = -J₀ U` read in the frame of piece `n`. -/
theorem elQ_pre (n : ℕ) (x y : Fin 2 → ℝ) :
    elQ (C.Sloc 0) (C.pre n *ᵥ x) (C.pre n *ᵥ y) = elQ (C.Sloc n) x y := by
  rw [elQ_mulVec]
  congr 1
  simp only [Sloc, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, C.transpose_pre_J0]
  rw [C.Mloc_pre n]
  simp only [Matrix.mul_assoc, Nat.cast_ofNat]

theorem elDet_pre (n : ℕ) (x y : Fin 2 → ℝ) :
    elDet (C.pre n *ᵥ x) (C.pre n *ᵥ y) = elDet x y := by
  rw [elDet_mulVec, C.det_pre, one_mul]

/-- `d_n = y_nᵀ S y_n`. -/
theorem yv_norm (n : ℕ) : elQ (C.Sloc 0) (C.yv n) (C.yv n) = C.swd n := by
  rw [yv, C.elQ_pre, C.Sloc_out]

/-- The global pair `(y_n, y_{n+1})` read in the frame of piece `n + 1`. -/
theorem yv_pair (n : ℕ) :
    elQ (C.Sloc 0) (C.yv n) (C.yv (n + 1)) =
        elQ (C.Sloc ((n + 1 : ℕ) : ℤ)) (C.inc ((n + 1 : ℕ) : ℤ)) (C.outv ((n + 1 : ℕ) : ℤ)) ∧
      elDet (C.yv n) (C.yv (n + 1)) =
        elDet (C.inc ((n + 1 : ℕ) : ℤ)) (C.outv ((n + 1 : ℕ) : ℤ)) := by
  rw [← C.yv_eq_inc n]
  exact ⟨by rw [yv, C.elQ_pre], by rw [yv, C.elDet_pre]⟩


/-- `S = -J₀ M_k` is symmetric. -/
theorem Sloc_symm (k : ℤ) : C.Sloc k 0 1 = C.Sloc k 1 0 := by
  obtain ⟨-, h1, h2, -⟩ := C.Sloc_apply k; rw [h1, h2]

theorem outv_add (k : ℤ) : C.outv (k + N) = C.outv k := by
  have hs : C.sw (k + N) = C.sw k := by
    simp only [sw, show k + N + 1 = k + 1 + N by ring, C.act_add]
  simp only [outv, show k + N + 1 = k + 1 + N by ring, C.lab_add, C.q_add, hs, add_left_inj]

theorem pre_add_N (n : ℕ) : C.pre (N + n) = C.pre N * C.pre n := by
  induction n with
  | zero => simp [pre]
  | succ n ih =>
    rw [← add_assoc, pre, ih, pre, Matrix.mul_assoc]
    congr 2
    rw [show ((N + n : ℕ) : ℤ) = (n : ℤ) + N by push_cast; ring, C.Amat_add]

/-- **The switch vectors close up to the monodromy**: `y_{N+n} = P_N y_n`. -/
theorem yv_add_N (n : ℕ) : C.yv (N + n) = C.pre N *ᵥ C.yv n := by
  rw [yv, C.pre_add_N, ← Matrix.mulVec_mulVec, yv,
    show ((N + n : ℕ) : ℤ) = (n : ℤ) + N by push_cast; ring, C.outv_add]

/-! ### The cross pairings of a nonelliptic multiplier -/

theorem elJ_ge (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 3 / 16 ≤ elJ a b := by
  simp only [elJ]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (a - b)]

/-- `e_k = ((a + p) d_{k-1} + (a + n) d_k - (G_a(a,p) + G_a(a,n))/16)/(2a)` at a same-sign piece. -/
private theorem cre_eq_same {k : ℤ} (hs : C.sgn (k - 1) = C.sgn k) :
    C.cre k = ((C.act k + C.act (k - 1)) * C.swd (k - 1) + (C.act k + C.act (k + 1)) * C.swd k -
      (elGa (C.act k) (C.act (k - 1)) + elGa (C.act k) (C.act (k + 1))) / 16) / (2 * C.act k) := by
  have hst := C.stationarity k
  have ha := C.act_pos k
  rw [hs] at hst
  have h1 : C.sgn k = 1 ∨ C.sgn k = -1 := by unfold sgn; split_ifs <;> simp
  rcases h1 with h1 | h1 <;> rw [h1] at hst <;> field_simp <;> linarith

/-- **Positive cross pairing**: if `γ² ≤ 0`, the cross pairing of a forward same-sign piece is
positive. -/
theorem cre_pos_pp {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1)
    (hout : C.lab (k + 1) = C.lab k + 1) (hgam : C.gam2 k ≤ 0) : 0 < C.cre k := by
  have ha := C.act_pos k
  have hp := C.act_pos (k - 1)
  have hn := C.act_pos (k + 1)
  have hs : C.sgn (k - 1) = C.sgn k := by
    rw [C.sgn_fwd (by rw [sub_add_cancel]; exact hin), C.sgn_fwd hout]
  have he := C.cre_eq_same hs
  have hd1 := C.swd_fwd (k := k - 1) (by rw [sub_add_cancel]; exact hin)
  have hd2 := C.swd_fwd hout
  rw [sub_add_cancel] at hd1
  have hX := el_cross_bound ha hp hn
  -- `e ≥ X`
  have hge : ((C.act k + C.act (k - 1)) * (elJ (C.act (k - 1)) (C.act k) / 2) +
      (C.act k + C.act (k + 1)) * (elJ (C.act k) (C.act (k + 1)) / 2) -
      (elGa (C.act k) (C.act (k - 1)) + elGa (C.act k) (C.act (k + 1))) / 16) / (2 * C.act k) ≤
      C.cre k := by
    rw [he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  -- `X > -1/16`
  have hfac := C.factor_pp hin hout
  have hq := C.one_lt_q k
  have hlog : 0 < Real.log ((C.act k + C.act (k - 1)) * (C.act k + C.act (k + 1)) /
      (C.act k ^ 2 + 4)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by positivity), one_mul]
    simp only [sw, sub_add_cancel] at hfac
    have : C.act k ^ 2 + 4 < C.q k * (C.act k ^ 2 + 4) := by
      have : 0 < C.act k ^ 2 + 4 := by positivity
      nlinarith
    rw [hfac] at this; linarith
  have hap : C.act k * C.act (k - 1) < 4 := by
    have hq4 := C.quad_rot k (C.lab k)
    have hp' : C.act (k - 1) = C.m k (C.lab k - 1) := by
      rw [C.act_pred, show C.lab (k - 1) = C.lab k - 1 by rw [hin, add_sub_cancel_right]]
    have := C.m_pos k (C.lab k + 1)
    rw [hp']; simp only [act]
    nlinarith [C.m_pos k (C.lab k), C.m_pos k (C.lab k - 1)]
  have hterm : C.act k ^ 2 / (C.act k ^ 2 + 4) < 2 * C.act k * (1 / (C.act k + C.act (k - 1))) := by
    rw [div_lt_iff₀ (by positivity)]
    field_simp
    nlinarith
  have hpos : 0 < 2 * C.act k * (1 / (C.act k + C.act (k + 1))) := by positivity
  rw [hX] at hge
  -- the Gram identity
  have hg := C.gram_pp hin hout
  have hK : 0 < (C.act k ^ 2 + 4) ^ 2 := by positivity
  have hgn : C.gam2 k / (C.act k ^ 2 + 4) ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hgam hK.le
  have hJ1 := elJ_ge _ _ hp ha
  have hJ2 := elJ_ge _ _ ha hn
  have hdd : (3 / 32) ^ 2 ≤ C.swd (k - 1) * C.swd k := by
    have h1 : 3 / 32 ≤ C.swd (k - 1) := by linarith
    have h2 : 3 / 32 ≤ C.swd k := by linarith
    nlinarith
  by_contra hcon
  push Not at hcon
  have : (3 / 32) ^ 2 ≤ C.cre k ^ 2 := by linarith
  have : C.cre k ≤ -(3 / 32) := by nlinarith
  linarith [mul_add (2 * C.act k) (1 / (C.act k + C.act (k - 1))) (1 / (C.act k + C.act (k + 1)))]

/-- **Negative cross pairing**: if `γ² ≤ 0`, the cross pairing at a centre with a strict minimum and
switch norms at least `3/32` is negative. -/
theorem cre_neg_mm {k : ℤ} (hin : C.lab k = C.lab (k - 1) - 1)
    (hout : C.lab (k + 1) = C.lab k - 1) (hmp : C.act k < C.act (k - 1))
    (hmn : C.act k < C.act (k + 1)) (hd1 : 3 / 32 ≤ C.swd (k - 1)) (hd2 : 3 / 32 ≤ C.swd k)
    (hgam : C.gam2 k ≤ 0) : C.cre k < 0 := by
  have ha := C.act_pos k
  have hp := C.act_pos (k - 1)
  have hn := C.act_pos (k + 1)
  have hs : C.sgn (k - 1) = C.sgn k := by
    rw [C.sgn_rev (by rw [sub_add_cancel]; exact hin), C.sgn_rev hout]
  have he := C.cre_eq_same hs
  have hu1 := C.swd_rev (k := k - 1) (by rw [sub_add_cancel]; exact hin)
  have hu2 := C.swd_rev hout
  rw [sub_add_cancel] at hu1
  have hX := el_cross_bound ha hp hn
  have hle : C.cre k ≤ ((C.act k + C.act (k - 1)) * (elJ (C.act (k - 1)) (C.act k) / 2) +
      (C.act k + C.act (k + 1)) * (elJ (C.act k) (C.act (k + 1)) / 2) -
      (elGa (C.act k) (C.act (k - 1)) + elGa (C.act k) (C.act (k + 1))) / 16) / (2 * C.act k) := by
    rw [he]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hfac := C.centre_factor hin hout
  have hq := C.one_lt_q k
  have hlog : Real.log ((C.act k + C.act (k - 1)) * (C.act k + C.act (k + 1)) /
      (C.act k ^ 2 + 4)) < 0 := by
    apply Real.log_neg (by positivity)
    rw [div_lt_one (by positivity)]
    have hpos : 0 < (C.act k + C.act (k - 1)) * (C.act k + C.act (k + 1)) := by positivity
    nlinarith
  have h1 : 2 * C.act k * (1 / (C.act k + C.act (k - 1)) + 1 / (C.act k + C.act (k + 1))) < 2 := by
    have e1 : C.act k * (1 / (C.act k + C.act (k - 1))) < 1 / 2 := by
      rw [mul_one_div, div_lt_iff₀ (by positivity)]; linarith
    have e2 : C.act k * (1 / (C.act k + C.act (k + 1))) < 1 / 2 := by
      rw [mul_one_div, div_lt_iff₀ (by positivity)]; linarith
    nlinarith
  have h2 : 0 ≤ C.act k ^ 2 / (C.act k ^ 2 + 4) := by positivity
  rw [hX] at hle
  have hg := C.gram_mm hin hout
  have hK : 0 < (C.act k ^ 2 + 4) ^ 2 := by positivity
  have hgn : C.gam2 k / (C.act k ^ 2 + 4) ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hgam hK.le
  have hdd : (3 / 32) ^ 2 ≤ C.swd (k - 1) * C.swd k := by nlinarith
  by_contra hcon
  push Not at hcon
  have : (3 / 32) ^ 2 ≤ C.cre k ^ 2 := by linarith
  have : 3 / 32 ≤ C.cre k := by nlinarith
  linarith

/-! ### The cost of a cycle: the signed action and the Euler identity -/

theorem sgn_add (k : ℤ) : C.sgn (k + N) = C.sgn k := by
  simp only [sgn, show k + N + 1 = k + 1 + N by ring, C.lab_add, add_left_inj]

theorem sgn_cases (k : ℤ) : C.sgn k = 1 ∨ C.sgn k = -1 := by
  unfold sgn; split_ifs <;> simp

/-- The cost of piece `k` split at its two switches: `arc_k = ε_k F₁(a_k, a_{k+1})
+ ε_{k-1} F₂(a_{k-1}, a_k)`. -/
theorem arc_eq (k : ℤ) :
    C.arc k = C.sgn k * elF1 (C.act k) (C.act (k + 1)) +
      C.sgn (k - 1) * elF2 (C.act (k - 1)) (C.act k) := by
  have ek : k - 1 + 1 = k := by ring
  have hquad := C.quad_rot k (C.lab k)
  obtain ⟨-, M1, M2, -⟩ := C.transport k (i := C.lab k) rfl
  have hq := C.q_pos k
  have hapos : 0 < C.m k (C.lab k) := C.m_pos k _
  have hbpos : 0 < C.m k (C.lab k + 1) := C.m_pos k _
  have hcpos : 0 < C.m k (C.lab k - 1) := C.m_pos k _
  have hK : 0 < C.m k (C.lab k) ^ 2 + 4 := by positivity
  simp only [Term.Cycle.arc]
  rw [C.act_pred]
  simp only [act]
  rcases C.lab_cases (k - 1) with hin | hin <;> rw [ek] at hin <;>
    rcases C.lab_cases k with hout | hout
  · have hp : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
    rw [C.sgn_fwd (k := k - 1) (by rw [ek]; exact hin), C.sgn_fwd hout, hp, hout]
    have hb : C.m k (C.lab k + 1) =
        (C.m k (C.lab k) ^ 2 + 4) / (C.m k (C.lab k) + C.m k (C.lab k - 1)) - C.m k (C.lab k) := by
      field_simp; linarith
    have h1 : 0 < C.m k (C.lab k) + C.m k (C.lab k - 1) := by linarith
    have h2 : 0 < C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1) := by
      linarith [C.m_pos (k + 1) (C.lab k + 1)]
    have hL : Real.log (C.q k) = Real.log (C.m k (C.lab k) + C.m k (C.lab k - 1)) +
        Real.log (C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1)) -
        Real.log (C.m k (C.lab k) ^ 2 + 4) := by
      have e : C.q k = (C.m k (C.lab k) + C.m k (C.lab k - 1)) *
          (C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1)) / (C.m k (C.lab k) ^ 2 + 4) := by
        rw [M1, hb]; field_simp; ring
      rw [e, Real.log_div (mul_pos h1 h2).ne' hK.ne', Real.log_mul h1.ne' h2.ne']
    rw [el_arc_pp hapos hcpos hq hb M1 hL]
    ring
  · have hp : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
    rw [C.sgn_fwd (k := k - 1) (by rw [ek]; exact hin), C.sgn_rev hout, hp, hout]
    have hb : C.m k (C.lab k + 1) =
        (C.m k (C.lab k) ^ 2 + 4) / (C.m k (C.lab k) + C.m k (C.lab k - 1)) - C.m k (C.lab k) := by
      field_simp; linarith
    have h1 : 0 < C.m k (C.lab k) + C.m k (C.lab k - 1) := by linarith
    have h2 : 0 < C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1) := by
      linarith [C.m_pos (k + 1) (C.lab k - 1)]
    have hL : Real.log (C.q k) = Real.log (C.m k (C.lab k) + C.m k (C.lab k - 1)) -
        Real.log (C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1)) := by
      have e : C.q k = (C.m k (C.lab k) + C.m k (C.lab k - 1)) /
          (C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1)) := by
        rw [M2, show ∀ x y z : ℝ, x + (y / z - x) = y / z from fun x y z ↦ by ring]
        field_simp
      rw [e, Real.log_div h1.ne' h2.ne']
    rw [el_arc_pm hapos hcpos hq hb M2 hL]
    ring
  · have hp : C.lab (k - 1) = C.lab k + 1 := by rw [hin, sub_add_cancel]
    rw [C.sgn_rev (k := k - 1) (by rw [ek]; exact hin), C.sgn_fwd hout, hp, hout]
    have hc : C.m k (C.lab k - 1) =
        (C.m k (C.lab k) ^ 2 + 4) / (C.m k (C.lab k) + C.m k (C.lab k + 1)) - C.m k (C.lab k) := by
      field_simp; linarith
    have h1 : 0 < C.m k (C.lab k) + C.m k (C.lab k + 1) := by linarith
    have h2 : 0 < C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1) := by
      linarith [C.m_pos (k + 1) (C.lab k + 1)]
    have hL : Real.log (C.q k) = -Real.log (C.m k (C.lab k) + C.m k (C.lab k + 1)) +
        Real.log (C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1)) := by
      have e : C.q k = (C.m k (C.lab k) + C.m (k + 1) (C.lab k + 1)) /
          (C.m k (C.lab k) + C.m k (C.lab k + 1)) := by
        rw [M1]; field_simp; ring
      rw [e, Real.log_div h2.ne' h1.ne']; ring
    rw [el_arc_mp hapos hbpos hq hc M1 hL]
    ring
  · have hp : C.lab (k - 1) = C.lab k + 1 := by rw [hin, sub_add_cancel]
    rw [C.sgn_rev (k := k - 1) (by rw [ek]; exact hin), C.sgn_rev hout, hp, hout]
    have hc : C.m k (C.lab k - 1) =
        (C.m k (C.lab k) ^ 2 + 4) / (C.m k (C.lab k) + C.m k (C.lab k + 1)) - C.m k (C.lab k) := by
      field_simp; linarith
    have h1 : 0 < C.m k (C.lab k) + C.m k (C.lab k + 1) := by linarith
    have h2 : 0 < C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1) := by
      linarith [C.m_pos (k + 1) (C.lab k - 1)]
    have hL : Real.log (C.q k) = -Real.log (C.m k (C.lab k) + C.m k (C.lab k + 1)) -
        Real.log (C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1)) +
        Real.log (C.m k (C.lab k) ^ 2 + 4) := by
      have e : C.q k = (C.m k (C.lab k) ^ 2 + 4) / ((C.m k (C.lab k) + C.m k (C.lab k + 1)) *
          (C.m k (C.lab k) + C.m (k + 1) (C.lab k - 1))) := by
        rw [M2, show ∀ x y z : ℝ, x + (y / z - x) = y / z from fun x y z ↦ by ring, hc,
          show ∀ x y z : ℝ, x + (y / z - x) = y / z from fun x y z ↦ by ring]
        field_simp
      rw [e, Real.log_div hK.ne' (mul_pos h1 h2).ne', Real.log_mul h1.ne' h2.ne']; ring
    rw [el_arc_mm hapos hbpos hq hc M2 hL]
    ring

/-- Shifting a sum over one period of an `N`-periodic function. -/
theorem el_sum_shift (f : ℤ → ℝ) (hf : ∀ k, f (k + N) = f k) :
    ∑ j ∈ Finset.range N, f ((j : ℤ) + 1) = ∑ j ∈ Finset.range N, f j := by
  have h := Finset.sum_range_succ (fun j : ℕ ↦ f j) N
  have h' := Finset.sum_range_succ' (fun j : ℕ ↦ f j) N
  have hN : f (N : ℤ) = f 0 := by simpa using hf 0
  push_cast at h h'
  linarith

/-- **The signed action**: the raw cost of the cycle is `8 J = ∑ ε_k G(a_k, a_{k+1})`. -/
theorem rawCost_eq :
    C.rawCost = ∑ k ∈ Finset.range N, C.sgn k * elG (C.act k) (C.act (k + 1)) := by
  simp only [Term.Cycle.rawCost]
  rw [show ∑ k ∈ Finset.range N, C.arc k = ∑ k ∈ Finset.range N,
      (C.sgn k * elF1 (C.act k) (C.act (k + 1)) + C.sgn ((k : ℤ) - 1) * elF2 (C.act (k - 1))
        (C.act k)) from Finset.sum_congr rfl fun k _ ↦ C.arc_eq k, Finset.sum_add_distrib]
  have hshift := el_sum_shift (N := N) (fun k ↦ C.sgn (k - 1) * elF2 (C.act (k - 1)) (C.act k))
    (fun k ↦ by simp only [show k + N - 1 = k - 1 + N by ring, C.sgn_add, C.act_add])
  simp only [add_sub_cancel_right] at hshift
  rw [← hshift, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← mul_add, elF1_add_elF2 (by linarith [C.act_pos k, C.act_pos (k + 1)])]

/-- **The Euler identity**: over one period, a weighted sum of the stationarity identities gives
`8 ∑ (ε_{k-1} + ε_k) e_k = C_raw/4 + 2 ∑ (ε_{k-1} + ε_k)/K_k`. -/
theorem euler_sum :
    8 * ∑ k ∈ Finset.range N, (C.sgn ((k : ℤ) - 1) + C.sgn k) * C.cre k =
      C.rawCost / 4 + 2 * ∑ k ∈ Finset.range N,
        (C.sgn ((k : ℤ) - 1) + C.sgn k) / (C.act k ^ 2 + 4) := by
  -- weighted sum of the stationarity identities
  have hst : ∀ k : ℤ, C.act k * (2 * (C.sgn (k - 1) * (C.act (k - 1) + C.act k) * C.swd (k - 1) +
      C.sgn k * (C.act k + C.act (k + 1)) * C.swd k -
      (C.sgn (k - 1) + C.sgn k) * C.act k * C.cre k)) =
      C.act k * ((C.sgn (k - 1) * elGa (C.act k) (C.act (k - 1)) +
        C.sgn k * elGa (C.act k) (C.act (k + 1))) / 8) := fun k ↦ by rw [C.stationarity k]
  have hsum := Finset.sum_congr rfl (fun (k : ℕ) (_ : k ∈ Finset.range N) ↦ hst k)
  -- the left side
  have hL : ∀ k : ℤ, C.act k * (2 * (C.sgn (k - 1) * (C.act (k - 1) + C.act k) * C.swd (k - 1) +
      C.sgn k * (C.act k + C.act (k + 1)) * C.swd k -
      (C.sgn (k - 1) + C.sgn k) * C.act k * C.cre k)) =
      (C.sgn (k - 1) * C.act k * (C.wt (k - 1) + C.wt k) / (C.act (k - 1) + C.act k) +
        C.sgn k * C.act k * (C.wt k + C.wt (k + 1)) / (C.act k + C.act (k + 1))) -
      (C.sgn (k - 1) + C.sgn k) * C.act k ^ 2 * C.wt k / (C.act k ^ 2 + 4) := by
    intro k
    have h1 := C.act_pos (k - 1); have h2 := C.act_pos k; have h3 := C.act_pos (k + 1)
    simp only [swd, cre, sub_add_cancel]
    field_simp
  have wt_add : ∀ k, C.wt (k + N) = C.wt k := fun k ↦ by
    simp only [wt, C.mu_add, C.lab_add, add_sub_cancel_right]
  rw [Finset.sum_congr rfl (fun (k : ℕ) (_ : k ∈ Finset.range N) ↦ hL k)] at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  -- shift the incoming terms
  have hA := el_sum_shift (N := N) (fun k ↦ C.sgn (k - 1) * C.act k * (C.wt (k - 1) + C.wt k) /
    (C.act (k - 1) + C.act k)) (fun k ↦ by
      simp only [show k + N - 1 = k - 1 + N by ring, C.sgn_add, C.act_add, wt_add])
  simp only [add_sub_cancel_right] at hA
  rw [← hA] at hsum
  have hAB : ∀ k : ℤ, C.sgn k * C.act (k + 1) * (C.wt k + C.wt (k + 1)) / (C.act k + C.act (k + 1)) +
      C.sgn k * C.act k * (C.wt k + C.wt (k + 1)) / (C.act k + C.act (k + 1)) =
      C.sgn k * C.wt k + C.sgn k * C.wt (k + 1) := fun k ↦ by
    have := C.act_pos k; have := C.act_pos (k + 1)
    field_simp; ring
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun (k : ℕ) _ ↦ hAB k),
    Finset.sum_add_distrib] at hsum
  have hW := el_sum_shift (N := N) (fun k ↦ C.sgn (k - 1) * C.wt k) (fun k ↦ by
      simp only [show k + N - 1 = k - 1 + N by ring, C.sgn_add, wt_add])
  simp only [add_sub_cancel_right] at hW
  rw [hW] at hsum
  -- the right side
  have hR : ∀ k : ℤ, C.act k * ((C.sgn (k - 1) * elGa (C.act k) (C.act (k - 1)) +
      C.sgn k * elGa (C.act k) (C.act (k + 1))) / 8) =
      C.sgn (k - 1) * C.act k * elGa (C.act k) (C.act (k - 1)) / 8 +
        C.sgn k * C.act k * elGa (C.act k) (C.act (k + 1)) / 8 := fun k ↦ by ring
  rw [Finset.sum_congr rfl (fun (k : ℕ) _ ↦ hR k), Finset.sum_add_distrib] at hsum
  have hG := el_sum_shift (N := N) (fun k ↦ C.sgn (k - 1) * C.act k * elGa (C.act k)
    (C.act (k - 1)) / 8) (fun k ↦ by
      simp only [show k + N - 1 = k - 1 + N by ring, C.sgn_add, C.act_add])
  simp only [add_sub_cancel_right] at hG
  rw [← hG] at hsum
  conv_rhs at hsum => rw [← Finset.sum_add_distrib]
  have hE : ∀ k : ℤ, C.sgn k * C.act (k + 1) * elGa (C.act (k + 1)) (C.act k) / 8 +
      C.sgn k * C.act k * elGa (C.act k) (C.act (k + 1)) / 8 =
      C.sgn k * elG (C.act k) (C.act (k + 1)) / 4 +
        2 * C.sgn k / (C.act k ^ 2 + 4) + 2 * C.sgn k / (C.act (k + 1) ^ 2 + 4) := fun k ↦ by
    have := elGa_euler (C.act_pos k) (C.act_pos (k + 1))
    have h1 : C.act k * elGa (C.act k) (C.act (k + 1)) + C.act (k + 1) *
        elGa (C.act (k + 1)) (C.act k) = 2 * elG (C.act k) (C.act (k + 1)) +
        16 / (C.act k ^ 2 + 4) + 16 / (C.act (k + 1) ^ 2 + 4) := this
    rw [show C.sgn k * C.act (k + 1) * elGa (C.act (k + 1)) (C.act k) / 8 +
        C.sgn k * C.act k * elGa (C.act k) (C.act (k + 1)) / 8 = C.sgn k / 8 *
        (C.act k * elGa (C.act k) (C.act (k + 1)) + C.act (k + 1) * elGa (C.act (k + 1)) (C.act k))
        by ring, h1]
    ring
  conv_rhs at hsum => rw [Finset.sum_congr rfl (fun (k : ℕ) _ ↦ hE k), Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hK := el_sum_shift (N := N) (fun k ↦ 2 * C.sgn (k - 1) / (C.act k ^ 2 + 4)) (fun k ↦ by
      simp only [show k + N - 1 = k - 1 + N by ring, C.sgn_add, C.act_add])
  simp only [add_sub_cancel_right] at hK
  rw [hK] at hsum
  rw [C.rawCost_eq]
  have hlhs : ∀ k : ℤ, (C.sgn (k - 1) + C.sgn k) * C.cre k * 8 =
      C.sgn (k - 1) * C.wt k + C.sgn k * C.wt k -
        (C.sgn (k - 1) + C.sgn k) * C.act k ^ 2 * C.wt k / (C.act k ^ 2 + 4) := fun k ↦ by
    have : 0 < C.act k ^ 2 + 4 := by positivity
    simp only [cre]; field_simp; ring
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  have e1 : ∑ k ∈ Finset.range N, 8 * ((C.sgn ((k : ℤ) - 1) + C.sgn k) * C.cre k) =
      ∑ k ∈ Finset.range N, (C.sgn ((k : ℤ) - 1) * C.wt k + C.sgn k * C.wt k -
        (C.sgn ((k : ℤ) - 1) + C.sgn k) * C.act k ^ 2 * C.wt k / (C.act k ^ 2 + 4)) :=
    Finset.sum_congr rfl fun k _ ↦ by rw [← hlhs]; ring
  have e1' : ∑ k ∈ Finset.range N, (C.sgn ((k : ℤ) - 1) * C.wt k + C.sgn k * C.wt k -
        (C.sgn ((k : ℤ) - 1) + C.sgn k) * C.act k ^ 2 * C.wt k / (C.act k ^ 2 + 4)) =
      ∑ k ∈ Finset.range N, C.sgn ((k : ℤ) - 1) * C.wt k + ∑ k ∈ Finset.range N, C.sgn k * C.wt k -
        ∑ k ∈ Finset.range N, (C.sgn ((k : ℤ) - 1) + C.sgn k) * C.act k ^ 2 * C.wt k /
          (C.act k ^ 2 + 4) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have e2 : ∑ k ∈ Finset.range N, 2 * ((C.sgn ((k : ℤ) - 1) + C.sgn k) / (C.act k ^ 2 + 4)) =
      ∑ k ∈ Finset.range N, 2 * C.sgn ((k : ℤ) - 1) / (C.act k ^ 2 + 4) +
        ∑ k ∈ Finset.range N, 2 * C.sgn k / (C.act k ^ 2 + 4) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ ↦ by ring
  linarith [e1, e1', e2, hsum]

/-! ### The all-short recurrence -/

/-- **The three-factor recurrence**, in the frame of a centre `n`: with the word `- - + - -` around
the pieces `n, …, n + 3` (centres `n`, `n + 3`, turns `n + 1`, `n + 2`),
`K_{n+3} A_n A_{n+1} A_{n+2} y = -K_n y⁻ + D y⁺`, where `y⁻, y⁺` are the incoming and outgoing
vectors of piece `n`, `y` the outgoing vector of piece `n + 3`, and
`D = s_n² + s_{n+2}² - s_{n+1}²`. -/
theorem next_centre_local (n : ℤ) (h0 : C.lab n = C.lab (n - 1) - 1)
    (h1 : C.lab (n + 1) = C.lab n - 1) (h2 : C.lab (n + 2) = C.lab (n + 1) + 1)
    (h3 : C.lab (n + 3) = C.lab (n + 2) - 1) (h4 : C.lab (n + 4) = C.lab (n + 3) - 1) :
    (C.act (n + 3) ^ 2 + 4) • ((C.Amat n * C.Amat (n + 1) * C.Amat (n + 2)) *ᵥ C.outv (n + 3)) =
      -(C.act n ^ 2 + 4) • C.inc n + (C.sw n ^ 2 + C.sw (n + 2) ^ 2 - C.sw (n + 1) ^ 2) • C.outv n := by
  have e1 : n + 1 - 1 = n := by ring
  have e2 : n + 2 - 1 = n + 1 := by ring
  have e3 : n + 3 - 1 = n + 2 := by ring
  have e3' : n + 3 + 1 = n + 4 := by ring
  have e2' : n + 2 + 1 = n + 3 := by ring
  have e1' : n + 1 + 1 = n + 2 := by ring
  have hf0 := C.centre_factor h0 h1
  have hf1 := C.factor_mp (k := n + 1) (by rw [e1]; exact h1) (by rw [e1']; exact h2)
  have hf2 := C.factor_pm (k := n + 2) (by rw [e2]; exact h2) (by rw [e2']; exact h3)
  have hf3 := C.centre_factor (k := n + 3) (by rw [e3]; exact h3) (by rw [e3']; exact h4)
  rw [e1] at hf1
  rw [e2] at hf2
  rw [e3, e3'] at hf3
  have hs0 := C.sw_pos (n - 1)
  have hs1 := C.sw_pos n
  have hs2 := C.sw_pos (n + 1)
  have hs3 := C.sw_pos (n + 2)
  have hs4 := C.sw_pos (n + 3)
  have hq0 := C.q_pos n
  have hq1 := C.q_pos (n + 1)
  have hq2 := C.q_pos (n + 2)
  have hq3 := C.q_pos (n + 3)
  have hK : 0 < C.act n ^ 2 + 4 := by positivity
  have hK' : 0 < C.act (n + 3) ^ 2 + 4 := by positivity
  -- the factors
  have Q0 : C.q n = (C.act n ^ 2 + 4) / (C.sw (n - 1) * C.sw n) := by
    rw [eq_div_iff (by positivity), ← hf0]; simp only [sw, sub_add_cancel]; ring
  have Q1 : C.q (n + 1) = C.sw (n + 1) / C.sw n := by rw [← hf1]; field_simp
  have Q2 : C.q (n + 2) = C.sw (n + 1) / C.sw (n + 2) := by rw [← hf2]; field_simp
  have Q3 : C.q (n + 3) * C.sw (n + 3) = (C.act (n + 3) ^ 2 + 4) / C.sw (n + 2) := by
    rw [eq_div_iff hs3.ne', ← hf3]
    simp only [sw, show n + 2 + 1 = n + 3 by ring, show n + 3 + 1 = n + 4 by ring]
    ring
  have hn1 : ¬ (C.lab n - 1 = C.lab n + 1) := by generalize C.lab n = i; revert i; decide
  have hn3 : ¬ (C.lab (n + 2) - 1 = C.lab (n + 2) + 1) := by
    generalize C.lab (n + 2) = i; revert i; decide
  have A0 : C.Amat n = Term.triFactor 0 (C.q n) * Term.triR := by
    simp only [Amat, h1, hn1, ↓reduceIte]
  have A1 : C.Amat (n + 1) = Term.triFactor 0 (C.q (n + 1)) * Term.triRinv := by
    simp only [Amat, e1', h2, ↓reduceIte]
  have A2 : C.Amat (n + 2) = Term.triFactor 0 (C.q (n + 2)) * Term.triR := by
    simp only [Amat, e2', h3, hn3, ↓reduceIte]
  have O3 : C.outv (n + 3) = ![0, (C.sw (n + 2)) / (C.act (n + 3) ^ 2 + 4)] := by
    rw [C.outv_rev (by rw [e3']; exact h4)]
    congr 1; rw [Q3]; field_simp
  rw [A0, A1, A2, O3, C.inc_rev h0, C.outv_rev h1, Q0, Q1, Q2]
  ext i; fin_cases i <;>
    simp [Term.triFactor, Term.triR, Term.triRinv, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.mul_apply] <;> field_simp <;> ring

end CostateCycle




/-! ### The polar angle of a frame -/

section Winding

open Reduction MeasureTheory Real

theorem el_zc_mul_R (M : Mat2) :
    clr_zc (M * R) = clr_zc M * Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_three,
    Real.sin_pi_div_three]
  apply Complex.ext <;>
    simp [clr_zc, R, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **The polar-angle bound** (the argument of `clr_winding`, for a frame not starting at `I`):
for a frame path `B' = B X` with star states, `det B = 1` and `B(T) = B(0) R`,
`∫₀ᵀ (ρ(X) + ρ(B X B⁻¹)) ≥ 2π/3`. -/
theorem el_winding {T : ℝ} (hT : 0 < T) {B X : ℝ → Mat2}
    (hBc : ContinuousOn B (Icc 0 T)) (hXc : ContinuousOn X (Icc 0 T))
    (hBd : ∀ s ∈ Ioo 0 T, Matrix.HasDerivAtEntrywise B (B s * X s) s)
    (hdet : ∀ s ∈ Icc 0 T, (B s).det = 1) (hstar : ∀ s ∈ Icc 0 T, IsStarState (X s))
    (hBT : B T = B 0 * R) :
    2 * π / 3 ≤ ∫ s in (0 : ℝ)..T, (clr_rho (X s) + clr_rhoR (B s) (X s)) := by
  set z : ℝ → ℂ := fun r ↦ clr_zc (B r) with hz
  set zp : ℝ → ℂ := fun r ↦ clr_zc (B r * X r) with hzp
  have hzc : ContinuousOn z (Icc 0 T) := clr_continuous_zc.comp_continuousOn hBc
  have hzpc : ContinuousOn zp (Icc 0 T) := clr_continuous_zc.comp_continuousOn (hBc.mul hXc)
  have hnormSq : ∀ s ∈ Icc 0 T, 1 ≤ Complex.normSq (z s) := fun s hs ↦
    clr_zc_normSq_ge (hdet s hs)
  have hz0 : ∀ s ∈ Icc 0 T, z s ≠ 0 := fun s hs h0 ↦ by
    have := hnormSq s hs
    rw [h0, map_zero] at this
    linarith
  have hzd : ∀ s ∈ Ioo 0 T, HasDerivAt z (zp s) s := by
    intro s hs
    have hd := hBd s hs
    simp only [hz, hzp, clr_zc]
    exact (((hd 0 0).add (hd 1 1)).div_const 2).ofReal_comp.add
      ((((hd 1 0).sub (hd 0 1)).div_const 2).ofReal_comp.mul_const Complex.I)
  set f : ℝ → ℂ := fun r ↦ zp r / z r with hf
  have hfc : ContinuousOn f (Icc 0 T) := hzpc.div hzc hz0
  have hfi : IntervalIntegrable f volume 0 T := (hfc.mono (by
    rw [uIcc_of_le hT.le])).intervalIntegrable
  set L : ℝ → ℂ := fun s ↦ ∫ r in (0 : ℝ)..s, f r with hL
  have hLc : ContinuousOn L (Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
      (f := f) (hfc.integrableOn_Icc.mono_set (by rw [uIcc_of_le hT.le]))
    rwa [uIcc_of_le hT.le] at this
  have hLd : ∀ s ∈ Ioo 0 T, HasDerivAt L (f s) s := by
    intro s hs
    exact intervalIntegral.integral_hasDerivAt_right
      (hfi.mono_set (by
        rw [uIcc_of_le hT.le, uIcc_of_le hs.1.le]
        exact Icc_subset_Icc_right hs.2.le))
      ((hfc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs)
      (hfc.continuousAt (Icc_mem_nhds hs.1 hs.2))
  set φ : ℝ → ℂ := fun s ↦ z s * Complex.exp (-L s) with hφ
  have hφc : ContinuousOn φ (Icc 0 T) :=
    hzc.mul (Complex.continuous_exp.comp_continuousOn hLc.neg)
  have hφd : ∀ s ∈ Ioo 0 T, HasDerivAt φ 0 s := by
    intro s hs
    have h1 := (hzd s hs).mul (hLd s hs).neg.cexp
    convert h1 using 1
    have hzs : z s ≠ 0 := hz0 s (Ioo_subset_Icc_self hs)
    simp only [hf]
    field_simp
    ring
  have hφT : φ T = φ 0 := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hφc hφd
      (intervalIntegrable_const (c := (0 : ℂ)))
    rw [intervalIntegral.integral_zero] at this
    exact (sub_eq_zero.mp this.symm)
  have hφ0 : φ 0 = z 0 := by simp [hφ, hL]
  have hzT : z T = z 0 * Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I) := by
    simp only [hz, hBT, el_zc_mul_R]
  have h00 : z 0 ≠ 0 := hz0 0 ⟨le_rfl, hT.le⟩
  have hexpL : Complex.exp (L T) = Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I) := by
    have e : z T * Complex.exp (-L T) = z 0 := by rw [← hφ0, ← hφT]
    rw [hzT, mul_assoc] at e
    have e2 : Complex.exp (((π / 3 : ℝ) : ℂ) * Complex.I) * Complex.exp (-L T) = 1 := by
      have := congrArg (· / z 0) e
      simpa [h00] using this
    have := congrArg (· * Complex.exp (L T)) e2
    simp only [← Complex.exp_add, one_mul] at this
    rw [add_assoc, neg_add_cancel, add_zero] at this
    exact this.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexpL
  have hLim : (L T).im = π / 3 + 2 * π * n := by
    rw [hn]
    simp
    ring
  have hIm : (L T).im = ∫ r in (0 : ℝ)..T, (f r).im := by
    simp only [hL]
    exact (Complex.imCLM.intervalIntegral_comp_comm hfi).symm
  have hfim : ∀ r ∈ Icc 0 T, (f r).im =
      (clr_rho (X r) + clr_rhoR (B r) (X r)) / 2 / Complex.normSq (z r) := by
    intro r hr
    have ha := clr_angular (B r) (hstar r hr).1
    rw [hdet r hr, mul_one] at ha
    simp only [hf, hz, hzp, Complex.div_im]
    rw [← ha]
    ring
  have hρpos : ∀ r ∈ Icc 0 T, 0 < clr_rho (X r) + clr_rhoR (B r) (X r) := fun r hr ↦
    add_pos (clr_rho_pos (hstar r hr)) (clr_rhoR_pos (hdet r hr) (hstar r hr))
  have hfim_pos : ∀ r ∈ Icc 0 T, 0 < (f r).im := by
    intro r hr
    rw [hfim r hr]
    have := hnormSq r hr
    have := hρpos r hr
    positivity
  have hfim_le : ∀ r ∈ Icc 0 T,
      (f r).im ≤ (clr_rho (X r) + clr_rhoR (B r) (X r)) / 2 := by
    intro r hr
    rw [hfim r hr]
    exact div_le_self (by linarith [hρpos r hr]) (hnormSq r hr)
  have hfimi : IntervalIntegrable (fun r ↦ (f r).im) volume 0 T :=
    (Complex.continuous_im.comp_continuousOn hfc |>.mono (by
      rw [uIcc_of_le hT.le])).intervalIntegrable
  have hint_pos : 0 < ∫ r in (0 : ℝ)..T, (f r).im :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hfimi
      (fun r hr ↦ hfim_pos r (Ioo_subset_Icc_self hr)) hT
  have hn0 : (0 : ℝ) ≤ n := by
    have : 0 < π / 3 + 2 * π * n := by rw [← hLim, hIm]; exact hint_pos
    have hn' : (-1 : ℝ) < n := by
      by_contra hc
      push Not at hc
      nlinarith [Real.pi_pos]
    exact_mod_cast (show (-1 : ℤ) < n by exact_mod_cast hn')
  have hρc : ContinuousOn (fun s ↦ clr_rho (X s) + clr_rhoR (B s) (X s)) (Icc 0 T) := by
    have hp : ContinuousOn (fun s ↦ (B s, X s)) (Icc 0 T) := hBc.prodMk hXc
    exact (clr_continuous_rho.comp_continuousOn hXc).add
      (clr_continuous_rhoR.comp_continuousOn (f := fun s ↦ (B s, X s)) hp)
  have hρi : IntervalIntegrable (fun s ↦ (clr_rho (X s) + clr_rhoR (B s) (X s)) / 2) volume 0 T :=
    ((hρc.div_const 2).mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hmono : ∫ r in (0 : ℝ)..T, (f r).im ≤
      ∫ r in (0 : ℝ)..T, (clr_rho (X r) + clr_rhoR (B r) (X r)) / 2 :=
    intervalIntegral.integral_mono_on hT.le hfimi hρi hfim_le
  rw [intervalIntegral.integral_div] at hmono
  rw [← hIm, hLim] at hmono
  nlinarith [Real.pi_pos]

end Winding


/-! ### Elliptic classes -/

/-- The sign of the lower-left entry of an elliptic traceless matrix is that of any conjugate by an
invertible matrix written with the adjugate (`A M adj A = det A · A M A⁻¹`). -/
theorem el_ell_sign {M : Mat2} (htr : M.trace = 0) (hdet : 0 < M.det) (A : Mat2)
    (hA : A.det ≠ 0) : 0 < (A * M * A.adjugate) 1 0 * M 1 0 := by
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdet hA
  have e11 : M 1 1 = -M 0 0 := by linarith
  have e : (A * M * A.adjugate) 1 0 * M 1 0 =
      (M 1 0 * A 1 1 + M 0 0 * A 1 0) ^ 2 + (M 0 0 * M 1 1 - M 0 1 * M 1 0) * A 1 0 ^ 2 := by
    rw [Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two, e11]
    ring
  rw [e]
  have hM10 : M 1 0 ≠ 0 := by
    intro h0; rw [h0, e11] at hdet; nlinarith [sq_nonneg (M 0 0)]
  rcases eq_or_ne (A 1 0) 0 with h | h
  · have hA11 : A 1 1 ≠ 0 := by intro h'; apply hA; rw [h, h']; ring
    rw [h]
    nlinarith [mul_self_pos.2 (mul_ne_zero hM10 hA11)]
  · have : 0 < (M 0 0 * M 1 1 - M 0 1 * M 1 0) * A 1 0 ^ 2 := by positivity
    nlinarith [sq_nonneg (M 1 0 * A 1 1 + M 0 0 * A 1 0)]

/-- A negative elliptic matrix `L` (`tr L = 0`, `det L > 0`, `L₁₀ < 0`) is `-κ h J h⁻¹` with
`κ = √(det L)` and `det h = 1`. -/
theorem el_negEll_repr {L : Mat2} (htr : L.trace = 0) (hdet : 0 < L.det) (h10 : L 1 0 < 0) :
    ∃ h : Mat2, h.det = 1 ∧ L = -√L.det • (h * J * h.adjugate) := by
  rw [Matrix.trace_fin_two] at htr
  have e11 : L 1 1 = -L 0 0 := by linarith
  set κ := √L.det with hκ
  have hκpos : 0 < κ := Real.sqrt_pos.2 hdet
  have hκ2 : κ ^ 2 = L.det := Real.sq_sqrt hdet.le
  rw [Matrix.det_fin_two, e11] at hκ2
  set p := √(κ / -L 1 0) with hp
  have hpp : 0 < p := Real.sqrt_pos.2 (div_pos hκpos (by linarith))
  have hp2 : p ^ 2 = κ / -L 1 0 := Real.sq_sqrt (div_pos hκpos (by linarith)).le
  have hL10 : L 1 0 ≠ 0 := h10.ne
  have hκp : κ = -L 1 0 * p ^ 2 := by rw [hp2]; field_simp
  refine ⟨!![p, L 0 0 / (L 1 0 * p); 0, 1 / p], ?_, ?_⟩
  · rw [Matrix.det_fin_two]; simp; field_simp
  · rw [hκp] at hκ2 ⊢
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two, J, e11]
    · field_simp
    · field_simp
      linear_combination hκ2
    · field_simp
    · field_simp

/-- The margins of a traceless matrix give its triangular form: `Y(p(M)) = C M C⁻¹`. -/
theorem el_triY_margin {M : Mat2} (htr : M.trace = 0) :
    triY (fun j ↦ margin j M) = Term.triC * M * Term.triCinv := by
  rw [Matrix.trace_fin_two] at htr
  have e11 : M 1 1 = -M 0 0 := by linarith
  have h3 := el_s3pos
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [triY, Term.triC, Term.triCinv, Matrix.mul_apply, Fin.sum_univ_two, margin_zero_apply,
      margin_one_apply, margin_two_apply, e11, Matrix.vecMul, dotProduct] <;> field_simp <;>
      el_ring

theorem el_triY_rot (p : Fin 3 → ℝ) (i : Fin 3) :
    ∃ A : Mat2, A.det = 1 ∧ triY (fun j ↦ p (j + i)) = A * triY p * A.adjugate := by
  fin_cases i
  · exact ⟨1, by simp, by simp⟩
  · refine ⟨Term.triR, by simp [Term.triR, Matrix.det_fin_two], ?_⟩
    have e : Term.triR.adjugate = Term.triRinv := by
      rw [Matrix.adjugate_fin_two]; simp [Term.triR, Term.triRinv]
    rw [e, ← triY_rot_succ]; rfl
  · refine ⟨Term.triRinv, by simp [Term.triRinv, Matrix.det_fin_two], ?_⟩
    have e : Term.triRinv.adjugate = Term.triR := by
      rw [Matrix.adjugate_fin_two]; ext a b; fin_cases a <;> fin_cases b <;>
        simp [Term.triR, Term.triRinv]
    rw [e, ← triY_rot_pred]
    congr 1; funext j; congr 1
    generalize j = x; revert x; decide

/-! ### Switch signs -/

namespace VertexRepresentation

variable {T : ℝ} {u : ℝ → Fin 3 → ℝ} (ρ : VertexRepresentation T u)

theorem el_fwd_or_rev (k : ℤ) : ρ.IsForward k ∨ ρ.IsReverse k :=
  cst_fin_ne_cases (ρ.label_ne k)

theorem el_not_fwd_rev (k : ℤ) : ¬ (ρ.IsForward k ∧ ρ.IsReverse k) := by
  rintro ⟨h1, h2⟩
  unfold IsForward at h1
  unfold IsReverse at h2
  rw [h1] at h2
  revert h2
  generalize ρ.label k = i
  revert i; decide

theorem el_fwd_add_N (k : ℤ) : ρ.IsForward (k + ρ.N) ↔ ρ.IsForward k := by
  unfold IsForward
  rw [show k + ρ.N + 1 = k + 1 + ρ.N by ring, ρ.label_add_period, ρ.label_add_period]
  constructor
  · intro h; have := congrArg (· - 1) h; simpa using this
  · intro h; rw [h]

theorem el_rev_add_N (k : ℤ) : ρ.IsReverse (k + ρ.N) ↔ ρ.IsReverse k := by
  unfold IsReverse
  rw [show k + ρ.N + 1 = k + 1 + ρ.N by ring, ρ.label_add_period, ρ.label_add_period]
  constructor
  · intro h; have := congrArg (· - 1) h; simp only [add_sub_cancel_right] at this
    rw [this]
  · intro h; rw [h]; abel

theorem el_fwd_add_mul_N (k : ℤ) (t : ℕ) : ρ.IsForward (k + t * ρ.N) ↔ ρ.IsForward k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show k + ((t + 1 : ℕ) : ℤ) * ρ.N = k + t * ρ.N + ρ.N by push_cast; ring, ρ.el_fwd_add_N, ih]

theorem el_rev_add_mul_N (k : ℤ) (t : ℕ) : ρ.IsReverse (k + t * ρ.N) ↔ ρ.IsReverse k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show k + ((t + 1 : ℕ) : ℤ) * ρ.N = k + t * ρ.N + ρ.N by push_cast; ring, ρ.el_rev_add_N, ih]

/-- The sign of switch `k` is that of `k mod N` shifted by any multiple of `N`. -/
theorem el_fwd_shift (k : ℤ) (t : ℤ) : ρ.IsForward (k + t * ρ.N) ↔ ρ.IsForward k := by
  rcases Int.eq_nat_or_neg t with ⟨n, rfl | rfl⟩
  · exact ρ.el_fwd_add_mul_N k n
  · have := ρ.el_fwd_add_mul_N (k + -(n : ℤ) * ρ.N) n
    rw [show k + -(n : ℤ) * ρ.N + n * ρ.N = k by ring] at this
    exact this.symm

theorem el_rev_shift (k : ℤ) (t : ℤ) : ρ.IsReverse (k + t * ρ.N) ↔ ρ.IsReverse k := by
  rcases Int.eq_nat_or_neg t with ⟨n, rfl | rfl⟩
  · exact ρ.el_rev_add_mul_N k n
  · have := ρ.el_rev_add_mul_N (k + -(n : ℤ) * ρ.N) n
    rw [show k + -(n : ℤ) * ρ.N + n * ρ.N = k by ring] at this
    exact this.symm

end VertexRepresentation

/-! ### Ellipticity and the cost–Casimir cap of a normal period -/

namespace NormalPeriod

variable (P : NormalPeriod)


/-- **Every reverse switch of a mixed period lies in a run of exactly two**: it is the first
(`+ - - +` from `k - 1`) or the second (`+ - - +` from `k - 2`) switch of its run. -/
theorem rev_run (hmix : P.rep.IsMixed) {k : ℤ} (hk : P.rep.IsReverse k) :
    (P.rep.IsForward (k - 1) ∧ P.rep.IsReverse (k + 1) ∧ P.rep.IsForward (k + 2)) ∨
      (P.rep.IsForward (k - 2) ∧ P.rep.IsReverse (k - 1) ∧ P.rep.IsForward (k + 1)) := by
  classical
  obtain ⟨⟨f, hf⟩, -⟩ := hmix
  have hN : (0 : ℤ) < P.N := by exact_mod_cast P.rep.N_pos
  -- a forward switch before and after
  have hb : ∃ j : ℕ, P.rep.IsForward (k - 1 - j) := by
    obtain ⟨t, ht⟩ : ∃ t : ℕ, f - t * P.N ≤ k - 1 := by
      refine ⟨(f - (k - 1)).toNat, ?_⟩
      have h1 : f - (k - 1) ≤ ((f - (k - 1)).toNat : ℤ) := Int.self_le_toNat _
      have h2 : ((f - (k - 1)).toNat : ℤ) ≤ (f - (k - 1)).toNat * P.N := by
        have : (0 : ℤ) ≤ (f - (k - 1)).toNat := by positivity
        nlinarith
      linarith
    refine ⟨(k - 1 - (f - t * P.N)).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by linarith), show k - 1 - (k - 1 - (f - t * P.N)) =
      f + (-(t : ℤ)) * P.N by ring, P.rep.el_fwd_shift]
    exact hf
  have ha : ∃ l : ℕ, P.rep.IsForward (k + 1 + l) := by
    obtain ⟨t, ht⟩ : ∃ t : ℕ, k + 1 ≤ f + t * P.N := by
      refine ⟨(k + 1 - f).toNat, ?_⟩
      have h1 : k + 1 - f ≤ ((k + 1 - f).toNat : ℤ) := Int.self_le_toNat _
      have h2 : ((k + 1 - f).toNat : ℤ) ≤ (k + 1 - f).toNat * P.N := by
        have : (0 : ℤ) ≤ (k + 1 - f).toNat := by positivity
        nlinarith
      linarith
    refine ⟨(f + t * P.N - (k + 1)).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by linarith), show k + 1 + (f + t * P.N - (k + 1)) =
      f + (t : ℤ) * P.N by ring, P.rep.el_fwd_shift]
    exact hf
  let j := Nat.find hb
  let l := Nat.find ha
  have hj : P.rep.IsForward (k - 1 - j) := Nat.find_spec hb
  have hl : P.rep.IsForward (k + 1 + l) := Nat.find_spec ha
  have hjm : ∀ j' : ℕ, j' < j → P.rep.IsReverse (k - 1 - j') := fun j' h ↦
    (P.rep.el_fwd_or_rev _).resolve_left (Nat.find_min hb h)
  have hlm : ∀ l' : ℕ, l' < l → P.rep.IsReverse (k + 1 + l') := fun l' h ↦
    (P.rep.el_fwd_or_rev _).resolve_left (Nat.find_min ha h)
  have hrun : P.rep.IsReverseRun (k - j) (j + 1 + l) := by
    refine ⟨by omega, by rw [show k - j - 1 = k - 1 - j by ring]; exact hj,
      by rw [show k - (j : ℤ) + ((j + 1 + l : ℕ) : ℤ) = k + 1 + l by push_cast; ring]; exact hl,
      fun i hi1 hi2 ↦ ?_⟩
    push_cast at hi2
    rcases lt_trichotomy i k with h | h | h
    · have := hjm (k - 1 - i).toNat (by omega)
      rwa [Int.toNat_of_nonneg (by omega), show k - 1 - (k - 1 - i) = i by ring] at this
    · rw [h]; exact hk
    · have := hlm (i - (k + 1)).toNat (by omega)
      rwa [Int.toNat_of_nonneg (by omega), show k + 1 + (i - (k + 1)) = i by ring] at this
  have hL := (reverseRun_two_and_centre_min P ⟨⟨f, hf⟩, ⟨k, hk⟩⟩ hrun).1
  rcases (show j = 0 ∧ l = 1 ∨ j = 1 ∧ l = 0 by omega) with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · left
    refine ⟨by simpa [h0] using hj, by simpa using hlm 0 (by omega), ?_⟩
    have := hl; rw [h1] at this
    rw [show k + 2 = k + 1 + ((1 : ℕ) : ℤ) by push_cast; ring]; exact this
  · right
    refine ⟨?_, by simpa using hjm 0 (by omega), by simpa [h1] using hl⟩
    have := hj; rw [h0] at this
    rw [show k - 2 = k - 1 - ((1 : ℕ) : ℤ) by push_cast; ring]; exact this

/-- In a mixed period every switch norm is at least `3/32`. -/
theorem swd_ge_of_mixed (hmix : P.rep.IsMixed) (k : ℤ) : 3 / 32 ≤ P.costateCycle.swd k := by
  set C := P.costateCycle
  rcases P.rep.el_fwd_or_rev k with hf | hr
  · have := C.swd_fwd (k := k) hf
    have := CostateCycle.elJ_ge _ _ (C.act_pos k) (C.act_pos (k + 1))
    linarith
  · rcases P.rev_run hmix hr with ⟨h1, -, -⟩ | ⟨-, h2, h3⟩
    · refine C.turn_swd_ge ?_
      rw [C.sgn_fwd (k := k - 1) h1, C.sgn_rev (k := k) hr]; norm_num
    · have ht : C.sgn (k + 1 - 1) = -C.sgn (k + 1) := by
        rw [add_sub_cancel_right, C.sgn_rev (k := k) hr, C.sgn_fwd (k := k + 1) h3]
      have := C.turn_swd_ge ht
      have e := (C.turn_secant ht).1
      rw [add_sub_cancel_right] at e
      rw [e]; exact this

/-- A centre (both incident switches reverse) of a mixed period is a strict local minimum. -/
theorem centre_min (hmix : P.rep.IsMixed) {k : ℤ} (h1 : P.rep.IsReverse (k - 1))
    (h2 : P.rep.IsReverse k) :
    P.costateCycle.act k < P.costateCycle.act (k - 1) ∧
      P.costateCycle.act k < P.costateCycle.act (k + 1) := by
  rcases P.rev_run hmix h1 with ⟨hf1, -, hf2⟩ | ⟨-, hr, -⟩
  · have hrun : P.rep.IsReverseRun (k - 1) 2 := by
      refine ⟨by norm_num, hf1, by rw [show k - 1 + ((2 : ℕ) : ℤ) = k - 1 + 2 by norm_num]; exact hf2,
        fun i hi1 hi2 ↦ ?_⟩
      push_cast at hi2
      rcases (show i = k - 1 ∨ i = k by omega) with h | h <;> rw [h]
      · exact h1
      · exact h2
    have hm := reverseRun_two_and_centre_min P hmix hrun
    rw [sub_add_cancel, show k - 1 + 2 = k + 1 by ring] at hm
    have hact : ∀ j, P.activeMargin j = P.costateCycle.act j :=
      fun j ↦ (P.costateCycle_m_lab j).symm
    obtain ⟨-, -, a1, a2, -⟩ := hm
    rw [hact, hact] at a1 a2
    exact ⟨a1, a2⟩
  · -- `k - 2, k - 1` would be a run of two followed by the reverse switch `k`
    exfalso
    rcases P.rev_run hmix h2 with ⟨hf, -, -⟩ | ⟨-, -, -⟩
    · exact P.rep.el_not_fwd_rev _ ⟨hf, h1⟩
    · rcases P.rev_run hmix h1 with ⟨-, -, hf⟩ | ⟨-, -, hf⟩
      · rw [show k - 1 + 2 = k + 1 by ring] at hf
        rcases P.rev_run hmix hr with ⟨-, -, hf'⟩ | ⟨-, -, hf'⟩
        · rw [show k - 1 - 1 + 2 = k by ring] at hf'; exact P.rep.el_not_fwd_rev _ ⟨hf', h2⟩
        · rw [show k - 1 - 1 + 1 = k - 1 by ring] at hf'; exact P.rep.el_not_fwd_rev _ ⟨hf', h1⟩
      · rw [sub_add_cancel] at hf; exact P.rep.el_not_fwd_rev _ ⟨hf, h2⟩

/-- **Negative ellipticity, mixed periods**: the normal multiplier of a mixed normal vertex period
has `γ² = det U = det Λ₁ / 12 > 0`. -/
theorem gam2_pos_of_mixed (hmix : P.rep.IsMixed) : 0 < P.costateCycle.gam2 0 := by
  set C := P.costateCycle with hC
  by_contra hcon
  push Not at hcon
  have hgam : ∀ k, C.gam2 k ≤ 0 := fun k ↦ by rw [C.gam2_eq]; exact hcon
  obtain ⟨-, s01, s10, -⟩ := C.Sloc_apply 0
  have hsym : C.Sloc 0 0 1 = C.Sloc 0 1 0 := by rw [s01, s10]
  set S := C.Sloc 0 with hS
  have hdet : S.det ≤ 0 := by
    have : S.det = C.gam2 0 := by
      rw [hS, CostateCycle.Sloc, Matrix.det_neg, Matrix.det_mul, C.det_Mloc]
      simp [elJ0, Matrix.det_fin_two]
    rw [this]; exact hcon
  have hd : ∀ n : ℕ, 0 < elQ S (C.yv n) (C.yv n) := fun n ↦ by
    rw [C.yv_norm]; linarith [P.swd_ge_of_mixed hmix n]
  -- the projective coordinate
  set y0 := C.yv 0
  set η0 := y0 0 * S 0 0 + y0 1 * S 1 0
  set η1 := y0 0 * S 0 1 + y0 1 * S 1 1
  let h : (Fin 2 → ℝ) → ℝ := fun v ↦ η0 * v 0 + η1 * v 1
  let l : (Fin 2 → ℝ) → ℝ := fun v ↦ η0 * v 1 - η1 * v 0
  have hh : ∀ v, h v = elQ S y0 v := fun v ↦ by simp only [h, elQ, η0, η1]; ring
  have hhl : ∀ a b, h a * l b - h b * l a = (η0 ^ 2 + η1 ^ 2) * elDet a b := fun a b ↦ by
    simp only [h, l, elDet]; ring
  have hη : 0 < η0 ^ 2 + η1 ^ 2 := by
    have h0 := hd 0
    rw [← hh] at h0
    by_contra hc
    push Not at hc
    have e0 : η0 = 0 := by nlinarith [sq_nonneg η0, sq_nonneg η1]
    have e1 : η1 = 0 := by nlinarith [sq_nonneg η0, sq_nonneg η1]
    simp only [h, e0, e1, zero_mul, add_zero] at h0
    exact lt_irrefl _ h0
  have hne : ∀ n : ℕ, h (C.yv n) ≠ 0 := fun n ↦ by
    have := el_three_gram hsym hdet (hd 0) (hd n) (hd n)
    rw [← hh] at this
    intro h0; rw [h0] at this; simp at this
  have hprod : ∀ n m : ℕ, 0 < h (C.yv n) * h (C.yv m) * elQ S (C.yv n) (C.yv m) := fun n m ↦ by
    have := el_three_gram hsym hdet (hd 0) (hd n) (hd m)
    rwa [← hh, ← hh] at this
  set z : (Fin 2 → ℝ) → ℝ := fun v ↦ l v / h v
  have hinc : ∀ n : ℕ, z (C.yv (n + 1)) - z (C.yv n) =
      (η0 ^ 2 + η1 ^ 2) * elDet (C.yv n) (C.yv (n + 1)) / (h (C.yv n) * h (C.yv (n + 1))) := by
    intro n
    have h1 := hne n
    have h2 := hne (n + 1)
    simp only [z]
    rw [← hhl]
    field_simp
  -- the increments are nonnegative, positive at a centre
  have hcase : ∀ n : ℕ, 0 ≤ z (C.yv (n + 1)) - z (C.yv n) ∧
      (P.rep.IsReverse n → P.rep.IsReverse (n + 1) → 0 < z (C.yv (n + 1)) - z (C.yv n)) := by
    intro n
    obtain ⟨hq, hdt⟩ := C.yv_pair n
    have ek : ((n + 1 : ℕ) : ℤ) - 1 = n := by push_cast; ring
    have hpr := hprod n (n + 1)
    rw [hinc]
    rcases P.rep.el_fwd_or_rev n with hin | hin <;>
      rcases P.rep.el_fwd_or_rev ((n + 1 : ℕ) : ℤ) with hout | hout
    · -- `+ +`
      have hin' : C.lab ((n + 1 : ℕ) : ℤ) = C.lab (((n + 1 : ℕ) : ℤ) - 1) + 1 := by
        rw [ek]; push_cast; exact hin
      obtain ⟨hc, hdl⟩ := C.cross_pp hin' hout
      have hpos := C.cre_pos_pp hin' hout (hgam _)
      rw [hq, hc] at hpr
      rw [hdt, hdl]
      have : 0 < h (C.yv n) * h (C.yv (n + 1)) := by
        by_contra hc'; push Not at hc'; nlinarith
      have hK : 0 < C.act ((n + 1 : ℕ) : ℤ) ^ 2 + 4 := by positivity
      refine ⟨by positivity, fun hr _ ↦ absurd ⟨hin, hr⟩ (P.rep.el_not_fwd_rev n)⟩
    · -- `+ -`: a turn
      have ht : C.sgn (((n + 1 : ℕ) : ℤ) - 1) = -C.sgn ((n + 1 : ℕ) : ℤ) := by
        rw [ek, C.sgn_fwd (k := n) hin, C.sgn_rev hout]; norm_num
      rw [hdt, C.outv_turn ht]
      simp only [elDet, Pi.neg_apply]
      refine ⟨by ring_nf; rfl, fun hr _ ↦ absurd ⟨hin, hr⟩ (P.rep.el_not_fwd_rev n)⟩
    · -- `- +`: a turn
      have ht : C.sgn (((n + 1 : ℕ) : ℤ) - 1) = -C.sgn ((n + 1 : ℕ) : ℤ) := by
        rw [ek, C.sgn_rev (k := n) hin, C.sgn_fwd hout]
      rw [hdt, C.outv_turn ht]
      simp only [elDet, Pi.neg_apply]
      refine ⟨by ring_nf; rfl, fun _ hr ↦ absurd ⟨hout, hr⟩ (P.rep.el_not_fwd_rev _)⟩
    · -- `- -`: a centre
      have hin' : C.lab ((n + 1 : ℕ) : ℤ) = C.lab (((n + 1 : ℕ) : ℤ) - 1) - 1 := by
        rw [ek]; push_cast; exact hin
      have hr1 : P.rep.IsReverse (((n + 1 : ℕ) : ℤ) - 1) := by rw [ek]; exact hin
      obtain ⟨hm1, hm2⟩ := P.centre_min hmix hr1 hout
      obtain ⟨hc, hdl⟩ := C.cross_mm hin' hout
      have hneg := C.cre_neg_mm hin' hout hm1 hm2 (P.swd_ge_of_mixed hmix _)
        (P.swd_ge_of_mixed hmix _) (hgam _)
      rw [hq, hc] at hpr
      rw [hdt, hdl]
      have : h (C.yv n) * h (C.yv (n + 1)) < 0 := by
        by_contra hc'; push Not at hc'; nlinarith
      have hK : 0 < C.act ((n + 1 : ℕ) : ℤ) ^ 2 + 4 := by positivity
      have hpos : 0 < (η0 ^ 2 + η1 ^ 2) * -(1 / (C.act ((n + 1 : ℕ) : ℤ) ^ 2 + 4)) /
          (h (C.yv n) * h (C.yv (n + 1))) := by
        apply div_pos_of_neg_of_neg _ this
        have : 0 < 1 / (C.act ((n + 1 : ℕ) : ℤ) ^ 2 + 4) := by positivity
        nlinarith
      exact ⟨hpos.le, fun _ _ ↦ hpos⟩
  -- a centre in `[1, N]`
  obtain ⟨r, hr⟩ := hmix.2
  obtain ⟨c, hc1, hc2⟩ : ∃ c : ℤ, P.rep.IsReverse (c - 1) ∧ P.rep.IsReverse c := by
    rcases P.rev_run hmix hr with ⟨-, h2, -⟩ | ⟨-, h2, -⟩
    · exact ⟨r + 1, by rwa [add_sub_cancel_right], h2⟩
    · exact ⟨r, h2, hr⟩
  have hN : (0 : ℤ) < P.N := by exact_mod_cast P.rep.N_pos
  set n₀ := ((c - 1) % P.N).toNat with hn₀
  have hn0 : 0 ≤ (c - 1) % P.N := Int.emod_nonneg _ hN.ne'
  have hn1 : (c - 1) % P.N < P.N := Int.emod_lt_of_pos _ hN
  have hn₀N : n₀ < P.N := by omega
  have hcast : (n₀ : ℤ) = (c - 1) + (-((c - 1) / P.N)) * P.N := by
    rw [hn₀, Int.toNat_of_nonneg hn0, Int.emod_def]; ring
  have hr0 : P.rep.IsReverse n₀ := by rw [hcast, P.rep.el_rev_shift]; exact hc1
  have hr1 : P.rep.IsReverse ((n₀ + 1 : ℕ) : ℤ) := by
    rw [show ((n₀ + 1 : ℕ) : ℤ) = c + (-((c - 1) / P.N)) * P.N by push_cast; rw [hcast]; ring,
      P.rep.el_rev_shift]
    exact hc2
  -- the telescoping sum vanishes
  have hsum := Finset.sum_range_sub (fun n ↦ z (C.yv n)) P.N
  have hend : z (C.yv P.N) = z (C.yv 0) := by
    have e := C.yv_add_N 0
    rw [add_zero] at e
    rw [e]
    rcases C.pre_N with h1 | h1
    · rw [h1, Matrix.one_mulVec]
    · rw [h1, Matrix.neg_mulVec, Matrix.one_mulVec]
      simp only [z, h, l, Pi.neg_apply]
      rw [show η0 * -C.yv 0 1 - η1 * -C.yv 0 0 = -(η0 * C.yv 0 1 - η1 * C.yv 0 0) by ring,
        show η0 * -C.yv 0 0 + η1 * -C.yv 0 1 = -(η0 * C.yv 0 0 + η1 * C.yv 0 1) by ring,
        neg_div_neg_eq]
  rw [hend, sub_self] at hsum
  have hpos : 0 < ∑ n ∈ Finset.range P.N, (z (C.yv (n + 1)) - z (C.yv n)) :=
    Finset.sum_pos' (fun n _ ↦ (hcase n).1)
      ⟨n₀, Finset.mem_range.2 hn₀N, (hcase n₀).2 hr0 hr1⟩
  linarith

/-- The local normal multiplier `𝒰₀ = (1/√12) X(0)⁻¹ Λ₁(0) X(0) = -(1/√12) X(0) Λ₁(0) X(0)` at the
initial time, in physical coordinates. -/
noncomputable def Ucal : Mat2 := -(1 / √12) • (P.X 0 * P.Λ₁ 0 * P.X 0)

theorem el_margin_J (j : Fin 3) : margin j J = 2 / √3 := by
  have h := el_s3pos
  fin_cases j <;> simp [margin_zero_apply, margin_one_apply, margin_two_apply, J] <;>
    field_simp <;> el_ring

/-- The margins of `𝒰₀` are the coordinates `μ_j` of the costate cycle at the switch `0`. -/
theorem mu_zero (j : Fin 3) : P.costateCycle.mu 0 j = margin j P.Ucal := by
  have hX := P.isStarState (t := 0) ⟨le_rfl, P.T_pos.le⟩
  have hΛ := (P.extremal.2.2.2.2.2.2.2.1 0 ⟨le_rfl, P.T_pos.le⟩).1
  have hz : P.rep.τ ((0 : ℤ) % P.N) = 0 := by rw [Int.zero_emod, P.rep.τ_zero]
  have hcs : P.cutShift 0 = 0 := by simp [cutShift]
  have hm : ∀ l, P.costateCycle.m 0 l = margin l (P.X 0) := fun l ↦ by
    simp only [costateCycle_m, termMargin_eq_cut, hcs, sub_zero, hz]
  have hα : P.costateCycle.α 0 j = margin j (costateA (P.Λ₁ 0) (P.X 0)) := by
    show P.cutAlpha 0 j = _
    simp only [cutAlpha, hcs, sub_zero, hz, costateAlpha]
  have hXJX := cst_mul_mul_self hX.1 hX.2.1 cst_trace_J
  have hA : costateA (P.Λ₁ 0) (P.X 0) = P.X 0 * P.Λ₁ 0 * P.X 0 +
      (3 / 2 : ℝ) • (P.X 0 * J * P.X 0) := by
    simp only [costateA, costateL, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  have hsum := sum_margin (P.X 0)
  have h3 := el_s3pos
  have h12 : √12 = 2 * √3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  simp only [CostateCycle.mu, hα, hm, Ucal, cst_margin_smul]
  rw [hA, hXJX] at *
  simp only [cst_margin_add, cst_margin_smul, el_margin_J]
  have ht : traceForm J (P.X 0) =
      -(margin 0 (P.X 0) + margin 1 (P.X 0) + margin 2 (P.X 0)) / √3 := by
    rw [hsum]; field_simp
  rw [ht, h12]
  field_simp
  el_ring

theorem trace_Ucal : P.Ucal.trace = 0 := by
  have hX := P.isStarState (t := 0) ⟨le_rfl, P.T_pos.le⟩
  have hΛ := (P.extremal.2.2.2.2.2.2.2.1 0 ⟨le_rfl, P.T_pos.le⟩).1
  rw [Ucal, Matrix.trace_smul, cst_mul_mul_self hX.1 hX.2.1 hΛ, Matrix.trace_add,
    Matrix.trace_smul, hX.1, hΛ]
  simp

theorem det_Ucal : P.Ucal.det = (P.Λ₁ 0).det / 12 := by
  have hX := P.isStarState (t := 0) ⟨le_rfl, P.T_pos.le⟩
  rw [Ucal, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, hX.2.1]
  have : (-(1 / √12)) ^ Fintype.card (Fin 2) = 1 / 12 := by
    simp only [Fintype.card_fin, neg_sq, div_pow, one_pow]
    rw [Real.sq_sqrt (by norm_num)]
  rw [this]; ring

/-- `γ² = det Λ₁(0) / 12`. -/
theorem det_Λ₁_zero : (P.Λ₁ 0).det = 12 * P.costateCycle.gam2 0 := by
  have e := el_triY_margin P.trace_Ucal
  have h1 : triY (fun j ↦ margin j P.Ucal) = triY (P.costateCycle.mu 0) := by
    congr 1; funext j; rw [P.mu_zero]
  rw [h1] at e
  have hd : (triY (P.costateCycle.mu 0)).det = P.Ucal.det := by
    rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
      Term.triCinv_mul_triC, Matrix.det_one, one_mul]
  rw [det_triY] at hd
  rw [CostateCycle.gam2, hd, P.det_Ucal]; ring

/-- **The orientation of the multiplier**: if `S = -J₀ U` has a positive diagonal entry `S₀₀ > 0`
and `γ² > 0`, then `Λ₁(0)` is negative elliptic (`Λ₁(0)₁₀ < 0`); the triangular coordinates reverse
orientation. -/
theorem Λ₁_zero_neg (hpos : 0 < P.costateCycle.gam2 0) (hS : 0 < P.costateCycle.Sloc 0 0 0) :
    (P.Λ₁ 0) 1 0 < 0 := by
  set C := P.costateCycle
  have hX := P.isStarState (t := 0) ⟨le_rfl, P.T_pos.le⟩
  have hΛ := (P.extremal.2.2.2.2.2.2.2.1 0 ⟨le_rfl, P.T_pos.le⟩).1
  -- `S₀₀ = (M₀)₁₀`
  have hM : 0 < C.Mloc 0 1 0 := by
    have : C.Sloc 0 0 0 = C.Mloc 0 1 0 := by
      simp [CostateCycle.Sloc, elJ0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul,
        dotProduct]
    linarith
  -- `M₀ = A Y A⁻¹`, `Y = triY(μ)`
  obtain ⟨A, hA, hMA⟩ := el_triY_rot (C.mu 0) (C.lab 0)
  have hY : 0 < (triY (C.mu 0)).det := by rw [det_triY]; simpa [CostateCycle.gam2] using hpos
  have htrY : (triY (C.mu 0)).trace = 0 := by simp [triY, Matrix.trace_fin_two]; ring
  have s1 := el_ell_sign htrY hY A (by rw [hA]; norm_num)
  have hMloc : C.Mloc 0 = A * triY (C.mu 0) * A.adjugate := by
    rw [← hMA]; rfl
  rw [← hMloc] at s1
  have hY10 : 0 < triY (C.mu 0) 1 0 := by
    by_contra h; push Not at h; nlinarith
  -- `Y = C 𝒰 C⁻¹`
  have e := el_triY_margin P.trace_Ucal
  have h1 : triY (fun j ↦ margin j P.Ucal) = triY (C.mu 0) := by
    congr 1; funext j; rw [P.mu_zero]
  rw [h1] at e
  have hCinv : Term.triCinv = -(1 / (2 * √3)) • Term.triC.adjugate := by
    have h3 := el_s3pos
    rw [Matrix.adjugate_fin_two]
    ext a b; fin_cases a <;> fin_cases b <;> simp [Term.triC, Term.triCinv] <;> field_simp
  have hdetU : 0 < P.Ucal.det := by
    have : (triY (C.mu 0)).det = P.Ucal.det := by
      rw [e, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
        Term.triCinv_mul_triC, Matrix.det_one, one_mul]
    linarith
  have hdC : Term.triC.det = -(2 * √3) := by simp [Term.triC, Matrix.det_fin_two]; ring
  have s2 := el_ell_sign P.trace_Ucal hdetU Term.triC (by
    rw [hdC]; have := el_s3pos; exact neg_ne_zero.2 (by positivity))
  have hU10 : P.Ucal 1 0 < 0 := by
    have : triY (C.mu 0) 1 0 = -(1 / (2 * √3)) * (Term.triC * P.Ucal * Term.triC.adjugate) 1 0 := by
      rw [e, hCinv, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
    have h3 := el_s3pos
    have hneg : (Term.triC * P.Ucal * Term.triC.adjugate) 1 0 < 0 := by
      have : 0 < 1 / (2 * √3) := by positivity
      nlinarith
    by_contra h; push Not at h; nlinarith
  -- `𝒰 = (1/√12) X Λ₁ X⁻¹`
  have hadj : (P.X 0).adjugate = -P.X 0 := by
    have := hX.1
    rw [Matrix.trace_fin_two] at this
    rw [Matrix.adjugate_fin_two]
    ext a b; fin_cases a <;> fin_cases b <;> simp <;> linarith
  have hdetΛ : 0 < (P.Λ₁ 0).det := by rw [P.det_Ucal] at hdetU; linarith
  have s3 := el_ell_sign hΛ hdetΛ (P.X 0) (by rw [hX.2.1]; norm_num)
  have hU : P.Ucal = (1 / √12) • (P.X 0 * P.Λ₁ 0 * (P.X 0).adjugate) := by
    rw [Ucal, hadj, Matrix.mul_neg, smul_neg, neg_smul]
  have : P.Ucal 1 0 = (1 / √12) * (P.X 0 * P.Λ₁ 0 * (P.X 0).adjugate) 1 0 := by
    rw [hU, Matrix.smul_apply, smul_eq_mul]
  have h12 : 0 < 1 / √12 := by positivity
  have hneg : (P.X 0 * P.Λ₁ 0 * (P.X 0).adjugate) 1 0 < 0 := by nlinarith
  by_contra h; push Not at h; nlinarith

open Reduction in
/-- **The cost–Casimir inequality**. If `Λ₁(0)` is negative elliptic with Casimir `κ = √(det Λ₁)`,
then `C ≥ 4πκ/(2κ + 3)`. -/
theorem cost_casimir (hdet : 0 < (P.Λ₁ 0).det) (h10 : (P.Λ₁ 0) 1 0 < 0) :
    4 * Real.pi * √(P.Λ₁ 0).det / (2 * √(P.Λ₁ 0).det + 3) ≤ P.cost := by
  have hΛtr := (P.extremal.2.2.2.2.2.2.2.1 0 ⟨le_rfl, P.T_pos.le⟩).1
  obtain ⟨h₀, hh₀, hrep⟩ := el_negEll_repr hΛtr hdet h10
  set κ := √(P.Λ₁ 0).det with hκ
  have hκpos : 0 < κ := Real.sqrt_pos.2 hdet
  have hT := P.T_pos
  obtain ⟨hst, hg0, hgT, -, -, -, -, -, -, -, -⟩ := P.extremal
  have hgc := clr_continuousOn_frame hst
  have hXc := clr_continuousOn_state hst
  have hdg : ∀ s ∈ Icc 0 P.T, (P.g s).det = 1 := fun s hs ↦ (hst.2.2.2.1 s hs).1
  have hstar : ∀ s ∈ Icc 0 P.T, IsStarState (P.X s) := fun s hs ↦ (hst.2.2.2.1 s hs).2
  set B : ℝ → Mat2 := fun s ↦ h₀.adjugate * P.g s with hB
  have hdetadj : h₀.adjugate.det = 1 := by
    rw [Matrix.det_adjugate, hh₀]; simp
  have hBc : ContinuousOn B (Icc 0 P.T) := continuousOn_const.mul hgc
  have hBd : ∀ s ∈ Ioo 0 P.T, Matrix.HasDerivAtEntrywise B (B s * P.X s) s := by
    intro s hs
    have := (clr_hasDerivAtEntrywise_frame hst hs).const_mul h₀.adjugate
    simpa [hB, Matrix.mul_assoc] using this
  have hBdet : ∀ s ∈ Icc 0 P.T, (B s).det = 1 := fun s hs ↦ by
    simp only [hB, Matrix.det_mul, hdetadj, hdg s hs, mul_one]
  have hBT : B P.T = B 0 * R := by simp only [hB, hgT, hg0, Matrix.mul_one]
  have hwind := el_winding hT hBc hXc hBd hBdet hstar hBT
  -- `tr(Λ₁ X) = 2κ ρ_R`
  have hcons := clr_conservation P.extremal
  have hρR : ∀ s ∈ Icc 0 P.T, traceForm (P.Λ₁ s) (P.X s) = 2 * κ * clr_rhoR (B s) (P.X s) := by
    intro s hs
    have hinv : (P.g s)⁻¹ = (P.g s).adjugate := by
      rw [Matrix.inv_def, hdg s hs]; simp
    have hadjB : (B s).adjugate = (P.g s).adjugate * h₀ := by
      simp only [hB, Matrix.adjugate_mul_distrib]
      rw [Matrix.adjugate_adjugate _ (by simp)]
      simp
    rw [hcons s hs, hrep, hinv, clr_rhoR, clr_rho, hadjB]
    simp only [traceForm, hB, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    have key : ∀ A B C D E F : Mat2, (A * (B * (C * (D * (E * F))))).trace =
        (F * (A * (B * (C * (D * E))))).trace := by
      intro A B C D E F; rw [Matrix.trace_mul_comm F]; simp only [Matrix.mul_assoc]
    have : ((P.g s).adjugate * (h₀ * J * h₀.adjugate) * P.g s * P.X s).trace =
        (J * (h₀.adjugate * P.g s * P.X s * ((P.g s).adjugate * h₀))).trace := by
      simp only [Matrix.mul_assoc]
      rw [key J, key h₀]
    rw [this]; ring
  -- `ρ_R ≤ 3ρ/(2κ)`
  have hle : ∀ s ∈ Icc 0 P.T, clr_rho (P.X s) + clr_rhoR (B s) (P.X s) ≤
      (1 + 3 / (2 * κ)) * clr_rho (P.X s) := by
    intro s hs
    have h1 := clr_traceForm_le_zero P.extremal s hs
    have h2 := hρR s hs
    simp only [traceForm, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul] at h1
    simp only [traceForm] at h2
    simp only [clr_rho, traceForm]
    rw [h2] at h1
    field_simp
    nlinarith
  have hρc : ContinuousOn (fun s ↦ clr_rho (P.X s)) (Icc 0 P.T) :=
    clr_continuous_rho.comp_continuousOn hXc
  have hρRc : ContinuousOn (fun s ↦ clr_rhoR (B s) (P.X s)) (Icc 0 P.T) :=
    clr_continuous_rhoR.comp_continuousOn (f := fun s ↦ (B s, P.X s)) (hBc.prodMk hXc)
  have hi1 : IntervalIntegrable (fun s ↦ clr_rho (P.X s) + clr_rhoR (B s) (P.X s))
      MeasureTheory.volume 0 P.T :=
    ((hρc.add hρRc).mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s ↦ (1 + 3 / (2 * κ)) * clr_rho (P.X s))
      MeasureTheory.volume 0 P.T :=
    ((hρc.const_smul (1 + 3 / (2 * κ))).mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hT.le hi1 hi2 hle
  rw [intervalIntegral.integral_const_mul] at hmono
  have hcost : P.cost = 3 * ∫ s in (0 : ℝ)..P.T, clr_rho (P.X s) := by
    simp only [cost, reinhardtCost, clr_rho, intervalIntegral.integral_const_mul]; ring
  rw [hcost]
  have := le_trans hwind hmono
  rw [div_le_iff₀ (by positivity)]
  field_simp at this
  nlinarith [Real.pi_pos]

/-- **The competitive Casimir cap**. If `γ² > 0` and the first switch norm is positive (so
`S = -J₀U` is positive definite and `Λ₁` negative elliptic), then a competitive period has
`γ² ≤ 97969/529200`. -/
theorem gam2_le_cap (hc : P.IsCompetitive) (hpos : 0 < P.costateCycle.gam2 0)
    (hd : 0 < P.costateCycle.swd 0) : P.costateCycle.gam2 0 ≤ 97969 / 529200 := by
  set C := P.costateCycle
  -- `S₀₀ > 0`
  obtain ⟨-, s01, s10, -⟩ := C.Sloc_apply 0
  have hsym : C.Sloc 0 0 1 = C.Sloc 0 1 0 := by rw [s01, s10]
  have hdetS : (C.Sloc 0).det = C.gam2 0 := by
    rw [CostateCycle.Sloc, Matrix.det_neg, Matrix.det_mul, C.det_Mloc]
    simp [elJ0, Matrix.det_fin_two]
  have hq : 0 < elQ (C.Sloc 0) (C.yv 0) (C.yv 0) := by rw [C.yv_norm]; exact_mod_cast hd
  have hS00 : 0 < C.Sloc 0 0 0 := by
    rw [Matrix.det_fin_two] at hdetS
    set y := C.yv 0
    have e : C.Sloc 0 0 0 * elQ (C.Sloc 0) y y = (C.Sloc 0 0 0 * y 0 + C.Sloc 0 0 1 * y 1) ^ 2 +
        (C.Sloc 0 0 0 * C.Sloc 0 1 1 - C.Sloc 0 0 1 * C.Sloc 0 1 0) * y 1 ^ 2 := by
      simp only [elQ, hsym]; ring
    have hne : C.Sloc 0 0 0 ≠ 0 := by
      intro h0; rw [h0, hsym] at hdetS; nlinarith [sq_nonneg (C.Sloc 0 1 0)]
    have : 0 ≤ C.Sloc 0 0 0 * elQ (C.Sloc 0) y y := by
      rw [e, hdetS]; positivity
    rcases lt_or_gt_of_ne hne with h | h
    · nlinarith
    · exact h
  have h10 := P.Λ₁_zero_neg hpos hS00
  have hdet : 0 < (P.Λ₁ 0).det := by rw [P.det_Λ₁_zero]; positivity
  have hcc := P.cost_casimir hdet h10
  rw [P.det_Λ₁_zero] at hcc
  set κ := √(12 * C.gam2 0) with hκ
  have hκpos : 0 < κ := Real.sqrt_pos.2 (by positivity)
  have hκ2 : κ ^ 2 = 12 * C.gam2 0 := Real.sq_sqrt (by positivity)
  have hA := Reduction.clr_octagonCost_lt
  have hpi := Real.pi_gt_d2
  have hcost : P.cost < 3.127 := lt_of_le_of_lt hc hA
  rw [div_le_iff₀ (by positivity)] at hcc
  have e1 : 3.14 * κ < Real.pi * κ := mul_lt_mul_of_pos_right hpi hκpos
  have e2 : P.cost * (2 * κ + 3) < 3.127 * (2 * κ + 3) :=
    mul_lt_mul_of_pos_right hcost (by positivity)
  have hκlt : κ < 14877 / 10000 := by
    by_contra h; push Not at h
    norm_num at e1 e2
    linarith
  have : κ ^ 2 < (14877 / 10000) ^ 2 := by nlinarith
  rw [hκ2] at this
  linarith

end NormalPeriod

end SmoothedOctagon
