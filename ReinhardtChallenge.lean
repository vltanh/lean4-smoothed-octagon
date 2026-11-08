module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The Reinhardt conjecture

Reinhardt (1934) asked which centrally symmetric convex disk in the plane packs worst: which one
has the least greatest packing density. He conjectured that the answer is the *smoothed octagon*,
a regular octagon whose corners are cut off by arcs of hyperbolas, with density

  `δ_oct = (8 - 4√2 - log 2)/(2√2 - 1) = 0.902414…`,

and that it is the only worst disk up to affine maps. This file states the conjecture with its
equality case. It imports only Mathlib.

## Definitions

Points of the plane are `Fin 2 → ℝ`, and areas are Lebesgue measure. The definitions sit in two
blocks between markers, each copied word for word from a library module
(`python3 scripts/sync_challenge_defs.py`).

The first block is from `SmoothedPolygons/Defs.lean` of `lean4-smoothed-polygon`, the formalization
of Hales and Vajjha, *Packings of Smoothed Polygons* (arXiv:2405.04331); the docstrings there
explain each definition. The statements use two of them:

* `greatestPackingDensity K` is the greatest density `δ(K)` of a packing of the plane by congruent
  copies of `K`: the supremum, over packings whose density exists, of the limit of the fraction of
  the disk of radius `r` that they cover, as `r → ∞`.
* `IsConvexDisk K`: `K` is compact and convex with nonempty interior. The theorems below take a
  centre `c` of symmetry, `2c - x ∈ K` for every `x ∈ K`.

The rest of the block defines Hales's control problem, through which the library proves the
conjecture; the statements do not use it.

The second block is from `SmoothedOctagon/Defs.lean` of this project. It defines the smoothed
octagon `smoothedOctagon` as Reinhardt described it. With `octagonSideDist k x` the distance from
`x` to the line `x₀ cos(kπ/4) + x₁ sin(kπ/4) = 1` of the `k`-th side of the regular octagon of
inradius `1` (`k : Fin 8`), positive on the side of the origin, the regular octagon is
`0 ≤ octagonSideDist k x` for all `k`. Its corner between sides `k` and `k + 1` is cut off along the
hyperbola `octagonSideDist (k - 1) x * octagonSideDist (k + 2) x = √2/4`, whose asymptotes are the
next two side lines. The hyperbola touches the two sides where
`octagonSideDist k x + octagonSideDist (k + 1) x = 3/2 - √2`; beyond that chord, only the points on
the side of the origin of the hyperbola are kept.

## Theorems

* `octagon_density`: the smoothed octagon is a centrally symmetric convex disk of greatest packing
  density `δ_oct`.
* `reinhardt`: every centrally symmetric convex disk has greatest packing density at least
  `δ_oct`.
* `reinhardt_equality`: a centrally symmetric convex disk has greatest packing density `δ_oct` if
  and only if it is the image of the smoothed octagon under an invertible affine map of the plane.
-/
@[expose] public section

-- BEGIN SHARED DEFINITIONS

namespace SmoothedPolygons

open MeasureTheory

/-- The control simplex `U_T = {(u₀, u₁, u₂) | 0 ≤ uᵢ ≤ 1, u₀ + u₁ + u₂ = 1}` (Definition 3.3.3). -/
def controlSimplex : Set (Fin 3 → ℝ) :=
  {u | (∀ i, 0 ≤ u i ∧ u i ≤ 1) ∧ u 0 + u 1 + u 2 = 1}

/-- The real `2 × 2` matrices. -/
abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℝ

/-- The trace form `⟨X, Y⟩ = tr(XY)` (§3.3). -/
def traceForm (X Y : Mat2) : ℝ := (X * Y).trace

/-- The infinitesimal generator `J` of the rotation group (Definition 3.1.5). -/
def J : Mat2 := !![0, -1; 1, 0]

/-- The rotation `R = exp(Jπ/3)` by the angle `π/3` (Definition 3.1.5), written out. -/
noncomputable def R : Mat2 := !![1 / 2, -(√3 / 2); √3 / 2, 1 / 2]

/-- The control matrix `Z_u` of a control `u = (u₀, u₁, u₂)` (equation `eqn:Z0`). -/
noncomputable def controlMatrix (u : Fin 3 → ℝ) : Mat2 :=
  !![(u 1 - u 2) / √3, (u 0 - 2 * u 1 - 2 * u 2) / 3; u 0, (u 2 - u 1) / √3]

/-- The matrix `Φ(x + iy)` of the adjoint orbit of `J` attached to a point `x + iy` of the upper
half-plane (Lemma 4.2.1). -/
noncomputable def Φ (x y : ℝ) : Mat2 := !![x / y, -(x ^ 2 + y ^ 2) / y; 1 / y, -x / y]

/-- The star function `ρ₀(X) = (c + √3 a)/√3` of `X = [[a, b], [c, -a]]` (Corollary 3.1.6). -/
noncomputable def ρ₀ (X : Mat2) : ℝ := (X 1 0 + √3 * X 0 0) / √3

/-- The star function `ρ₁(X) = (c - √3 a)/√3` of `X = [[a, b], [c, -a]]` (Corollary 3.1.6). -/
noncomputable def ρ₁ (X : Mat2) : ℝ := (X 1 0 - √3 * X 0 0) / √3

/-- The star function `ρ₂(X) = -(3b + c)/(2√3)` of `X = [[a, b], [c, -a]]` (Corollary 3.1.6). -/
noncomputable def ρ₂ (X : Mat2) : ℝ := -(3 * X 0 1 + X 1 0) / (2 * √3)

/-- The state space of the Lie-algebra variable: `X ∈ 𝔰𝔩₂(ℝ)` with `det X = 1` satisfying the star
inequalities `ρᵢ(X) > 0` (Corollary 3.1.6, §3.5, Theorem 4.4.1). -/
def IsStarState (X : Mat2) : Prop :=
  X.trace = 0 ∧ X.det = 1 ∧ 0 < ρ₀ X ∧ 0 < ρ₁ X ∧ 0 < ρ₂ X

/-- The matrix `P = Z_u / ⟨Z_u, X⟩` (Theorem 3.4.2, Problem 6.7.1). -/
noncomputable def controlP (u : Fin 3 → ℝ) (X : Mat2) : Mat2 :=
  (traceForm (controlMatrix u) X)⁻¹ • controlMatrix u

/-- The control-dependent Hamiltonian
`H(Λ₁, Λ_R, X; Z_u) = ⟨Λ₁ - (3/2) λ_cost J, X⟩ - ⟨Λ_R, Z_u⟩ / ⟨X, Z_u⟩`
(equation `eqn:full-hamiltonian`). -/
noncomputable def hamiltonian (lam : ℝ) (Λ₁ ΛR X : Mat2) (u : Fin 3 → ℝ) : ℝ :=
  traceForm (Λ₁ - (3 / 2 * lam) • J) X -
    traceForm ΛR (controlMatrix u) / traceForm X (controlMatrix u)

/-- `f` solves `f' = v` on `[0, T]` in Carathéodory's sense: each entry of `v` is integrable on
`[0, T]` and each entry of `f` is the indefinite integral of the corresponding entry of `v`. -/
def IsIntegralCurve (f v : ℝ → Mat2) (T : ℝ) : Prop :=
  ∀ i j, IntervalIntegrable (fun s ↦ v s i j) volume 0 T ∧
    ∀ t ∈ Set.Icc 0 T, f t i j = f 0 i j + ∫ s in (0 : ℝ)..t, v s i j

/-- A state trajectory of the Reinhardt control problem on `[0, T]` (Problem 3.6.2, with state
space `SL₂(ℝ) × 𝔥*` by Theorem 4.4.1): a measurable control `u` with values in the simplex `U_T`,
`g` with values in `SL₂(ℝ)`, `X` with values in the star states, `g' = gX` and
`X' = [P, X]` with `P = Z_u / ⟨Z_u, X⟩`. No boundary condition is imposed. -/
def IsStateTrajectory (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X : ℝ → Mat2) : Prop :=
  0 < T ∧ Measurable u ∧ (∀ t ∈ Set.Icc 0 T, u t ∈ controlSimplex) ∧
    (∀ t ∈ Set.Icc 0 T, (g t).det = 1 ∧ IsStarState (X t)) ∧
    IsIntegralCurve g (fun t ↦ g t * X t) T ∧
    IsIntegralCurve X (fun t ↦ controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) T

/-- A Pontryagin extremal of the Reinhardt control problem on `[0, T]` (§6.2, Problem 6.7.1,
§6.6): a state trajectory `(g, X)` with control `u`, lifted by costate variables `Λ₁, Λ_R` and a
constant multiplier `λ_cost ≤ 0`, such that

* `Λ₁, Λ_R ∈ 𝔰𝔩₂(ℝ)`, `Λ_R ⊥ X` (because `Λ_R = [Λ₂, X]`), and `(λ_cost, Λ₁, Λ_R) ≠ 0` at every
  time (the nontriviality condition of §6.2, for the reduced costate `(Λ₁, Λ_R)` of
  Problem 6.7.1; it excludes the spurious lift `λ_cost = 0`, `Λ₁ = 0`, `Λ₂ = X`);
* the costate equations `Λ₁' = [Λ₁, X]` and
  `Λ_R' = [P, Λ_R] - ⟨Λ_R, P⟩ [P, X] + [-Λ₁ + (3/2) λ_cost J, X]` hold;
* for almost every time the control maximizes the Hamiltonian over `U_T`, and the Hamiltonian
  vanishes;
* the transversality conditions `g(0) = I`, `g(T) = R`, `X(T) = R⁻¹X(0)R`,
  `Λ₁(T) = R⁻¹Λ₁(0)R` and `Λ_R(T) = R⁻¹Λ_R(0)R` hold. -/
def IsPontryaginExtremal (T : ℝ) (u : ℝ → Fin 3 → ℝ) (g X Λ₁ ΛR : ℝ → Mat2) (lam : ℝ) : Prop :=
  IsStateTrajectory T u g X ∧
    g 0 = 1 ∧ g T = R ∧ X T = R⁻¹ * X 0 * R ∧ Λ₁ T = R⁻¹ * Λ₁ 0 * R ∧ ΛR T = R⁻¹ * ΛR 0 * R ∧
    lam ≤ 0 ∧
    (∀ t ∈ Set.Icc 0 T, (Λ₁ t).trace = 0 ∧ (ΛR t).trace = 0 ∧ traceForm (ΛR t) (X t) = 0 ∧
      (lam ≠ 0 ∨ Λ₁ t ≠ 0 ∨ ΛR t ≠ 0)) ∧
    IsIntegralCurve Λ₁ (fun t ↦ Λ₁ t * X t - X t * Λ₁ t) T ∧
    IsIntegralCurve ΛR (fun t ↦
      (controlP (u t) (X t) * ΛR t - ΛR t * controlP (u t) (X t)) -
        traceForm (ΛR t) (controlP (u t) (X t)) •
          (controlP (u t) (X t) * X t - X t * controlP (u t) (X t)) +
        ((-Λ₁ t + (3 / 2 * lam) • J) * X t - X t * (-Λ₁ t + (3 / 2 * lam) • J))) T ∧
    ∀ᵐ t, t ∈ Set.Ioo 0 T →
      hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t) = 0 ∧
        ∀ v ∈ controlSimplex,
          hamiltonian lam (Λ₁ t) (ΛR t) (X t) v ≤ hamiltonian lam (Λ₁ t) (ΛR t) (X t) (u t)

/-- A control is bang-bang on `[0, T]` if its values are extreme points of the control simplex
`U_T` (Definition 7.3.2; the clause "with discontinuous switching" of the definition describes the
switching and is not a condition). -/
def IsBangBang (T : ℝ) (u : ℝ → Fin 3 → ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, u t ∈ Set.extremePoints ℝ (controlSimplex)

/-- The cost `-(3/2) ∫₀ᵀ ⟨J, X⟩ dt` of a trajectory (equation `eqn:cost`); for the trajectory of a
balanced disk in circle representation it is the area of the disk. -/
noncomputable def reinhardtCost (T : ℝ) (X : ℝ → Mat2) : ℝ :=
  -(3 / 2) * ∫ t in (0 : ℝ)..T, traceForm J (X t)

/-- The angle `θ_k = πk/(3k+1)` of the smoothed `(6k+2)`-gon (Lemma 7.5.5). -/
noncomputable def θ (k : ℕ) : ℝ := Real.pi * k / (3 * k + 1)

/-- The height `y₀` of the initial point `z₀ = i y₀` of the smoothed `(6k+2)`-gon: the positive
solution of `4/(3y₀² + 1) = 2 cos θ_k` (Lemma 7.5.5). -/
noncomputable def y₀ (k : ℕ) : ℝ := √((2 / Real.cos (θ k) - 1) / 3)

/-- The switching time `t_sw = ln(4/(3y₀² + 1)) / (√3 y₀)` of the smoothed `(6k+2)`-gon
(equation `eqn:t1`). -/
noncomputable def tsw (k : ℕ) : ℝ := Real.log (4 / (3 * y₀ k ^ 2 + 1)) / (√3 * y₀ k)

/-- The terminal time `t_f = (3k+1) t_sw` of the smoothed `(6k+2)`-gon (Lemma 7.5.5). -/
noncomputable def tf (k : ℕ) : ℝ := (3 * k + 1) * tsw k

/-- The control of the smoothed `(6k+2)`-gon (equation `eqn:3k+1`): on the `i`-th switching interval
`[i t_sw, (i+1) t_sw)` it is the vertex `R⁻ⁱ · e₃` of `U_T`, so the controls are
`e₃, e₁, e₂, e₃, e₁, …`, that is, `Pi.single ((2 + i) mod 3) 1`. -/
noncomputable def polygonControl (k : ℕ) (t : ℝ) : Fin 3 → ℝ :=
  Pi.single (⟨(2 + ⌊t / tsw k⌋₊) % 3, Nat.mod_lt _ (by norm_num)⟩ : Fin 3) 1

/-! ### Multi-points and balanced disks (Definitions 2.4.1, 2.4.7) -/

/-- The determinant `det(v, w) = v₁w₂ - v₂w₁` of the `2 × 2` matrix with columns `v, w`. -/
def det2 (v w : Fin 2 → ℝ) : ℝ := v 0 * w 1 - v 1 * w 0

/-- A multi-point (Definition 2.4.1): `s : ℤ/6ℤ → ℝ²` with `s₀ + s₂ + s₄ = 0`,
`s_{j+3} = -s_j` and `det(s_j, s_{j+1}) = √3/2` for all `j` (equations `eqn:multi`,
`eqn:sqrt12`); the first condition is imposed for every shift `j`, as in equation
`eqn:multi-point-properties`. -/
def IsMultiPoint (s : ZMod 6 → Fin 2 → ℝ) : Prop :=
  ∀ j : ZMod 6, s j + s (j + 2) + s (j + 4) = 0 ∧ s (j + 3) = -s j ∧
    det2 (s j) (s (j + 1)) = √3 / 2

/-- The sixth roots of unity `s_j* = exp(2πij/6)`, as points of `ℝ²`. -/
noncomputable def sixthRoot (j : ZMod 6) : Fin 2 → ℝ :=
  ![Real.cos (Real.pi * j.val / 3), Real.sin (Real.pi * j.val / 3)]

/-- A centrally symmetric convex disk centered at the origin (§1.1, §2.1): a compact convex set
with nonempty interior, invariant under `x ↦ -x`. -/
def IsCCSDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧ ∀ x ∈ K, -x ∈ K

/-- A balanced pair `(K, σ)` (Definition 2.4.7): `K` is a centrally symmetric convex disk and
`σ` is a multi-curve of six regular `C¹` curves `σ_j : ℝ → ℝ²` such that

1. each `σ_j` is `C¹` and regular;
2. each derivative `σ_j'` is Lipschitz;
3. `j ↦ σ_j(t)` is a multi-point for every `t`;
4. the curvature constraint `det(σ_j'(t), σ_j''(t)) ≥ 0` holds for almost every `t`;
5. (star condition) `σ_j'(t)` points into the open cone with apex `σ_j(t)` and rays through
   `σ_{j+1}(t)` and `σ_j(t) + σ_{j+1}(t)`, that is, `σ_j' = α (σ_{j+1} - σ_j) + β σ_{j+1}` with
   `α, β > 0`;
6. the curves are periodic with the common period `6 t_f`, and each `σ_j` restricted to one
   period is a simple closed curve whose image is the boundary of `K`.

The counterclockwise orientation required by item 1 of the definition follows from items 3 and 5
(`det(σ_j, σ_j') > 0`). -/
def IsBalancedPair (K : Set (Fin 2 → ℝ)) (σ : ZMod 6 → ℝ → Fin 2 → ℝ) (tf : ℝ) : Prop :=
  IsCCSDisk K ∧
    (∀ j, ContDiff ℝ 1 (σ j) ∧ ∀ t, deriv (σ j) t ≠ 0) ∧
    (∀ j, ∃ C, LipschitzWith C (deriv (σ j))) ∧
    (∀ t, IsMultiPoint fun j ↦ σ j t) ∧
    (∀ j, ∀ᵐ t, 0 ≤ det2 (deriv (σ j) t) (deriv (deriv (σ j)) t)) ∧
    (∀ j t, ∃ α β : ℝ, 0 < α ∧ 0 < β ∧
      deriv (σ j) t = α • (σ (j + 1) t - σ j t) + β • σ (j + 1) t) ∧
    0 < tf ∧ (∀ j t, σ j (t + 6 * tf) = σ j t) ∧
    (∀ j, Set.InjOn (σ j) (Set.Ico 0 (6 * tf))) ∧
    (∀ j, σ j '' Set.Ico 0 (6 * tf) = frontier K)

/-- A balanced pair is in circle representation (§2.4) if `σ_j(0) = s_j*` for all `j`. -/
def IsCircleRepresentation (σ : ZMod 6 → ℝ → Fin 2 → ℝ) : Prop :=
  ∀ j, σ j 0 = sixthRoot j

/-! ### Convex disks and packing densities (Definition 2.1.1) -/

/-- A convex disk (§1.1, §2.1): a compact convex set with nonempty interior. -/
def IsConvexDisk (K : Set (Fin 2 → ℝ)) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/-- The Euclidean disk `B_r = {x | x₀² + x₁² ≤ r²}` of radius `r` centered at the origin
(Definition 2.1.1). -/
def euclidDisk (r : ℝ) : Set (Fin 2 → ℝ) := {x | x 0 ^ 2 + x 1 ^ 2 ≤ r ^ 2}

/-- `K'` is a congruent copy of `K` (§2.1): its image `{A x + b | x ∈ K}` under a Euclidean
isometry, with `A` an orthogonal matrix. -/
def IsCongruentCopy (K K' : Set (Fin 2 → ℝ)) : Prop :=
  ∃ A ∈ Matrix.orthogonalGroup (Fin 2) ℝ, ∃ b : Fin 2 → ℝ, K' = (fun x ↦ Matrix.mulVec A x + b) '' K

/-- A packing (§2.1): a family of convex disks, any two distinct members of which do not overlap,
that is, have disjoint interiors. -/
def IsPacking (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  (∀ K' ∈ P, IsConvexDisk K') ∧ P.Pairwise fun A B ↦ Disjoint (interior A) (interior B)

/-- A packing with congruent copies of `K` (Definition 2.1.1). -/
def IsPackingOfCopies (K : Set (Fin 2 → ℝ)) (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  IsPacking P ∧ ∀ K' ∈ P, IsCongruentCopy K K'

/-- The ratio `(1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of Definition 2.1.1, in `[0, ∞]`. -/
noncomputable def packingRatio (P : Set (Set (Fin 2 → ℝ))) (r : ℝ) : ENNReal :=
  (∑' K' : P, volume ((K' : Set (Fin 2 → ℝ)) ∩ euclidDisk r)) / volume (euclidDisk r)

/-- The upper density `limsup_{r → ∞} (1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of a packing
(Definition 2.1.1). -/
noncomputable def upperDensity (P : Set (Set (Fin 2 → ℝ))) : ENNReal :=
  Filter.limsup (packingRatio P) Filter.atTop

/-- The lower density `liminf_{r → ∞} (1/area(B_r)) Σ_{K' ∈ P} area(K' ∩ B_r)` of a packing
(Definition 2.1.1). -/
noncomputable def lowerDensity (P : Set (Set (Fin 2 → ℝ))) : ENNReal :=
  Filter.liminf (packingRatio P) Filter.atTop

/-- The density of `P` exists (Definition 2.1.1): the upper and lower densities exist (are
finite) and coincide. -/
def HasDensity (P : Set (Set (Fin 2 → ℝ))) : Prop :=
  upperDensity P ≠ ⊤ ∧ upperDensity P = lowerDensity P

/-- The density `δ(K, P)` of a packing (Definition 2.1.1): the common value of the upper and
lower densities, when the density exists (`HasDensity`). -/
noncomputable def packingDensity (P : Set (Set (Fin 2 → ℝ))) : ℝ :=
  (upperDensity P).toReal

/-- **Definition 2.1.1** (greatest packing density).
`δ(K) = sup {δ(K, P) | δ(K, P) exists, and P is a packing with congruent copies of K}`. -/
noncomputable def greatestPackingDensity (K : Set (Fin 2 → ℝ)) : ℝ :=
  sSup {d | ∃ P, IsPackingOfCopies K P ∧ HasDensity P ∧ packingDensity P = d}

end SmoothedPolygons

-- END SHARED DEFINITIONS

-- BEGIN SHARED OCTAGON
namespace SmoothedOctagon

/-- The distance `d_k(x) = 1 - (x₀ cos(kπ/4) + x₁ sin(kπ/4))` from `x` to the line
`x₀ cos(kπ/4) + x₁ sin(kπ/4) = 1` of the `k`-th side of the regular octagon of inradius `1`,
positive on the side of the origin. -/
noncomputable def octagonSideDist (k : Fin 8) (x : Fin 2 → ℝ) : ℝ :=
  1 - (x 0 * Real.cos ((k : ℕ) * Real.pi / 4) + x 1 * Real.sin ((k : ℕ) * Real.pi / 4))

/-- **Reinhardt's smoothed octagon.** The regular octagon `d_k ≥ 0` (`k : Fin 8`) with each corner
cut off by an arc of a hyperbola. The corner between sides `k` and `k + 1` is replaced by the arc of
the hyperbola `d_{k-1} d_{k+2} = √2/4`, whose asymptotes are the next two side lines; the arc
touches the two sides where `d_k + d_{k+1} = 3/2 - √2`, and beyond that chord only the points with
`d_{k-1} d_{k+2} ≥ √2/4` are kept. -/
def smoothedOctagon : Set (Fin 2 → ℝ) :=
  {x | ∀ k : Fin 8, 0 ≤ octagonSideDist k x ∧
    (octagonSideDist k x + octagonSideDist (k + 1) x ≤ 3 / 2 - √2 →
      √2 / 4 ≤ octagonSideDist (k - 1) x * octagonSideDist (k + 2) x)}

end SmoothedOctagon
-- END SHARED OCTAGON

namespace ReinhardtChallenge

open SmoothedPolygons SmoothedOctagon MeasureTheory

/-- **The smoothed octagon.** Reinhardt's smoothed octagon is a centrally symmetric convex disk of
greatest packing density `δ_oct = (8 - 4√2 - log 2)/(2√2 - 1)`. -/
theorem octagon_density :
    IsConvexDisk smoothedOctagon ∧ (∀ x ∈ smoothedOctagon, -x ∈ smoothedOctagon) ∧
      greatestPackingDensity smoothedOctagon = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) := by
  sorry

/-- **The Reinhardt conjecture.** Every centrally symmetric convex disk `K` in the plane has
greatest packing density at least `δ_oct`, the density of the smoothed octagon. -/
theorem reinhardt (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ≤ greatestPackingDensity K := by
  sorry

/-- **The equality case.** A centrally symmetric convex disk has greatest packing density `δ_oct`
if and only if it is the image of the smoothed octagon under an invertible affine map. -/
theorem reinhardt_equality (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    greatestPackingDensity K = (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ↔
      ∃ A : (Fin 2 → ℝ) ≃ᵃ[ℝ] (Fin 2 → ℝ), K = A '' smoothedOctagon := by
  sorry

end ReinhardtChallenge

end
