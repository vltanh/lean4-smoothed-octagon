module

public import SmoothedOctagon.Interval.Trig

/-!
# Reflected real expressions and their interval evaluators

`IExpr` is a small expression language over real variables `ρ 0, ρ 1, …` with rational
constants, `+ - × ÷`, natural powers, `√`, `log`, `Hlog`, `arctan` and `logDiv`. It has a real denotation
`IExpr.denote ρ` and two kernel-evaluable interval evaluators on a box `B : List Ival`:

* `IExpr.evalR B e : Option Ival`, the natural interval extension (`none` on a domain error:
  a denominator interval meeting `0`, `log`/`logDiv` of a non-positive interval, `Hlog` of an
  interval meeting `(-∞, 0)`);
* `IExpr.evalS B e : Option Slope`, a first-order slope (centred) form. A `Slope` `⟨R, V, G⟩`
  certifies, for every point `ρ` of the box, `e(ρ) ∈ R` and `e(ρ) = v + ∑ⱼ gⱼ (ρⱼ - cⱼ)` for some
  `v ∈ V`, `gⱼ ∈ Gⱼ`, where `cⱼ = mid Bⱼ` is the centre. Products use `G = G₁·R₂ + V₁·G₂`,
  reciprocals `G = -G·R⁻¹·V⁻¹`, `√` the identity `√y - √v = (y - v)/(√y + √v)`, `arctan` the mean
  value theorem (`G' = G/(1 + ξ²)`, `ξ ∈ hull(R, V)`), and `logDiv` its series
  `(1 - t)∑ t²ᵏ/(2k + 1)` run through slope arithmetic after two square-root reductions
  `logDiv q = 2 logDiv(√q)/(1 + √q)` (eight terms, tail frozen). `log` and `Hlog` are frozen
  (`V = φ(R)`, `G = 0`). `Slope.bound` encloses `e` on the box by `V + ∑ⱼ Gⱼ (Bⱼ - cⱼ)`; on boxes
  of width `w` its overestimation is `O(w²)`.

Sharing: the kernel caches the reduction of each closed subterm, so an `IExpr` built from named
sub-definitions is evaluated once per node and box, however often it is used.

## Main API

`IExpr`, `IExpr.denote`, `InBox`, `IExpr.evalR`, `IExpr.evalR_sound`, `Slope`, `Slope.Sound`,
`IExpr.evalS`, `IExpr.evalS_sound`, `Slope.bound`, `Slope.bound_sound`, `Slope.scale`,
`Slope.add`.
-/

@[expose] public section

namespace SmoothedOctagon.Interval

/-- Reflected real expressions. -/
inductive IExpr where
  /-- The variable `ρ i`. -/
  | var (i : ℕ)
  /-- The rational constant `n/d`. -/
  | const (n : ℤ) (d : ℕ)
  /-- Sum. -/
  | add (a b : IExpr)
  /-- Difference. -/
  | sub (a b : IExpr)
  /-- Negation. -/
  | neg (a : IExpr)
  /-- Product. -/
  | mul (a b : IExpr)
  /-- Quotient (Lean's `x / 0 = 0`; the evaluators fail on a denominator interval meeting `0`). -/
  | div (a b : IExpr)
  /-- Natural power. -/
  | pow (a : IExpr) (n : ℕ)
  /-- `Real.sqrt`. -/
  | sqrt (a : IExpr)
  /-- `Real.log`. -/
  | log (a : IExpr)
  /-- `hlogR z = (log(1 + z) - z + z²/2)/z³`, `1/3` at `0`. -/
  | hlog (a : IExpr)
  /-- `Real.arctan`. -/
  | atan (a : IExpr)
  /-- `logDivR q = log q/(q - 1)`, `1` at `1`. -/
  | logdiv (a : IExpr)

namespace IExpr

/-- The real value of an expression at the point `ρ`. -/
noncomputable def denote (ρ : ℕ → ℝ) : IExpr → ℝ
  | var i => ρ i
  | const n d => (n : ℝ) / d
  | add a b => a.denote ρ + b.denote ρ
  | sub a b => a.denote ρ - b.denote ρ
  | neg a => -a.denote ρ
  | mul a b => a.denote ρ * b.denote ρ
  | div a b => a.denote ρ / b.denote ρ
  | pow a n => a.denote ρ ^ n
  | sqrt a => Real.sqrt (a.denote ρ)
  | log a => Real.log (a.denote ρ)
  | hlog a => hlogR (a.denote ρ)
  | atan a => Real.arctan (a.denote ρ)
  | logdiv a => logDivR (a.denote ρ)

end IExpr

/-- The point `ρ` lies in the box `B` (coordinates beyond `B` are free). -/
def InBox (B : List Ival) (ρ : ℕ → ℝ) : Prop := ∀ i (I : Ival), B[i]? = some I → I.Mem (ρ i)

namespace Ival

/-- Natural powers (`x²` by `sq`, higher powers by products). -/
def powI (x : Ival) : ℕ → Ival
  | 0 => one
  | 1 => x
  | 2 => x.sq
  | n + 3 => (powI x (n + 2)).mul x

theorem mem_powI {x : Ival} {a : ℝ} (ha : x.Mem a) : ∀ n, (x.powI n).Mem (a ^ n)
  | 0 => by simpa [powI] using mem_one
  | 1 => by simpa [powI] using ha
  | 2 => mem_sq ha
  | n + 3 => by
    rw [powI, pow_succ]
    exact mem_mul (mem_powI ha (n + 2)) ha

/-- The midpoint `⌊(lo + hi)/2⌋` (any point works for soundness). -/
def mid (x : Ival) : ℤ := (x.lo + x.hi) >>> 1

/-- The hull of two intervals. -/
def hull (x y : Ival) : Ival := ⟨zmin x.lo y.lo, zmax x.hi y.hi⟩

theorem mem_hull_of {x y : Ival} {a b c : ℝ} (ha : x.Mem a) (hb : y.Mem b) (h1 : min a b ≤ c)
    (h2 : c ≤ max a b) : (hull x y).Mem c := by
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  obtain ⟨a1, a2⟩ := ha; obtain ⟨b1, b2⟩ := hb
  simp only [Mem, hull, zmin_eq, zmax_eq]
  push_cast
  constructor
  · rcases le_total a b with h | h
    · rw [min_eq_left h] at h1
      exact le_trans (min_le_left _ _) (le_trans a1 (by nlinarith))
    · rw [min_eq_right h] at h1
      exact le_trans (min_le_right _ _) (le_trans b1 (by nlinarith))
  · rcases le_total a b with h | h
    · rw [max_eq_right h] at h2
      exact le_trans (by nlinarith) (le_trans b2 (le_max_right _ _))
    · rw [max_eq_left h] at h2
      exact le_trans (by nlinarith) (le_trans a2 (le_max_left _ _))

theorem zero_mem_iff {a : ℝ} : zero.Mem a ↔ a = 0 := by
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  simp only [Mem, zero, Int.cast_zero]
  constructor
  · rintro ⟨h1, h2⟩; nlinarith
  · rintro rfl; simp

theorem ne_zero_of_inv {x y : Ival} {a : ℝ} (hx : x.inv = some y) (ha : x.Mem a) : a ≠ 0 := by
  rintro rfl
  obtain ⟨h1, h2⟩ := ha
  simp only [zero_mul] at h1 h2
  unfold inv at hx
  split at hx
  · rename_i l h hl hh
    rw [hl] at h1
    simp only [Int.ofNat_eq_natCast, Nat.cast_succ] at h1
    push_cast at h1
    linarith [(by positivity : (0 : ℝ) ≤ l)]
  · rename_i l h hl hh
    rw [hh] at h2; simp only [Int.cast_negSucc] at h2; push_cast at h2
    linarith [(by positivity : (0 : ℝ) ≤ h)]
  · cases hx

end Ival

open Ival

/-! ### Natural interval evaluation -/

namespace IExpr

/-- Natural interval extension on the box `B`. -/
def evalR (B : List Ival) : IExpr → Option Ival
  | var i => B[i]?
  | const n d => some (ofRat n d)
  | add a b => (evalR B a).bind fun x => (evalR B b).map x.add
  | sub a b => (evalR B a).bind fun x => (evalR B b).map x.sub
  | neg a => (evalR B a).map Ival.neg
  | mul a b => (evalR B a).bind fun x => (evalR B b).map x.mul
  | div a b => (evalR B a).bind fun x => (evalR B b).bind fun y => y.inv.map x.mul
  | pow a n => (evalR B a).map fun x => x.powI n
  | sqrt a => (evalR B a).map Ival.sqrtI
  | log a => (evalR B a).bind Ival.logI
  | hlog a => (evalR B a).bind Ival.hlogI
  | atan a => (evalR B a).bind Ival.atanI
  | logdiv a => (evalR B a).bind Ival.logDivI

theorem evalR_sound {B : List Ival} {ρ : ℕ → ℝ} (hB : InBox B ρ) :
    ∀ (e : IExpr) {I : Ival}, e.evalR B = some I → I.Mem (e.denote ρ)
  | var i, I, h => hB i I h
  | const n d, I, h => by
    simp only [evalR, Option.some.injEq] at h; subst h; exact mem_ofRat n d
  | add a b, I, h => by
    simp only [evalR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact mem_add (evalR_sound hB a hx) (evalR_sound hB b hy)
  | sub a b, I, h => by
    simp only [evalR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact mem_sub (evalR_sound hB a hx) (evalR_sound hB b hy)
  | neg a, I, h => by
    simp only [evalR, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact mem_neg (evalR_sound hB a hx)
  | mul a b, I, h => by
    simp only [evalR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact mem_mul (evalR_sound hB a hx) (evalR_sound hB b hy)
  | div a b, I, h => by
    simp only [evalR, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
    simp only [denote, div_eq_mul_inv]
    exact mem_mul (evalR_sound hB a hx) (mem_inv hz (evalR_sound hB b hy))
  | pow a n, I, h => by
    simp only [evalR, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact mem_powI (evalR_sound hB a hx) n
  | sqrt a, I, h => by
    simp only [evalR, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact mem_sqrtI (evalR_sound hB a hx)
  | log a, I, h => by
    simp only [evalR, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, hy⟩ := h
    exact mem_logI hy (evalR_sound hB a hx)
  | hlog a, I, h => by
    simp only [evalR, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, hy⟩ := h
    exact mem_hlogI hy (evalR_sound hB a hx)
  | atan a, I, h => by
    simp only [evalR, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, hy⟩ := h
    exact mem_atanI hy (evalR_sound hB a hx)
  | logdiv a, I, h => by
    simp only [evalR, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, hy⟩ := h
    exact mem_logDivI hy (evalR_sound hB a hx)

end IExpr

/-! ### Slope (centred) form -/

/-- Entry `j` of a slope vector, `0` beyond its end. -/
def gAt : List Ival → ℕ → Ival
  | [], _ => zero
  | x :: _, 0 => x
  | _ :: xs, j + 1 => gAt xs j

/-- Entrywise sum of slope vectors, padding with `0`. -/
def gadd : List Ival → List Ival → List Ival
  | [], ys => ys
  | x :: xs, [] => x :: xs
  | x :: xs, y :: ys => x.add y :: gadd xs ys

/-- The unit slope vector `eᵢ`. -/
def unitVec (i : ℕ) : List Ival := List.replicate i zero ++ [one]

/-- A first-order slope enclosure: range `r`, centre value `v`, slopes `g`. -/
structure Slope where
  /-- Range over the box. -/
  r : Ival
  /-- Centre value (up to the frozen parts). -/
  v : Ival
  /-- Slopes, one per variable (missing entries are `0`). -/
  g : List Ival

/-- The offset of coordinate `j` from the centre of the box. -/
noncomputable def dvec (B : List Ival) (ρ : ℕ → ℝ) (j : ℕ) : ℝ :=
  ρ j - (mid (gAt B j) : ℝ) / 2 ^ prec

namespace Slope

/-- `s` encloses the value `y` at a point with centre offsets `d`, over `N` coordinates. -/
def Sound (s : Slope) (N : ℕ) (d : ℕ → ℝ) (y : ℝ) : Prop :=
  s.r.Mem y ∧ ∃ v : ℝ, s.v.Mem v ∧ ∃ g : ℕ → ℝ, (∀ j, (gAt s.g j).Mem (g j)) ∧
    y = v + ∑ j ∈ Finset.range N, g j * d j

/-- A constant. -/
def const (k : Ival) : Slope := ⟨k, k, []⟩

/-- Sum. -/
def add (s t : Slope) : Slope := ⟨s.r.add t.r, s.v.add t.v, gadd s.g t.g⟩

/-- Negation. -/
def neg (s : Slope) : Slope := ⟨s.r.neg, s.v.neg, s.g.map Ival.neg⟩

/-- Difference. -/
def sub (s t : Slope) : Slope := s.add t.neg

/-- Product: `G = G₁·R₂ + V₁·G₂`. -/
def mul (s t : Slope) : Slope :=
  ⟨s.r.mul t.r, s.v.mul t.v, gadd (s.g.map fun a => a.mul t.r) (t.g.map s.v.mul)⟩

/-- Square: `G = G·(V + R)`. -/
def sq (s : Slope) : Slope := ⟨s.r.sq, s.v.sq, s.g.map fun a => a.mul (s.v.add s.r)⟩

/-- Reciprocal: `G = -G·R⁻¹·V⁻¹`. -/
def inv (s : Slope) : Option Slope :=
  s.r.inv.bind fun ri => s.v.inv.map fun vi => ⟨ri, vi, s.g.map fun a => ((a.mul ri).mul vi).neg⟩

/-- Natural powers. -/
def pow (s : Slope) : ℕ → Slope
  | 0 => const Ival.one
  | 1 => s
  | 2 => s.sq
  | n + 3 => (pow s (n + 2)).mul s

/-- A frozen value: `V = R`, no slope. -/
def freeze (k : Ival) : Slope := ⟨k, k, []⟩

/-- Exact scaling by a natural weight. -/
def scale (w : ℕ) (s : Slope) : Slope := ⟨s.r.smul w, s.v.smul w, s.g.map (Ival.smul w)⟩

/-- Horner's rule on slopes. -/
def hornerS (x : Slope) : List Ival → Slope
  | [] => const zero
  | c :: cs => (const c).add (x.mul (hornerS x cs))

/-- The coefficients `1/(2k + 1)`, `k < 24`. -/
def ld24 : List Ival := (List.range 24).map fun k => ofRat 1 (2 * k + 1)

/-- `x²⁴` by squarings. -/
def pow24 (x : Ival) : Ival :=
  let x2 := x.sq
  let x3 := x2.mul x
  let x6 := x3.sq
  let x12 := x6.sq
  x12.sq

/-- Slope of `logDivR`: its series `(1 - t)∑ t²ᵏ/(2k + 1)`, `t = 1 - 2/(q + 1)`, through slope
arithmetic, with the tail frozen. -/
def logDiv (s : Slope) : Option Slope :=
  cond (zPos s.r.lo)
    ((s.add (const Ival.one)).inv.bind fun W =>
      let T := (const Ival.one).sub (W.scale 2)
      let T2 := T.sq
      cond (zle (Int.add T2.r.hi 1) (.ofNat (2 ^ prec)))
        ((Ival.one.sub (point T2.r.hi)).inv.map fun d =>
          ((const Ival.one).sub T).mul
            ((hornerS T2 ld24).add (const ⟨0, ((pow24 (point T2.r.hi)).mul d).hi⟩)))
        none)
    none

/-- Slope of `arctan` by the mean value theorem: `G' = G/(1 + ξ²)`, `ξ ∈ hull(R, V)`. -/
def atan (s : Slope) : Option Slope :=
  s.r.atanI.bind fun a => s.v.atanI.bind fun b =>
    (Ival.one.add (Ival.hull s.r s.v).sq).inv.map fun D => ⟨a, b, s.g.map fun g => g.mul D⟩

/-- Slope of `√`: `√y - √v = (y - v)/(√y + √v)` when both are nonnegative. -/
def sqrt (s : Slope) : Slope :=
  cond (zNonneg s.r.lo && zNonneg s.v.lo)
    (match (s.r.sqrtI.add s.v.sqrtI).inv with
     | some w => ⟨s.r.sqrtI, s.v.sqrtI, s.g.map fun a => a.mul w⟩
     | none => freeze s.r.sqrtI)
    (freeze s.r.sqrtI)

/-- The coefficients `1/(2k + 1)`, `k < 8`. -/
def ld8 : List Ival := (List.range 8).map fun k => ofRat 1 (2 * k + 1)

/-- `x⁸` by squarings. -/
def pow8 (x : Ival) : Ival := x.sq.sq.sq

/-- The series of `logDivR` with eight terms, for arguments near `1` (after two square roots). -/
def logDiv8 (s : Slope) : Option Slope :=
  cond (zPos s.r.lo)
    ((s.add (const Ival.one)).inv.bind fun W =>
      let T := (const Ival.one).sub (W.scale 2)
      let T2 := T.sq
      cond (zle (Int.add T2.r.hi 1) (.ofNat (2 ^ prec)))
        ((Ival.one.sub (point T2.r.hi)).inv.map fun d =>
          ((const Ival.one).sub T).mul
            ((hornerS T2 ld8).add (const ⟨0, ((pow8 (point T2.r.hi)).mul d).hi⟩)))
        none)
    none

/-- Slope of `logDivR` by `logDivR q = 4 logDivR(q^{1/4})/((1 + √q)(1 + q^{1/4}))` and the
eight-term series. -/
def logDivQ (s : Slope) : Option Slope :=
  cond (zPos s.r.lo)
    (let s1 := s.sqrt
     let s2 := s1.sqrt
     (logDiv8 s2).bind fun L => ((const Ival.one).add s1).inv.bind fun i1 =>
       ((const Ival.one).add s2).inv.map fun i2 => (L.mul (i2.scale 2)).mul (i1.scale 2))
    none

/-- `∑ⱼ G j·(Bⱼ - cⱼ)` over the box. -/
def lin : List Ival → List Ival → Ival
  | _, [] => zero
  | gs, b :: bs => ((gAt gs 0).mul (b.sub (point (mid b)))).add (lin gs.tail bs)

/-- The enclosure `V + ∑ⱼ Gⱼ (Bⱼ - cⱼ)` of the value on the box. -/
def bound (B : List Ival) (s : Slope) : Ival := s.v.add (lin s.g B)

end Slope

/-! #### Lemmas on slope vectors -/

theorem gAt_nil (j : ℕ) : gAt [] j = zero := by cases j <;> rfl

theorem mem_gAt_gadd {xs ys : List Ival} {a b : ℕ → ℝ} (ha : ∀ j, (gAt xs j).Mem (a j))
    (hb : ∀ j, (gAt ys j).Mem (b j)) : ∀ j, (gAt (gadd xs ys) j).Mem (a j + b j) := by
  induction xs generalizing ys a b with
  | nil =>
    intro j
    have : a j = 0 := zero_mem_iff.1 (by simpa [gAt_nil] using ha j)
    simpa [gadd, this] using hb j
  | cons x xs ih =>
    cases ys with
    | nil =>
      intro j
      have : b j = 0 := zero_mem_iff.1 (by simpa [gAt_nil] using hb j)
      simpa [gadd, this] using ha j
    | cons y ys =>
      intro j
      cases j with
      | zero => exact mem_add (ha 0) (hb 0)
      | succ j =>
        exact ih (a := fun j => a (j + 1)) (b := fun j => b (j + 1)) (fun j => ha (j + 1))
          (fun j => hb (j + 1)) j

theorem mem_gAt_map {xs : List Ival} {a : ℕ → ℝ} (f : Ival → Ival) (k : ℝ → ℝ)
    (hf : ∀ I c, I.Mem c → (f I).Mem (k c)) (hk : k 0 = 0)
    (ha : ∀ j, (gAt xs j).Mem (a j)) : ∀ j, (gAt (xs.map f) j).Mem (k (a j)) := by
  induction xs generalizing a with
  | nil =>
    intro j
    have : a j = 0 := zero_mem_iff.1 (by simpa [gAt_nil] using ha j)
    simpa [gAt_nil, this, hk] using mem_zero
  | cons x xs ih =>
    intro j
    cases j with
    | zero => exact hf _ _ (ha 0)
    | succ j => exact ih (a := fun j => a (j + 1)) (fun j => ha (j + 1)) j

theorem mem_gAt_unitVec (i : ℕ) : ∀ j, (gAt (unitVec i) j).Mem (if j = i then 1 else 0) := by
  induction i with
  | zero =>
    intro j
    cases j with
    | zero => simpa [unitVec, gAt] using mem_one
    | succ j => simpa [unitVec, gAt, gAt_nil] using mem_zero
  | succ i ih =>
    intro j
    cases j with
    | zero => simpa [unitVec, gAt, List.replicate_succ] using mem_zero
    | succ j =>
      have := ih j
      simpa [unitVec, gAt, List.replicate_succ] using this

theorem gAt_tail (gs : List Ival) (j : ℕ) : gAt gs.tail j = gAt gs (j + 1) := by
  cases gs <;> simp [gAt, gAt_nil]

namespace Slope

theorem bound_sound {s : Slope} {B : List Ival} {ρ : ℕ → ℝ} {y : ℝ} (hB : InBox B ρ)
    (hs : s.Sound B.length (dvec B ρ) y) : (s.bound B).Mem y := by
  obtain ⟨-, v, hv, g, hg, rfl⟩ := hs
  refine mem_add hv ?_
  clear hv
  induction B generalizing ρ g s with
  | nil => simpa [lin] using mem_zero
  | cons b bs ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [lin]
    rw [add_comm]
    refine mem_add (mem_mul (hg 0) ?_) ?_
    · have hb : b.Mem (ρ 0) := hB 0 b rfl
      have := mem_sub hb (mem_point (mid b))
      simpa [dvec, gAt] using this
    · have := ih (ρ := fun j => ρ (j + 1)) (g := fun j => g (j + 1)) (s := ⟨s.r, s.v, s.g.tail⟩)
        (fun i I h => hB (i + 1) I (by simpa using h))
        (fun j => by simpa [gAt_tail] using hg (j + 1))
      simpa [dvec, gAt] using this

theorem sound_const {k : Ival} {c : ℝ} (hk : k.Mem c) (N : ℕ) (d : ℕ → ℝ) :
    (const k).Sound N d c :=
  ⟨hk, c, hk, fun _ => 0, fun j => by simpa [const, gAt_nil] using mem_zero, by simp⟩

theorem sound_add {s t : Slope} {N d y z} (hs : s.Sound N d y) (ht : t.Sound N d z) :
    (s.add t).Sound N d (y + z) := by
  obtain ⟨hr, v, hv, g, hg, rfl⟩ := hs
  obtain ⟨hr', v', hv', g', hg', rfl⟩ := ht
  refine ⟨mem_add hr hr', v + v', mem_add hv hv', fun j => g j + g' j, mem_gAt_gadd hg hg', ?_⟩
  simp only [add_mul, Finset.sum_add_distrib]; ring

theorem sound_neg {s : Slope} {N d y} (hs : s.Sound N d y) : s.neg.Sound N d (-y) := by
  obtain ⟨hr, v, hv, g, hg, rfl⟩ := hs
  refine ⟨mem_neg hr, -v, mem_neg hv, fun j => -g j,
    mem_gAt_map _ (fun c => -c) (fun _ _ h => mem_neg h) (by simp) hg, ?_⟩
  simp only [neg_mul, Finset.sum_neg_distrib]; ring

theorem sound_sub {s t : Slope} {N d y z} (hs : s.Sound N d y) (ht : t.Sound N d z) :
    (s.sub t).Sound N d (y - z) := by
  rw [sub_eq_add_neg]; exact sound_add hs (sound_neg ht)

theorem sound_mul {s t : Slope} {N d y z} (hs : s.Sound N d y) (ht : t.Sound N d z) :
    (s.mul t).Sound N d (y * z) := by
  obtain ⟨hr, v, hv, g, hg, hy⟩ := hs
  obtain ⟨hr', v', hv', g', hg', hz⟩ := ht
  refine ⟨mem_mul hr hr', v * v', mem_mul hv hv', fun j => g j * z + v * g' j,
    mem_gAt_gadd (mem_gAt_map _ (fun c => c * z) (fun _ _ h => mem_mul h hr') (by simp) hg)
      (mem_gAt_map _ (fun c => v * c) (fun _ _ h => mem_mul hv h) (by simp) hg'), ?_⟩
  have e1 : ∑ j ∈ Finset.range N, (g j * z + v * g' j) * d j =
      z * ∑ j ∈ Finset.range N, g j * d j + v * ∑ j ∈ Finset.range N, g' j * d j := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1]
  have hy' : ∑ j ∈ Finset.range N, g j * d j = y - v := by rw [hy]; ring
  have hz' : ∑ j ∈ Finset.range N, g' j * d j = z - v' := by rw [hz]; ring
  rw [hy', hz']; ring

theorem sound_sq {s : Slope} {N d y} (hs : s.Sound N d y) : s.sq.Sound N d (y ^ 2) := by
  obtain ⟨hr, v, hv, g, hg, hy⟩ := hs
  refine ⟨mem_sq hr, v ^ 2, mem_sq hv, fun j => g j * (v + y),
    mem_gAt_map _ (fun c => c * (v + y)) (fun _ _ h => mem_mul h (mem_add hv hr)) (by simp) hg,
    ?_⟩
  have e1 : ∑ j ∈ Finset.range N, g j * (v + y) * d j =
      (v + y) * ∑ j ∈ Finset.range N, g j * d j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hy' : ∑ j ∈ Finset.range N, g j * d j = y - v := by rw [hy]; ring
  rw [e1, hy']; ring

theorem sound_inv {s t : Slope} {N d y} (hs : s.Sound N d y) (ht : s.inv = some t) :
    t.Sound N d y⁻¹ := by
  obtain ⟨hr, v, hv, g, hg, hy⟩ := hs
  simp only [inv, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ht
  obtain ⟨ri, hri, vi, hvi, rfl⟩ := ht
  have hy0 : y ≠ 0 := ne_zero_of_inv hri hr
  have hv0 : v ≠ 0 := ne_zero_of_inv hvi hv
  refine ⟨mem_inv hri hr, v⁻¹, mem_inv hvi hv, fun j => -(g j * y⁻¹ * v⁻¹),
    mem_gAt_map _ (fun c => -(c * y⁻¹ * v⁻¹))
      (fun _ _ h => mem_neg (mem_mul (mem_mul h (mem_inv hri hr)) (mem_inv hvi hv))) (by simp) hg,
    ?_⟩
  have e1 : ∑ j ∈ Finset.range N, -(g j * y⁻¹ * v⁻¹) * d j =
      -(y⁻¹ * v⁻¹) * ∑ j ∈ Finset.range N, g j * d j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hy' : ∑ j ∈ Finset.range N, g j * d j = y - v := by rw [hy]; ring
  rw [e1, hy']; field_simp; ring

theorem sound_pow {s : Slope} {N d y} (hs : s.Sound N d y) : ∀ n, (s.pow n).Sound N d (y ^ n)
  | 0 => by simpa [pow] using sound_const mem_one N d
  | 1 => by simpa [pow] using hs
  | 2 => sound_sq hs
  | n + 3 => by
    rw [pow, _root_.pow_succ]
    exact sound_mul (sound_pow hs (n + 2)) hs

theorem sound_freeze {k : Ival} {c : ℝ} (hk : k.Mem c) (N : ℕ) (d : ℕ → ℝ) :
    (freeze k).Sound N d c := sound_const hk N d

theorem sound_scale (w : ℕ) {s : Slope} {N d y} (hs : s.Sound N d y) :
    (s.scale w).Sound N d (w * y) := by
  obtain ⟨hr, v, hv, g, hg, rfl⟩ := hs
  refine ⟨mem_smul w hr, w * v, mem_smul w hv, fun j => w * g j,
    mem_gAt_map _ (fun c => w * c) (fun _ _ h => mem_smul w h) (by simp) hg, ?_⟩
  rw [mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sound_hornerS {x : Slope} {N d t} (hx : x.Sound N d t) :
    ∀ (cs : List Ival) (rs : List ℝ), List.Forall₂ (fun (c : Ival) r => c.Mem r) cs rs →
      (hornerS x cs).Sound N d (hornerR t rs)
  | [], [], _ => by simpa [hornerS, hornerR] using sound_const mem_zero N d
  | _ :: cs, _ :: rs, .cons h hs =>
    sound_add (sound_const h N d) (sound_mul hx (sound_hornerS hx cs rs hs))

theorem ld24_mem : List.Forall₂ (fun (c : Ival) r => c.Mem r) ld24
    ((List.range 24).map fun k : ℕ => (1 : ℝ) / (2 * (k : ℝ) + 1)) := by
  rw [ld24, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro k _
  have := mem_ofRat 1 (2 * k + 1)
  push_cast at this
  exact this

theorem mem_pow24 {x : Ival} {a : ℝ} (ha : x.Mem a) : (pow24 x).Mem (a ^ 24) := by
  have := mem_sq (mem_sq (mem_sq (mem_mul (mem_sq ha) ha)))
  have e : a ^ 24 = (((a ^ 2 * a) ^ 2) ^ 2) ^ 2 := by ring
  rw [e]; exact this

attribute [local irreducible] ld24 pow24 hornerS in
theorem sound_logDiv {s t : Slope} {N d y} (hs : s.Sound N d y) (ht : s.logDiv = some t) :
    t.Sound N d (logDivR y) := by
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  unfold logDiv at ht
  cases hc : zPos s.r.lo
  · rw [hc] at ht; simp at ht
  rw [hc, Bool.cond_true, Option.bind_eq_some_iff] at ht
  obtain ⟨W, hW, ht⟩ := ht
  dsimp only at ht
  set T := (const Ival.one).sub (W.scale 2) with hTdef
  set T2 := T.sq with hT2def
  cases hc2 : zle (Int.add T2.r.hi 1) (.ofNat (2 ^ prec))
  · rw [hc2] at ht; simp at ht
  rw [hc2, Bool.cond_true, Option.map_eq_some_iff] at ht
  obtain ⟨dd, hdd, rfl⟩ := ht
  have hy0 : 0 < y := by
    have h1 := hs.1.1
    have h2 : (0 : ℝ) < s.r.lo := by exact_mod_cast (zPos_iff _).1 hc
    nlinarith
  have hWs := sound_inv (sound_add hs (sound_const mem_one N d)) hW
  have hTs : T.Sound N d (1 - (2 : ℕ) * (y + 1)⁻¹) := sound_sub (sound_const mem_one N d)
    (sound_scale 2 hWs)
  have hT2s : T2.Sound N d ((1 - (2 : ℕ) * (y + 1)⁻¹) ^ 2) := sound_sq hTs
  set τ : ℝ := (T2.r.hi : ℝ) / 2 ^ prec with hτ
  have hτ1 : τ < 1 := by
    have h := (zle_iff _ _).1 hc2
    simp only [Int.add_def, Int.ofNat_eq_natCast] at h
    have h' : (T2.r.hi : ℝ) + 1 ≤ ((2 ^ prec : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [hτ, div_lt_one hp]; linarith
  have htτ : (1 - 2 * (y + 1)⁻¹) ^ 2 ≤ τ := by
    have := hT2s.1.2
    push_cast at this
    rw [hτ, le_div_iff₀ hp]; exact this
  obtain ⟨R, hR0, hR1, hdec⟩ := logDiv_decomp hy0 24 htτ hτ1
  have hP := sound_hornerS hT2s _ _ ld24_mem
  rw [hornerR_range] at hP
  have hD := mem_inv hdd (mem_sub mem_one (mem_point T2.r.hi))
  have hPD := mem_mul (mem_pow24 (mem_point T2.r.hi)) hD
  have hRm : (⟨0, ((pow24 (point T2.r.hi)).mul dd).hi⟩ : Ival).Mem R := by
    refine mem_zero_to hR0 (le_trans ?_ hPD.2)
    rw [← hτ]
    exact mul_le_mul_of_nonneg_right (by rwa [div_eq_mul_inv] at hR1) hp.le
  have hsum := sound_add hP (sound_const hRm N d)
  have := sound_mul (sound_sub (sound_const mem_one N d) hTs) hsum
  push_cast at this
  rw [hdec]
  convert this using 2
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sound_sqrt {s : Slope} {N d y} (hs : s.Sound N d y) : s.sqrt.Sound N d (Real.sqrt y) := by
  unfold sqrt
  cases hc : (zNonneg s.r.lo && zNonneg s.v.lo)
  · exact sound_freeze (mem_sqrtI hs.1) N d
  rw [Bool.cond_true]
  split
  · rename_i w hw
    obtain ⟨hr, v, hv, g, hg, hy⟩ := hs
    simp only [Bool.and_eq_true] at hc
    have hy0 : 0 ≤ y := nonneg_of_mem hr hc.1
    have hv0 : 0 ≤ v := nonneg_of_mem hv hc.2
    have hsum := mem_add (mem_sqrtI hr) (mem_sqrtI hv)
    have hne := ne_zero_of_inv hw hsum
    have hwm := mem_inv hw hsum
    refine ⟨mem_sqrtI hr, Real.sqrt v, mem_sqrtI hv,
      fun j => g j * (Real.sqrt y + Real.sqrt v)⁻¹,
      mem_gAt_map _ (fun c => c * (Real.sqrt y + Real.sqrt v)⁻¹) (fun _ _ h => mem_mul h hwm)
        (by simp) hg, ?_⟩
    have e1 : ∑ j ∈ Finset.range N, g j * (Real.sqrt y + Real.sqrt v)⁻¹ * d j =
        (Real.sqrt y + Real.sqrt v)⁻¹ * ∑ j ∈ Finset.range N, g j * d j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have hy' : ∑ j ∈ Finset.range N, g j * d j = y - v := by rw [hy]; ring
    rw [e1, hy']
    have hsy := Real.sq_sqrt hy0
    have hsv := Real.sq_sqrt hv0
    field_simp
    nlinarith [hsy, hsv]
  · exact sound_freeze (mem_sqrtI hs.1) N d

theorem sound_atan {s t : Slope} {N d y} (hs : s.Sound N d y) (ht : s.atan = some t) :
    t.Sound N d (Real.arctan y) := by
  simp only [atan, Option.bind_eq_some_iff, Option.map_eq_some_iff] at ht
  obtain ⟨a, ha, b, hb, D, hD, rfl⟩ := ht
  obtain ⟨hr, v, hv, g, hg, hy⟩ := hs
  obtain ⟨ξ, h1, h2, hmvt⟩ := arctan_mvt y v
  have hDm := mem_inv hD (mem_add mem_one (mem_sq (mem_hull_of hr hv h1 h2)))
  refine ⟨mem_atanI ha hr, Real.arctan v, mem_atanI hb hv, fun j => g j * (1 + ξ ^ 2)⁻¹,
    mem_gAt_map _ (fun c => c * (1 + ξ ^ 2)⁻¹) (fun _ _ h => mem_mul h hDm) (by simp) hg, ?_⟩
  have e1 : ∑ j ∈ Finset.range N, g j * (1 + ξ ^ 2)⁻¹ * d j =
      (1 + ξ ^ 2)⁻¹ * ∑ j ∈ Finset.range N, g j * d j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hy' : ∑ j ∈ Finset.range N, g j * d j = y - v := by rw [hy]; ring
  rw [e1, hy']
  linear_combination hmvt

theorem ld8_mem : List.Forall₂ (fun (c : Ival) r => c.Mem r) ld8
    ((List.range 8).map fun k : ℕ => (1 : ℝ) / (2 * (k : ℝ) + 1)) := by
  rw [ld8, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro k _
  have := mem_ofRat 1 (2 * k + 1)
  push_cast at this
  exact this

theorem mem_pow8 {x : Ival} {a : ℝ} (ha : x.Mem a) : (pow8 x).Mem (a ^ 8) := by
  have := mem_sq (mem_sq (mem_sq ha))
  have e : a ^ 8 = ((a ^ 2) ^ 2) ^ 2 := by ring
  rw [e]; exact this

attribute [local irreducible] ld8 pow8 hornerS in
theorem sound_logDiv8 {s t : Slope} {N d y} (hs : s.Sound N d y) (ht : s.logDiv8 = some t) :
    t.Sound N d (logDivR y) := by
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  unfold logDiv8 at ht
  cases hc : zPos s.r.lo
  · rw [hc] at ht; simp at ht
  rw [hc, Bool.cond_true, Option.bind_eq_some_iff] at ht
  obtain ⟨W, hW, ht⟩ := ht
  dsimp only at ht
  set T := (const Ival.one).sub (W.scale 2) with hTdef
  set T2 := T.sq with hT2def
  cases hc2 : zle (Int.add T2.r.hi 1) (.ofNat (2 ^ prec))
  · rw [hc2] at ht; simp at ht
  rw [hc2, Bool.cond_true, Option.map_eq_some_iff] at ht
  obtain ⟨dd, hdd, rfl⟩ := ht
  have hy0 : 0 < y := by
    have h1 := hs.1.1
    have h2 : (0 : ℝ) < s.r.lo := by exact_mod_cast (zPos_iff _).1 hc
    nlinarith
  have hWs := sound_inv (sound_add hs (sound_const mem_one N d)) hW
  have hTs : T.Sound N d (1 - (2 : ℕ) * (y + 1)⁻¹) := sound_sub (sound_const mem_one N d)
    (sound_scale 2 hWs)
  have hT2s : T2.Sound N d ((1 - (2 : ℕ) * (y + 1)⁻¹) ^ 2) := sound_sq hTs
  set τ : ℝ := (T2.r.hi : ℝ) / 2 ^ prec with hτ
  have hτ1 : τ < 1 := by
    have h := (zle_iff _ _).1 hc2
    simp only [Int.add_def, Int.ofNat_eq_natCast] at h
    have h' : (T2.r.hi : ℝ) + 1 ≤ ((2 ^ prec : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [hτ, div_lt_one hp]; linarith
  have htτ : (1 - 2 * (y + 1)⁻¹) ^ 2 ≤ τ := by
    have := hT2s.1.2
    push_cast at this
    rw [hτ, le_div_iff₀ hp]; exact this
  obtain ⟨R, hR0, hR1, hdec⟩ := logDiv_decomp hy0 8 htτ hτ1
  have hP := sound_hornerS hT2s _ _ ld8_mem
  rw [hornerR_range] at hP
  have hD := mem_inv hdd (mem_sub mem_one (mem_point T2.r.hi))
  have hPD := mem_mul (mem_pow8 (mem_point T2.r.hi)) hD
  have hRm : (⟨0, ((pow8 (point T2.r.hi)).mul dd).hi⟩ : Ival).Mem R := by
    refine mem_zero_to hR0 (le_trans ?_ hPD.2)
    rw [← hτ]
    exact mul_le_mul_of_nonneg_right (by rwa [div_eq_mul_inv] at hR1) hp.le
  have hsum := sound_add hP (sound_const hRm N d)
  have := sound_mul (sound_sub (sound_const mem_one N d) hTs) hsum
  push_cast at this
  rw [hdec]
  convert this using 2
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sound_logDivQ {s t : Slope} {N d y} (hs : s.Sound N d y) (ht : s.logDivQ = some t) :
    t.Sound N d (logDivR y) := by
  unfold logDivQ at ht
  cases hc : zPos s.r.lo
  · rw [hc] at ht; simp at ht
  rw [hc, Bool.cond_true] at ht
  dsimp only at ht
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at ht
  obtain ⟨L, hL, i1, hi1, i2, hi2, rfl⟩ := ht
  have hy0 : 0 < y := by
    have h1 := hs.1.1
    have h2 : (0 : ℝ) < s.r.lo := by exact_mod_cast (zPos_iff _).1 hc
    have hp : (0 : ℝ) < 2 ^ prec := by positivity
    nlinarith
  have h1 := sound_sqrt hs
  have h2 := sound_sqrt h1
  have hLs := sound_logDiv8 h2 hL
  have hi1s := sound_inv (sound_add (sound_const mem_one N d) h1) hi1
  have hi2s := sound_inv (sound_add (sound_const mem_one N d) h2) hi2
  have := sound_mul (sound_mul hLs (sound_scale 2 hi2s)) (sound_scale 2 hi1s)
  have hq1 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy0
  rw [logDivR_sqrt hy0, logDivR_sqrt hq1]
  push_cast at this
  exact this

end Slope

namespace IExpr

/-- Slope evaluation on the box `B` (centres `mid Bⱼ`). -/
def evalS (B : List Ival) : IExpr → Option Slope
  | var i => B[i]?.map fun b => ⟨b, point (mid b), unitVec i⟩
  | const n d => some (Slope.const (ofRat n d))
  | add a b => (evalS B a).bind fun s => (evalS B b).map s.add
  | sub a b => (evalS B a).bind fun s => (evalS B b).map s.sub
  | neg a => (evalS B a).map Slope.neg
  | mul a b => (evalS B a).bind fun s => (evalS B b).map s.mul
  | div a b => (evalS B a).bind fun s => (evalS B b).bind fun t => t.inv.map s.mul
  | pow a n => (evalS B a).map fun s => s.pow n
  | sqrt a => (evalS B a).map Slope.sqrt
  | log a => (evalS B a).bind fun s => s.r.logI.map Slope.freeze
  | hlog a => (evalS B a).bind fun s => s.r.hlogI.map Slope.freeze
  | atan a => (evalS B a).bind Slope.atan
  | logdiv a => (evalS B a).bind Slope.logDivQ

theorem getElem?_gAt {B : List Ival} {i : ℕ} {b : Ival} (h : B[i]? = some b) : gAt B i = b := by
  induction B generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simpa [gAt] using h
    | succ i => simpa [gAt] using ih (by simpa using h)

theorem evalS_sound {B : List Ival} {ρ : ℕ → ℝ} (hB : InBox B ρ) :
    ∀ (e : IExpr) {s : Slope}, e.evalS B = some s → s.Sound B.length (dvec B ρ) (e.denote ρ)
  | var i, s, h => by
    simp only [evalS, Option.map_eq_some_iff] at h
    obtain ⟨b, hb, rfl⟩ := h
    have hi : i < B.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; cases hb
    refine ⟨hB i b hb, (mid b : ℝ) / 2 ^ prec, mem_point _, fun j => if j = i then 1 else 0,
      mem_gAt_unitVec i, ?_⟩
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_range, hi, ite_true,
      dvec, getElem?_gAt hb, denote]
    ring
  | const n d, s, h => by
    simp only [evalS, Option.some.injEq] at h; subst h
    exact Slope.sound_const (mem_ofRat n d) _ _
  | add a b, s, h => by
    simp only [evalS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact Slope.sound_add (evalS_sound hB a hx) (evalS_sound hB b hy)
  | sub a b, s, h => by
    simp only [evalS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact Slope.sound_sub (evalS_sound hB a hx) (evalS_sound hB b hy)
  | neg a, s, h => by
    simp only [evalS, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact Slope.sound_neg (evalS_sound hB a hx)
  | mul a b, s, h => by
    simp only [evalS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact Slope.sound_mul (evalS_sound hB a hx) (evalS_sound hB b hy)
  | div a b, s, h => by
    simp only [evalS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
    simp only [denote, div_eq_mul_inv]
    exact Slope.sound_mul (evalS_sound hB a hx) (Slope.sound_inv (evalS_sound hB b hy) hz)
  | pow a n, s, h => by
    simp only [evalS, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact Slope.sound_pow (evalS_sound hB a hx) n
  | sqrt a, s, h => by
    simp only [evalS, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact Slope.sound_sqrt (evalS_sound hB a hx)
  | log a, s, h => by
    simp only [evalS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact Slope.sound_freeze (mem_logI hy (evalS_sound hB a hx).1) _ _
  | hlog a, s, h => by
    simp only [evalS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact Slope.sound_freeze (mem_hlogI hy (evalS_sound hB a hx).1) _ _
  | atan a, s, h => by
    simp only [evalS, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, hy⟩ := h
    exact Slope.sound_atan (evalS_sound hB a hx) hy
  | logdiv a, s, h => by
    simp only [evalS, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, hy⟩ := h
    exact Slope.sound_logDivQ (evalS_sound hB a hx) hy

end IExpr

end SmoothedOctagon.Interval
