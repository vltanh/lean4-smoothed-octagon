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
  `v ∈ V`, `gⱼ ∈ Gⱼ`, where `cⱼ = mid Bⱼ` is the centre. Products use
  `G = G₁·R₂ + V₁·G₂`, reciprocals `G = -G·R⁻¹·V⁻¹`, and the special functions are frozen
  (`V = φ(R)`, `G = 0`), which needs no derivative. `Slope.bound` encloses `e` on the box by
  `V + ∑ⱼ Gⱼ (Bⱼ - cⱼ)`; on boxes of width `w` its overestimation is `O(w²)`.

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
  | sqrt a => (evalS B a).map fun s => Slope.freeze s.r.sqrtI
  | log a => (evalS B a).bind fun s => s.r.logI.map Slope.freeze
  | hlog a => (evalS B a).bind fun s => s.r.hlogI.map Slope.freeze
  | atan a => (evalS B a).bind fun s => s.r.atanI.map Slope.freeze
  | logdiv a => (evalS B a).bind fun s => s.r.logDivI.map Slope.freeze

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
    exact Slope.sound_freeze (mem_sqrtI (evalS_sound hB a hx).1) _ _
  | log a, s, h => by
    simp only [evalS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact Slope.sound_freeze (mem_logI hy (evalS_sound hB a hx).1) _ _
  | hlog a, s, h => by
    simp only [evalS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact Slope.sound_freeze (mem_hlogI hy (evalS_sound hB a hx).1) _ _
  | atan a, s, h => by
    simp only [evalS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact Slope.sound_freeze (mem_atanI hy (evalS_sound hB a hx).1) _ _
  | logdiv a, s, h => by
    simp only [evalS, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact Slope.sound_freeze (mem_logDivI hy (evalS_sound hB a hx).1) _ _

end IExpr

end SmoothedOctagon.Interval
