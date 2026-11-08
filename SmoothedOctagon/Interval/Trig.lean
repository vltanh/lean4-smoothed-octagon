module

public import SmoothedOctagon.Interval.Special
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Interval enclosures of `logDiv` and `arctan`

* `logDivR q = log q/(q - 1)` (`1` at `q = 1`), the function `SmallerShort.logDiv`. With
  `t = (q - 1)/(q + 1) = 1 - 2/(q + 1)`, `logDivR q = (1 - t) ∑ₙ t²ⁿ/(2n + 1)` for `q > 0`, which
  has no singularity at `q = 1`. `Ival.logDivI` evaluates forty terms by Horner's rule on the
  interval `T²` (natural interval extension, no monotonicity needed) and adds the tail
  `[0, τ⁴⁰/(1 - τ)]`, `τ = sup T²`, provided `τ < 1`.
* `arctan`: two half-angle steps `arctan x = 2 arctan (x/(1 + √(1 + x²)))` bring any real
  argument into `|y| ≤ tan(π/8) < 0.42`, where twenty-six terms of the series leave a tail below
  `2⁻⁶⁰` (`Real.two_mul_arctan`, `Complex.hasSum_arctan`); no enclosure of `π` is needed.
  `arctan` is monotone, so `Ival.atanI` encloses the two endpoints.

## Main API

`logDivR`, `Ival.one`, `Ival.logDivI`, `Ival.mem_logDivI`, `Ival.atanI`, `Ival.mem_atanI`,
`arctan_half`, `hasSum_arctan_real`.
-/

@[expose] public section

namespace SmoothedOctagon.Interval

/-- `0 < n`, read off the constructor. -/
def zPos : ℤ → Bool
  | .ofNat (_ + 1) => true
  | _ => false

theorem zPos_iff (n : ℤ) : zPos n = true ↔ 0 < n := by
  rcases n with (_ | n) | n <;> simp [zPos]

/-- `log q/(q - 1)`, `1` at `q = 1`; the same function as
`SmoothedOctagon.Certificates.SmallerShort.logDiv`. -/
noncomputable def logDivR (q : ℝ) : ℝ := if q = 1 then 1 else Real.log q / (q - 1)

namespace Ival

/-- The interval `[1, 1]`. -/
def one : Ival := ⟨.ofNat (2 ^ prec), .ofNat (2 ^ prec)⟩

theorem mem_one : one.Mem 1 := by simp [Mem, one]

/-- The interval `[0, c]`. -/
theorem mem_zero_to {c : ℤ} {b : ℝ} (h0 : 0 ≤ b) (hc : b * 2 ^ prec ≤ c) :
    (⟨0, c⟩ : Ival).Mem b := ⟨by simp only [Int.cast_zero]; positivity, hc⟩

/-! ### `logDiv` -/

/-- The coefficients `1/(2k + 1)`, `k < 40`. -/
def ldCoeffs : List Ival := (List.range 40).map fun k => ofRat 1 (2 * k + 1)

/-- `x⁴⁰` by squarings. -/
def pow40 (x : Ival) : Ival :=
  let x2 := x.sq
  let x4 := x2.sq
  let x5 := x4.mul x
  let x10 := x5.sq
  let x20 := x10.sq
  x20.sq

/-- `logDivR` on an interval with `lo > 0`. -/
def logDivI (x : Ival) : Option Ival :=
  match x.lo with
  | .ofNat (_ + 1) =>
    (x.add one).inv.bind fun w =>
      let T := one.sub (w.smul 2)
      let T2 := T.sq
      cond (zle (Int.add T2.hi 1) (.ofNat (2 ^ prec)))
        ((one.sub (point T2.hi)).inv.map fun d =>
          (one.sub T).mul ((hornerI T2 ldCoeffs).add ⟨0, ((pow40 (point T2.hi)).mul d).hi⟩))
        none
  | _ => none

/-! ### `arctan` -/

/-- The coefficients `(-1)ᵏ/(2k + 1)`, `k < 26`. -/
def atCoeffs : List Ival :=
  (List.range 26).map fun k => ofRat (cond (Nat.beq (k % 2) 0) 1 (-1)) (2 * k + 1)

/-- `y ↦ y/(1 + √(1 + y²))`, the half-angle map of `arctan`. -/
def halfI (Y : Ival) : Option Ival := (one.add (one.add Y.sq).sqrtI).inv.map Y.mul

/-- `arctan` on an interval with `y² ≤ 0.1764` (twenty-six terms, one unit for the tail). -/
def atanSmall (Y : Ival) : Option Ival :=
  let Y2 := Y.sq
  cond (zle (Int.mul 10000 Y2.hi) (Int.mul 1764 (.ofNat (2 ^ prec))))
    (let S := Y.mul (hornerI Y2 atCoeffs)
     some ⟨Int.sub S.lo 1, Int.add S.hi 1⟩)
    none

/-- `arctan (m/2^prec)`. -/
def atanPt (m : ℤ) : Option Ival :=
  (halfI (point m)).bind fun y1 => (halfI y1).bind fun y2 => (atanSmall y2).map (smul 4)

/-- `arctan` on an interval (monotone). -/
def atanI (x : Ival) : Option Ival :=
  (atanPt x.lo).bind fun a => (atanPt x.hi).map fun b => ⟨a.lo, b.hi⟩

end Ival

/-! ### Real analysis -/

/-- The series of `logDivR`. -/
theorem logDiv_hasSum {t : ℝ} (ht : |t| < 1) :
    HasSum (fun k : ℕ => (t ^ 2) ^ k / (2 * k + 1)) (logDivR ((1 + t) / (1 - t)) / (1 - t)) := by
  have h1 : 0 < 1 - t := by linarith [(abs_lt.1 ht).2]
  have h2 : 0 < 1 + t := by linarith [(abs_lt.1 ht).1]
  rcases eq_or_ne t 0 with rfl | ht0
  · have e : logDivR ((1 + 0) / (1 - 0)) / (1 - 0) =
        (fun k : ℕ => ((0 : ℝ) ^ 2) ^ k / (2 * k + 1)) 0 := by simp [logDivR]
    rw [e]
    exact hasSum_single 0 fun k hk => by simp [hk]
  · have hq : (1 + t) / (1 - t) ≠ 1 := by
      intro h; rw [div_eq_one_iff_eq h1.ne'] at h; exact ht0 (by linarith)
    have hs := (Real.hasSum_log_sub_log_of_abs_lt_one ht).div_const (2 * t)
    convert hs using 1
    · funext k
      rw [show t ^ (2 * k + 1) = (t ^ 2) ^ k * t by rw [pow_succ, pow_mul]]
      field_simp
    · rw [logDivR, ite_eq_right_of_eq_false _ _ (eq_false hq), Real.log_div h2.ne' h1.ne']
      have : (1 + t) / (1 - t) - 1 = 2 * t / (1 - t) := by field_simp; ring
      rw [this]; field_simp

/-- Tail of `∑ sᵏ/(2k + 1)`. -/
theorem odd_tail_bounds {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) {L : ℝ}
    (h : HasSum (fun k : ℕ => s ^ k / (2 * k + 1)) L) (N : ℕ) :
    0 ≤ L - ∑ k ∈ Finset.range N, s ^ k / (2 * k + 1) ∧
      L - ∑ k ∈ Finset.range N, s ^ k / (2 * k + 1) ≤ s ^ N / (1 - s) := by
  have htail := (hasSum_nat_add_iff' N).2 h
  refine ⟨htail.nonneg fun k => by positivity, ?_⟩
  have hg := (hasSum_geometric_of_lt_one hs0 hs1).mul_left (s ^ N)
  have := hasSum_le (fun k => ?_) htail hg
  · simpa [div_eq_mul_inv] using this
  · have hk : (1 : ℝ) ≤ 2 * ((k + N : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((k + N : ℕ) : ℝ) := by positivity
      linarith
    calc s ^ (k + N) / (2 * ((k + N : ℕ) : ℝ) + 1) ≤ s ^ (k + N) :=
          div_le_self (by positivity) hk
      _ = s ^ N * s ^ k := by ring

/-- `logDivR q = (1 - t)(∑_{k<N} t²ᵏ/(2k + 1) + R)`, `t = 1 - 2/(q + 1)`, with
`0 ≤ R ≤ τᴺ/(1 - τ)` whenever `t² ≤ τ < 1`. -/
theorem logDiv_decomp {q τ : ℝ} (hq : 0 < q) (N : ℕ) (hτ : (1 - 2 * (q + 1)⁻¹) ^ 2 ≤ τ)
    (hτ1 : τ < 1) :
    ∃ R, 0 ≤ R ∧ R ≤ τ ^ N / (1 - τ) ∧
      logDivR q = (1 - (1 - 2 * (q + 1)⁻¹)) *
        (∑ k ∈ Finset.range N, ((1 - 2 * (q + 1)⁻¹) ^ 2) ^ k / (2 * (k : ℝ) + 1) + R) := by
  set t := 1 - 2 * (q + 1)⁻¹ with htdef
  have hs0 : 0 ≤ t ^ 2 := sq_nonneg t
  have ht1 : |t| < 1 := by rw [← sq_lt_one_iff_abs_lt_one]; linarith
  have hqt : (1 + t) / (1 - t) = q := by
    have : q + 1 ≠ 0 := by linarith
    rw [htdef]; field_simp; ring
  have hsum := logDiv_hasSum ht1
  rw [hqt] at hsum
  obtain ⟨b1, b2⟩ := odd_tail_bounds hs0 (by linarith) hsum N
  refine ⟨logDivR q / (1 - t) - ∑ k ∈ Finset.range N, (t ^ 2) ^ k / (2 * (k : ℝ) + 1), b1, ?_, ?_⟩
  · refine le_trans b2 ?_
    have hτ0 : 0 ≤ τ := le_trans hs0 hτ
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul (pow_le_pow_left₀ hs0 hτ N) (inv_anti₀ (by linarith) (by linarith))
      (inv_nonneg.2 (by linarith)) (by positivity)
  · have : 1 - t ≠ 0 := by linarith [(abs_lt.1 ht1).2]
    field_simp; ring

/-- The square-root reduction `logDivR q = 2 logDivR(√q)/(1 + √q)`. -/
theorem logDivR_sqrt {q : ℝ} (hq : 0 < q) :
    logDivR q = logDivR (Real.sqrt q) * (2 * (1 + Real.sqrt q)⁻¹) := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hs2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  by_cases h1 : q = 1
  · subst h1; simp [logDivR]; norm_num
  have hs1 : Real.sqrt q ≠ 1 := by
    intro h; apply h1; rw [← hs2, h]; norm_num
  have hlog : Real.log q = 2 * Real.log (Real.sqrt q) := by
    rw [Real.log_sqrt hq.le]; ring
  simp only [logDivR, h1, hs1, ↓reduceIte]
  rw [hlog]
  have e : q - 1 = (Real.sqrt q - 1) * (1 + Real.sqrt q) := by nlinarith
  rw [e]
  have h3 : Real.sqrt q - 1 ≠ 0 := sub_ne_zero.2 hs1
  have h4 : 1 + Real.sqrt q ≠ 0 := by linarith
  field_simp

theorem hasSum_arctan_real {y : ℝ} (hy : |y| < 1) :
    HasSum (fun n : ℕ => (-1) ^ n * y ^ (2 * n + 1) / (2 * n + 1)) (Real.arctan y) := by
  have h := Complex.hasSum_arctan (z := (y : ℂ)) (by simpa [Complex.norm_real] using hy)
  rw [← Complex.ofReal_arctan] at h
  have e : (fun n : ℕ => (-1 : ℂ) ^ n * (y : ℂ) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℂ)) =
      fun n : ℕ => (((-1 : ℝ) ^ n * y ^ (2 * n + 1) / (2 * (n : ℝ) + 1) : ℝ) : ℂ) := by
    funext n; push_cast; ring
  rw [e] at h
  exact Complex.hasSum_ofReal.1 h

theorem atan_num : (1 : ℝ) / 2 * (1764 / 10000) ^ 26 * (1 - 1764 / 10000)⁻¹ ≤ 1 / 2 ^ prec := by
  norm_num [prec]

/-- The series of `arctan` with twenty-six terms, for `y² ≤ 0.1764`. -/
theorem arctan_series_bound {y : ℝ} (hy : y ^ 2 ≤ 1764 / 10000) :
    |Real.arctan y - ∑ n ∈ Finset.range 26, (-1) ^ n * y ^ (2 * n + 1) / (2 * n + 1)| ≤
      1 / 2 ^ prec := by
  have hy2 : |y| ≤ 1 / 2 := by
    rw [← sq_le_sq₀ (abs_nonneg y) (by norm_num), sq_abs]; linarith
  have hy1 : |y| < 1 := by linarith
  have h := hasSum_arctan_real hy1
  have htail := (hasSum_nat_add_iff' 26).2 h
  have hs0 : 0 ≤ y ^ 2 := sq_nonneg y
  have hs1 : y ^ 2 < 1 := by nlinarith
  have hg := (hasSum_geometric_of_lt_one hs0 hs1).mul_left (|y| ^ 53)
  have hterm : ∀ n : ℕ, |(-1) ^ (n + 26) * y ^ (2 * (n + 26) + 1) / (2 * ((n + 26 : ℕ) : ℝ) + 1)| ≤
      |y| ^ 53 * (y ^ 2) ^ n := fun n => by
    have hk : (1 : ℝ) ≤ 2 * ((n + 26 : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((n + 26 : ℕ) : ℝ) := by positivity
      linarith
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
      abs_of_pos (by linarith : (0 : ℝ) < 2 * ((n + 26 : ℕ) : ℝ) + 1)]
    calc |y| ^ (2 * (n + 26) + 1) / (2 * ((n + 26 : ℕ) : ℝ) + 1) ≤ |y| ^ (2 * (n + 26) + 1) :=
          div_le_self (by positivity) hk
      _ = |y| ^ 53 * (y ^ 2) ^ n := by
          rw [← sq_abs y]; ring
  have up := hasSum_le (fun n => le_trans (le_abs_self _) (hterm n)) htail hg
  have lo := hasSum_le (fun n => neg_le.2 (neg_le_of_abs_le (hterm n))) htail.neg hg
  have hb : |y| ^ 53 * (1 - y ^ 2)⁻¹ ≤ 1 / 2 ^ prec := by
    have e53 : |y| ^ 53 = |y| * (y ^ 2) ^ 26 := by rw [← sq_abs y]; ring
    have p1 : (y ^ 2) ^ 26 ≤ (1764 / 10000) ^ 26 := pow_le_pow_left₀ hs0 hy 26
    have p2 : (1 - y ^ 2)⁻¹ ≤ (1 - 1764 / 10000)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    have q1 : |y| * (y ^ 2) ^ 26 ≤ 1 / 2 * (1764 / 10000) ^ 26 :=
      mul_le_mul hy2 p1 (by positivity) (by norm_num)
    have q2 := mul_le_mul q1 p2 (inv_nonneg.2 (by linarith)) (by positivity)
    rw [e53]; exact le_trans q2 atan_num
  rw [abs_le]; constructor <;> linarith

/-- Mean value theorem for `arctan`: `arctan y - arctan v = (y - v)/(1 + ξ²)` for some `ξ`
between `v` and `y`. -/
theorem arctan_mvt (y v : ℝ) :
    ∃ ξ, min y v ≤ ξ ∧ ξ ≤ max y v ∧ Real.arctan y - Real.arctan v = (y - v) * (1 + ξ ^ 2)⁻¹ := by
  rcases lt_trichotomy v y with h | rfl | h
  · obtain ⟨c, hc, hd⟩ := exists_deriv_eq_slope Real.arctan h
      Real.continuous_arctan.continuousOn Real.differentiable_arctan.differentiableOn
    rw [Real.deriv_arctan] at hd
    refine ⟨c, by rw [min_eq_right h.le]; exact hc.1.le, by rw [max_eq_left h.le]; exact hc.2.le, ?_⟩
    have hne : y - v ≠ 0 := sub_ne_zero.2 h.ne'
    simp only at hd
    rw [eq_div_iff hne] at hd
    rw [← hd]; ring
  · exact ⟨v, min_le_left _ _, le_max_left _ _, by ring⟩
  · obtain ⟨c, hc, hd⟩ := exists_deriv_eq_slope Real.arctan h
      Real.continuous_arctan.continuousOn Real.differentiable_arctan.differentiableOn
    rw [Real.deriv_arctan] at hd
    refine ⟨c, by rw [min_eq_left h.le]; exact hc.1.le, by rw [max_eq_right h.le]; exact hc.2.le, ?_⟩
    have hne : v - y ≠ 0 := sub_ne_zero.2 h.ne'
    simp only at hd
    rw [eq_div_iff hne] at hd
    linear_combination hd

/-- The half-angle step. -/
theorem arctan_half (x : ℝ) :
    Real.arctan x = 2 * Real.arctan (x * (1 + Real.sqrt (1 + x ^ 2))⁻¹) := by
  set s := Real.sqrt (1 + x ^ 2) with hsdef
  have hs2 : s ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hxs : |x| < 1 + s := by
    have : |x| ≤ s := Real.abs_le_sqrt (by linarith)
    linarith
  have hp : 0 < 1 + s := by linarith
  have hy1 : -1 < x * (1 + s)⁻¹ := by
    rw [← div_eq_mul_inv, lt_div_iff₀ hp]; linarith [neg_abs_le x]
  have hy2 : x * (1 + s)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hp]; linarith [le_abs_self x]
  rw [Real.two_mul_arctan hy1 hy2]
  congr 1
  have e1 : 1 - (x * (1 + s)⁻¹) ^ 2 = 2 * (1 + s)⁻¹ := by
    field_simp; nlinarith [hs2]
  rw [e1]; field_simp

namespace Ival

theorem mem_pow40 {x : Ival} {a : ℝ} (ha : x.Mem a) : (pow40 x).Mem (a ^ 40) := by
  have := mem_sq (mem_sq (mem_sq (mem_mul (mem_sq (mem_sq ha)) ha)))
  have e : a ^ 40 = ((((a ^ 2) ^ 2 * a) ^ 2) ^ 2) ^ 2 := by ring
  rw [e]; exact this

theorem ldCoeffs_mem : List.Forall₂ (fun (c : Ival) r => c.Mem r) ldCoeffs
    ((List.range 40).map fun k : ℕ => (1 : ℝ) / (2 * (k : ℝ) + 1)) := by
  rw [ldCoeffs, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro k _
  have := mem_ofRat 1 (2 * k + 1)
  push_cast at this
  exact this

theorem atCoeffs_mem : List.Forall₂ (fun (c : Ival) r => c.Mem r) atCoeffs
    ((List.range 26).map fun k : ℕ => (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1)) := by
  rw [atCoeffs, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro k _
  have := mem_ofRat (cond (Nat.beq (k % 2) 0) 1 (-1)) (2 * k + 1)
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at this
  convert this using 2
  rcases Nat.even_or_odd k with he | ho
  · have : k % 2 = 0 := Nat.even_iff.1 he
    simp [this, he.neg_one_pow]
  · have : k % 2 = 1 := Nat.odd_iff.1 ho
    simp [this, ho.neg_one_pow]

attribute [local irreducible] ldCoeffs pow40 hornerI in
theorem mem_logDivI {x y : Ival} {q : ℝ} (hx : x.logDivI = some y) (hq : x.Mem q) :
    y.Mem (logDivR q) := by
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  obtain ⟨lo, hi⟩ := x
  rcases lo with (_ | l) | l
  · simp [logDivI] at hx
  swap
  · simp [logDivI] at hx
  simp only [logDivI, Option.bind_eq_some_iff] at hx
  obtain ⟨w, hw, hy⟩ := hx
  set T := one.sub (w.smul 2) with hTdef
  set T2 := T.sq with hT2def
  cases hc : zle (Int.add T2.hi 1) (.ofNat (2 ^ prec))
  · rw [hc] at hy; simp at hy
  rw [hc, Bool.cond_true, Option.map_eq_some_iff] at hy
  obtain ⟨d, hd, rfl⟩ := hy
  -- the real quantities
  have hq0 : 0 < q := by
    have h1 := hq.1
    simp only [Int.ofNat_eq_natCast, Nat.cast_succ] at h1
    push_cast at h1
    nlinarith [(by positivity : (0 : ℝ) ≤ l)]
  have hwq := mem_inv hw (mem_add hq mem_one)
  set t : ℝ := 1 - (2 : ℕ) * (q + 1)⁻¹ with htdef
  have hT : T.Mem t := mem_sub mem_one (mem_smul 2 hwq)
  have hT2 : T2.Mem (t ^ 2) := mem_sq hT
  set τ : ℝ := (T2.hi : ℝ) / 2 ^ prec with hτ
  have hτ1 : τ < 1 := by
    have h := (zle_iff _ _).1 hc
    simp only [Int.add_def, Int.ofNat_eq_natCast] at h
    have h' : (T2.hi : ℝ) + 1 ≤ ((2 ^ prec : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [hτ, div_lt_one hp]; linarith
  have htτ : t ^ 2 ≤ τ := by rw [hτ, le_div_iff₀ hp]; exact hT2.2
  have hs0 : 0 ≤ t ^ 2 := sq_nonneg t
  have ht1 : |t| < 1 := by
    rw [← sq_lt_one_iff_abs_lt_one]; linarith
  have hqt : (1 + t) / (1 - t) = q := by
    have : q + 1 ≠ 0 := by linarith
    rw [htdef]; push_cast; field_simp; ring
  have hsum := logDiv_hasSum ht1
  rw [hqt] at hsum
  obtain ⟨b1, b2⟩ := odd_tail_bounds hs0 (by linarith) hsum 40
  -- the enclosures
  have hH := mem_hornerI hT2 _ _ ldCoeffs_mem
  rw [hornerR_range] at hH
  have hP := mem_pow40 (mem_point T2.hi)
  have hD := mem_inv hd (mem_sub mem_one (mem_point T2.hi))
  have hPD := mem_mul hP hD
  set L := logDivR q / (1 - t)
  set S0 := ∑ k ∈ Finset.range 40, (t ^ 2) ^ k / (2 * (k : ℝ) + 1)
  have eS0 : ∑ k ∈ Finset.range 40, 1 / (2 * (k : ℝ) + 1) * (t ^ 2) ^ k = S0 :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [eS0] at hH
  have htail : L - S0 ≤ τ ^ 40 * (1 - τ)⁻¹ := by
    refine le_trans b2 ?_
    have hτ0 : 0 ≤ τ := le_trans hs0 htτ
    have a1 : (t ^ 2) ^ 40 ≤ τ ^ 40 := pow_le_pow_left₀ hs0 htτ 40
    have a2 : (1 - t ^ 2)⁻¹ ≤ (1 - τ)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    rw [div_eq_mul_inv]
    exact mul_le_mul a1 a2 (inv_nonneg.2 (by linarith)) (by positivity)
  have hR : (⟨0, ((pow40 (point T2.hi)).mul d).hi⟩ : Ival).Mem (L - S0) :=
    mem_zero_to b1 (le_trans (mul_le_mul_of_nonneg_right htail hp.le) hPD.2)
  have hS := mem_add hH hR
  rw [show S0 + (L - S0) = L by ring] at hS
  have := mem_mul (mem_sub mem_one hT) hS
  have e : (1 - t) * L = logDivR q := by
    have : 1 - t ≠ 0 := by linarith [(abs_lt.1 ht1).2]
    simp only [L]; field_simp
  rw [e] at this
  exact this

theorem mem_halfI {Y Z : Ival} {y : ℝ} (h : halfI Y = some Z) (hy : Y.Mem y) :
    Z.Mem (y * (1 + Real.sqrt (1 + y ^ 2))⁻¹) := by
  simp only [halfI, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  exact mem_mul hy (mem_inv hw (mem_add mem_one (mem_sqrtI (mem_add mem_one (mem_sq hy)))))

attribute [local irreducible] atCoeffs hornerI in
theorem mem_atanSmall {Y Z : Ival} {y : ℝ} (h : atanSmall Y = some Z) (hy : Y.Mem y) :
    Z.Mem (Real.arctan y) := by
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  unfold atanSmall at h
  dsimp only at h
  cases hc : zle (Int.mul 10000 Y.sq.hi) (Int.mul 1764 (.ofNat (2 ^ prec)))
  · rw [hc] at h; simp at h
  rw [hc, Bool.cond_true, Option.some.injEq] at h
  subst h
  have hY2 := mem_sq hy
  have hy2 : y ^ 2 ≤ 1764 / 10000 := by
    have h1 := (zle_iff _ _).1 hc
    simp only [Int.mul_def, Int.ofNat_eq_natCast] at h1
    have h1' : (10000 : ℝ) * Y.sq.hi ≤ 1764 * ((2 ^ prec : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at h1'
    have := hY2.2
    rw [div_eq_mul_inv, ← sub_nonneg]
    nlinarith
  have hS := mem_mul hy (mem_hornerI hY2 _ _ atCoeffs_mem)
  rw [hornerR_range] at hS
  have e : y * ∑ k ∈ Finset.range 26, (-1) ^ k / (2 * (k : ℝ) + 1) * (y ^ 2) ^ k =
      ∑ n ∈ Finset.range 26, (-1) ^ n * y ^ (2 * n + 1) / (2 * n + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by
      rw [show y ^ (2 * k + 1) = (y ^ 2) ^ k * y by rw [pow_succ, pow_mul]]; ring
  rw [e] at hS
  have hb := abs_le.1 (arctan_series_bound hy2)
  obtain ⟨s1, s2⟩ := hS
  have e1 : (1 : ℝ) / 2 ^ prec * 2 ^ prec = 1 := by field_simp
  simp only [Mem, zsub_def, Int.add_def]
  push_cast
  constructor <;> nlinarith

theorem mem_atanPt {m : ℤ} {Z : Ival} (h : atanPt m = some Z) :
    Z.Mem (Real.arctan ((m : ℝ) / 2 ^ prec)) := by
  simp only [atanPt, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨y1, h1, y2, h2, s, h3, rfl⟩ := h
  have m1 := mem_halfI h1 (mem_point m)
  have m2 := mem_halfI h2 m1
  have m3 := mem_smul 4 (mem_atanSmall h3 m2)
  rw [Nat.cast_ofNat] at m3
  set y1v := (m : ℝ) / 2 ^ prec * (1 + Real.sqrt (1 + ((m : ℝ) / 2 ^ prec) ^ 2))⁻¹
  have e : Real.arctan ((m : ℝ) / 2 ^ prec) =
      4 * Real.arctan (y1v * (1 + Real.sqrt (1 + y1v ^ 2))⁻¹) := by
    rw [arctan_half ((m : ℝ) / 2 ^ prec), arctan_half y1v]; ring
  rw [e]; exact m3

attribute [local irreducible] atanPt in
theorem mem_atanI {x y : Ival} {a : ℝ} (hx : x.atanI = some y) (ha : x.Mem a) :
    y.Mem (Real.arctan a) := by
  have hp : (0 : ℝ) < 2 ^ prec := by positivity
  simp only [atanI, Option.bind_eq_some_iff, Option.map_eq_some_iff] at hx
  obtain ⟨A, hA, B, hB, rfl⟩ := hx
  have m1 : (x.lo : ℝ) / 2 ^ prec ≤ a := by rw [div_le_iff₀ hp]; exact ha.1
  have m2 : a ≤ (x.hi : ℝ) / 2 ^ prec := by rw [le_div_iff₀ hp]; exact ha.2
  have k1 := Real.arctan_strictMono.monotone m1
  have k2 := Real.arctan_strictMono.monotone m2
  obtain ⟨p1, -⟩ := mem_atanPt hA
  obtain ⟨-, q2⟩ := mem_atanPt hB
  exact ⟨le_trans p1 (by nlinarith), le_trans (by nlinarith) q2⟩

end Ival

end SmoothedOctagon.Interval
