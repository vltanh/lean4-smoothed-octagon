module

public import SmoothedOctagon.Period.Elliptic
public import SmoothedOctagon.Exclusion.Forward.Scalar
public import SmoothedOctagon.Exclusion.Forward.Cap

/-!
# Wiring `Period/Elliptic` to the case-F and case-M2 interfaces

The facts about the normal multiplier and the window of a global minimum that
`Exclusion/Forward/Interface` and `Exclusion/Mixed/Interface` state, proved on a
`CostateCycle` from the API of `Period/Elliptic` (`mu`, `wt`, `swd`, `cre`, `Mloc`, `stationarity`,
`gram_pp`, `Λ₁_zero_neg`, …), in the conventions of the interfaces: `u = 8 d`, `E = 16 e`, the
cost derivative `ff_Cph p a n = (G_a(a,p) + G_a(a,n))/2 = 4 J_a`.

## Main API

* `wire_Cph_eq`: `ff_Cph p a n = (elGa a p + elGa a n)/2`.
* `CostateCycle.wire_Mloc_apply`, `wire_Mloc_00`, `wire_Mloc_01_fwd`, `wire_Mloc_10_fwd`,
  `wire_Mloc_10_next`, `wire_wt_grow`, `wire_wt_decr`, `wire_norm_fwd`, `wire_norm_rev`: the entries of
  `M_k` in the weights `w`, and eight times the switch norms read in the frame of piece `k`.
* `CostateCycle.wire_stat_w`, `wire_stat_M`: stationarity at a same-sign piece,
  `8 s d + 8 s' d' - 16 a e = 4 J_a`.
* `CostateCycle.wire_w_rel`: the transport of `w` across a doubly forward piece.
* `wire_rows_alg`: the three stationarity rows of the window from three stationarity identities and
  two transports.
* `wire_mc_alg`, `CostateCycle.wire_mc`: **the missing-control inequality** at a forward switch:
  `σ_{missing} = -4√3 G_L/s²`, so `G_L ≥ 0`.
* `wire_floor_out_alg`, `wire_floor_in_alg`, `CostateCycle.wire_floor_out`, `wire_floor_in`: **the
  exterior floors** at a doubly forward piece.
* `NormalPeriod.wire_gam2_pos_of_allForward`: `γ² > 0` for an all-forward period (the projective
  argument of `gam2_pos_of_mixed`, every increment being positive).
* `NormalPeriod.wire_S00_pos`, `wire_negEll`: `γ² > 0` and one positive switch norm give `S₀₀ > 0`,
  hence negative ellipticity of `Λ₁(0)`.
* `wire_spec_key` (the pointwise spectral inequality `(ρ + ρ_R)² ≤ 4|z|²ρρ_R`), `wire_winding` (the
  polar angle integrates to at least `π/3`), and `NormalPeriod.wire_spectral`: **the spectral
  cost–Casimir bound** `C ≥ (π/3)(κ + 3/2)` for negative elliptic `Λ₁(0)`.
* `wire_gam2_cap`: the competitive cap from the exact positive-moment cost ratio;
  `(π/3)(κ + 3/2) ≤ C ≤ A_oct ⇒ γ² = κ²/12 < 9193/50000`.
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Real Set

private lemma wire_s3pos : (0 : ℝ) < √3 := by positivity

/-- `ff_Cph p a n = (G_a(a, p) + G_a(a, n))/2`, four times the cost derivative `J_a`. -/
theorem wire_Cph_eq {p a n : ℝ} (hp : 0 < p) (ha : 0 < a) (hn : 0 < n) :
    ff_Cph p a n = (elGa a p + elGa a n) / 2 := by
  simp only [ff_Cph, ff_fac, elGa]
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    add_comm p a]
  field_simp
  ring

/-! ### Algebraic cores -/

/-- The three stationarity rows of the window, from the stationarity identities at the pieces `b`,
`a`, `c` and the transports of `w` across the pieces `a` and `c`. -/
theorem wire_rows_alg {p b a c d h q k wmm wm w0 wp wpp : ℝ} (hp : 0 < p) (hb : 0 < b)
    (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hh : h * (b ^ 2 + 4) = (p + b) * (b + a)) (hq : q * (a ^ 2 + 4) = (b + a) * (a + c))
    (hk : k * (c ^ 2 + 4) = (a + c) * (c + d))
    (hrelL : wmm + wm = h ^ 2 * (wm - w0 + (w0 + wp) / q ^ 2))
    (hrelR : wm + w0 = q ^ 2 * (w0 - wp + (wp + wpp) / k ^ 2))
    (sL : 4 * (wmm + wm) / (p + b) + 4 * (wm + w0) / (b + a) - 8 * b * wm / (b ^ 2 + 4) =
      ff_Cph p b a)
    (s0 : 4 * (wm + w0) / (b + a) + 4 * (w0 + wp) / (a + c) - 8 * a * w0 / (a ^ 2 + 4) =
      ff_Cph b a c)
    (sR : 4 * (w0 + wp) / (a + c) + 4 * (wp + wpp) / (c + d) - 8 * c * wp / (c ^ 2 + 4) =
      ff_Cph a c d) :
    (a + b) * (4 * (wm + w0) / (b + a) ^ 2) + (a + c) * (4 * (w0 + wp) / (a + c) ^ 2) -
        a * (8 * w0 / (a ^ 2 + 4)) = ff_Cph b a c ∧
      ff_Mn a b (ff_fac p b a) * (4 * (wm + w0) / (b + a) ^ 2) +
          ff_Mm a b (ff_fac b a c) (ff_fac p b a) * (4 * (w0 + wp) / (a + c) ^ 2) =
        ff_Mal a b (ff_fac p b a) * ff_Cph b a c - ff_Cph p b a ∧
      ff_Mm a c (ff_fac b a c) (ff_fac a c d) * (4 * (wm + w0) / (b + a) ^ 2) +
          ff_Mn a c (ff_fac a c d) * (4 * (w0 + wp) / (a + c) ^ 2) =
        ff_Mal a c (ff_fac a c d) * ff_Cph b a c - ff_Cph a c d := by
  have hK : 0 < a ^ 2 + 4 := by positivity
  have hKb : 0 < b ^ 2 + 4 := by positivity
  have hKc : 0 < c ^ 2 + 4 := by positivity
  have eh : ff_fac p b a = h := by simp only [ff_fac]; field_simp; linarith
  have eq : ff_fac b a c = q := by simp only [ff_fac]; field_simp; linarith
  have ek : ff_fac a c d = k := by simp only [ff_fac]; field_simp; linarith
  have hh' : h = (p + b) * (b + a) / (b ^ 2 + 4) := by field_simp; linarith
  have hq' : q = (b + a) * (a + c) / (a ^ 2 + 4) := by field_simp; linarith
  have hk' : k = (a + c) * (c + d) / (c ^ 2 + 4) := by field_simp; linarith
  have hhpos : 0 < h := by rw [hh']; positivity
  have hqpos : 0 < q := by rw [hq']; positivity
  have hkpos : 0 < k := by rw [hk']; positivity
  have ewmm : wmm = h ^ 2 * (wm - w0 + (w0 + wp) / q ^ 2) - wm := by linarith
  have ewpp : wpp = k ^ 2 * ((wm + w0) / q ^ 2 - w0 + wp) - wp := by
    field_simp at hrelR ⊢; linarith
  rw [eh, eq, ek, ← sL, ← s0, ← sR, ewmm, ewpp]
  simp only [ff_Mn, ff_Mm, ff_Mal]
  rw [hh', hq', hk']
  refine ⟨?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring

/-- **The missing-control identity** in coordinates: at a forward switch into a piece of label `i`
with margins `x = m_i`, `y = m_{i-1}`, `z = m_{i+1}`, costate coordinates `A_j = α_j`, `B_j = β_j`
and `σ_i = σ_{i-1} = 0`, the missing `σ_{i+1}` is `-4√3 G_L/(x + y)²`; hence `G_L ≥ 0`. -/
theorem wire_mc_alg {x y z A0 Am Ap B0 Bm Bp : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : x * z + z * y + y * x = 4) (h0 : 2 * A0 + B0 = 0) (hm : 2 * Am + Bm = 0)
    (hperp : B0 * (z + y) + Bp * (x + y) + Bm * (x + z) = 0) (hσ : 2 * Ap + Bp ≤ 0) :
    0 ≤ 4 * x * (y + x) * (-(-(A0 / (2 * √3)) - (x + z + y) * x / 4 + 1 / 2) / 2) +
      2 * (x ^ 2 + 4) * (((-(A0 / (2 * √3)) - (x + z + y) * x / 4 + 1 / 2) +
        (-(Am / (2 * √3)) - (x + z + y) * y / 4 + 1 / 2)) / 2) -
      2 * (y + x) ^ 2 * (-((-(A0 / (2 * √3)) - (x + z + y) * x / 4 + 1 / 2) +
        (-(Ap / (2 * √3)) - (x + z + y) * z / 4 + 1 / 2)) / 2) +
      y * (y + x) + (x ^ 2 + 4) := by
  have h3 := wire_s3pos
  have hxy : 0 < x + y := by linarith
  have ez : z = (4 - x * y) / (x + y) := by field_simp; linarith
  have eBp : Bp = -(B0 * (z + y) + Bm * (x + z)) / (x + y) := by field_simp; linarith
  have eB0 : B0 = -2 * A0 := by linarith
  have eBm : Bm = -2 * Am := by linarith
  have key : 4 * x * (y + x) * (-(-(A0 / (2 * √3)) - (x + z + y) * x / 4 + 1 / 2) / 2) +
      2 * (x ^ 2 + 4) * (((-(A0 / (2 * √3)) - (x + z + y) * x / 4 + 1 / 2) +
        (-(Am / (2 * √3)) - (x + z + y) * y / 4 + 1 / 2)) / 2) -
      2 * (y + x) ^ 2 * (-((-(A0 / (2 * √3)) - (x + z + y) * x / 4 + 1 / 2) +
        (-(Ap / (2 * √3)) - (x + z + y) * z / 4 + 1 / 2)) / 2) +
      y * (y + x) + (x ^ 2 + 4) = -((x + y) ^ 2 * (2 * Ap + Bp)) / (4 * √3) := by
    rw [eBp, eB0, eBm, ez]
    field_simp
    ring
  rw [key]
  have : 0 ≤ -((x + y) ^ 2 * (2 * Ap + Bp)) := by
    have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (x + y)) hσ; linarith
  positivity

/-- The floor of the outgoing norm of a doubly forward piece: with `G_L ≥ 0` at its incoming switch
and its stationarity identity, `u ≥ F_{b/(b+a)}(h)`. -/
theorem wire_floor_out_alg {p b a h wm w0 wp : ℝ} (hp : 0 < p) (hb : 0 < b) (ha : 0 < a)
    (hh1 : 1 < h) (hh : h * (b ^ 2 + 4) = (p + b) * (b + a))
    (hG : 0 ≤ 4 * b * (p + b) * (w0 / 2) + 2 * (b ^ 2 + 4) * (-(wm + w0) / 2) -
      2 * (p + b) ^ 2 * ((w0 + wp) / (2 * h ^ 2)) + p * (p + b) + (b ^ 2 + 4))
    (hs : 4 * (wm + w0) / (p + b) + 4 * (w0 + wp) / (b + a) - 8 * b * w0 / (b ^ 2 + 4) =
      ff_Cph p b a) :
    ff_F (b / (b + a)) h ≤ 4 * (w0 + wp) / (b + a) ^ 2 := by
  have hKb : 0 < b ^ 2 + 4 := by positivity
  have eh : ff_fac p b a = h := by simp only [ff_fac]; field_simp; linarith
  have hh' : h = (p + b) * (b + a) / (b ^ 2 + 4) := by field_simp; linarith
  have hh0 : 0 < h := by linarith
  have hs' := hs
  simp only [ff_Cph, eh] at hs'
  set L := Real.log h with hL
  have key : (b ^ 2 + 4) ^ 2 * (h - 1) / 4 * (4 * (w0 + wp) / (b + a) ^ 2 - ff_F (b / (b + a)) h) =
      4 * b * (p + b) * (w0 / 2) + 2 * (b ^ 2 + 4) * (-(wm + w0) / 2) -
        2 * (p + b) ^ 2 * ((w0 + wp) / (2 * h ^ 2)) + p * (p + b) + (b ^ 2 + 4) +
      h * (b ^ 2 + 4) ^ 2 / (4 * (b + a)) *
        ((4 * (wm + w0) / (p + b) + 4 * (w0 + wp) / (b + a) - 8 * b * w0 / (b ^ 2 + 4)) -
          (p + b + a - b ^ 2 * (1 / (p + b) + 1 / (b + a)) + b ^ 3 / (b ^ 2 + 4) - b * L)) := by
    simp only [ff_F, ← hL]
    have hh1' : h - 1 ≠ 0 := by linarith
    obtain ⟨s0, rfl⟩ : ∃ s0, p = s0 - b := ⟨p + b, by ring⟩
    simp only [sub_add_cancel] at hh ⊢
    have es0 : s0 = h * (b ^ 2 + 4) / (b + a) := by field_simp; linarith
    rw [es0]
    field_simp
    ring
  rw [hs', sub_self, mul_zero, add_zero] at key
  have hpos : 0 < (b ^ 2 + 4) ^ 2 * (h - 1) / 4 := by
    have : 0 < h - 1 := by linarith
    positivity
  rw [← key] at hG
  have := (mul_nonneg_iff_of_pos_left hpos).1 hG
  linarith

/-- The floor of the incoming norm of a doubly forward piece (the reflected statement): with
`G_L ≥ 0` at its outgoing switch and its stationarity identity, `v ≥ F_{c/(a+c)}(k)`. -/
theorem wire_floor_in_alg {a c d k wm w0 wp : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : 0 < d)
    (hk1 : 1 < k) (hk : k * (c ^ 2 + 4) = (a + c) * (c + d))
    (hG : 0 ≤ 4 * d * (c + d) * (wp / 2) + 2 * (d ^ 2 + 4) * (-(w0 + wp) / 2) -
      2 * (c + d) ^ 2 * ((wp - w0 + (wm + w0) / k ^ 2) / 2) + c * (c + d) + (d ^ 2 + 4))
    (hs : 4 * (wm + w0) / (a + c) + 4 * (w0 + wp) / (c + d) - 8 * c * w0 / (c ^ 2 + 4) =
      ff_Cph a c d) :
    ff_F (c / (a + c)) k ≤ 4 * (wm + w0) / (a + c) ^ 2 := by
  have hKc : 0 < c ^ 2 + 4 := by positivity
  have ek : ff_fac a c d = k := by simp only [ff_fac]; field_simp; linarith
  have hk' : k = (a + c) * (c + d) / (c ^ 2 + 4) := by field_simp; linarith
  have hk0 : 0 < k := by linarith
  have hs' := hs
  simp only [ff_Cph, ek] at hs'
  set L := Real.log k with hL
  have key : (c ^ 2 + 4) ^ 2 * (k - 1) / 4 * (4 * (wm + w0) / (a + c) ^ 2 - ff_F (c / (a + c)) k) =
      4 * d * (c + d) * (wp / 2) + 2 * (d ^ 2 + 4) * (-(w0 + wp) / 2) -
        2 * (c + d) ^ 2 * ((wp - w0 + (wm + w0) / k ^ 2) / 2) + c * (c + d) + (d ^ 2 + 4) +
      (c + d) * (c ^ 2 + 4) / 4 *
        ((4 * (wm + w0) / (a + c) + 4 * (w0 + wp) / (c + d) - 8 * c * w0 / (c ^ 2 + 4)) -
          (a + c + d - c ^ 2 * (1 / (a + c) + 1 / (c + d)) + c ^ 3 / (c ^ 2 + 4) - c * L)) := by
    simp only [ff_F, ← hL]
    have hk1' : k - 1 ≠ 0 := by linarith
    obtain ⟨t, rfl⟩ : ∃ t, a = t - c := ⟨a + c, by ring⟩
    simp only [sub_add_cancel] at hk ⊢
    have et : t = k * (c ^ 2 + 4) / (c + d) := by field_simp; linarith
    rw [et]
    field_simp
    ring
  rw [hs', sub_self, mul_zero, add_zero] at key
  have hpos : 0 < (c ^ 2 + 4) ^ 2 * (k - 1) / 4 := by
    have : 0 < k - 1 := by linarith
    positivity
  rw [← key] at hG
  have := (mul_nonneg_iff_of_pos_left hpos).1 hG
  linarith

/-! ### The costate cycle in the coordinates of the interfaces -/

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

private theorem wire_fin_sub_sub (i : Fin 3) : i - 1 - 1 = i + 1 := by revert i; decide

private theorem wire_fin_add_add (i : Fin 3) : i + 1 + 1 = i - 1 := by revert i; decide

/-- The entries of `M_k = Y(μ)` in the label order of piece `k`. -/
theorem wire_Mloc_apply (k : ℤ) :
    C.Mloc k 0 0 = -C.mu k (C.lab k) / 2 ∧
      C.Mloc k 0 1 = (C.mu k (C.lab k) + C.mu k (C.lab k - 1)) / 2 ∧
      C.Mloc k 1 0 = -(C.mu k (C.lab k) + C.mu k (C.lab k + 1)) / 2 ∧
      C.Mloc k 1 1 = C.mu k (C.lab k) / 2 := by
  have e1 : (1 : Fin 3) + C.lab k = C.lab k + 1 := by abel
  have e2 : (2 : Fin 3) + C.lab k = C.lab k - 1 := by generalize C.lab k = i; revert i; decide
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Mloc, triY, e1, e2]

theorem wire_wt_grow {k : ℤ} (hout : C.lab (k + 1) = C.lab k + 1) :
    C.wt k + C.wt (k + 1) = -(C.q k ^ 2 * (C.mu k (C.lab k) + C.mu k (C.lab k + 1))) := by
  simp only [wt]; rw [hout, ← C.mu_grow k, C.mu_act k]; ring

theorem wire_wt_decr {k : ℤ} (hout : C.lab (k + 1) = C.lab k - 1) :
    C.wt k + C.wt (k + 1) = -((C.q k)⁻¹ ^ 2 * (C.mu k (C.lab k) + C.mu k (C.lab k - 1))) := by
  simp only [wt]; rw [hout, ← C.mu_decr k, C.mu_act k]; ring

/-- `(M_k)₀₀ = w_k/2`. -/
theorem wire_Mloc_00 (k : ℤ) : C.Mloc k 0 0 = C.wt k / 2 := by
  rw [(C.wire_Mloc_apply k).1, wt, neg_div]

/-- After a forward switch into piece `k`: `(M_k)₀₁ = -(w_{k-1} + w_k)/2`. -/
theorem wire_Mloc_01_fwd {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1) :
    C.Mloc k 0 1 = -(C.wt (k - 1) + C.wt k) / 2 := by
  have hl : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
  rw [(C.wire_Mloc_apply k).2.1, C.wt_pred, hl, wt]; ring

/-- Before a forward switch out of piece `k`: `(M_k)₁₀ = (w_k + w_{k+1})/(2 q_k²)`. -/
theorem wire_Mloc_10_fwd {k : ℤ} (hout : C.lab (k + 1) = C.lab k + 1) :
    C.Mloc k 1 0 = (C.wt k + C.wt (k + 1)) / (2 * C.q k ^ 2) := by
  have hq := (C.q_pos k).ne'
  rw [(C.wire_Mloc_apply k).2.2.1, C.wire_wt_grow hout]; field_simp

/-- Eight times the norm of a forward switch, read in the frame of the piece before it. -/
theorem wire_norm_fwd {k : ℤ} (hout : C.lab (k + 1) = C.lab k + 1) :
    8 * C.q k ^ 2 * C.Mloc k 1 0 / (C.act k + C.act (k + 1)) ^ 2 = 8 * C.swd k := by
  have hq := (C.q_pos k).ne'
  have hs := (C.sw_pos k).ne'
  simp only [sw] at hs
  rw [C.wire_Mloc_10_fwd hout, swd]; field_simp

/-- Eight times the norm of a reverse switch, read in the frame of the piece before it. -/
theorem wire_norm_rev {k : ℤ} (hout : C.lab (k + 1) = C.lab k - 1) :
    -8 * C.Mloc k 0 1 / (C.q k ^ 2 * (C.act k + C.act (k + 1)) ^ 2) = 8 * C.swd k := by
  have hq := (C.q_pos k).ne'
  have hs := (C.sw_pos k).ne'
  simp only [sw] at hs
  rw [(C.wire_Mloc_apply k).2.1, swd, C.wire_wt_decr hout]; field_simp

/-- **Stationarity at a same-sign piece** (four times the first stationarity identity), in the
weights: `8 s_{k-1} d_{k-1} + 8 s_k d_k - 16 a_k e_k = 4 J_{a_k}`. -/
theorem wire_stat_w {k : ℤ} (hs : C.sgn (k - 1) = C.sgn k) :
    4 * (C.wt (k - 1) + C.wt k) / (C.act (k - 1) + C.act k) +
        4 * (C.wt k + C.wt (k + 1)) / (C.act k + C.act (k + 1)) -
        8 * C.act k * C.wt k / (C.act k ^ 2 + 4) =
      ff_Cph (C.act (k - 1)) (C.act k) (C.act (k + 1)) := by
  have hst := C.stationarity k
  rw [wire_Cph_eq (C.act_pos _) (C.act_pos _) (C.act_pos _)]
  rw [hs] at hst
  have h1 := C.act_pos (k - 1)
  have h2 := C.act_pos k
  have h3 := C.act_pos (k + 1)
  have e : 4 * (C.wt (k - 1) + C.wt k) / (C.act (k - 1) + C.act k) +
        4 * (C.wt k + C.wt (k + 1)) / (C.act k + C.act (k + 1)) -
        8 * C.act k * C.wt k / (C.act k ^ 2 + 4) =
      8 * ((C.act (k - 1) + C.act k) * C.swd (k - 1) + (C.act k + C.act (k + 1)) * C.swd k) -
        16 * C.act k * C.cre k := by
    simp only [swd, cre, sub_add_cancel]; field_simp; ring
  rw [e]
  rcases C.sgn_cases k with h | h <;> rw [h] at hst <;> linarith

/-- The same identity in the form of the case-M2 interface: `s_{k-1} (8 d_{k-1}) + s_k (8 d_k)
- 16 a_k (M_k)₀₀/K_k = 4 J_{a_k}`. -/
theorem wire_stat_M {k : ℤ} (hs : C.sgn (k - 1) = C.sgn k) :
    (C.act (k - 1) + C.act k) * (8 * C.swd (k - 1)) + (C.act k + C.act (k + 1)) * (8 * C.swd k) -
        16 * C.act k * C.Mloc k 0 0 / (C.act k ^ 2 + 4) =
      ff_Cph (C.act (k - 1)) (C.act k) (C.act (k + 1)) := by
  rw [← C.wire_stat_w hs, C.wire_Mloc_00]
  have h1 := C.act_pos (k - 1)
  have h2 := C.act_pos k
  have h3 := C.act_pos (k + 1)
  simp only [swd, sub_add_cancel]; field_simp; ring

/-- **The transport of the weights across a doubly forward piece** (`k - 2 → k - 1 → k → k + 1` all
forward): `w_{k-2} + w_{k-1} = q_{k-1}² (w_{k-1} - w_k + (w_k + w_{k+1})/q_k²)`. -/
theorem wire_w_rel {k : ℤ} (h0 : C.lab (k - 1) = C.lab (k - 2) + 1)
    (hin : C.lab k = C.lab (k - 1) + 1) (hout : C.lab (k + 1) = C.lab k + 1) :
    C.wt (k - 2) + C.wt (k - 1) =
      C.q (k - 1) ^ 2 * (C.wt (k - 1) - C.wt k + (C.wt k + C.wt (k + 1)) / C.q k ^ 2) := by
  have hq := (C.q_pos k).ne'
  have hq' := (C.q_pos (k - 1)).ne'
  have hl1 : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
  have hl2 : C.lab (k - 2) = C.lab k + 1 := by
    rw [show C.lab (k - 2) = C.lab (k - 1) - 1 by rw [h0, add_sub_cancel_right], hl1,
      wire_fin_sub_sub]
  have e2 : C.wt (k - 2) = -C.mu (k - 1) (C.lab (k - 2)) := by
    have := C.wt_pred (k - 1); rwa [show k - 1 - 1 = k - 2 by ring] at this
  have e1 : C.wt (k - 1) = -C.mu k (C.lab k - 1) := by rw [C.wt_pred, hl1]
  have e1' : C.wt (k - 1) = -C.mu (k - 1) (C.lab (k - 1)) := rfl
  have hd := C.mu_decr (k - 1)
  rw [sub_add_cancel, hl1, wire_fin_sub_sub, ← hl1] at hd
  have hg := C.wire_wt_grow hout
  have hw0 : C.wt k = -C.mu k (C.lab k) := rfl
  have hp' : C.q k ^ 2 * C.mu k (C.lab k + 1) = -(C.wt k + C.wt (k + 1)) + C.q k ^ 2 * C.wt k := by
    linear_combination hg - C.q k ^ 2 * hw0
  have hp : C.mu k (C.lab k + 1) = -(C.wt k + C.wt (k + 1)) / C.q k ^ 2 + C.wt k := by
    field_simp; linear_combination hp'
  have f1 : C.mu k (C.lab (k - 1)) = -C.wt (k - 1) := by rw [C.wt_pred]; ring
  have f2 : C.mu (k - 1) (C.lab k + 1) = -C.wt (k - 2) := by rw [e2, hl2]; ring
  have f3 : C.mu (k - 1) (C.lab (k - 1)) = -C.wt (k - 1) := by rw [e1']; ring
  rw [f1, f2, f3, hp] at hd
  have hd2 : C.q (k - 1) ^ 2 * (-C.wt (k - 1) + (-(C.wt k + C.wt (k + 1)) / C.q k ^ 2 + C.wt k)) =
      -C.wt (k - 1) + -C.wt (k - 2) := by
    rw [hd]; field_simp
  linear_combination hd2

/-- At a doubly forward piece `k`, the entry `(M_{k+1})₁₀` read through the transport across
piece `k`: `(w_{k+1} - w_k + (w_{k-1} + w_k)/q_k²)/2`. -/
theorem wire_Mloc_10_next {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1)
    (hout : C.lab (k + 1) = C.lab k + 1) :
    C.Mloc (k + 1) 1 0 = (C.wt (k + 1) - C.wt k + (C.wt (k - 1) + C.wt k) / C.q k ^ 2) / 2 := by
  have hq := (C.q_pos k).ne'
  have hl : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
  have e10 := (C.wire_Mloc_apply (k + 1)).2.2.1
  rw [hout, wire_fin_add_add] at e10
  have h1 : C.mu (k + 1) (C.lab k + 1) = -C.wt (k + 1) := by simp only [wt, hout]; ring
  have hd := C.mu_decr k
  have ha := C.mu_act k
  have h2 : C.mu k (C.lab k - 1) = -C.wt (k - 1) := by rw [C.wt_pred, hl]; ring
  have h3 : C.mu k (C.lab k) = -C.wt k := by simp only [wt]; ring
  have h4 : C.mu (k + 1) (C.lab k - 1) = (C.q k)⁻¹ ^ 2 * (-C.wt k - C.wt (k - 1)) + C.wt k := by
    linear_combination hd - ha + (C.q k)⁻¹ ^ 2 * (h3 + h2) - h3
  rw [e10, h1, h4]
  field_simp
  ring

/-- **The missing-control inequality** at a forward switch into piece `k`: in the frame of piece
`k`, `G_L = 4 a_k s (M_k)₀₀ + 2 K_k (M_k)₀₁ - 2 s² (M_k)₁₀ + a_{k-1} s + K_k ≥ 0`,
`s = a_{k-1} + a_k`; the missing `σ` is `-4√3 G_L/s²` (`wire_mc_alg`). -/
theorem wire_mc {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1) :
    0 ≤ 4 * C.act k * (C.act (k - 1) + C.act k) * C.Mloc k 0 0 +
      2 * (C.act k ^ 2 + 4) * C.Mloc k 0 1 -
      2 * (C.act (k - 1) + C.act k) ^ 2 * C.Mloc k 1 0 +
      C.act (k - 1) * (C.act (k - 1) + C.act k) + (C.act k ^ 2 + 4) := by
  have hl : C.lab (k - 1) = C.lab k - 1 := by rw [hin, add_sub_cancel_right]
  obtain ⟨e00, e01, e10, -⟩ := C.wire_Mloc_apply k
  have hy : C.act (k - 1) = C.m k (C.lab k - 1) := by rw [C.act_pred, hl]
  have hm : 2 * C.α k (C.lab k - 1) + C.β k (C.lab k - 1) = 0 := by
    have := C.sig_act_succ (k - 1); rw [sub_add_cancel, hl] at this; simpa only [sig] using this
  rw [e00, e01, e10, hy]
  simp only [mu, el_sum_rot (C.m k) (C.lab k), act]
  exact wire_mc_alg (C.m_pos k _) (C.m_pos k _) (C.quad_rot k _) (C.sig_act k) hm
    (C.perp_rot k _) (C.sig_le k _)

/-- **The floor of the outgoing norm** of a doubly forward piece `k`, from the missing control at
the switch before it: `8 d_k ≥ F_{a_k/(a_k + a_{k+1})}(q_k)`. -/
theorem wire_floor_out {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1)
    (hout : C.lab (k + 1) = C.lab k + 1) :
    ff_F (C.act k / (C.act k + C.act (k + 1))) (C.q k) ≤ 8 * C.swd k := by
  have hG := C.wire_mc hin
  rw [C.wire_Mloc_00, C.wire_Mloc_01_fwd hin, C.wire_Mloc_10_fwd hout] at hG
  have hf := C.factor_pp hin hout
  simp only [sw, sub_add_cancel] at hf
  have hs := C.wire_stat_w (k := k) (by
    rw [C.sgn_fwd (k := k - 1) (by rw [sub_add_cancel]; exact hin), C.sgn_fwd hout])
  have h := wire_floor_out_alg (C.act_pos (k - 1)) (C.act_pos k) (C.act_pos (k + 1))
    (C.one_lt_q k) hf hG hs
  have hs2 := C.act_pos k
  have hs3 := C.act_pos (k + 1)
  have e : 8 * C.swd k = 4 * (C.wt k + C.wt (k + 1)) / (C.act k + C.act (k + 1)) ^ 2 := by
    simp only [swd]; field_simp; ring
  rw [e]; exact h

/-- **The floor of the incoming norm** of a doubly forward piece `k`, from the missing control at
the switch after it: `8 d_{k-1} ≥ F_{a_k/(a_{k-1} + a_k)}(q_k)`. -/
theorem wire_floor_in {k : ℤ} (hin : C.lab k = C.lab (k - 1) + 1)
    (hout : C.lab (k + 1) = C.lab k + 1) :
    ff_F (C.act k / (C.act (k - 1) + C.act k)) (C.q k) ≤ 8 * C.swd (k - 1) := by
  have hin' : C.lab (k + 1) = C.lab (k + 1 - 1) + 1 := by rw [add_sub_cancel_right]; exact hout
  have hG := C.wire_mc hin'
  rw [C.wire_Mloc_00, C.wire_Mloc_01_fwd hin', C.wire_Mloc_10_next hin hout,
    add_sub_cancel_right] at hG
  have hf := C.factor_pp hin hout
  simp only [sw, sub_add_cancel] at hf
  have hs := C.wire_stat_w (k := k) (by
    rw [C.sgn_fwd (k := k - 1) (by rw [sub_add_cancel]; exact hin), C.sgn_fwd hout])
  have h := wire_floor_in_alg (C.act_pos (k - 1)) (C.act_pos k) (C.act_pos (k + 1))
    (C.one_lt_q k) hf hG hs
  have hs1 := C.act_pos (k - 1)
  have hs2 := C.act_pos k
  have e : 8 * C.swd (k - 1) = 4 * (C.wt (k - 1) + C.wt k) / (C.act (k - 1) + C.act k) ^ 2 := by
    simp only [swd, sub_add_cancel]; field_simp; ring
  rw [e]; exact h

end CostateCycle

/-! ### The spectral cost–Casimir inequality -/

section Spectral

open Reduction MeasureTheory

/-- **The spectral pointwise inequality**: for `det B = 1` and a star state `Y`,
`(ρ + ρ_R)² ≤ 4 |z(B)|² ρ ρ_R`, i.e. `r + 1/r ≤ tr P` for the Rayleigh quotient `r = ρ_R/ρ` of
`P = B⁻¹B⁻ᵀ`. Proof: the explicit sum of squares
`4|z|²ρρ_R - (ρ + ρ_R)² = ((b₀-b₃)² + (b₁+b₂)²)((b₀+b₃)² + (b₁-b₂)²) det Y/4 + [Q, P]₀₁²/4`. -/
theorem wire_spec_key {B Y : Mat2} (hB : B.det = 1) (hY : IsStarState Y) :
    (clr_rho Y + clr_rhoR B Y) ^ 2 ≤ 4 * Complex.normSq (clr_zc B) * clr_rho Y * clr_rhoR B Y := by
  obtain ⟨htr, hdY, -, -, -⟩ := hY
  rw [Matrix.trace_fin_two] at htr
  rw [Matrix.det_fin_two] at hdY hB
  have e11 : Y 1 1 = -Y 0 0 := by linarith
  have key := clr_rhoR_eq B Y
  have hR : clr_rhoR B Y = ((Y 0 0 - Y 1 1) * (B 0 0 * B 0 1 + B 1 0 * B 1 1) -
      Y 0 1 * (B 0 0 ^ 2 + B 1 0 ^ 2) + Y 1 0 * (B 0 1 ^ 2 + B 1 1 ^ 2)) / 2 := by linarith
  rw [Complex.normSq_apply, clr_zc_re, clr_zc_im, clr_rho_eq, hR, e11]
  rw [e11] at hdY
  set b0 := B 0 0
  set b1 := B 0 1
  set b2 := B 1 0
  set b3 := B 1 1
  set x0 := Y 0 0
  set x1 := Y 0 1
  set x2 := Y 1 0
  have hid : 4 * (((b0 + b3) / 2) * ((b0 + b3) / 2) + ((b2 - b1) / 2) * ((b2 - b1) / 2)) *
        ((x2 - x1) / 2) * (((x0 - -x0) * (b0 * b1 + b2 * b3) - x1 * (b0 ^ 2 + b2 ^ 2) +
          x2 * (b1 ^ 2 + b3 ^ 2)) / 2) -
      ((x2 - x1) / 2 + ((x0 - -x0) * (b0 * b1 + b2 * b3) - x1 * (b0 ^ 2 + b2 ^ 2) +
          x2 * (b1 ^ 2 + b3 ^ 2)) / 2) ^ 2 =
      ((b0 - b3) ^ 2 + (b1 + b2) ^ 2) * ((b0 + b3) ^ 2 + (b1 - b2) ^ 2) * (x0 * -x0 - x1 * x2) / 4 +
        (-b0 ^ 2 * x0 - b0 * b1 * x1 - b0 * b1 * x2 + b1 ^ 2 * x0 - b2 ^ 2 * x0 - b2 * b3 * x1 -
          b2 * b3 * x2 + b3 ^ 2 * x0) ^ 2 / 4 +
        (-(x1 - x2) * (-2 * b0 ^ 2 * x1 + 4 * b0 * b1 * x0 - b0 * b3 * x1 + b0 * b3 * x2 +
          2 * b1 ^ 2 * x2 + b1 * b2 * x1 - b1 * b2 * x2 - 2 * b2 ^ 2 * x1 + 4 * b2 * b3 * x0 +
          2 * b3 ^ 2 * x2 - x1 + x2) / 4) * (b0 * b3 - b1 * b2 - 1) := by
    ring
  rw [hdY, hB, sub_self, mul_zero, add_zero] at hid
  have : 0 ≤ ((b0 - b3) ^ 2 + (b1 + b2) ^ 2) * ((b0 + b3) ^ 2 + (b1 - b2) ^ 2) * 1 / 4 +
      (-b0 ^ 2 * x0 - b0 * b1 * x1 - b0 * b1 * x2 + b1 ^ 2 * x0 - b2 ^ 2 * x0 - b2 * b3 * x1 -
          b2 * b3 * x2 + b3 ^ 2 * x0) ^ 2 / 4 := by positivity
  nlinarith

/-- **The winding of the frame**, in the sharp form: for a frame path `B' = B X` with star states,
`det B = 1` and `B(T) = B(0) R`, the polar angle `θ' = (ρ + ρ_R)/(2|z|²)` integrates to at least
`π/3`. -/
theorem wire_winding {T : ℝ} (hT : 0 < T) {B X : ℝ → Mat2}
    (hBc : ContinuousOn B (Icc 0 T)) (hXc : ContinuousOn X (Icc 0 T))
    (hBd : ∀ s ∈ Ioo 0 T, Matrix.HasDerivAtEntrywise B (B s * X s) s)
    (hdet : ∀ s ∈ Icc 0 T, (B s).det = 1) (hstar : ∀ s ∈ Icc 0 T, IsStarState (X s))
    (hBT : B T = B 0 * R) :
    π / 3 ≤ ∫ s in (0 : ℝ)..T,
      (clr_rho (X s) + clr_rhoR (B s) (X s)) / 2 / Complex.normSq (clr_zc (B s)) := by
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
  have hcongr : ∫ r in (0 : ℝ)..T, (f r).im = ∫ r in (0 : ℝ)..T,
      (clr_rho (X r) + clr_rhoR (B r) (X r)) / 2 / Complex.normSq (clr_zc (B r)) := by
    refine intervalIntegral.integral_congr (fun r hr ↦ ?_)
    rw [uIcc_of_le hT.le] at hr
    exact hfim r hr
  rw [← hcongr, ← hIm, hLim]
  nlinarith [Real.pi_pos]

end Spectral

/-- The exact moment ratio gives the competitive cap for the spectral cost bound. -/
theorem wire_gam2_cap {x c : ℝ} (hx : 0 < x) (h : π/3*(√x+3/2) ≤ c)
    (hc : c ≤ octagonCost) : x/12 < 9193/50000 :=
  octagon_spectral_cap hx h hc

/-! ### Ellipticity and the spectral cost–Casimir bound of a normal period -/

namespace NormalPeriod

variable (P : NormalPeriod)

/-- **Negative ellipticity, all-forward periods**: `γ² > 0`, by the projective argument of
`gam2_pos_of_mixed`: at a `+ +` piece the increment of the projective coordinate is
`η²/(K h h') > 0` (`cross_pp`, `cre_pos_pp`), so the increments over one period cannot telescope to
`0`. -/
theorem wire_gam2_pos_of_allForward (hF : P.rep.AllForward) : 0 < P.costateCycle.gam2 0 := by
  set C := P.costateCycle with hC
  by_contra hcon
  push Not at hcon
  have hfwd : ∀ k : ℤ, C.lab (k + 1) = C.lab k + 1 := hF
  have hgam : ∀ k, C.gam2 k ≤ 0 := fun k ↦ by rw [C.gam2_eq]; exact hcon
  have hsym : C.Sloc 0 0 1 = C.Sloc 0 1 0 := C.Sloc_symm 0
  set S := C.Sloc 0 with hS
  have hdet : S.det ≤ 0 := by
    have : S.det = C.gam2 0 := by
      rw [hS, CostateCycle.Sloc, Matrix.det_neg, Matrix.det_mul, C.det_Mloc]
      simp [elJ0, Matrix.det_fin_two]
    rw [this]; exact hcon
  have hd : ∀ n : ℕ, 0 < elQ S (C.yv n) (C.yv n) := fun n ↦ by
    rw [C.yv_norm]
    have := C.swd_fwd (hfwd n)
    have := CostateCycle.elJ_ge _ _ (C.act_pos n) (C.act_pos (n + 1))
    linarith
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
  -- every increment is positive
  have hstep : ∀ n : ℕ, 0 < z (C.yv (n + 1)) - z (C.yv n) := by
    intro n
    obtain ⟨hq, hdt⟩ := C.yv_pair n
    have ek : ((n + 1 : ℕ) : ℤ) - 1 = n := by push_cast; ring
    have hpr := hprod n (n + 1)
    rw [hinc]
    have hin' : C.lab ((n + 1 : ℕ) : ℤ) = C.lab (((n + 1 : ℕ) : ℤ) - 1) + 1 := by
      rw [ek]; push_cast; exact hfwd n
    have hout := hfwd ((n + 1 : ℕ) : ℤ)
    obtain ⟨hc, hdl⟩ := C.cross_pp hin' hout
    have hpos := C.cre_pos_pp hin' hout (hgam _)
    rw [hq, hc] at hpr
    rw [hdt, hdl]
    have : 0 < h (C.yv n) * h (C.yv (n + 1)) := by
      by_contra hc'; push Not at hc'; nlinarith
    have hK : 0 < C.act ((n + 1 : ℕ) : ℤ) ^ 2 + 4 := by positivity
    positivity
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
    Finset.sum_pos (fun n _ ↦ hstep n) (Finset.nonempty_range_iff.2 P.rep.N_pos.ne')
  linarith

/-- `γ² > 0` and a positive switch norm make `S = -J₀U` positive definite: `S₀₀ > 0`. -/
theorem wire_S00_pos (hpos : 0 < P.costateCycle.gam2 0) {n : ℕ}
    (hd : 0 < P.costateCycle.swd n) : 0 < P.costateCycle.Sloc 0 0 0 := by
  set C := P.costateCycle
  have hsym : C.Sloc 0 0 1 = C.Sloc 0 1 0 := C.Sloc_symm 0
  have hdetS : (C.Sloc 0).det = C.gam2 0 := by
    rw [CostateCycle.Sloc, Matrix.det_neg, Matrix.det_mul, C.det_Mloc]
    simp [elJ0, Matrix.det_fin_two]
  have hq : 0 < elQ (C.Sloc 0) (C.yv n) (C.yv n) := by rw [C.yv_norm]; exact_mod_cast hd
  rw [Matrix.det_fin_two] at hdetS
  set y := C.yv n
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

/-- **Negative ellipticity** from `γ² > 0` and one positive switch norm: `det Λ₁(0) > 0`,
`Λ₁(0)₁₀ < 0`. -/
theorem wire_negEll (hpos : 0 < P.costateCycle.gam2 0) {n : ℕ} (hd : 0 < P.costateCycle.swd n) :
    0 < (P.Λ₁ 0).det ∧ (P.Λ₁ 0) 1 0 < 0 :=
  ⟨by rw [P.det_Λ₁_zero]; positivity, P.Λ₁_zero_neg hpos (P.wire_S00_pos hpos hd)⟩

open Reduction in
/-- **The spectral cost–Casimir inequality.** If `Λ₁(0)` is negative elliptic with Casimir
`κ = √(det Λ₁)`, then `C ≥ (π/3)(κ + 3/2)`. The proof follows `cost_casimir`, with its pointwise
bound `θ' ≤ (ρ + ρ_R)/2` sharpened to `θ' ≤ 2ρρ_R/(ρ + ρ_R) ≤ 6ρ/(2κ + 3)` (`wire_spec_key`,
`2κρ_R ≤ 3ρ`). -/
theorem wire_spectral (hdet : 0 < (P.Λ₁ 0).det) (h10 : (P.Λ₁ 0) 1 0 < 0) :
    π / 3 * (√(P.Λ₁ 0).det + 3 / 2) ≤ P.cost := by
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
  have hwind := wire_winding hT hBc hXc hBd hBdet hstar hBT
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
  -- `2κ ρ_R ≤ 3ρ`
  have hkR : ∀ s ∈ Icc 0 P.T, 2 * κ * clr_rhoR (B s) (P.X s) ≤ 3 * clr_rho (P.X s) := by
    intro s hs
    have h1 := clr_traceForm_le_zero P.extremal s hs
    have h2 := hρR s hs
    simp only [traceForm, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul,
      Matrix.trace_smul, smul_eq_mul] at h1
    simp only [traceForm] at h2
    simp only [clr_rho, traceForm]
    rw [h2] at h1
    linarith
  -- the pointwise bound `θ' ≤ 6ρ/(2κ + 3)`
  have hle : ∀ s ∈ Icc 0 P.T,
      (clr_rho (P.X s) + clr_rhoR (B s) (P.X s)) / 2 / Complex.normSq (clr_zc (B s)) ≤
        6 / (2 * κ + 3) * clr_rho (P.X s) := by
    intro s hs
    have hk := hkR s hs
    have hkey := wire_spec_key (hBdet s hs) (hstar s hs)
    have hρ := clr_rho_pos (hstar s hs)
    have hρR' := clr_rhoR_pos (hBdet s hs) (hstar s hs)
    have hN := clr_zc_normSq_ge (hBdet s hs)
    set r := clr_rho (P.X s)
    set rR := clr_rhoR (B s) (P.X s)
    set Nz := Complex.normSq (clr_zc (B s))
    have h1 : (r + rR) * (2 * κ + 3) * rR ≤ 3 * (r + rR) ^ 2 := by nlinarith
    have h2 : (r + rR) * (2 * κ + 3) * rR ≤ 12 * Nz * r * rR := by nlinarith
    have h3 : (r + rR) * (2 * κ + 3) ≤ 12 * Nz * r := by
      by_contra hc; push Not at hc; nlinarith
    rw [div_div, div_le_iff₀ (by positivity)]
    rw [div_mul_eq_mul_div, mul_comm, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith
  have hρc : ContinuousOn (fun s ↦ clr_rho (P.X s)) (Icc 0 P.T) :=
    clr_continuous_rho.comp_continuousOn hXc
  have hρRc : ContinuousOn (fun s ↦ clr_rhoR (B s) (P.X s)) (Icc 0 P.T) :=
    clr_continuous_rhoR.comp_continuousOn (f := fun s ↦ (B s, P.X s)) (hBc.prodMk hXc)
  have hNc : ContinuousOn (fun s ↦ Complex.normSq (clr_zc (B s))) (Icc 0 P.T) :=
    Complex.continuous_normSq.comp_continuousOn (clr_continuous_zc.comp_continuousOn hBc)
  have hi1 : IntervalIntegrable
      (fun s ↦ (clr_rho (P.X s) + clr_rhoR (B s) (P.X s)) / 2 / Complex.normSq (clr_zc (B s)))
      MeasureTheory.volume 0 P.T :=
    ((((hρc.add hρRc).div_const 2).div hNc (fun s hs ↦ by
      have := clr_zc_normSq_ge (hBdet s hs); positivity)).mono
      (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s ↦ 6 / (2 * κ + 3) * clr_rho (P.X s))
      MeasureTheory.volume 0 P.T :=
    ((hρc.const_smul (6 / (2 * κ + 3))).mono (by rw [uIcc_of_le hT.le])).intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hT.le hi1 hi2 hle
  rw [intervalIntegral.integral_const_mul] at hmono
  have hcost : P.cost = 3 * ∫ s in (0 : ℝ)..P.T, clr_rho (P.X s) := by
    simp only [cost, reinhardtCost, clr_rho, intervalIntegral.integral_const_mul]; ring
  rw [hcost]
  have := le_trans hwind hmono
  set I := ∫ s in (0 : ℝ)..P.T, clr_rho (P.X s)
  have hI : π / 3 * (2 * κ + 3) ≤ 6 * I := by
    have e : 6 / (2 * κ + 3) * I * (2 * κ + 3) = 6 * I := by field_simp
    have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 2 * κ + 3)
    linarith
  nlinarith [Real.pi_pos]

end NormalPeriod

end SmoothedOctagon
