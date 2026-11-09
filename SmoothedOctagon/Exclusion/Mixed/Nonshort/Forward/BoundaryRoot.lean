module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Reverse.WindowData

/-!
# Case M2, forward successor: the normalized boundary root and next norm

In the normalized coordinates `t = a/T`, `x = (d - a)/T`, `k = K/T²`, `q = WZ/Q` (with `e = q/W`,
`J = t + Y`, `D = eJ - p`, `E = e²B + 1 - 2pe`), with the central margin at its boundary value
`b* = K/T - a` and a free central incident norm `u`:

* `nsfHn` (`16 h/T²`), `nsfwn` (the transported norm), `nsfRn` (the root function `R_d/T`) and
  `nsfTn` (the next transported norm `𝒯`), all affine in `u`;
* `nsf_root_u`, `nsf_next_u`: the physical root function and next norm in these coordinates;
* `nsf_Rn_sub`, `nsf_Tn_sub`: their `u`-slopes `-k²D/(tB)` and `e²k²(Je² - 1)/(tE²)`;
* `nsf_Rn_U`: at the ceiling `U(t/k)` the root function is `nsrR`;
* `nsfComb`: the combined residual of the multiplier arguments;
* `nsfTP`: the cleared transport part `4qW² C_*(3/4 - 𝒯_U)`, `C_* = tW²DE²/e`, and
  `nsf_TP_eq` relating them.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The normalized central diagonal `16 h/T²` at the boundary, for a free incident norm `u`:
`H(u) = (k²u + k(v - 1 + t²) + t²(2 - t) - (k² - kt + t²))/t`. -/
noncomputable def nsfHn (t k v u : ℝ) : ℝ :=
  (k ^ 2 * u + k * (v - 1 + t ^ 2) + t ^ 2 * (2 - t) - (k ^ 2 - k * t + t ^ 2)) / t

/-- The normalized transported norm `w(u) = (k²u + H(u)Y + vY²)/B²`. -/
noncomputable def nsfwn (t x k v u : ℝ) : ℝ :=
  (k ^ 2 * u + nsfHn t k v u * (x * (x + 2)) + v * (x * (x + 2)) ^ 2) / (k + 2 * t * x + x ^ 2) ^ 2

/-- The normalized root function `R(u) = R_d/T` (`nsrR` at `u = U(t/k)`). -/
noncomputable def nsfRn (t x k q v L u : ℝ) : ℝ :=
  (1 - t) + q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x) ^ 2 / (1 + x)
    - (t + x) ^ 2 / (q * (k + 2 * t * x + x ^ 2) / (1 + x))
    + (t + x) ^ 3 / (k + 2 * t * x + x ^ 2) - (t + x) * L - (1 + x) * v
    - q * (k + 2 * t * x + x ^ 2) / (1 + x) * nsfwn t x k v u
    + (t + x) * (nsfHn t k v u + 2 * v * (x * (x + 2))) / (k + 2 * t * x + x ^ 2)

/-- `E = e²B + 1 - 2pe`, `e = q/W`. -/
noncomputable def nsfE (t x k q : ℝ) : ℝ :=
  (q / (1 + x)) ^ 2 * (k + 2 * t * x + x ^ 2) + 1 - 2 * (t + x) * (q / (1 + x))

/-- `D = eJ - p`, `J = t + x(x + 2)`. -/
noncomputable def nsfD (t x q : ℝ) : ℝ := q / (1 + x) * (t + x * (x + 2)) - (t + x)

/-- The normalized next transported norm `𝒯(u) = (v - e²(H + 2vY) + e⁴B²w)/E²`. -/
noncomputable def nsfTn (t x k q v u : ℝ) : ℝ :=
  (v - (q / (1 + x)) ^ 2 * (nsfHn t k v u + 2 * v * (x * (x + 2)))
    + (q / (1 + x)) ^ 4 * (k + 2 * t * x + x ^ 2) ^ 2 * nsfwn t x k v u) / nsfE t x k q ^ 2

/-- `t H_U = k(v - 1 + t²) + t²(2 - t)`. -/
noncomputable def nsfHt (t k v : ℝ) : ℝ := k * (v - 1 + t ^ 2) + t ^ 2 * (2 - t)

/-- `t B² w_U = t(k² - kt + t²) + (tH_U)Y + tvY²`. -/
noncomputable def nsfKt (t x k v : ℝ) : ℝ :=
  t * (k ^ 2 - k * t + t ^ 2) + nsfHt t k v * (x * (x + 2)) + t * v * (x * (x + 2)) ^ 2

/-- `E₀ = W²E = q²B + W² - 2pqW`. -/
noncomputable def nsfE0 (t x k q : ℝ) : ℝ :=
  q ^ 2 * (k + 2 * t * x + x ^ 2) + (1 + x) ^ 2 - 2 * (t + x) * q * (1 + x)

/-- **The cleared transport part** `4qW² C_*(3/4 - 𝒯_U)`, `C_* = tW²DE²/e`:
`(qJ - pW){3tE₀² - 4tvW⁴ + 4q²W²(tH_U + 2tvY) - 4q⁴ tB²w_U}`. -/
noncomputable def nsfTP (t x k q v : ℝ) : ℝ :=
  (q * (t + x * (x + 2)) - (t + x) * (1 + x)) *
    (3 * t * nsfE0 t x k q ^ 2 - 4 * t * v * (1 + x) ^ 4
      + 4 * q ^ 2 * (1 + x) ^ 2 * (nsfHt t k v + 2 * t * v * (x * (x + 2)))
      - 4 * q ^ 4 * nsfKt t x k v)

/-- **The combined residual** `4qW²[(α + 1 - Je²)N + C_*(3/4 - 𝒯_U) + M(F - v)]` (the multiplier
combination, cleared by `4qW²`), with the floor value `F` and the logarithm `L` as free
arguments. -/
noncomputable def nsfComb (α M t x k q v L F : ℝ) : ℝ :=
  4 * q * ((α + 1) * (1 + x) ^ 2 - (t + x * (x + 2)) * q ^ 2) * nsrN t x k q v L
    + nsfTP t x k q v + 4 * q * (1 + x) ^ 2 * M * (F - v)

/-- The normalized central diagonal at a free incident norm. -/
theorem nsf_m2h_u {a c T t k u v : ℝ} (hT : 0 < T) (ht : 0 < t) (hk : 0 < k) (ha : a = t * T)
    (hc : c = (1 - t) * T) (hK : a ^ 2 + 4 = k * T ^ 2) :
    m2h a (m2bStar a c) c u v = T ^ 2 / 16 * nsfHn t k v u := by
  have hac : a + c = T := by rw [ha, hc]; ring
  have hb : m2bStar a c = k * T - a := by
    unfold m2bStar; rw [hac, hK]; field_simp
  have hlog : Real.log ((m2bStar a c + a) * (a + c) / (a ^ 2 + 4)) = 0 := by
    rw [show (m2bStar a c + a) * (a + c) / (a ^ 2 + 4) = 1 by
      rw [hb, hac, hK]; field_simp; ring]
    exact Real.log_one
  unfold m2h
  unfold m2Stat
  rw [hlog, hb, hac, hK]
  subst ha hc
  have h1 : t * T + (k * T - t * T) = k * T := by ring
  have h2 : k * T - t * T + t * T = k * T := by ring
  rw [h1, h2]
  unfold nsfHn
  field_simp
  ring

/-- The transported norm and the diagonal at `d`, for a free incident norm. -/
theorem nsf_m2wOf_u {a c d T t x k u v h H : ℝ} (hT : 0 < T) (_hB : 0 < k + 2 * t * x + x ^ 2)
    (ha : a = t * T) (hc : c = (1 - t) * T) (hd : d = (t + x) * T) (hK : a ^ 2 + 4 = k * T ^ 2)
    (hQ : d ^ 2 + 4 = T ^ 2 * (k + 2 * t * x + x ^ 2)) (hh : h = T ^ 2 / 16 * H) :
    m2wOf a c d u v h = (k ^ 2 * u + H * (x * (x + 2)) + v * (x * (x + 2)) ^ 2) /
        (k + 2 * t * x + x ^ 2) ^ 2 ∧
      m2hd a c d v h = T ^ 2 / 16 * (H + 2 * v * (x * (x + 2))) := by
  have hY : m2Y a c d = T ^ 2 * (x * (x + 2)) := by
    unfold m2Y; rw [ha, hc, hd]; ring
  constructor
  · unfold m2wOf
    rw [hY, hK, hQ, hh]
    field_simp
  · unfold m2hd
    rw [hY, hh]
    ring

/-- **The physical root function at the boundary, normalized**: `R_d(u; b*) = T·R(u)`. -/
theorem nsf_root_u {a c d r v u T t x k q : ℝ} (hT : 0 < T) (ht : 0 < t) (hx : 0 < x)
    (hk : 0 < k) (hq : 0 < q) (ha : a = t * T) (hc : c = (1 - t) * T) (hd : d = (t + x) * T)
    (hK : a ^ 2 + 4 = k * T ^ 2) (hQ : d ^ 2 + 4 = T ^ 2 * (k + 2 * t * x + x ^ 2))
    (hZ : d + r = q * (k + 2 * t * x + x ^ 2) / (1 + x) * T)
    (hqd : (c + d) * (d + r) / (d ^ 2 + 4) = q) :
    m2RootAt a (m2bStar a c) c d r v u = T * nsfRn t x k q v (Real.log q) u := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hh := nsf_m2h_u (u := u) (v := v) hT ht hk ha hc hK
  obtain ⟨hw, hhd⟩ := nsf_m2wOf_u (u := u) (v := v) hT hB ha hc hd hK hQ hh
  have hS := nsr_m2Stat_d (r := r) hT hx hB hq hc hd hQ hZ (by rw [hqd])
  unfold m2RootAt m2Root
  rw [hw, hhd, hS, hQ, hZ]
  have hcd : c + d = (1 + x) * T := by rw [hc, hd]; ring
  rw [hcd, hd]
  unfold nsfRn nsfwn
  have hW : 0 < 1 + x := by linarith
  field_simp

/-- **The physical next norm at the boundary, normalized**: `𝒯(u) = nsfTn`. -/
theorem nsf_next_u {a c d r v u T t x k q : ℝ} (hT : 0 < T) (ht : 0 < t) (hx : 0 < x)
    (hk : 0 < k) (_hq : 0 < q) (ha : a = t * T) (hc : c = (1 - t) * T) (hd : d = (t + x) * T)
    (hK : a ^ 2 + 4 = k * T ^ 2) (hQ : d ^ 2 + 4 = T ^ 2 * (k + 2 * t * x + x ^ 2))
    (hZ : d + r = q * (k + 2 * t * x + x ^ 2) / (1 + x) * T) :
    m2Next a c d r u v (m2h a (m2bStar a c) c u v) = nsfTn t x k q v u := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hh := nsf_m2h_u (u := u) (v := v) hT ht hk ha hc hK
  obtain ⟨hw, hhd⟩ := nsf_m2wOf_u (u := u) (v := v) hT hB ha hc hd hK hQ hh
  have hW : 0 < 1 + x := by linarith
  -- `r² + 4 = T² B E`
  have hs : 4 = T ^ 2 * (k - t ^ 2) := by
    have : a ^ 2 = t ^ 2 * T ^ 2 := by rw [ha]; ring
    nlinarith
  have hr : r = (q * (k + 2 * t * x + x ^ 2) / (1 + x) - (t + x)) * T := by
    rw [sub_mul, ← hZ, hd]; ring
  have hKr : r ^ 2 + 4 = T ^ 2 * ((k + 2 * t * x + x ^ 2) * nsfE t x k q) := by
    rw [hr, hs]; unfold nsfE; field_simp; ring
  have hE : nsfE t x k q ≠ 0 := by
    intro h0
    have : r ^ 2 + 4 = 0 := by rw [hKr, h0]; ring
    nlinarith [sq_nonneg r]
  unfold m2Next
  rw [hw, hhd, hQ, hZ, hKr]
  unfold nsfTn nsfwn
  field_simp

/-- The root function is affine in `u` with slope `-k²D/(tB)`. -/
theorem nsf_Rn_sub {t x k q v L u u' : ℝ} (ht : 0 < t) (hx : 0 < x) (hk : 0 < k) (hq : 0 < q) :
    nsfRn t x k q v L u - nsfRn t x k q v L u' =
      (u - u') * (-(k ^ 2 * nsfD t x q / (t * (k + 2 * t * x + x ^ 2)))) := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hW : 0 < 1 + x := by linarith
  unfold nsfRn nsfwn nsfHn nsfD
  field_simp
  ring

/-- The next norm is affine in `u` with slope `e²k²(Je² - 1)/(tE²)`. -/
theorem nsf_Tn_sub {t x k q v u u' : ℝ} (ht : 0 < t) (hx : 0 < x) (hk : 0 < k) :
    nsfTn t x k q v u - nsfTn t x k q v u' =
      (u - u') * ((q / (1 + x)) ^ 2 * k ^ 2 * ((t + x * (x + 2)) * (q / (1 + x)) ^ 2 - 1) /
        (t * nsfE t x k q ^ 2)) := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hW : 0 < 1 + x := by linarith
  unfold nsfTn nsfwn nsfHn
  by_cases hE : nsfE t x k q = 0
  · simp [hE]
  field_simp
  ring

/-- At the incident ceiling `U(t/k)` the root function is `nsrR`. -/
theorem nsf_Rn_U {t x k q v L : ℝ} (ht : 0 < t) (hk : 0 < k) :
    nsfRn t x k q v L (m2U (t / k)) = nsrR t x k q v L := by
  have hH : nsfHn t k v (m2U (t / k)) = k / t * (v - 1 + t ^ 2) + t * (2 - t) := by
    unfold nsfHn m2U; field_simp; ring
  have hw : k ^ 2 * m2U (t / k) = k ^ 2 - k * t + t ^ 2 := by unfold m2U; field_simp
  unfold nsfRn nsfwn nsrR
  rw [hH, hw]

/-- **The cleared transport part** is `4qW² C_*(3/4 - 𝒯_U)` with `C_* = tW²DE²/e`. -/
theorem nsf_TP_eq {t x k q v : ℝ} (ht : 0 < t) (hx : 0 < x) (hk : 0 < k) (hq : 0 < q)
    (hE : nsfE t x k q ≠ 0) :
    nsfTP t x k q v = 4 * q * (1 + x) ^ 2 *
      (t * (1 + x) ^ 2 * nsfD t x q * nsfE t x k q ^ 2 / (q / (1 + x))) *
        (3 / 4 - nsfTn t x k q v (m2U (t / k))) := by
  have hB : 0 < k + 2 * t * x + x ^ 2 := by positivity
  have hW : 0 < 1 + x := by linarith
  have hH : nsfHn t k v (m2U (t / k)) = nsfHt t k v / t := by
    unfold nsfHn nsfHt m2U; field_simp; ring
  have hw : nsfwn t x k v (m2U (t / k)) = nsfKt t x k v / (t * (k + 2 * t * x + x ^ 2) ^ 2) := by
    unfold nsfwn nsfKt; rw [hH]; unfold m2U nsfHt; field_simp
  have hE0 : nsfE t x k q = nsfE0 t x k q / (1 + x) ^ 2 := by unfold nsfE nsfE0; field_simp
  unfold nsfTn
  rw [hH, hw]
  rw [hE0] at hE ⊢
  have hE' : nsfE0 t x k q ≠ 0 := by intro h0; apply hE; rw [h0]; simp
  unfold nsfTP nsfD
  field_simp
  ring

end SmoothedOctagon
