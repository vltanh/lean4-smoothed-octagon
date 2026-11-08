module

public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S4HandW1a

/-!
# W1, part b: the normalized shape source `N` and its boundary jets

`archive/lighter-proofs/SHORT_CASIMIR_FIRST_DERIVATIVES.md` §3.2. On the upper faces
`b = 20x/19`, `u = 19/25` the normalized source is
`N(x, a) = 3325a²(19a + 20x)²K³Φ_a(x, a, 20x/19, 19/25)`. The note prints its boundary jets
`N(2, a) = V(a)`, `N_x(2, a) = W(a)` and its second derivative `-N_xx = P_N(c, h)`
(`c = a - 1`, `h = x - 2`). Integrating `P_N = Σ_j π_j(c) h^j` twice in `h`,

`N = V(a) + W(a)h - h²Q(c, h)`, `Q = Σ_j π_j(c) h^j/((j + 1)(j + 2))`,

an identity of polynomials of degree ten in two variables (`hl46_w1_N_taylor`), proved from the
source form `hl46W1Nsrc` (`hl46_w1_Pa_src`). The monomial rule of the note (§3: discard the
positive terms containing `c`, bound `c^i` by `(3/19)^i` in the negative ones) applied to the
printed `P_N`, `-W(1 + c)`, `V'(1 + c)` gives `Q ≥ 1100000000 + 1770000000h`,
`-W(1 + c) > 172000000`, `V'(1 + c) > 0`.

## Main API

* `hl46W1Nsrc`, `hl46W1V`, `hl46W1V1`, `hl46W1W`, `hl46W1Q`.
* `hl46_w1_Pa_src`: `Φ_a = -Nsrc/(7a²B²K³)`.
* `hl46_w1_N_taylor`: `-171475·Nsrc(x, 20x/19, a, 19/25) = V(a) + W(a)(x - 2) - (x - 2)²Q`.
* `hl46_w1_mon`, `hl46_w1_nn`: the monomial rule.
* `hl46_w1_Q_ge`, `hl46_w1_W_neg`, `hl46_w1_V1_pos`, `hl46_w1_V_deriv`, `hl46_w1_V_mono`,
  `hl46_w1_V_le`, `hl46_w1_V_neg`.
-/

@[expose] public section

namespace SmoothedOctagon

open Real

/-- The source `a²B²K³(2w_a + (R - log)_a + (log y)_a)`, a polynomial in `D`, `E`, `x, a, b`. -/
noncomputable def hl46W1Nsrc (x be al u : ℝ) : ℝ :=
  2 * al ^ 2 * (al + be) ^ 2 *
      ((2 * hsDg x be al * u - hh46S4P x u) * (2 * (al + be)) * (x * (x + 2) + al ^ 2) -
        4 * al * ((1 + x) ^ 2 * ((1 + x) ^ 2 - (1 + x) + 1) + hsDg x be al ^ 2 * u -
          hsDg x be al * hh46S4P x u)) +
    (-(u - 1) * be * (al + be) ^ 2 * (x * (x + 2) + al ^ 2) ^ 3 +
      be * al ^ 2 * (x * (x + 2) + al ^ 2) ^ 3 -
      2 * al ^ 3 * (x * (x + 2)) * (al + be) ^ 2 * (x * (x + 2) + al ^ 2) -
      al ^ 2 * (al + be) ^ 2 * (x * (x + 2) + al ^ 2) *
        (2 * u * (2 * (al + be)) * (x * (x + 2) + al ^ 2) -
          (2 * hsDg x be al * u - hh46S4P x u) * (2 * al))) +
    al * (al + be) * (x * (x + 2) + al ^ 2) ^ 2 * (x * (x + 2) * (2 * al + be) - al ^ 2 * be)

/-- `V(a) = N(2, a)` (note §3.2, printed). -/
noncomputable def hl46W1V (a : ℝ) : ℝ :=
  1010800 * a ^ 8 + 7782704 * a ^ 7 - 67738240 * a ^ 6 - 224073888 * a ^ 5 + 174466560 * a ^ 4 +
    959667200 * a ^ 3 - 202055680 * a ^ 2 - 575897600 * a - 196608000

/-- `V'`. -/
noncomputable def hl46W1V1 (a : ℝ) : ℝ :=
  8086400 * a ^ 7 + 54478928 * a ^ 6 - 406429440 * a ^ 5 - 1120369440 * a ^ 4 +
    697866240 * a ^ 3 + 2879001600 * a ^ 2 - 404111360 * a - 575897600

/-- `W(a) = N_x(2, a)` (note §3.2, printed). -/
noncomputable def hl46W1W (a : ℝ) : ℝ :=
  505400 * a ^ 8 + 8976170 * a ^ 7 - 80987040 * a ^ 6 - 435736672 * a ^ 5 + 226700800 * a ^ 4 +
    2482515200 * a ^ 3 - 346757120 * a ^ 2 - 1871667200 * a - 737280000

/-- `Q = Σ_j π_j(c)h^j/((j + 1)(j + 2))`, where `P_N = -N_xx = Σ_j π_j(c)h^j` is the printed
degree-eight polynomial of note §3.2 (its coefficients grouped by powers of `h`). -/
noncomputable def hl46W1Q (c h : ℝ) : ℝ :=
  (-5372896 * c ^ 7 + 17904608 * c ^ 6 + 842261304 * c ^ 5 + 3719761880 * c ^ 4 +
      1853070800 * c ^ 3 - 8463256816 * c ^ 2 - 6417881512 * c + 3430692024) / 2 +
    (-493848 * c ^ 7 + 821064 * c ^ 6 + 588053628 * c ^ 5 + 3567218220 * c ^ 4 +
      496121760 * c ^ 3 - 14675499648 * c ^ 2 - 7030594116 * c + 12109411788) * h / 6 +
    (-8317440 * c ^ 6 + 69503784 * c ^ 5 + 1312248840 * c ^ 4 + 648953520 * c ^ 3 -
      6268171920 * c ^ 2 + 2516207400 * c + 16603897224) * h ^ 2 / 12 +
    (-4911120 * c ^ 5 + 322024400 * c ^ 4 + 1202862800 * c ^ 3 + 1183126000 * c ^ 2 +
      6279212800 * c + 11547694080) * h ^ 3 / 20 +
    (47289600 * c ^ 4 + 505890900 * c ^ 3 + 1314887100 * c ^ 2 + 3055947900 * c +
      4388462100) * h ^ 4 / 30 +
    (59068800 * c ^ 3 + 251685840 * c ^ 2 + 585994080 * c + 901409040) * h ^ 5 / 42 +
    (10752000 * c ^ 2 + 37251200 * c + 91011200) * h ^ 6 / 56 + 3456000 * h ^ 7 / 72

/-- `Φ_a = -Nsrc/(7a²B²K³)`. -/
theorem hl46_w1_Pa_src {x be al u : ℝ} (hx : 0 < x) (hal : 0 < al) (hbe : 0 < be) :
    hl46W1Pa x be al u =
      -hl46W1Nsrc x be al u / (7 * al ^ 2 * (al + be) ^ 2 * (x * (x + 2) + al ^ 2) ^ 3) := by
  have hK : 0 < x * (x + 2) + al ^ 2 := by positivity
  have hB : 0 < al + be := by positivity
  unfold hl46W1Pa hl46W1Wa hl46W1Ra hl46W1La hl46W1Nsrc
  field_simp

/-- The two integrations of `-N_xx = P_N` from the boundary jets `V`, `W`. -/
theorem hl46_w1_N_taylor (x al : ℝ) :
    -171475 * hl46W1Nsrc x (20 * x / 19) al (19 / 25) =
      hl46W1V al + hl46W1W al * (x - 2) - (x - 2) ^ 2 * hl46W1Q (al - 1) (x - 2) := by
  unfold hl46W1Nsrc hl46W1V hl46W1W hl46W1Q hsDg hh46S4P
  ring

/-! ### The monomial rule -/

theorem hl46_w1_mon {c h γ : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ γ) (hh : 0 ≤ h) (i j : ℕ) :
    c ^ i * h ^ j ≤ γ ^ i * h ^ j :=
  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hc0 hc i) (pow_nonneg hh j)

theorem hl46_w1_nn {c h : ℝ} (hc0 : 0 ≤ c) (hh : 0 ≤ h) (i j : ℕ) : 0 ≤ c ^ i * h ^ j := by
  positivity

/-- The monomial rule on `P_N` (note §3.2, `L_N(h) > 0`), integrated twice. -/
theorem hl46_w1_Q_ge {c h : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 3 / 19) (hh : 0 ≤ h) :
    1100000000 + 1770000000 * h ≤ hl46W1Q c h := by
  have m := hl46_w1_mon hc0 hc hh
  have n := hl46_w1_nn hc0 hh
  unfold hl46W1Q
  linarith [m 7 0, m 2 0, m 1 0, m 7 1, m 2 1, m 1 1, m 6 2, m 2 2, m 5 3,
    n 6 0, n 5 0, n 4 0, n 3 0, n 6 1, n 5 1, n 4 1, n 3 1, n 5 2, n 4 2, n 3 2, n 1 2,
    n 4 3, n 3 3, n 2 3, n 1 3, n 4 4, n 3 4, n 2 4, n 1 4, n 3 5, n 2 5, n 1 5,
    n 2 6, n 1 6, n 0 2, n 0 3, n 0 4, n 0 5, n 0 6, n 0 7]

/-- `-W(1 + c) > 172000000` (note §3.2, `L_W > 172746439`). -/
theorem hl46_w1_W_neg {a : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 22 / 19) : hl46W1W a ≤ -172000000 := by
  have hc0 : 0 ≤ a - 1 := by linarith
  have hc : a - 1 ≤ 3 / 19 := by linarith
  have e : -hl46W1W a = -505400 * (a - 1) ^ 8 - 13019370 * (a - 1) ^ 7 + 4002650 * (a - 1) ^ 6 +
      704856942 * (a - 1) ^ 5 + 2817244210 * (a - 1) ^ 4 + 2245320770 * (a - 1) ^ 3 -
      3091471730 * (a - 1) ^ 2 - 3191438150 * (a - 1) + 753730462 := by
    unfold hl46W1W; ring
  have m := hl46_w1_mon hc0 hc zero_le_one
  have n := hl46_w1_nn hc0 zero_le_one
  simp only [one_pow, mul_one] at m n
  generalize a - 1 = c at *
  have : 172000000 ≤ -hl46W1W a := by
    rw [e]
    linarith [m 8 0, m 7 0, m 2 0, m 1 0, n 6 0, n 5 0, n 4 0, n 3 0]
  linarith

/-- `V'(1 + c) > 0` (note §3.2, `L_V > 0`). -/
theorem hl46_w1_V1_pos {a : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 22 / 19) : 0 < hl46W1V1 a := by
  have hc0 : 0 ≤ a - 1 := by linarith
  have hc : a - 1 ≤ 3 / 19 := by linarith
  have e : hl46W1V1 a = 8086400 * (a - 1) ^ 7 + 111083728 * (a - 1) ^ 6 + 90258528 * (a - 1) ^ 5 -
      2052308720 * (a - 1) ^ 4 - 6475303360 * (a - 1) ^ 3 - 4826912400 * (a - 1) ^ 2 +
      1317343968 * (a - 1) + 1132625328 := by
    unfold hl46W1V1; ring
  have m := hl46_w1_mon hc0 hc zero_le_one
  have n := hl46_w1_nn hc0 zero_le_one
  simp only [one_pow, mul_one] at m n
  generalize a - 1 = c at *
  rw [e]
  linarith [m 4 0, m 3 0, m 2 0, n 7 0, n 6 0, n 5 0, n 1 0]

theorem hl46_w1_V_deriv (a : ℝ) : HasDerivAt hl46W1V (hl46W1V1 a) a := by
  have := ((((((((((hasDerivAt_pow 8 a).const_mul 1010800).fun_add
    ((hasDerivAt_pow 7 a).const_mul 7782704)).fun_sub
    ((hasDerivAt_pow 6 a).const_mul 67738240)).fun_sub
    ((hasDerivAt_pow 5 a).const_mul 224073888)).fun_add
    ((hasDerivAt_pow 4 a).const_mul 174466560)).fun_add
    ((hasDerivAt_pow 3 a).const_mul 959667200)).fun_sub
    ((hasDerivAt_pow 2 a).const_mul 202055680)).fun_sub
    ((hasDerivAt_id' a).const_mul 575897600)).sub_const 196608000)
  refine this.congr_deriv ?_
  unfold hl46W1V1
  push_cast
  ring

/-- `V` increases on the shape interval. -/
theorem hl46_w1_V_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 22 / 19) :
    hl46W1V a ≤ hl46W1V b :=
  hl46_mono_of (a := 1) (b := 22 / 19) (fun z _ => hl46_w1_V_deriv z)
    (fun _ hz => (hl46_w1_V1_pos hz.1 hz.2).le) ha hab hb

/-- `V(22/19) < 64431000`. -/
theorem hl46_w1_V_le {a : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 22 / 19) : hl46W1V a < 64431000 :=
  (hl46_w1_V_mono ha ha' le_rfl).trans_lt (by norm_num [hl46W1V])

/-- `V(11/10) < -5000000`. -/
theorem hl46_w1_V_neg {a : ℝ} (ha : 1 ≤ a) (ha' : a ≤ 11 / 10) : hl46W1V a < -5000000 :=
  (hl46_w1_V_mono ha ha' (by norm_num)).trans_lt (by norm_num [hl46W1V])

end SmoothedOctagon
