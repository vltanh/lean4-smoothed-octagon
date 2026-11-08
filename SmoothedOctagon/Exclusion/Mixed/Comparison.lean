module

public import SmoothedOctagon.Exclusion.Mixed.Window
public import SmoothedOctagon.Exclusion.Mixed.ChartAux.Root

/-!
# Case M2: the scalar boundary comparison `b → b*`

An ODE-free comparison between the actual smaller-nonshort window and its boundary window. Hold
`a, c, d, r` and the actual incoming secant `v` fixed and move the central margin `b` up to
`b* = K/T - a` (central factor one). The root function `R_d(u; b)` (`m2RootAt`, with central
stationarity imposed) is affine in `u` with slope `R_u(b) < 0` on `[a, b*]`, so it has the unique
root `u(b)` (`m2uRoot`). Along the incident ceiling,
`G(b) = R_d(U(a/(a+b)); b)` has `G'(b) = R_u(b) a (b - a)/(a + b)³ < 0`, and on the root curve
`dw/db = d K³ G(b)/(a Q³ R_u(b)²)`. Since `G(b_act) = R_u (U - u_act) ≤ 0`, `G(b*) < 0`, the
boundary root lies strictly below the ceiling, `u* < U(aT/K)`, and `w* < w_act`.

## Main API

* `m2RootAt`, `m2uRoot`, `m2bStar`; `M2Window.bStar`, `uStar`, `hStar`, `wStar`, `tStar` (the
  boundary values).
* `m2_comparison`: `G(b*) < 0`, `R_d(u*; b*) = 0`, `u* < U(aT/K)` and `w* < w`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The root function `R_d(u; b)` with central stationarity `h = m2h a b c u v` imposed. -/
noncomputable def m2RootAt (a b c d r v u : ℝ) : ℝ := m2Root a c d r u v (m2h a b c u v)

/-- The root of the affine map `u ↦ m2RootAt a b c d r v u`. -/
noncomputable def m2uRoot (a b c d r v : ℝ) : ℝ :=
  -m2RootAt a b c d r v 0 / (m2RootAt a b c d r v 1 - m2RootAt a b c d r v 0)

/-- The boundary value `b* = K/T - a` of the central margin. -/
noncomputable def m2bStar (a c : ℝ) : ℝ := (a ^ 2 + 4) / (a + c) - a

namespace M2Window

variable (W : M2Window)

/-- `b* = K/T - a`. -/
noncomputable def bStar : ℝ := m2bStar W.a W.c

/-- The boundary root `u* = u(b*)`. -/
noncomputable def uStar : ℝ := m2uRoot W.a W.bStar W.c W.d W.r W.v

/-- The boundary diagonal `h* = h(u*, b*)`. -/
noncomputable def hStar : ℝ := m2h W.a W.bStar W.c W.uStar W.v

/-- The boundary transported norm `w* = w(b*)`. -/
noncomputable def wStar : ℝ := m2wOf W.a W.c W.d W.uStar W.v W.hStar

/-- The boundary next norm `t* = 𝒯(w*)`. -/
noncomputable def tStar : ℝ := m2Next W.a W.c W.d W.r W.uStar W.v W.hStar

/-- The incident ceiling at the boundary, `U* = U(a/S*) = U(aT/K)`. -/
noncomputable def ceilStar : ℝ := m2U (W.a * (W.a + W.c) / (W.a ^ 2 + 4))

end M2Window

/-- **The boundary comparison**. For the actual smaller-nonshort window: `G(b*) = R_d(U*; b*) < 0`,
the boundary root solves `R_d(u*; b*) = 0`, lies strictly below the incident ceiling, `u* < U*`,
and the boundary transported norm is strictly below the actual one, `w* < w`.
The proof is ODE-free: `G` and the root-curve diagonal `chH` are strictly decreasing on `[b, b*]`
by their derivatives (`Mixed/ChartAux/Root`); only the weak `u ≤ U(a/S)` is used. -/
theorem m2_comparison (W : M2Window) :
    m2RootAt W.a W.bStar W.c W.d W.r W.v W.ceilStar < 0 ∧
      m2RootAt W.a W.bStar W.c W.d W.r W.v W.uStar = 0 ∧ W.uStar < W.ceilStar ∧ W.wStar < W.w := by
  have ha := W.a_pos
  have hc : 0 < W.c := by linarith [W.a_lt_c]
  have hd : 0 < W.d := by linarith [W.a_lt_d]
  have hr : 0 < W.r := by linarith [W.a_le_r]
  have hT : 0 < W.a + W.c := by linarith
  have hK : 0 < W.a ^ 2 + 4 := by positivity
  have hSstar : W.a + W.bStar = (W.a ^ 2 + 4) / (W.a + W.c) := by
    unfold M2Window.bStar m2bStar; ring
  have hbb : W.b < W.bStar := by
    have : W.a + W.b < (W.a ^ 2 + 4) / (W.a + W.c) := by
      rw [lt_div_iff₀ hT]; exact W.central
    linarith
  have hRu : ∀ x ∈ Set.Icc W.b W.bStar, chRu W.a x W.c W.d W.r < 0 := by
    intro x hx
    refine ch_Ru_neg ha hc W.a_lt_d W.factor_d (by linarith [hx.1, W.a_lt_b]) ?_
    have : W.a + x ≤ (W.a ^ 2 + 4) / (W.a + W.c) := by rw [← hSstar]; linarith [hx.2]
    rwa [le_div_iff₀ hT] at this
  -- `G` is strictly decreasing on `[b, b*]`
  have hGanti : StrictAntiOn (chG W.a W.c W.d W.r W.v) (Set.Icc W.b W.bStar) := by
    refine ch_strictAntiOn (fun x hx => ch_hasDerivAt_G ha (by linarith [hx.1, W.a_lt_b]) hT) ?_
    intro x hx
    refine mul_neg_of_neg_of_pos (hRu x (Set.Ioo_subset_Icc_self hx)) ?_
    have : 0 < W.a + x := by linarith [hx.1, W.a_lt_b]
    exact div_pos (mul_pos ha (by linarith [hx.1, W.a_lt_b])) (by positivity)
  have hroot0 : m2Root W.a W.c W.d W.r W.u W.v (m2h W.a W.b W.c W.u W.v) = 0 := by
    rw [← W.h_eq]; exact W.root
  -- `G(b) ≤ 0`
  have hG0 : chG W.a W.c W.d W.r W.v W.b ≤ 0 := by
    have hU : W.u ≤ m2U (W.a / (W.a + W.b)) := by
      rw [← m2g_eq_m2U (by linarith [W.a_lt_b])]; exact W.u_le
    have hR0 := hRu W.b ⟨le_rfl, hbb.le⟩
    have h1 := hroot0
    unfold chG
    rw [ch_root_affine ha.ne'] at h1 ⊢
    nlinarith
  have hGlt : ∀ x ∈ Set.Ioc W.b W.bStar, chG W.a W.c W.d W.r W.v x < 0 := fun x hx =>
    lt_of_lt_of_le (hGanti ⟨le_rfl, hbb.le⟩ ⟨hx.1.le, hx.2⟩ hx.1) hG0
  have hGs := hGlt W.bStar ⟨hbb, le_rfl⟩
  have hceil : W.ceilStar = m2U (W.a / (W.a + W.bStar)) := by
    unfold M2Window.ceilStar
    rw [hSstar]
    congr 1
    field_simp
  have hRs := hRu W.bStar ⟨hbb.le, le_rfl⟩
  -- the boundary root
  have hR1 : m2RootAt W.a W.bStar W.c W.d W.r W.v 1 - m2RootAt W.a W.bStar W.c W.d W.r W.v 0 =
      chRu W.a W.bStar W.c W.d W.r := by
    unfold m2RootAt; rw [ch_root_affine (u := 1) ha.ne']; ring
  have hus : W.uStar = -m2RootAt W.a W.bStar W.c W.d W.r W.v 0 / chRu W.a W.bStar W.c W.d W.r := by
    unfold M2Window.uStar m2uRoot; rw [hR1]
  have hrootS : m2RootAt W.a W.bStar W.c W.d W.r W.v W.uStar = 0 := by
    unfold m2RootAt
    rw [ch_root_affine ha.ne', hus]
    unfold m2RootAt
    have := hRs.ne
    field_simp
    ring
  have hGs' : m2RootAt W.a W.bStar W.c W.d W.r W.v W.ceilStar < 0 := by
    rw [hceil]; exact hGs
  have huU : W.uStar < W.ceilStar := by
    have h1 := hGs'
    have h2 := hrootS
    unfold m2RootAt at h1 h2
    rw [ch_root_affine ha.ne'] at h1 h2
    nlinarith
  refine ⟨hGs', hrootS, huU, ?_⟩
  -- `w* < w`: the diagonal on the root curve decreases
  have hβ : chβ W.a W.d W.r < 0 := by
    unfold chβ
    have : 0 < (W.d ^ 2 + 4) ^ 2 := by positivity
    have h1 : 0 < (W.d + W.r) * (W.a ^ 2 + 4) ^ 2 := mul_pos (by linarith) (by positivity)
    exact div_neg_of_neg_of_pos (by linarith [neg_mul (W.d + W.r) ((W.a ^ 2 + 4) ^ 2)]) this
  have hHanti : StrictAntiOn (chH W.a W.c W.d W.r W.v) (Set.Icc W.b W.bStar) := by
    refine ch_strictAntiOn (fun x hx => ch_hasDerivAt_H ha (by linarith [hx.1, W.a_lt_b]) hT
      (hRu x hx).ne) ?_
    intro x hx
    have hG := hGlt x ⟨hx.1, hx.2.le⟩
    have hR := hRu x (Set.Ioo_subset_Icc_self hx)
    have hk : 0 < (W.a ^ 2 + 4) / (16 * W.a) := by positivity
    have : 0 < -((W.a ^ 2 + 4) / (16 * W.a)) * chβ W.a W.d W.r := by nlinarith
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg this hG) (by nlinarith)
  have hHlt := hHanti ⟨le_rfl, hbb.le⟩ ⟨hbb.le, le_rfl⟩ hbb
  have hhs : W.hStar = chH W.a W.c W.d W.r W.v W.bStar := ch_h_of_root ha hRs.ne hrootS
  have hh0 : W.h = chH W.a W.c W.d W.r W.v W.b := by
    rw [W.h_eq]; exact ch_h_of_root ha (hRu W.b ⟨le_rfl, hbb.le⟩).ne hroot0
  have hZ : 0 < W.d + W.r := by linarith
  have hws : W.wStar = (m2Stat W.c W.d W.r - (W.c + W.d) * W.v +
      16 * W.d * m2hd W.a W.c W.d W.v W.hStar / (W.d ^ 2 + 4)) / (W.d + W.r) :=
    ch_w_of_root hZ hrootS
  have hw : W.w = (m2Stat W.c W.d W.r - (W.c + W.d) * W.v +
      16 * W.d * m2hd W.a W.c W.d W.v W.h / (W.d ^ 2 + 4)) / (W.d + W.r) := by
    rw [W.w_eq]; exact ch_w_of_root hZ W.root
  rw [hws, hw]
  apply div_lt_div_of_pos_right _ hZ
  have hQ : 0 < W.d ^ 2 + 4 := by positivity
  have : 16 * W.d * m2hd W.a W.c W.d W.v W.hStar / (W.d ^ 2 + 4) <
      16 * W.d * m2hd W.a W.c W.d W.v W.h / (W.d ^ 2 + 4) := by
    apply div_lt_div_of_pos_right _ hQ
    unfold m2hd
    rw [hhs, hh0]
    nlinarith
  linarith

end SmoothedOctagon
