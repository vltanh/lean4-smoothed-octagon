module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.Shape3

/-!
# Smaller-short window, lower ratio: the central low-ratio face

`lr_central_face_proof` proves the central face sign `lr_central_face`.
The duration reduction `lrc_face_red` leaves `F₀`, `F₁` (cubic majorant). On the central face
(`x ≥ 41/25`, `1 ≤ α ≤ α_c = √(x(x + 2)/6)`, strip `x + (α - 1)/2 ≤ β ≤ β₊ = x + (10/13)(α - 1)`,
`3/4 ≤ u ≤ u_ℓ(x, β) ≤ 19/25`):

* `F₁`: the norm rises to `19/25`, `β` to `β₊` (`CentralFace/NormBeta`, `CentralFace/Beta`), `F₁` is concave in `α`
  along `β₊` (`CentralFace/Shape3`), and its two ends are the univariate face `α = 1` and the cap `α = α_c`;
* `F₀`: the norm rises to the ceiling `u_ℓ(x, β)`, `β` to `β₊` along it, and `α` to the cap along
  `(β₊, u_ℓ)` (`lrc_F0_astep_ul`);
* at the cap `K = 7α²` the central and outer transports coincide (`lrc_cap`), so the outer
  branch-B signs `lro_B_F0`, `lro_B_F1` close both tests.

## Main API

* `lrc_F0_astep`, `lrc_F0_astep_ul`, `lrc_F1_conc`, `lrcT1`, `lrc_cap`,
  `lr_central_face_proof`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real


/-! ### The first test along `β₊` -/

theorem lrc_fa_affine {x t b u : ℝ} :
    lrcR2a x t b u + 10 / 13 * lrcR2b x t b u = (lrcR2a x t b (3 / 4) + 10 / 13 * lrcR2b x t b (3 / 4)) +
      (u - 3 / 4) * 100 * ((lrcR2a x t b (19 / 25) + 10 / 13 * lrcR2b x t b (19 / 25)) -
        (lrcR2a x t b (3 / 4) + 10 / 13 * lrcR2b x t b (3 / 4))) := by
  simp only [lrcR2a, lrcwa, lrcELa, lrcR2b, lrcwb, lrcE]
  ring

theorem lrc_fa_id {x t u : ℝ} (hx : 41 / 25 ≤ x) (ht : 1 ≤ t) (hu : u = 3 / 4 ∨ u = 19 / 25) :
    1 / 40 + 2 / 625 ≤ lrcR2a x t (x + 10 / 13 * (t - 1)) u +
      10 / 13 * lrcR2b x t (x + 10 / 13 * (t - 1)) u ∨ t > (1013 * x + 676) / 2340 ∨ x > 2 := by
  by_cases hreg : t ≤ (1013 * x + 676) / 2340 ∧ x ≤ 2
  · left
    obtain ⟨htU, hx2⟩ := hreg
    have hx0 : 0 < x := by linarith
    have ht0 : 0 < t := by linarith
    have hS : 1 + x ≠ 0 := by linarith
    have hKn : x * (x + 2) + t ^ 2 ≠ 0 := by positivity
    have hs0 : 0 ≤ (1013 * x + 676) / 2340 - t := by linarith
    have hs1 : (1013 * x + 676) / 2340 - t ≤ 31 / 200 := by linarith
    have hden : 0 < t ^ 2 * (23 * t + 13 * x - 10) ^ 2 * (x * (x + 2) + t ^ 2) ^ 3 := by
      have : 0 < 23 * t + 13 * x - 10 := by linarith
      positivity
    have hBq : t + (x + 10 / 13 * (t - 1)) = (23 * t + 13 * x - 10) / 13 := by ring
    rcases hu with rfl | rfl
    · have hP := lrcPafs_pos (t := x - 41 / 25) (s := (1013 * x + 676) / 2340 - t) (by linarith)
        (by linarith) hs0 hs1
      rw [← lrcPafx_eq] at hP
      have hid : lrcR2a x t (x + 10 / 13 * (t - 1)) (3 / 4) +
          10 / 13 * lrcR2b x t (x + 10 / 13 * (t - 1)) (3 / 4) - 1 / 40 - 2 / 625 =
            lrcPafx x t / (t ^ 2 * (23 * t + 13 * x - 10) ^ 2 * (x * (x + 2) + t ^ 2) ^ 3) := by
        simp only [lrcR2a, lrcwa, lrcELa, lrcLa, lrcda, lrcqa, lrcq, lrcR2b, lrcwb, lrcdb,
          lrcd, lrcL, lrcv, lrcE, ssDg, lrcK, lrcPafx]
        rw [hBq]
        have hB : 23 * t + 13 * x - 10 ≠ 0 := by linarith
        generalize hBg : 23 * t + 13 * x - 10 = Bg at hB ⊢
        field_simp
        subst hBg
        ring
      have : 0 ≤ lrcPafx x t / (t ^ 2 * (23 * t + 13 * x - 10) ^ 2 * (x * (x + 2) + t ^ 2) ^ 3) :=
        div_nonneg hP hden.le
      linarith
    · have hP := lrcPavs_pos (t := x - 41 / 25) (s := (1013 * x + 676) / 2340 - t) (by linarith)
        (by linarith) hs0 hs1
      rw [← lrcPavx_eq] at hP
      have hid : lrcR2a x t (x + 10 / 13 * (t - 1)) (19 / 25) +
          10 / 13 * lrcR2b x t (x + 10 / 13 * (t - 1)) (19 / 25) - 1 / 40 - 2 / 625 =
            lrcPavx x t / (t ^ 2 * (23 * t + 13 * x - 10) ^ 2 * (x * (x + 2) + t ^ 2) ^ 3) := by
        simp only [lrcR2a, lrcwa, lrcELa, lrcLa, lrcda, lrcqa, lrcq, lrcR2b, lrcwb, lrcdb,
          lrcd, lrcL, lrcv, lrcE, ssDg, lrcK, lrcPavx]
        rw [hBq]
        have hB : 23 * t + 13 * x - 10 ≠ 0 := by linarith
        generalize hBg : 23 * t + 13 * x - 10 = Bg at hB ⊢
        field_simp
        subst hBg
        ring
      have : 0 ≤ lrcPavx x t / (t ^ 2 * (23 * t + 13 * x - 10) ^ 2 * (x * (x + 2) + t ^ 2) ^ 3) :=
        div_nonneg hP hden.le
      linarith
  · right
    push Not at hreg
    by_contra h
    push Not at h
    exact absurd (hreg h.1) (not_lt.mpr h.2)

/-- The slope of the first test along `β₊` at a fixed norm. -/
theorem lrc_fa_ge {x t u : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ht : 1 ≤ t)
    (htU : t ≤ (1013 * x + 676) / 2340) (hu0 : 3 / 4 ≤ u) (hu1 : u ≤ 19 / 25) :
    1 / 40 + 2 / 625 ≤ lrcR2a x t (x + 10 / 13 * (t - 1)) u +
      10 / 13 * lrcR2b x t (x + 10 / 13 * (t - 1)) u := by
  have h1 := lrc_fa_id (u := 3 / 4) hx ht (Or.inl rfl)
  have h2 := lrc_fa_id (u := 19 / 25) hx ht (Or.inr rfl)
  rcases h1 with h1 | h1 | h1
  · rcases h2 with h2 | h2 | h2
    · rw [lrc_fa_affine]
      nlinarith
    · exact absurd htU (not_le.mpr h2)
    · exact absurd hx2 (not_le.mpr h2)
  · exact absurd htU (not_le.mpr h1)
  · exact absurd hx2 (not_le.mpr h1)

/-- **`α ↦ F₀(x, α, β₊(α), u)` decreases** at a fixed norm, with slope at most `-c/40`. -/
theorem lrc_F0_astep {x a1 a2 u : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (h1 : 1 ≤ a1)
    (h12 : a1 ≤ a2) (h2U : a2 ≤ (1013 * x + 676) / 2340) (h2 : a2 ≤ 7 / 6) (hu0 : 3 / 4 ≤ u)
    (hu1 : u ≤ 19 / 25) :
    lrcF0 x a2 (x + 10 / 13 * (a2 - 1)) u ≤
      lrcF0 x a1 (x + 10 / 13 * (a1 - 1)) u - 7 / 96 * (1 / 40) * (a2 - a1) := by
  have hx0 : 0 < x := by linarith
  have key := ss_le_of_deriv (f := fun t => -(lrcF0 x t (x + 10 / 13 * (t - 1)) u +
      7 / 96 * (1 / 40) * t))
    (f' := fun t => -(0 * (lrcGx x u - 7 / 96 * lrcR2x x t (x + 10 / 13 * (t - 1)) u) +
      1 * (-(7 / 96) * lrcR2a x t (x + 10 / 13 * (t - 1)) u) +
      10 / 13 * (-(7 / 96) * lrcR2b x t (x + 10 / 13 * (t - 1)) u) +
      0 * (lrcGu x u - 7 / 96 * lrcR2u x t (x + 10 / 13 * (t - 1))) +
      7 / 96 * lreps (lrcy x t (x + 10 / 13 * (t - 1))) *
        (-(2 * (1 + x) / lrcK x t) * 0 + (1 / t + 1 / (t + (x + 10 / 13 * (t - 1))) -
          2 * t / lrcK x t) * 1 + 1 / (t + (x + 10 / 13 * (t - 1))) * (10 / 13)) +
      7 / 96 * (1 / 40)))
    (x := a1) (y := a2) h12
    (fun t ht => by
      have hb : HasDerivAt (fun s => x + 10 / 13 * (s - 1)) (10 / 13) t := by
        simpa using (((hasDerivAt_id' t).sub_const 1).const_mul (10 / 13)).const_add x
      exact ((lrc_F0_hasDerivAt (hasDerivAt_const t x) (hasDerivAt_id' t) hb
        (hasDerivAt_const t u) hx0 (by linarith [ht.1]) (by nlinarith [ht.1])).add
          ((hasDerivAt_id' t).const_mul (7 / 96 * (1 / 40)))).neg |>.congr_deriv (by ring))
    (fun t ht => by
      have ht1 : 1 ≤ t := by linarith [ht.1]
      have ht2 : t ≤ 7 / 6 := by linarith [ht.2]
      have htU : t ≤ (1013 * x + 676) / 2340 := by linarith [ht.2]
      have hf := lrc_fa_ge hx hx2 ht1 htU hu0 hu1
      obtain ⟨hy0, hy1⟩ := lrc_y_bounds (b := x + 10 / 13 * (t - 1)) (by linarith) hx2 ht1 ht2
        (by nlinarith) (by nlinarith)
      have he := lr_eps_le hy0 hy1
      have he0 := lr_eps_nonneg (lrcy x t (x + 10 / 13 * (t - 1)))
      have hK : 0 < lrcK x t := by unfold lrcK; positivity
      have hB : 2 ≤ t + (x + 10 / 13 * (t - 1)) := by nlinarith
      have hbr : (1 / t + 1 / (t + (x + 10 / 13 * (t - 1))) - 2 * t / lrcK x t) * 1 +
          1 / (t + (x + 10 / 13 * (t - 1))) * (10 / 13) ≤ 2 := by
        have i1 : 1 / t ≤ 1 := by rw [div_le_one (by linarith)]; exact ht1
        have i2 : 1 / (t + (x + 10 / 13 * (t - 1))) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        have i3 : 0 ≤ 2 * t / lrcK x t := by positivity
        nlinarith
      have hε : lreps (lrcy x t (x + 10 / 13 * (t - 1))) *
          ((-(2 * (1 + x) / lrcK x t) * 0 + (1 / t + 1 / (t + (x + 10 / 13 * (t - 1))) -
            2 * t / lrcK x t) * 1 + 1 / (t + (x + 10 / 13 * (t - 1))) * (10 / 13))) ≤ 2 / 625 := by
        rw [show -(2 * (1 + x) / lrcK x t) * 0 = (0 : ℝ) by ring, zero_add]
        rcases le_total 0 ((1 / t + 1 / (t + (x + 10 / 13 * (t - 1))) - 2 * t / lrcK x t) * 1 +
          1 / (t + (x + 10 / 13 * (t - 1))) * (10 / 13)) with hp | hn
        · have := mul_le_mul he hbr hp (by norm_num)
          linarith
        · have := mul_nonpos_of_nonneg_of_nonpos he0 hn
          linarith
      nlinarith)
  linarith

/-- **`α ↦ F₀` along `(β₊, u_ℓ(x, β₊))` decreases** to the cap. -/
theorem lrc_F0_astep_ul {x a1 a2 : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (h1 : 1 ≤ a1)
    (h12 : a1 ≤ a2) (h2U : a2 ≤ (1013 * x + 676) / 2340) (h2 : a2 ≤ 7 / 6) :
    lrcF0 x a2 (x + 10 / 13 * (a2 - 1)) (ssUl x (x + 10 / 13 * (a2 - 1))) ≤
      lrcF0 x a1 (x + 10 / 13 * (a1 - 1)) (ssUl x (x + 10 / 13 * (a1 - 1))) := by
  have hx1 : 1 < x := by linarith
  have hb1 : x ≤ x + 10 / 13 * (a1 - 1) := by nlinarith
  have hb12 : x + 10 / 13 * (a1 - 1) ≤ x + 10 / 13 * (a2 - 1) := by nlinarith
  obtain ⟨hmv, hU21⟩ := lr_Ul_mv hx1 hx2 hb1 hb12
  obtain ⟨hU10, hU11⟩ := lr_Ul_bounds hx1 hx2 hb1
  have hA := lrc_F0_astep hx hx2 h1 h12 h2U h2 hU10 (by linarith)
  have hq := lrc_F0_uquad x a2 (x + 10 / 13 * (a2 - 1)) (ssUl x (x + 10 / 13 * (a2 - 1)))
    (ssUl x (x + 10 / 13 * (a1 - 1)))
  have hu := lrc_F0u_ge (u := ssUl x (x + 10 / 13 * (a1 - 1))) hx hx2 (by linarith) h2U
    (by nlinarith) le_rfl (by linarith)
  generalize hU1 : ssUl x (x + 10 / 13 * (a1 - 1)) = U1 at *
  generalize hU2 : ssUl x (x + 10 / 13 * (a2 - 1)) = U2 at *
  have hK : 0 ≤ (U2 - U1) ^ 2 * (1 + x) ^ 6 / (16 * (x * (x + 2)) ^ 2) := by positivity
  have hstep : lrcF0 x a2 (x + 10 / 13 * (a2 - 1)) U2 - lrcF0 x a2 (x + 10 / 13 * (a2 - 1)) U1 ≤
      (U1 - U2) * (1 / 5) := by
    have := mul_le_mul_of_nonneg_left (show -(lrcGu x U1 - 7 / 96 * lrcR2u x a2
      (x + 10 / 13 * (a2 - 1))) ≤ 1 / 5 by linarith) (by linarith : (0 : ℝ) ≤ U1 - U2)
    nlinarith
  have hmv' : U1 - U2 ≤ 15 / 1992 * (10 / 13 * (a2 - a1)) := by
    have : x + 10 / 13 * (a2 - 1) - (x + 10 / 13 * (a1 - 1)) = 10 / 13 * (a2 - a1) := by ring
    rw [← this]; exact hmv
  nlinarith

/-! ### The second test is concave in the shape -/

theorem lrc_F1_conc {x a ac : ℝ} (hx : 41 / 25 ≤ x) (hx2 : x ≤ 2) (ha1 : 1 ≤ a) (hac : a ≤ ac)
    (hacU : ac ≤ (1013 * x + 676) / 2340) (hac2 : ac ≤ 7 / 6) :
    min (lrcF1 x 1 (x + 10 / 13 * (1 - 1)) (19 / 25)) (lrcF1 x ac (x + 10 / 13 * (ac - 1)) (19 / 25)) ≤
      lrcF1 x a (x + 10 / 13 * (a - 1)) (19 / 25) := by
  have hx0 : 0 < x := by linarith
  rw [lrc_F1_phi hx0 le_rfl, lrc_F1_phi hx0 (ha1.trans hac), lrc_F1_phi hx0 ha1]
  set φ := fun s => lrcN x s / lrcV x s + lrell (lrcY x s / lrcK x s) with hφ
  have hd : ∀ s, 1 ≤ s → HasDerivAt φ (lrPhi1 (lrcN x s) (lrcN1 x s) (lrcV x s) (lrcV1 x s)
      (lrcY x s) (lrcY1 x s) (lrcK x s) (2 * s)) s ∧
      HasDerivAt (fun s => lrPhi1 (lrcN x s) (lrcN1 x s) (lrcV x s) (lrcV1 x s) (lrcY x s)
        (lrcY1 x s) (lrcK x s) (2 * s))
        (lrPhi2 (lrcN x s) (lrcN1 x s) (lrcN2 x s) (lrcV x s) (lrcV1 x s) (lrcV2 x s)
          (lrcY x s) (lrcY1 x s) (lrcY2 x s) (lrcK x s) (2 * s) 2) s := by
    intro s hs
    have hs0 : 0 < s := by linarith
    have hK : 0 < lrcK x s := by unfold lrcK; positivity
    have hB : 0 < lrcB x s := by unfold lrcB; nlinarith
    have hV : 0 < lrcV x s := by unfold lrcV; positivity
    have hY : 0 < lrcY x s := by unfold lrcY; positivity
    exact lr_qphi_hasDerivAt (N := lrcN x) (N1 := lrcN1 x) (N2 := lrcN2 x) (V := lrcV x)
      (V1 := lrcV1 x) (V2 := lrcV2 x) (Y := lrcY x) (Y1 := lrcY1 x) (Y2 := lrcY2 x)
      (K := lrcK x) (K1 := fun s => 2 * s) (K2 := fun _ => 2) (lrcN_d x s) (lrcN1_d x s)
      (lrcV_d x s) (lrcV1_d x s) (lrcY_d x s) (lrcY1_d x s) (lrcK_d x s) (lrcK1_d s)
      hV.ne' hK.ne' (by have : 0 < lrcY x s / lrcK x s := div_pos hY hK; linarith)
  have hm := lr_conc_min (f := fun s => -φ s)
    (f' := fun s => -lrPhi1 (lrcN x s) (lrcN1 x s) (lrcV x s) (lrcV1 x s) (lrcY x s)
      (lrcY1 x s) (lrcK x s) (2 * s))
    (f'' := fun s => -lrPhi2 (lrcN x s) (lrcN1 x s) (lrcN2 x s) (lrcV x s) (lrcV1 x s)
      (lrcV2 x s) (lrcY x s) (lrcY1 x s) (lrcY2 x s) (lrcK x s) (2 * s) 2)
    (p := 1) (q := ac) (t := a) ha1 hac
    (fun s hs => (hd s hs.1).1.neg) (fun s hs => (hd s hs.1).2.neg)
    (fun s hs => by
      have := lrc_phi2_nonneg hx hx2 hs.1 (by linarith [hs.2]) (by linarith [hs.2])
      linarith)
  simp only [hφ] at hm
  rcases le_total (lrcN x 1 / lrcV x 1 + lrell (lrcY x 1 / lrcK x 1))
    (lrcN x ac / lrcV x ac + lrell (lrcY x ac / lrcK x ac)) with h | h
  · rw [min_eq_right (by linarith)]; rw [min_eq_right (by linarith)] at hm; linarith
  · rw [min_eq_left (by linarith)]; rw [min_eq_left (by linarith)] at hm; linarith

theorem lrcT1_num {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ (9 / 25 : ℝ)) :
    (0 : ℝ) < 157 / 5000 * z ^ 17 + 7516417 / 6000000 * z ^ 16 + 5144573689 / 225000000 * z ^ 15 + 31552071211 / 125000000 * z ^ 14 + 26383088279047 / 14062500000 * z ^ 13 + 69434767096486979 / 7031250000000 * z ^ 12 + 3303424269445344289 / 87890625000000 * z ^ 11 + 113240020334264462651 / 1098632812500000 * z ^ 10 + 44796791375411356171 / 228881835937500 * z ^ 9 + 3813943043520753032333 / 17166137695312500 * z ^ 8 + 23689359200074905369229 / 715255737304687500 * z ^ 7 - 3409789972605575581847891 / 8940696716308593750 * z ^ 6 - 27409674427754664440397938 / 37252902984619140625 * z ^ 5 - 129886574479469745211332366 / 186264514923095703125 * z ^ 4 - 1530490080394818233038911816 / 4656612873077392578125 * z ^ 3 - 8708410559996989097910721056 / 582076609134674072265625 * z ^ 2 + 819724320927595214325155541888 / 14551915228366851806640625 * z + 6738944780630940421399249895424 / 363797880709171295166015625 := by
  nlinarith [mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 5),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 4),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 3),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z ^ 2),
    mul_le_mul_of_nonneg_left hz1 (by positivity : (0 : ℝ) ≤ z),
    hz1,
    (by positivity : (0 : ℝ) ≤ z ^ 17),
    (by positivity : (0 : ℝ) ≤ z ^ 16),
    (by positivity : (0 : ℝ) ≤ z ^ 15),
    (by positivity : (0 : ℝ) ≤ z ^ 14),
    (by positivity : (0 : ℝ) ≤ z ^ 13),
    (by positivity : (0 : ℝ) ≤ z ^ 12),
    (by positivity : (0 : ℝ) ≤ z ^ 11),
    (by positivity : (0 : ℝ) ≤ z ^ 10),
    (by positivity : (0 : ℝ) ≤ z ^ 9),
    (by positivity : (0 : ℝ) ≤ z ^ 8),
    (by positivity : (0 : ℝ) ≤ z ^ 7)]

theorem lrcT1_id {x : ℝ} (h0 : 41 / 25 ≤ x) :
    lrcF1 x 1 x (19 / 25) = (157 / 5000 * (x - (41 / 25 : ℝ)) ^ 17 + 7516417 / 6000000 * (x - (41 / 25 : ℝ)) ^ 16 + 5144573689 / 225000000 * (x - (41 / 25 : ℝ)) ^ 15 + 31552071211 / 125000000 * (x - (41 / 25 : ℝ)) ^ 14 + 26383088279047 / 14062500000 * (x - (41 / 25 : ℝ)) ^ 13 + 69434767096486979 / 7031250000000 * (x - (41 / 25 : ℝ)) ^ 12 + 3303424269445344289 / 87890625000000 * (x - (41 / 25 : ℝ)) ^ 11 + 113240020334264462651 / 1098632812500000 * (x - (41 / 25 : ℝ)) ^ 10 + 44796791375411356171 / 228881835937500 * (x - (41 / 25 : ℝ)) ^ 9 + 3813943043520753032333 / 17166137695312500 * (x - (41 / 25 : ℝ)) ^ 8 + 23689359200074905369229 / 715255737304687500 * (x - (41 / 25 : ℝ)) ^ 7 - 3409789972605575581847891 / 8940696716308593750 * (x - (41 / 25 : ℝ)) ^ 6 - 27409674427754664440397938 / 37252902984619140625 * (x - (41 / 25 : ℝ)) ^ 5 - 129886574479469745211332366 / 186264514923095703125 * (x - (41 / 25 : ℝ)) ^ 4 - 1530490080394818233038911816 / 4656612873077392578125 * (x - (41 / 25 : ℝ)) ^ 3 - 8708410559996989097910721056 / 582076609134674072265625 * (x - (41 / 25 : ℝ)) ^ 2 + 819724320927595214325155541888 / 14551915228366851806640625 * (x - (41 / 25 : ℝ)) + 6738944780630940421399249895424 / 363797880709171295166015625) / (x ^ 2 * (x + 2) ^ 2 * (x + 3) ^ 3 * (x + 1) ^ 8) := by
  have hx0 : 0 < x := by linarith
  have e := lrc_F1_phi (x := x) (t := 1) hx0 le_rfl
  rw [show x + 10 / 13 * ((1 : ℝ) - 1) = x by ring] at e
  rw [e]
  have hY : lrcY x 1 / lrcK x 1 = 2 / (1 + x) := by
    unfold lrcY lrcB lrcK
    have : (1 : ℝ) + x ≠ 0 := by linarith
    field_simp; ring
  rw [hY, lr_ell_frac (by linarith) (by norm_num)]
  have h1 : x + 1 ≠ 0 := by linarith
  have h1' : 1 + x ≠ 0 := by linarith
  have h2 : x + 2 ≠ 0 := by linarith
  have h3 : x + 3 ≠ 0 := by linarith
  have h3' : 2 + (1 + x) ≠ 0 := by linarith
  simp only [lrcN, lrcV, lrcB, lrcK, lrcG, lrcv, lrcE]
  field_simp
  ring

theorem lrcT1 {x : ℝ} (h0 : 41 / 25 ≤ x) (h1 : x ≤ 2) : 0 < lrcF1 x 1 x (19 / 25) := by
  rw [lrcT1_id h0]
  have hn := lrcT1_num (z := x - 41 / 25) (by linarith) (by linarith)
  apply div_pos hn
  have : 0 < x := by linarith
  positivity
end SmoothedOctagon
