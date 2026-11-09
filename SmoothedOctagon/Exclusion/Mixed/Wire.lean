module

public import SmoothedOctagon.Exclusion.Forward.Wire
public import SmoothedOctagon.Exclusion.Mixed.Scalar
public import SmoothedOctagon.Exclusion.Reverse
public import SmoothedOctagon.Exclusion.Mixed.Density.Bound

/-!
# Case M2: wiring `Period/Elliptic` to the covector calculus

The scalar bridges between the case-M2 functions of `Exclusion/Mixed/Scalar` and those of
`Period/Elliptic` and `Exclusion/Forward/Scalar`, and the two Casimir bounds of the calculus
`NormalPeriod.M2Calculus` (`Exclusion/Mixed/Interface`).

## Main API

* `wire_m2Stat_eq` (`m2Stat = ff_Cph`), `wire_m2g_eq` (`m2g = 4 j`), `wire_m2F_eq` (`m2F = ff_F` off
  `q = 1`), `wire_m2Sec_eq` (the turn secant from `16 (n - p) d = G_a(a,n) - G_a(a,p)`).
* `CostateCycle.wire_turn_ne`: the outer active margins of a turn differ.
* `NormalPeriod.wire_cas_lt`: **the competitive cap** `γ² < 9193/50000`, from the spectral
  cost–Casimir bound; ellipticity comes from `γ² > 0` and a forward switch, which exists by case R
  (`reverse_exclusion`).
* `NormalPeriod.wire_cas_gt`: the lower bound `γ² > 27/256` of a competitive mixed period,
  `NormalPeriod.dens_cas_gt` of `Exclusion/Mixed/Density` (the whole-period winding `dens_winding`,
  the forward-piece bound `dens_pp_bound` and the reverse-centre gap `m1_angle_gap`).
-/

@[expose] public section

namespace SmoothedOctagon

open SmoothedPolygons Real

theorem wire_m2Stat_eq (p a n : ℝ) : m2Stat p a n = ff_Cph p a n := rfl

/-- `m2g a b = 4 j(a, b)`. -/
theorem wire_m2g_eq (a b : ℝ) : m2g a b = 4 * elJ a b := by
  simp only [m2g, elJ]
  rcases eq_or_ne (a + b) 0 with h | h
  · simp [h]
  · field_simp

theorem wire_m2F_eq {x q : ℝ} (hq : 1 < q) : m2F x q = ff_F x q := by
  rw [m2F_of_ne hq.ne', ff_F]

/-- **The turn secant**: `16 (n - p) d = G_a(a,n) - G_a(a,p)` with `p ≠ n`
gives `8 d = Sec(p, a, n)`. -/
theorem wire_m2Sec_eq {p a n d : ℝ} (hp : 0 < p) (ha : 0 < a) (hn : 0 < n) (hne : p ≠ n)
    (h : 16 * (n - p) * d = elGa a n - elGa a p) : 8 * d = m2Sec p a n := by
  have hnp : n - p ≠ 0 := sub_ne_zero.2 hne.symm
  rw [m2Sec_of_ne hne, Real.log_div (by positivity) (by positivity)]
  have hd : d = (elGa a n - elGa a p) / (16 * (n - p)) := by
    field_simp; linarith
  rw [hd]
  simp only [elGa]
  rw [add_comm n a, add_comm p a]
  field_simp
  ring

namespace CostateCycle

variable {N : ℕ} (C : CostateCycle N)

/-- At a turn the outer active margins differ. -/
theorem wire_turn_ne {k : ℤ} (hturn : C.sgn (k - 1) = -C.sgn k) :
    C.act (k - 1) ≠ C.act (k + 1) := by
  have ek : k - 1 + 1 = k := by ring
  rcases C.lab_cases (k - 1) with hin | hin <;> rw [ek] at hin <;>
    rcases C.lab_cases k with hout | hout
  · rw [C.sgn_fwd (by rw [ek]; exact hin), C.sgn_fwd hout] at hturn; norm_num at hturn
  · have := C.turn_down (k - 1) (by rw [ek]; exact hin)
      (by rw [ek, show k - 1 + 2 = k + 1 by ring]; exact hout)
    rw [show k - 1 + 2 = k + 1 by ring] at this; exact this.ne'
  · have := C.turn_up (k - 1) (by rw [ek]; exact hin)
      (by rw [ek, show k - 1 + 2 = k + 1 by ring]; exact hout)
    rw [show k - 1 + 2 = k + 1 by ring] at this; exact this.ne
  · rw [C.sgn_rev (by rw [ek]; exact hin), C.sgn_rev hout] at hturn; norm_num at hturn

/-- **Both norms at a turn are its secant**: `8 d_{k-1} = 8 d_k = Sec(a_{k-1}, a_k,
a_{k+1})`. -/
theorem wire_turn_sec {k : ℤ} (hturn : C.sgn (k - 1) = -C.sgn k) :
    8 * C.swd (k - 1) = m2Sec (C.act (k - 1)) (C.act k) (C.act (k + 1)) ∧
      8 * C.swd k = m2Sec (C.act (k - 1)) (C.act k) (C.act (k + 1)) := by
  obtain ⟨he, hs⟩ := C.turn_secant hturn
  have h := wire_m2Sec_eq (C.act_pos _) (C.act_pos _) (C.act_pos _) (C.wire_turn_ne hturn) hs
  exact ⟨by rw [he]; exact h, h⟩

end CostateCycle

namespace NormalPeriod

variable (P : NormalPeriod)

/-- Some switch of a normal period is forward (case R, `reverse_exclusion`). -/
theorem wire_exists_fwd : ∃ n : ℕ, P.rep.IsForward n := by
  obtain ⟨k, hk⟩ : ∃ k, P.rep.IsForward k := by
    by_contra h
    push Not at h
    exact reverse_exclusion P (fun k ↦ (P.rep.el_fwd_or_rev k).resolve_left (h k))
  have hN : (0 : ℤ) < P.N := by exact_mod_cast P.rep.N_pos
  have hn0 : 0 ≤ k % P.N := Int.emod_nonneg _ hN.ne'
  refine ⟨(k % P.N).toNat, ?_⟩
  have hcast : (((k % P.N).toNat : ℕ) : ℤ) = k + (-(k / P.N)) * P.N := by
    rw [Int.toNat_of_nonneg hn0, Int.emod_def]; ring
  rw [hcast, P.rep.el_fwd_shift]
  exact hk

/-- **The competitive Casimir cap** `γ² < 9193/50000`, from the spectral cost–Casimir bound
(`wire_gam2_cap`, `wire_spectral`); ellipticity comes from `γ² > 0` and a forward switch. -/
theorem wire_cas_lt (hc : P.IsCompetitive) : P.costateCycle.gam2 0 < 9193 / 50000 := by
  by_cases hpos : 0 < P.costateCycle.gam2 0
  swap
  · push Not at hpos; linarith
  obtain ⟨n, hn⟩ := P.wire_exists_fwd
  have hd : 0 < P.costateCycle.swd n := by
    have := P.costateCycle.swd_fwd (k := n) hn
    have := CostateCycle.elJ_ge _ _ (P.costateCycle.act_pos n) (P.costateCycle.act_pos (n + 1))
    linarith
  obtain ⟨hdet, h10⟩ := P.wire_negEll hpos hd
  have h := wire_gam2_cap hdet (P.wire_spectral hdet h10) hc
  rw [P.det_Λ₁_zero] at h
  linarith

/-- **The lower Casimir bound of a competitive mixed period**: `γ² > 27/256`
(`NormalPeriod.dens_cas_gt`; the compact domain is not used). The proof uses the whole-period
winding in its telescoped form `∑ δ_n = π/3` (`dens_winding`), the reverse gap `cos φ < 3/10`
(`m1_angle_gap`) and the bound `e ≥ 0 ∨ 4e² ≤ d_- d_+` at `+ +` (`dens_pp_bound`). -/
theorem wire_cas_gt (hc : P.IsCompetitive) (_hD : P.InCompactDomain) (hmix : P.rep.IsMixed) :
    27 / 256 < P.costateCycle.gam2 0 :=
  P.dens_cas_gt hc hmix

end NormalPeriod

end SmoothedOctagon
