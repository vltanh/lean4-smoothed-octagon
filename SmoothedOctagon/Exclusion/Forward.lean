module

public import SmoothedOctagon.Period.Defs
public import SmoothedOctagon.Exclusion.Forward.Interface
public import SmoothedOctagon.Exclusion.Forward.Window
public import SmoothedOctagon.Exclusion.Forward.Core

/-!
# Case F: no competitive entirely forward period with six or more pieces

`GLOBAL_FORWARD_PERIOD_EXCLUSION`, in the hand form `HAND_FORWARD_PERIOD_EXCLUSION` (HFPE). A
competitive normal vertex period with every switch forward has at most five pieces (with the twist,
`N ≡ 1 mod 3`, so `N = 4`: the octagon's word).

Route (HFPE): `N ≡ 1 (mod 3)` gives `N ≥ 7` (`NormalPeriod.ff_N_mod_three`). At a global minimum
`a = a_m` of the active margins, the window `(p, b, a, c, d) = (a_{m-2}, …, a_{m+2})` carries
* the factors and strict-star products of the costate cycle (`Forward/Window.lean`),
* the seven-entry cost bound (`ff_seven_le`, `CostateCycle.ff_rawCost`, `cost_eq_rawCost`),
* the three stationarity rows, the two exterior floors and the Gram identity of the normal
  multiplier (`Forward/Interface.lean`, to be supplied by `Period/Elliptic`),
* the competitive Casimir cap `γ² < 23/125` (`NormalPeriod.ff_cost_casimir`, `ff_gam2_cap`).
These form an `ff_Win`, which the scalar argument of `Forward/Core.lean` excludes. No interval
cover is used.
-/

@[expose] public section

namespace SmoothedOctagon

/-- **Case F** (`GLOBAL_FORWARD_PERIOD_EXCLUSION`). No competitive normal vertex period with at least
six pieces has every switch forward. -/
theorem forward_exclusion (P : NormalPeriod)
    (hc : P.IsCompetitive) (hF : P.rep.AllForward) (hN : 6 ≤ P.N) : False := by
  set C := P.costateCycle with hC
  have hF' : ∀ k, C.lab (k + 1) = C.lab k + 1 := fun k ↦ hF k
  have hN7 : 7 ≤ P.N := by have := P.ff_N_mod_three hF; omega
  obtain ⟨m, hm⟩ := C.exists_act_min P.rep.N_pos
  have hprod : ∀ k, C.act k * C.act (k + 1) < 4 := fun k ↦ by
    have := C.ff_act_mul_lt hF' (k + 1); rwa [add_sub_cancel_right] at this
  have hq : ∀ k, 1 < ff_fac (C.act (k - 1)) (C.act k) (C.act (k + 1)) := fun k ↦ by
    rw [← C.ff_q_eq hF' k]; exact C.one_lt_q k
  obtain ⟨h0, hL, hR⟩ := C.ff_rows hF' m
  obtain ⟨fL, fR⟩ := C.ff_floors hF' m
  have hgram := C.ff_gram hF' m
  have hgam := P.ff_gam2_eq m
  obtain ⟨hdet, hcc⟩ := P.ff_cost_casimir hF
  have hcost : P.cost = √3 / 4 * ∑ j ∈ Finset.range P.N, ff_G (C.act j) (C.act (j + 1)) := by
    rw [P.cost_eq_rawCost, ← C.ff_rawCost hF']; rfl
  obtain ⟨n, hn⟩ := ff_seven_le C.act C.act_add C.act_pos hprod m hm hN7
  have hcap := ff_gam2_cap hdet hcc hc
  have e1 : m - 1 - 1 = m - 2 := by ring
  have e2 : m - 1 + 1 = m := by ring
  have e3 : m + 1 - 1 = m := by ring
  have e4 : m + 1 + 1 = m + 2 := by ring
  have hpb := hprod (m - 2)
  have hab := hprod (m - 1)
  have hcd := hprod (m + 1)
  have hac := hprod m
  rw [show m - 2 + 1 = m - 1 by ring] at hpb
  rw [e2] at hab
  rw [e4] at hcd
  have hh := hq (m - 1)
  have hk := hq (m + 1)
  rw [e1, e2] at hh
  rw [e3, e4] at hk
  have W : ff_Win :=
    { a := C.act m
      p := C.act (m - 2)
      b := C.act (m - 1)
      c := C.act (m + 1)
      d := C.act (m + 2)
      u := C.ff_u m
      v := C.ff_v m
      E := C.ff_E m
      a_pos := C.act_pos m
      a_le_p := hm _
      a_le_b := hm _
      a_le_c := hm _
      a_le_d := hm _
      pb_lt := hpb
      ab_lt := by linarith [mul_comm (C.act (m - 1)) (C.act m)]
      ac_lt := hac
      cd_lt := hcd
      one_lt_h := hh
      one_lt_q := hq m
      one_lt_k := hk
      row0 := h0
      rowL := hL
      rowR := hR
      floorL := fL
      floorR := fR
      cost := ⟨n, by
        have h3 : (0 : ℝ) ≤ √3 / 4 := by positivity
        calc _ ≤ √3 / 4 * ∑ j ∈ Finset.range P.N, ff_G (C.act j) (C.act (j + 1)) :=
              mul_le_mul_of_nonneg_left hn h3
          _ = P.cost := hcost.symm
          _ ≤ octagonCost := hc⟩
      cap := by rw [← hgram, hgam]; exact hcap.le }
  exact W.elim

end SmoothedOctagon
