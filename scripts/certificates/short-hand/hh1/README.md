# Gate S1 heavy faces (`hh1`): certificate generators

Generators for the S1 modules `SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy/S1*.lean`
(the central face `hs1_central_face_proof` and the outer face `hs1_outer_face_proof`).
Requires Python 3 with `sympy`. Run from any directory; paths are relative to this folder.

## Method

Every generated claim is `0 ≤ E` (or `0 < E`) for an explicit rational function `E` on a box.
The Lean proof

1. clears the denominators: `E * DEN = NUM` by `field_simp; ring` (each factor of `DEN` is shown
   positive on the box);
2. substitutes `x = X0 + z` and `v_i = lo_i + w_i` for the remaining variables, bounds the terms of
   `NUM` containing `w_k` termwise (negative coefficients use `w_k ≤ hi_k(z)`, lemma `hh1_tw_sub`),
   innermost variable first, leaving a polynomial `H(z)` (identity checked by `ring`);
3. certifies `H ≥ 0` on `[0, Zmax]` by its Bernstein coefficients (all positive).

Univariate terminal signs (`uni.py`) are step 3 alone on a cleared one-variable numerator.

## Files

* libraries: `claim.py` (fractions, Bernstein), `claim3.py` / `emit3.py` (claims in
  `z, A = α - 1, t = β - x ∈ [Clo·A, Chi·A], m = u - 3/4`), `claimg.py` / `emitg.py` (general
  claims, termwise variables with affine upper bounds in `z`), `uni.py`, `emit.py`;
* central face: `cexprs.py` (transport atoms and partials), `gen_cclaims.py` → `S1CClaimU`,
  `S1CClaimB`, `S1CClaimA`, `S1CClaimX`; `gen_cuni.py` → `S1CUni`;
* outer face: `faces.py` (both faces), `orep_coeffs.py` (writes `rrep.pkl`, the reciprocal-shape
  coefficients `P₀..P₄, Q`), `gen_orep.py` → `S1ORep`; `oexprs.py` (outer atoms and partials);
  `gen_occ.py` → `S1OCurv0..3` (curvature signs); `gen_oclaims.py` → `S1OClaimS`, `S1OClaimF`,
  `S1OClaimB1`, `S1OClaimB2`, `S1OClaimW1`, `S1OClaimW2`; `gen_ouni.py` → `S1OUni`.

## Commands

```
H=SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy
python3 gen_cclaims.py $H/S1CClaimU.lean U0 U1 M0
python3 gen_cclaims.py $H/S1CClaimB.lean B0 B1
python3 gen_cclaims.py $H/S1CClaimA.lean A0
python3 gen_cclaims.py $H/S1CClaimX.lean X1a X1b
python3 gen_cuni.py $H/S1CUni.lean
python3 orep_coeffs.py && python3 gen_orep.py $H/S1ORep.lean
python3 gen_occ.py $H 0 1 2 3
python3 gen_oclaims.py $H/S1OClaimS.lean dS S2uf S2vb
python3 gen_oclaims.py $H/S1OClaimF.lean dg lo A65uf A65vb
python3 gen_oclaims.py $H/S1OClaimB1.lean OB0 OM1 OA0
python3 gen_oclaims.py $H/S1OClaimB2.lean OBV
python3 gen_oclaims.py $H/S1OClaimW1.lean wS1 wS2 wA1 wA2
python3 gen_oclaims.py $H/S1OClaimW2.lean wA3 wA4 wA5 wA6
python3 gen_ouni.py $H/S1OUni.lean T1uf T1vb T2uf T2vb T3uf T3vb T4uf T4ul T5uf T5ul
```

Each generator asserts its certificate before writing; rerunning the commands reproduces the
committed modules byte for byte.
