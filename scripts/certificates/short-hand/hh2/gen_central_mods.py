"""Writes Heavy/S2CenPoly, S2CenStage, S2CenLinkG, S2CenLinkA, S2CenLinkD (central face, stage identities)."""
from gen_central import *
# ---------------- base polynomials

body="\n".join([emit_defs('hh2CnG',pG,VARS,"`18522 · G₂ · M · U_d` (numerator of the central `G₂` with the log majorant)"),
                emit_defs('hh2CnA',pA,VARS,"`18522 · A · M · U_d` (numerator of the duration slope `A`)"),
                emit_defs('hh2CnD',pD,VARS,"`18522 · M · U_d`, `M = K³αB`, `U_d = 9600S²(β - 1)` (the common denominator)")])
write('S2CenPoly.lean',[M+'S2Bern'],'central face polynomials',
      f"The cleared numerators of the central face (`CENTRAL_RATIO_HAND_SIGN` (3)-(4)) in {COORD}.",
      "* `hh2CnG`, `hh2CnA`, `hh2CnD`: the numerators of `G₂`, `A` and the common denominator.",body)
# ---------------- stage 1 + combine
def tmpl(Sx,Kx,Dx,Bx,ax,ux):
    W=f"(({Sx}) ^ 2 * (({Sx}) ^ 2 - ({Sx}) + 1) + ({Dx}) ^ 2 * ({ux}) - ({Dx}) * (({Sx}) ^ 3 * (({ux}) - 1) + 3 * ({Sx}) - 1)) / ({Kx}) ^ 2"
    return W
def atoms_sub(e, Sx, Kx, Dx, Bx, ax):
    s=lean(e)
    for nm,v in [('S',Sx),('K',Kx),('D',Dx),('B',Bx),('a',ax)]:
        s=re.sub(r'\b'+nm+r'\b','('+v+')',s)
    return s
ABS=dict(Sx='S',Kx='K',Dx='D',Bx='B',ax='a')
def faceG2(l, S_,K_,D_,B_,a_,u_):
    W=f"({S_} ^ 2 * ({S_} ^ 2 - {S_} + 1) + {D_} ^ 2 * {u_} - {D_} * ({S_} ^ 3 * ({u_} - 1) + 3 * {S_} - 1)) / {K_} ^ 2"
    EL=f"(2 * {D_} * {u_} - ({S_} ^ 3 * ({u_} - 1) + 3 * {S_} - 1)) / {K_}"
    q=f"{a_} ^ 2 / {K_}"; rA=f"{a_} / {B_}"; k=f"({q} / ({rA}))"
    cc=f"(({u_} - 1) / ({rA}) + {rA} + 1 - {q} - {EL})"
    LB=f"(-296 / 1029 + (4 * (2 * {k}) / 3 - 1) - (4 * (2 * {k}) / 3 - 1) ^ 2 / 2 + (4 * (2 * {k}) / 3 - 1) ^ 3 / 3)"
    lv = LB if l is None else l
    G2=f"({W} - 1) * 2 + 1 / 2 + {cc} + {lv} + (2 - 7 * 2 * {k} / 4) * ({W} - 3 / 4)"
    A=f"(1 - 7 * {k} / 4) * ({W} - 3 / 4)"
    return G2,A
G2abs,Aabs=faceG2(None,'S','K','D','B','a','u')
P0G=atoms_sub(st['G'][0],**ABS); P1G=atoms_sub(st['G'][1],**ABS)
P0A=atoms_sub(st['A'][0],**ABS); P1A=atoms_sub(st['A'][1],**ABS)
body=f'''/-- **Stage 1 for `G₂`** (abstract atoms `S, K, D, B, α, u`): `G₂ · K³αB = Π₀ + uΠ₁`. -/
theorem hh2_cen_stage1_G (S K D B a u : ℝ) (hK : K ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) :
    ({G2abs}) * (K ^ 3 * a * B) =
      {P0G} + u * ({P1G}) := by
  field_simp
  ring

/-- **Stage 1 for `A`**: `A · K³αB = Π₀ + uΠ₁`. -/
theorem hh2_cen_stage1_A (S K D B a u : ℝ) (hK : K ≠ 0) (ha : a ≠ 0) (hB : B ≠ 0) :
    ({Aabs}) * (K ^ 3 * a * B) =
      {P0A} + u * ({P1A}) := by
  field_simp
  ring

/-- **Recombination**: from the stage identities and `u U_d = U_n`, the sign of
`G₂ + (α + βA)` is that of the cleared numerator `-(N_G + αN_D + βN_A)`. -/
theorem hh2_combine {{EG EA M Ud u Un P0G P1G P0A P1A NG NA ND al be : ℝ}} (hM : 0 < M) (hUd : 0 < Ud)
    (hG : EG * M = P0G + u * P1G) (hA : EA * M = P0A + u * P1A) (hu : u * Ud = Un)
    (h2G : 18522 * (P0G * Ud + P1G * Un) = NG) (h2A : 18522 * (P0A * Ud + P1A * Un) = NA)
    (h2D : 18522 * (M * Ud) = ND) (hc : 0 < -(NG + al * ND + be * NA)) : EG + (al + be * EA) < 0 := by
  have key : (EG + (al + be * EA)) * (18522 * M * Ud) = -(-(NG + al * ND + be * NA)) := by
    linear_combination (18522 * Ud) * hG + (18522 * be * Ud) * hA + (18522 * (P1G + be * P1A)) * hu +
      h2G + be * h2A + al * h2D
  exact hh2_neg_of_mul (by positivity) hc key
'''
write('S2CenStage.lean',[M+'S2Face'],'central face, stage-1 identities',
      "The central face value `G₂` (with the log majorant) and the duration slope `A` in abstract atoms "
      "`S = 1 + x`, `K = x(x + 2) + α²`, `D`, `B = α + β`, `α`, `u` (`CENTRAL_RATIO_HAND_SIGN` (3)-(4)), "
      "and the recombination lemma.",
      "* `hh2_cen_stage1_G`, `hh2_cen_stage1_A`, `hh2_combine`.",body)
# ---------------- stage 2
def dnames(P,X):
    from leangen import nested_coeffs
    d=nested_coeffs(P)
    return [f"{X}_d{i}_{j}" for i in range(len(d)) for j in range(len(d[0])) if any(c!=0 for c in d[i][j])]
HBE="(hbe : be = x + ((24 * x + 51) / 128 - t) * (al - 1))"
for nm,P,X,P0,P1 in [('G',pG,'hh2CnG',st['G'][0],st['G'][1]),('A',pA,'hh2CnA',st['A'][0],st['A'][1])]:
    p0=atoms_sub(P0,**CON); p1=atoms_sub(P1,**CON)
    body=f'''/-- **Stage 2 for `{nm}`**: the atom polynomial in `(t, x, α)` is `{X}`. -/
theorem hh2_cen_stage2_{nm} (t x al be : ℝ) {HBE} :
    18522 * (({p0}) * {UdL} + ({p1}) * {UnL}) = {X} t x al := by
  subst hbe
  unfold hsDg {X} {" ".join(dnames(P,X))}
  ring
'''
    write(f'S2CenLink{nm}.lean',[M+'S2CenPoly',M+'S2Face'],f'central face, stage 2 for `{nm}`',
          f"The expansion of the stage-1 atom polynomial for `{nm}` in {COORD}.",f"* `hh2_cen_stage2_{nm}`.",body)
body=f'''/-- **Stage 2 for the denominator**. -/
theorem hh2_cen_stage2_D (t x al be : ℝ) {HBE} :
    18522 * ({MLx} * {UdL}) = hh2CnD t x al := by
  subst hbe
  unfold hh2CnD {" ".join(dnames(pD,'hh2CnD'))}
  ring

/-- `u_C · U_d = U_n`. -/
theorem hh2_cen_uC (x be : ℝ) (hS : 1 + x ≠ 0) (hb : be - 1 ≠ 0) :
    hsUC x be * {UdL} = {UnL} := by
  unfold hsUC
  field_simp
  ring
'''
write('S2CenLinkD.lean',[M+'S2CenPoly',M+'S2Face'],'central face, the denominator','The common denominator and `u_C`.',
      "* `hh2_cen_stage2_D`, `hh2_cen_uC`.",body)
