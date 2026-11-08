import pickle, sympy as sp
from loglin import *
r,d=sp.symbols('r d')
res=pickle.load(open('Nasym_parts.pkl','rb'))
atoms=[('(2 + r)',2+r),('(4 + 2 * r + r ^ 2 - d)',4+2*r+r**2-d),('(8 + 6 * r + 2 * r ^ 2 - d)',8+6*r+2*r**2-d),
       ('(4 - d)',4-d),('(26 + 7 * r - 3 * d)',26+7*r-3*d),('(43 - 9 * d)',43-9*d),('(92 - 9 * d)',92-9*d),('(2 + 3 * d)',2+3*d)]
G=Gen(r,d,atoms)
gs=sp.symbols('g0:%d'%len(atoms))
gmap={ln:g for (ln,ap),g in zip(atoms,gs)}
gval={g:ap for (ln,ap),g in zip(atoms,gs)}
glean={g:f"g{k}" for k,g in enumerate(gs)}
# log terms: N,M as g-expressions and lean text
logs=[('cH','((2 + r) ^ 2)','(4 + 2 * r + r ^ 2 - d)',gs[0]**2,gs[1],'up'),
      ('cq','(7 * (2 + r))','(3 * (4 - d))',7*gs[0],3*gs[3],'lo'),
      ('cW','(49 : ℝ)','(43 - 9 * d)',sp.Integer(49),gs[5],'up')]
def Bup(N,M): return (N**2-M**2)/(2*N*M)-(N-M)**3/(3*N*M*(N+M))
def Blo(N,M): return 2*(N-M)/(N+M)+2*(N-M)**3/(3*(N+M)**3)
def Bup_l(N,M): return f"({N} ^ 2 - {M} ^ 2) / (2 * {N} * {M}) - ({N} - {M}) ^ 3 / (3 * {N} * {M} * ({N} + {M}))"
def Blo_l(N,M): return f"2 * ({N} - {M}) / ({N} + {M}) + 2 * ({N} - {M}) ^ 3 / (3 * ({N} + {M}) ^ 3)"
def sym_lean(e):
    s=sp.sstr(e).replace('**','^')
    for k in range(len(gs)-1,-1,-1): s=s.replace(f'g{k}',f'g{k}')
    return s
def sym_to_actual_lean(e):
    s=sp.sstr(e).replace('**','^')
    for k in range(len(gs)-1,-1,-1): s=s.replace(f'g{k}',atoms[k][0])
    return s
box=((0,Fr(1,3)),(0,Fr(3,5)))
Xsym=sp.symbols('XR X0 X1 X2')
out=[]
for name in ['E','T']:
    p=res[name]
    toS=lambda e: sp.sympify(str(e))
    Rn,Rc=G.frac(toS(p['R'][0])/toS(p['R'][1]))
    Rc_sym=sp.Mul(*[gmap[ln]**e for ln,e in Rc.items()])
    terms=[]
    total=Xsym[0]/Rc_sym
    for k,(key,Nl,Ml,Ns,Ms,kind) in enumerate(logs):
        cn,cc=G.frac(toS(p[key][0])/toS(p[key][1]))
        cc_sym=sp.Mul(*[gmap[ln]**e for ln,e in cc.items()])
        B=Bup(Ns,Ms) if kind=='up' else Blo(Ns,Ms)
        total+=Xsym[k+1]/cc_sym*B
        terms.append(dict(key=key,Nl=Nl,Ml=Ml,cn=cn,cc=cc,kind=kind,Bl=(Bup_l(Nl,Ml) if kind=='up' else Blo_l(Nl,Ml))))
    num,den=sp.fraction(sp.together(total))
    den=sp.factor(den); num=sp.expand(num)
    Ms=[sp.factor(sp.Poly(num,*Xsym).coeff_monomial(X)) for X in Xsym]
    # actual numerator sum and reduced
    nums=[Rn]+[tm['cn'] for tm in terms]
    full=sp.expand(sum(n_*M.subs(gval) for n_,M in zip(nums,Ms)))
    den_act=sp.expand(den.subs(gval))
    nred,cred=G.frac(full/den_act)
    extra=sp.factor(sp.cancel(full/nred))
    print(name,'den',den,'red deg',sp.Poly(nred,r,d).degree_list(),'extra',extra)
    lem_c=[]
    for tm in terms:
        poly = tm['cn'] if tm['kind']=='up' else -tm['cn']
        s,mn=bern_lemma_n(f"fs_NA{name}_{tm['key']}", poly, r, d, box)
        out.append(s); lem_c.append(f"fs_NA{name}_{tm['key']}")
    s,mn=bern_lemma_n(f"fs_NA{name}_N0", -nred, r, d, box, eps=1)
    out.append(s)
    out.append(f"""theorem fs_NA{name}_N {{r d : ℝ}} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 3) (hd0 : 0 ≤ d) (hd1 : d ≤ 3 / 5) :
    {G.L(nred)} < 0 := by
  have := fs_NA{name}_N0 hr0 hr1 hd0 hd1
  linarith only [this]
""")
    stmt = f"({G.L(Rn)}) / ({G.plean(Rc)})" + "".join(
        f" +\n      ({G.L(tm['cn'])}) / ({G.plean(tm['cc'])}) * Real.log ({tm['Nl']} / {tm['Ml']})" for tm in terms)
    atom_hyps="\n".join(f"  have hA{k} : 0 < {ln} := by nlinarith" for k,(ln,ap) in enumerate(atoms))
    logh=[]
    for k,tm in enumerate(terms):
        lem='fs_log_div_le_pade' if tm['kind']=='up' else 'fs_log_div_ge'
        logh.append(f"  have hl{k} := {lem} (N := {tm['Nl']}) (M := {tm['Ml']}) (by positivity) (by nlinarith)")
        cs=f"({G.L(tm['cn'])}) / ({G.plean(tm['cc'])})"
        if tm['kind']=='up':
            logh.append(f"  have hm{k} := mul_le_mul_of_nonneg_left hl{k} (div_nonneg ({lem_c[k]} hr0 hr1 hd0 hd1) (by positivity) :\n    0 ≤ {cs})")
        else:
            logh.append(f"  have hm{k} := mul_le_mul_of_nonpos_left hl{k} (div_nonpos_of_nonpos_of_nonneg (by linarith [{lem_c[k]} hr0 hr1 hd0 hd1]) (by positivity) :\n    {cs} ≤ 0)")
    Xs=["XR","X0","X1","X2"]
    comp=["(g0 ^ 2 + g1)","(7 * g0 + 3 * g3)","(49 + g5)"]
    comp_h="\n".join(f"    have hc{k} : 0 < {c} := by positivity" for k,c in enumerate(comp))
    lhs1=f"XR / ({G.plean(Rc)})"+"".join(f" + X{k} / ({G.plean(tm['cc'])}) * ({tm['Bl']})" for k,tm in enumerate(terms))
    rhs_sym="("+" + ".join(f"{X} * ({sym_lean(M)})" for X,M in zip(Xs,Ms))+f") / ({sym_lean(den)})"
    rhs_act="("+" + ".join(f"{X} * ({sym_to_actual_lean(M)})" for X,M in zip(Xs,Ms))+f") / ({sym_to_actual_lean(den)})"
    gens="\n".join(f"    generalize {ln} = g{k} at *" for k,(ln,ap) in reversed(list(enumerate(atoms))) )
    # composite positivity hyps (for field_simp): N+M forms
    numsL=[G.L(n_) for n_ in nums]
    sumexpr="("+" + ".join(f"({x}) * ({sym_to_actual_lean(M)})" for x,M in zip(numsL,Ms))+")"
    den_l=sym_to_actual_lean(den)
    ex_num,ex_den=sp.fraction(extra)
    glist=" ".join(f"g{k}" for k in range(len(atoms)))
    ghyps=" ".join(f"(hg{k} : 0 < g{k})" for k in range(len(atoms)))
    lhs_g=lhs1
    for k in range(len(atoms)-1,-1,-1): lhs_g=lhs_g.replace(atoms[k][0],f"g{k}")
    termlemmas=[]
    # termwise identities
    Bls=[f"XR / ({G.plean(Rc)})"]+[f"X{k} / ({G.plean(tm['cc'])}) * ({tm['Bl']})" for k,tm in enumerate(terms)]
    for k,(X,M,Bl) in enumerate(zip(Xs,Ms,Bls)):
        lg=Bl
        for kk in range(len(atoms)-1,-1,-1): lg=lg.replace(atoms[kk][0],f"g{kk}")
        out.append(f"""theorem fs_NA{name}_k{k} ({X} {glist} : ℝ) {ghyps} :
    {lg} = {X} * ({sym_lean(M)}) / ({sym_lean(den)}) := by
{comp_h.replace('    have','  have')}
  field_simp
  try ring
""")
    out.append(f"""/-- The asymmetric-face value `{name}` with its three logarithms is negative. -/
theorem fs_NA{name}_bound {{r d : ℝ}} (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 3) (hd0 : 0 ≤ d) (hd1 : d ≤ 3 / 5) :
    {stmt} < 0 := by
{atom_hyps}
{chr(10).join(logh)}
  have key1 : ∀ XR X0 X1 X2 : ℝ, {lhs1} =
      {rhs_act} := by
    intro XR X0 X1 X2
    rw [{", ".join(f"fs_NA{name}_k{k} _ {' '.join('_' for _ in atoms)} {' '.join(f'hA{j}' for j in range(len(atoms)))}" for k in range(len(Xs)))}]
    rw [← add_div, ← add_div, ← add_div]
  have key2 : {sumexpr} = ({sp.sstr(extra).replace('**','^')}) * ({G.L(nred)}) := by ring
  have hN := fs_NA{name}_N hr0 hr1 hd0 hd1
  have hneg : {sumexpr} / ({den_l}) < 0 := by
    rw [key2]
    apply div_neg_of_neg_of_pos _ (by positivity)
    exact mul_neg_of_pos_of_neg (by positivity) hN
  calc _ ≤ ({G.L(Rn)}) / ({G.plean(Rc)})""" + "".join(f" +\n        ({G.L(tm['cn'])}) / ({G.plean(tm['cc'])}) * ({tm['Bl']})" for tm in terms) + f""" :=
        add_le_add (add_le_add (add_le_add le_rfl hm0) hm1) hm2
    _ = {sumexpr} / ({den_l}) := key1 {' '.join('('+x+')' for x in numsL)}
    _ < 0 := hneg
""")
open('Nasym.lean','w').write("\n".join(out))
print('ok')
