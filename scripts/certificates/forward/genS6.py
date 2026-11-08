from genS import *
from collections import Counter
info=pickle.load(open('S_info.pkl','rb'))
P1s='(2 - 2 * a ^ 2 - t * (5 + 3 * a + 2 * a ^ 2))'
P2s='(5 - 3 * a - 2 * a ^ 2 - t * (5 + 3 * a + 2 * a ^ 2))'
P3s='(8 - 6 * a - 2 * a ^ 2 - t * (5 + 3 * a + 2 * a ^ 2))'
UBI_s="((1 + t) - 1 / (1 + t)) / 2 - t ^ 3 / (3 * (1 + t) * ((1 + t) + 1))"
UBc_s="-(a * (1 + t)) - (a * (1 + t)) ^ 2 / 2 - (a * (1 + t)) ^ 3 / 3"
AT={ln:ap for ln,ap in ATOMS}
R1=((0,Fr(1,7)),(0,Fr(1,4)))
B1=((0,Fr(1,10)),(0,Fr(1,4))); B2=((0,Fr(1,7)),(Fr(39,400),Fr(1,4)))
def atoms_of(den):
    kappa,fs=atomize(den)
    assert kappa==1, kappa
    return Counter({ln:e for ln,ap,e in fs})
def prod_lean(cnt, extra=None):
    parts=([extra] if extra else [])+[ln if e==1 else f"{ln} ^ {e}" for ln,e in sorted(cnt.items()) if e>0]
    return " * ".join(parts) if parts else "1"
def prod_poly(cnt):
    return sp.Mul(*[AT[ln]**e for ln,e in cnt.items()])
def gen(sx): return sx.replace(P1s,'p1').replace(P2s,'p2').replace(P3s,'p3')
out=[]
def fr(num, cnt): return f"({L(num)}) / ({prod_lean(cnt)})"
pos_hyps=f"""  have hb : 0 < 1 - a := by linarith
  have hP1 : 0 < {P1s} := by nlinarith [mul_nonneg ha0 ht0.le, mul_nonneg (mul_nonneg ha0 ha0) ht0.le]
  have hP2 : 0 < {P2s} := by nlinarith [mul_nonneg ha0 ht0.le, mul_nonneg (mul_nonneg ha0 ha0) ht0.le]
  have hP3 : 0 < {P3s} := by nlinarith [mul_nonneg ha0 ht0.le, mul_nonneg (mul_nonneg ha0 ha0) ht0.le]"""
res=pickle.load(open('S_parts.pkl','rb'))
lin_info={}
for name,boxes,strict in [('A0',[R1],False),('E3',[R1],True),('E4',[B1,B2],True)]:
    parts={}
    for nm in ['R','cI','cc']:
        n,d=res[name][nm]
        n=sp.sympify(str(n)); d=sp.sympify(str(d))
        nump,dl,dp=frac_lean(n,d)
        parts[nm]=(nump,atoms_of(dp))
    lin_info[name]=parts
    Rn,Rc=parts['R']; In,Ic=parts['cI']; Cn,Cc=parts['cc']
    Pi=Rc | (Ic + Counter({'(1 + t)':1,'(2 + t)':1})) | Cc
    M1=Pi-Rc; M2=Pi-(Ic+Counter({'(1 + t)':1,'(2 + t)':1})); M3=Pi-Cc
    M1l=prod_lean(M1,"6"); M2l=prod_lean(M2,"(t * (t ^ 2 + 12 * t + 12))"); M3l=prod_lean(M3,"(-(a * (1 + t) * (6 + 3 * (a * (1 + t)) + 2 * (a * (1 + t)) ^ 2)))")
    M1p=6*prod_poly(M1); M2p=t*(t**2+12*t+12)*prod_poly(M2); y=a*(1+t); M3p=-(y*(6+3*y+2*y**2))*prod_poly(M3)
    Bn=sp.expand(Rn*M1p+In*M2p+Cn*M3p)
    Bdl="6 * "+prod_lean(Pi)
    # sanity: value check
    import random
    for _ in range(3):
        av=sp.Rational(random.randint(1,100),800); tv=sp.Rational(random.randint(1,100),400)
        lhs=(Rn/prod_poly(Rc)+In/prod_poly(Ic)*UBI+Cn/prod_poly(Cc)*UBc).subs({a:av,t:tv})
        rhs=(Bn/(6*prod_poly(Pi))).subs({a:av,t:tv})
        assert sp.simplify(lhs-rhs)==0
    lem={}
    for nm,poly in [('cI',In),('cc',Cn)]:
        lem[nm]=[]
        for k,bx in enumerate(boxes):
            s,mn=bern_lemma_n(f"fs_S{name}_{nm}{k}", poly, a, t, bx)
            out.append(s); lem[nm].append(f"fs_S{name}_{nm}{k}")
    lem['N']=[]
    for k,bx in enumerate(boxes):
        p = -Bn - (t/100 if strict else 0)
        s,mn=bern_lemma_n(f"fs_S{name}_N{k}", sp.expand(p), a, t, bx)
        print(name,k,'N min',float(mn))
        out.append(s); lem['N'].append(f"fs_S{name}_N{k}")
    def use(key):
        if len(boxes)==1:
            return f" {lem[key][0]} ha0 ha1 ht0.le ht1"
        return (f" by\n    rcases le_total a (1 / 10) with h | h\n"
                f"    · exact {lem[key][0]} ha0 h ht0.le ht1\n"
                f"    · exact {lem[key][1]} ha0 ha1 (by linarith) ht1")
    Npoly = sp.expand(-Bn - (t/100 if strict else 0))
    if name=='E4':
        Nuse=(f" by\n    rcases le_total a (1 / 10) with h | h\n"
              f"    · exact {lem['N'][0]} ha0 h ht0.le ht1\n"
              f"    · exact {lem['N'][1]} ha0 ha1 (by linarith) ht1")
    else: Nuse=use('N')
    extra = " (h39 : 39 * a / 40 ≤ t)" if name=='E4' else ""
    concl = "< 0" if strict else "≤ 0"
    final = ("div_neg_of_neg_of_pos (by linarith) (by positivity)" if strict
             else "div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)")
    hlt = "<" if strict else "≤"
    sgn = "<" if strict else "≤"
    out.append(f"""/-- The cleared numerator of the bounded `{name}` value has the required sign. -/
theorem fs_S{name}_Nsign {{a t : ℝ}} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 7) (ht0 : 0 < t) (ht1 : t ≤ 1 / 4){extra} :
    {L(Bn)} {sgn} 0 := by
  have hN : 0 ≤ {L(Npoly)} :={Nuse}
  linarith only [hN, ht0]
""")
    out.append(f"""/-- The `{name}` value, linear in the two logarithms, is {'negative' if strict else 'nonpositive'}. -/
theorem fs_S{name}_bound {{a t : ℝ}} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 7) (ht0 : 0 < t) (ht1 : t ≤ 1 / 4){extra} :
    {fr(Rn,Rc)} + {fr(In,Ic)} * Real.log (1 + t) +
      {fr(Cn,Cc)} * Real.log (1 - a * (1 + t)) {concl} := by
{pos_hyps}
  have hy0 : 0 ≤ a * (1 + t) := by positivity
  have hy1 : a * (1 + t) < 1 := by nlinarith
  have hlI := fs_log_le_pade ht0.le
  have hlc := fs_log_one_sub_le hy0 hy1
  have hN := fs_S{name}_Nsign ha0 ha1 ht0 ht1{' h39' if name=='E4' else ''}
  have hcI : 0 ≤ {L(In)} :={use('cI')}
  have hcc : 0 ≤ {L(Cn)} :={use('cc')}
  have h1 := mul_le_mul_of_nonneg_left hlI (div_nonneg hcI (by positivity) : 0 ≤ {fr(In,Ic)})
  have h2 := mul_le_mul_of_nonneg_left hlc (div_nonneg hcc (by positivity) : 0 ≤ {fr(Cn,Cc)})
  have key1 : ∀ X Y W p1 p2 p3 : ℝ, 0 < p1 → 0 < p2 → 0 < p3 →
      X / ({gen(prod_lean(Rc))}) + Y / ({gen(prod_lean(Ic))}) * ({UBI_s}) +
      W / ({gen(prod_lean(Cc))}) * ({UBc_s}) =
      (X * ({gen(M1l)}) + Y * ({gen(M2l)}) + W * ({gen(M3l)})) / ({gen(Bdl)}) := by
    intro X Y W p1 p2 p3 hp1 hp2 hp3
    field_simp
    ring
  have key2 : {L(Bn)} = ({L(Rn)}) * ({M1l}) + ({L(In)}) * ({M2l}) + ({L(Cn)}) * ({M3l}) := by ring
  have hneg : (({L(Rn)}) * ({M1l}) + ({L(In)}) * ({M2l}) + ({L(Cn)}) * ({M3l})) / ({Bdl}) {hlt} 0 := by
    rw [← key2]; exact {final.replace("(by linarith)","hN")}
  calc _ ≤ {fr(Rn,Rc)} + {fr(In,Ic)} * ({UBI_s}) +
        {fr(Cn,Cc)} * ({UBc_s}) := add_le_add (add_le_add le_rfl h1) h2
    _ = (({L(Rn)}) * ({M1l}) + ({L(In)}) * ({M2l}) + ({L(Cn)}) * ({M3l})) / ({Bdl}) :=
        key1 _ _ _ _ _ _ hP1 hP2 hP3
    _ {hlt} 0 := hneg
""")
open('Sat.lean','w').write("\n".join(out))
pickle.dump(lin_info,open('S_lin.pkl','wb'))
print('ok')
