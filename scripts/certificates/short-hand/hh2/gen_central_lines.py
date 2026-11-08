import sys, re
import sympy as sp
from fractions import Fraction as Fr
from bern import from_sympy, lincomb
from leangen import Lib, emit_nested, lnum, nested_coeffs
from cen_common import *
from gen_central import write, M, pG, pA, pD, VARS, COORD
which=[int(v) for v in sys.argv[1].split(',')] if len(sys.argv)>1 else range(5)
dG=nested_coeffs(pG); dA_=nested_coeffs(pA); dD=nested_coeffs(pD)
def has(d,i,j): return i<len(d) and j<len(d[0]) and any(c!=0 for c in d[i][j])
BOX=[((Fr(0),Fr(229,1024)),(Fr(13,6),Fr(12,5)),(Fr(1),Fr(4,3)))]
for li in which:
    al,be=LINES[li]
    P=lincomb([pG,pD,pA],[Fr(-1),-al,-be])
    X=f"hh2CnL{li}"
    def dexpr(i,j):
        terms=[]; names=[]
        if has(dG,i,j): terms.append(f"hh2CnG_d{i}_{j} a"); names.append(f"hh2CnG_d{i}_{j}")
        if al!=0 and has(dD,i,j): terms.append(f"{lnum(al)} * hh2CnD_d{i}_{j} a"); names.append(f"hh2CnD_d{i}_{j}")
        if be!=0 and has(dA_,i,j): terms.append(f"{lnum(be)} * hh2CnA_d{i}_{j} a"); names.append(f"hh2CnA_d{i}_{j}")
        return "-(" + " + ".join(terms) + ")", names
    doc=(f"Line {li} of the duration bound (`ℓ{li}(A) = {al} + ({be})A`): the polynomial "
         f"`-(N_G + ({al})N_D + ({be})N_A)` in {COORD}.")
    d=nested_coeffs(P)
    N1=len(d)-1; half=(N1+1)//2
    libA=Lib(X+'a')
    codeA,nlA,_=emit_nested(libA,X,P,VARS,BOX,doc=doc,dexpr=dexpr,kset=set(range(half)),emit_box=False,kpublic=True)
    libB=Lib(X+'b')
    codeB,nlB,_=emit_nested(libB,X,P,VARS,BOX,doc=doc,dexpr=dexpr,defs=False,kset=set(range(half,N1+1)),emit_box=True,kpublic=True)
    nl=nlA+nlB
    ldn=" ".join(f"{X}_d{i}_{j}" for i in range(len(d)) for j in range(len(d[0])) if any(c!=0 for c in d[i][j]))
    eq=f'''/-- `{X}` is the combination `-(N_G + αN_D + βN_A)`. -/
theorem {X}_eq (t x a : ℝ) :
    {X} t x a = -(hh2CnG t x a + {lnum(al)} * hh2CnD t x a + {lnum(be)} * hh2CnA t x a) := by
  unfold {X} {ldn} hh2CnG hh2CnD hh2CnA
  ring
'''
    write(f'S2CenL{li}a.lean',[M+'S2CenPoly'],f'central face, generated certificate `{X}` (part 1)',doc,
          f"* `{X}`: the polynomial in nested form; `{X}_eq`: its definition as a combination; the first half of the level-1 Bernstein coefficients.",
          libA.render()+"\n"+codeA+"\n"+eq)
    write(f'S2CenL{li}.lean',[M+f'S2CenL{li}a'],f'central face, generated certificate `{X}`',doc,
          f"* `{X}_pos`: positivity on `[0, 229/1024] × [13/6, 12/5] × [1, 4/3]`.",
          libB.render()+"\n"+codeB)
    print('leaves',nl)
