import pickle, sympy as sp, time, sys, json
from fractions import Fraction as Fr
from plan3 import to_dict, pmul, padd, pscale
from gen4 import structure, lnum, lemma0g, lemmaI
from gen5 import plan_all, emit_job, Out, emit_pos_y
h,j,q,y=sp.symbols('h j q y')
R=Fr
LEAN=__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '../../../SmoothedOctagon/Exclusion/Mixed/Nonshort/Forward/')

def poly_hs_pow(base, e):
    r = {(0,0): Fr(1)}
    for _ in range(e): r = pmul(r, base)
    return r

def multipliers(kind, ny, jlo, Yc=None):
    if kind == 'zgen':
        from gen5 import zgen_M
        (Nm, Dn), (Nmd, Dnd) = Yc
        Ms = [pmul(poly_hs_pow(Nmd, i), poly_hs_pow(Dnd, ny-i)) for i in range(ny+1)]
        return Ms, [zgen_M(i, ny, Nm, Dn) for i in range(ny+1)]
    if kind == 'one':
        return [{(0,0):Fr(1)}]*(ny+1), ["1"]*(ny+1)
    if kind == 'sym':   # y = Yc*h*z
        Ms = [{(i,0): Fr(Yc)**i} for i in range(ny+1)]
        Ys = "h" if Yc == 1 else f"({lnum(Yc)} * h)"
        from gen5 import sym_M
        return Ms, [sym_M(i, Ys) for i in range(ny+1)]
    if kind == 'zpar':  # y = z (h - j)/(1 + 2j), j = jlo + s
        hm = padd({(1,0):Fr(1)}, {(0,0):Fr(jlo), (0,1):Fr(1)} if jlo else {(0,1):Fr(1)}, -1)
        tj = {(0,0):Fr(1)+2*Fr(jlo), (0,1):Fr(2)}
        Ms = [pmul(poly_hs_pow(hm, i), poly_hs_pow(tj, ny-i)) for i in range(ny+1)]
        from gen5 import zpar_M
        return Ms, [zpar_M(i, ny) for i in range(ny+1)]

def build(X, pkl, h0, h1, jlo, g, gstr, kind, Yc=None, zlo=Fr(0), zhi=Fr(1), vars3=None):
    P = pickle.load(open(pkl,'rb'))
    if vars3 is None:
        P = sp.expand(P.subs(q, 1+y))
        d = to_dict(P, [h, j, y])
    else:
        d = to_dict(P, [sp.Symbol(v) for v in vars3])
    D = structure(d, jlo)
    ny = len(D) - 1
    Ms, Mstrs = multipliers(kind, ny, jlo, Yc)
    t0 = time.time()
    plan = plan_all(D, Ms, g, Fr(h0), Fr(h1), Fr(zlo), Fr(zhi))
    print(X, 'plan', [(float(a), float(b), r[0], r[3]) for a, b, r in plan], 'time', round(time.time()-t0,1), flush=True)
    out = Out(); needI = set(); need0g = set()
    final, cs = emit_job(out, X, D, Mstrs, gstr, Fr(jlo), Fr(h0), Fr(h1), plan, needI, need0g)
    sstr = "j" if jlo == 0 else f"(j - {lnum(Fr(jlo))})"
    from gen4 import poly_str
    cs_plain = ["(" + poly_str([f"{X}D{i}_{l} h" for l in range(len(D[i]))], sstr) + ")" for i in range(ny+1)]
    yform = emit_pos_y(out, X, D, kind, gstr, Fr(jlo), Fr(h0), Fr(h1), final, cs_plain, ny, Yc[0] if kind == 'zgen' else Yc) if kind != 'one' else final
    return out, needI, need0g, yform, cs_plain, D, ny

JOBS = {
 'nsfCPn': dict(pkl='Phat.pkl', h0=R(0), h1=R(1,15), jlo=0, g=[R(1,30)], gstr='1 / 30', kind='one', vars3=('A','J','Z'), zlo=0, zhi=R(1,30)),
 'nsfCLRb': dict(pkl='lr_ko.pkl', h0=R(1,3), h1=R(1,2), jlo=0, g=[R(0),R(1)], gstr='h', kind='sym', Yc=R(1)),
}
DOC = {
 'nsfCPn': 'the Casimir excess `3125t²p²W⁴Q²(N(V) - 16s²·9193/50000)`-(11))',
 'nsfCLRb': 'the low-ratio residual `Ĝ` at the order shape `k = 2t + x`',
}
# the output module and the title of each certificate
OUT = {
 'nsfCPn': 'SmallGap/CasimirExcessSigns.lean',
 'nsfCLRb': 'LowRatio/OrderShapeSigns.lean',
}
TITLE = {
 'nsfCPn': 'the sign of the Casimir excess',
 'nsfCLRb': 'the low-ratio residual at the order shape',
}
if __name__ == '__main__':
    names = sys.argv[1:]
    for X in names:
        out, needI, need0g, final, cs, D, ny = build(X, **JOBS[X])
        print(X, 'leaves', out.nleaf, 'chars', len("\n".join(out.code)), flush=True)
        pickle.dump(dict(code=out.code, needI=needI, need0g=need0g, final=final, cs=cs, D=D, ny=ny, kind=JOBS[X]['kind']), open(f'{X}.gen.pkl','wb'))
