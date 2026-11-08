from sympy import *
def lnum(c):
    c=Rational(c)
    if c.q==1: s=str(abs(c.p))
    else: s=f"({abs(c.p)} / {c.q})"
    return s
def mono(vars, exps):
    parts=[]
    for v,e in zip(vars,exps):
        if e==0: continue
        parts.append(v if e==1 else f"{v} ^ ({e} : ℕ)")
    return " * ".join(parts)
def poly_str(expr, gens, names):
    P=Poly(expand(expr), *gens)
    terms=sorted(P.terms(), key=lambda t: t[0])
    out=[]
    for exps,c in terms:
        m=mono(names,exps)
        cs=lnum(c)
        if m=="": t=cs
        elif cs=="1": t=m
        else: t=f"{cs} * {m}"
        sign = "-" if c<0 else "+"
        out.append((sign,t))
    if not out: return "0"
    s=("-" if out[0][0]=="-" else "")+out[0][1]
    for sg,t in out[1:]:
        s+=f" {sg} {t}"
    return s
