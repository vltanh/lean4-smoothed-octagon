from model import *
import json
R_=sp.Rational
def lean(expr, vars_=(t,x,k)):
    P = sp.Poly(sp.expand(expr), *vars_)
    names=[str(v) for v in vars_]
    terms=[]
    for mon,c in sorted(P.terms()):
        c=sp.Rational(c); fs=[]
        for v,e in zip(names,mon):
            if e==1: fs.append(v)
            elif e>1: fs.append(f"{v} ^ ({e} : ℕ)")
        ac=abs(c); cs=(str(ac) if ac.q==1 else f"({ac.p} / {ac.q})")
        body=" * ".join(([cs] if (ac!=1 or not fs) else [])+fs)
        terms.append(("-" if c<0 else "+", body))
    s=("-" if terms[0][0]=="-" else "")+terms[0][1]
    for sg,b in terms[1:]: s+=f" {sg} {b}"
    return s
B=Bk(k); Qq=x**2+6*x+6
Pv=Y*(k/t+Y); K0=k**2-k*t+t**2+(k/t*(-1+t**2)+t*(2-t))*Y
g=1-c*p/W**2
Dp=B*(1+W/p)+Pv/(p*W)
D0=B*((-c+p**2/W)/p)+(K0-B**2)/(p*W)+p*W-p**2-B*g
out={}
for name,e in [('NV',W*Qq*Vq),('NK',t*K0),('NP',t*Pv),('ND0',t*p*W**2*D0),('NDp',t*p*W*Dp)]:
    ee=sp.factor(sp.together(e)); n,d=sp.fraction(ee); assert d==1, (name,d)
    out[name]=lean(ee)
json.dump(out,open('nums2.json','w'))
print({k_:len(v) for k_,v in out.items()})
