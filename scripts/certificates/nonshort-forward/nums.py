from model import *
R_=sp.Rational
def lean(expr):
    P = sp.Poly(sp.expand(expr), t, x, q)
    terms=[]
    for (a,b,cq),c in sorted(P.terms()):
        c=sp.Rational(c)
        fs=[]
        for v,e in (('t',a),('x',b),('q',cq)):
            if e==1: fs.append(v)
            elif e>1: fs.append(f"{v} ^ ({e} : ℕ)")
        ac=abs(c)
        cs = (str(ac) if ac.q==1 else f"({ac.p} / {ac.q})")
        body=" * ".join(([cs] if (ac!=1 or not fs) else [])+fs)
        terms.append(("-" if c<0 else "+", body))
    s=("-" if terms[0][0]=="-" else "")+terms[0][1]
    for sg,b in terms[1:]: s+=f" {sg} {b}"
    return s
rho = R_(3,4)*(q+2*t+x-1)
vhat = VG + rho*(VG-Fl(q))
Nvh = sp.factor(vhat*12*R*W**2*(q+1)); assert sp.fraction(sp.together(Nvh))[1]==1
NVG = sp.factor(VG*12*R*W**2); assert sp.fraction(sp.together(NVG))[1]==1
NFl = sp.factor(Fl(q)*6*W**2*(q+1)); assert sp.fraction(sp.together(NFl))[1]==1
NV2 = sp.factor(V2*12*W**2); assert sp.fraction(sp.together(NV2))[1]==1
import json
json.dump({'Nvh':lean(Nvh),'NVG':lean(NVG),'NFl':lean(NFl),'NV2':lean(NV2)}, open('nums.json','w'))
print({k:len(v) for k,v in json.load(open('nums.json')).items()})
