from defs import *
from mpmath import diff
mp.dps=25
def face(U,z,w):
    S=1+z;Z=z*z+U
    H=S*S/Z
    hc=S*(5*U-2-3*w)/(3*Z); hs=S/z
    hup=min(hc,hs)
    if hup<H: return None
    E=resN(U,z,w,H)
    dE=diff(lambda hh: resN(U,z,w,hh), H)
    T=E+(hup-H)*dE
    # true max over h
    mx=max(resN(U,z,w,H+(hup-H)*k/20) for k in range(21))
    return E,T,mx,(hup==hc)
# symmetric face
wE=wT=wM=-1e9
for i in range(31):
    z=mpf(4)/3+mpf(i)/30/3
    Ulo=1+6*z/5
    for j in range(31):
        U=Ulo+(3-Ulo)*j/30
        if U>=3: U=3-mpf(10)**-9
        r=face(U,z,z)
        if r is None: continue
        E,T,mx,c=r
        wE=max(wE,E);wT=max(wT,T);wM=max(wM,mx)
print('sym face: E',wE,'T',wT,'true max',wM)
wE=wT=wM=-1e9
for i in range(31):
    z=1+mpf(i)/30/3
    Ulo=mpf(9)/5+3*z/5
    for j in range(31):
        U=Ulo+(3-Ulo)*j/30
        if U>=3: U=3-mpf(10)**-9
        r=face(U,z,mpf(4)/3)
        if r is None: continue
        E,T,mx,c=r
        wE=max(wE,E);wT=max(wT,T);wM=max(wM,mx)
print('asym face: E',wE,'T',wT,'true max',wM)
