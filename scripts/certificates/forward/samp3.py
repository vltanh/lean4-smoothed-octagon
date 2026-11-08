from defs import *
mp.dps=20
# resS decomposition: E(H) = A0 + A1 H + z k(H)
def parts(U,z):
    S=1+z;Z=z*z+U;K=1+U;d=3-U;x=z-1
    D=(d+4*x+x*x)/Z
    eps=mpf(10)**-8
    E0=resS(U,z,z,1+eps)  # ~A0
    # fit A0, A1 from exact formula: E(H) - z k(H)
    def k(H): return D*H*H/(2*(1+H))-f(1+H)
    H1=mpf('0.1');H2=mpf('0.2')
    e1=resS(U,z,z,1+H1)-z*k(H1); e2=resS(U,z,z,1+H2)-z*k(H2)
    A1=(e2-e1)/(H2-H1); A0=e1-A1*H1
    return A0,A1,D
worst=-1;arg=None
N=30
for i in range(N+1):
    z=1+mpf(i)/N/3
    Ulo=1+6*z/5
    for j in range(N+1):
        U=Ulo+(3-Ulo)*mpf(j)/N
        if U>=3: U=3-mpf(10)**-6
        A0,A1,D=parts(U,z)
        lo=(1+z)**2/(z*z+U); hi=(1+z)*(5*U-2-3*z)/(3*(z*z+U))
        for k in range(11):
            h=lo+(hi-lo)*k/10
            H=h-1
            v=resS(U,z,z,h)/H
            if v>worst: worst=v;arg=(float(U),float(z),float(H),float(A0),float(A1),float(D),float(lo-1),float(hi-1))
print(worst,arg)
