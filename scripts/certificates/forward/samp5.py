from defs import *
from mpmath import diff
mp.dps=20
mx=-1e9;mn=1e9
N=30
for i in range(N+1):
    z=1+mpf(i)/N/3
    Ulo=1+6*z/5
    for j in range(N+1):
        U=Ulo+(3-Ulo)*mpf(j)/N
        if U>=3: U=3-mpf(10)**-6
        lo=(1+z)**2/(z*z+U); hi=(1+z)*(5*U-2-3*z)/(3*(z*z+U))
        for k in range(6):
            h=lo+(hi-lo)*k/5
            dv=diff(lambda UU: resS(UU,z,z,h), U)
            dz=diff(lambda zz: resS(U,zz,zz,h), z)
            mx=max(mx,dv); mn=min(mn,dv)
print('dE/dU range',mx,mn)
