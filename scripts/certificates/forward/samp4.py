from defs import *
from mpmath import diff
mp.dps=20
worst=-1e9;arg=None; worstI=-1e9; argI=None
N=40
for i in range(N+1):
    z=1+mpf(i)/N/3
    Ulo=1+6*z/5
    for j in range(N+1):
        U=Ulo+(3-Ulo)*mpf(j)/N
        if U>=3: U=3-mpf(10)**-6
        lo=(1+z)**2/(z*z+U); hi=(1+z)*(5*U-2-3*z)/(3*(z*z+U))
        for k in range(11):
            h=lo+(hi-lo)*k/10
            dv=diff(lambda hh: resS(U,z,z,hh), h)
            if dv>worst: worst=dv;arg=(float(U),float(z),float(h-1),float(lo-1),float(hi-1))
        v=resS(U,z,z,lo)/(lo-1)
        if v>worstI: worstI=v; argI=(float(U),float(z))
print('max dE/dh',worst,arg)
print('max E(I)/t',worstI,argI)
