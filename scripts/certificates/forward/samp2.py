from defs import *
mp.dps=20
best={'S':(-1e9,None),'V':(-1e9,None)}
N=30
for i in range(N+1):
    z=1+mpf(i)/N/3
    Ulo=1+6*z/5
    for j in range(N+1):
        U=Ulo+(3-Ulo)*mpf(j)/N
        if U>=3: U=3-mpf(10)**-9
        lo=(1+z)**2/(z*z+U); hi=(1+z)*(5*U-2-3*z)/(3*(z*z+U))
        if hi<lo: continue
        for k in range(N+1):
            h=lo+(hi-lo)*mpf(k)/N
            if h<=1: h=1+mpf(10)**-12
            s=resS(U,z,z,h)/(h-1); v=resV(U,z,z,h)/(h-1)
            if s>best['S'][0]: best['S']=(s,(float(U),float(z),float(h),float(lo),float(hi)))
            if v>best['V'][0]: best['V']=(v,(float(U),float(z),float(h),float(lo),float(hi)))
print(best)
