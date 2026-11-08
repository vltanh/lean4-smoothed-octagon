from mpmath import mp, mpf, log, sqrt
import random
mp.dps=40
def f(r): return (r-1/r)/2-log(r)
def F(x,r): return 1+x**2*r - x*r*log(r)/(r-1)
for trial in range(5):
    a=mpf(random.uniform(1.16,1.34)); b=a*mpf(random.uniform(1,1.3)); c=a*mpf(random.uniform(1,1.3))
    p=a*mpf(random.uniform(1,1.5)); d=a*mpf(random.uniform(1,1.5))
    K=a*a+4;Kb=b*b+4;Kc=c*c+4;s=a+b;t=a+c
    h=(p+b)*s/Kb;q=s*t/K;k=t*(c+d)/Kc
    A=b+a+c-a*a*(1/s+1/t)+a**3/K-a*log(q)
    B=h*Kb/s+a-b*b*(s/(h*Kb)+1/s)+b**3/Kb-b*log(h)
    M11=s*s*(4-a*b)*(h-1)/(a*Kb); M12=K*K*(a*(q-1)+(h-1)*(s*q-a))/(a*s*Kb); RL=K*(h*s-b)/(a*Kb)*A-B
    U=4/a**2;z=b/a;w=c/a;S=1+z;T=1+w;Kd=1+U;Z=z*z+U;W=w*w+U
    Ad=1+z+w-1/S-1/T+1/Kd-log(q)
    Bd=Z*h/S+1-z*z*S/(Z*h)-z*z/S+z**3/Z-z*log(h)
    al=Kd*(h*S-z)/Z; nL=S*S*(U-z)*(h-1)/Z; mL=Kd**2/(S*Z)*(q-1+(h-1)*(q*S-1))
    print('q', q - S*T/Kd, 'A', A-a*Ad, 'B', B-a*Bd, 'M11', M11-a*nL, 'M12', M12-a*mL, 'RL', RL-a*(al*Ad-Bd))
    dd=3-U;x=z-1;H=h-1
    Pdx=dd**2*(x*x+4*x+2)+8*dd*x*(x+1)+2*x*x*(8+4*x-x*x)
    Phi=f(S/2)+f(T/2)+f(4/Kd)
    r=(dd*x*(dd+2*x)+H*Pdx)/(8*S*Z)+H*H*z*(dd+4*x+x*x)/(2*h*Z)+Kd*(1+S*H)/Z*Phi-z*f(h)
    print(' r', r-(al*Ad-Bd-mpf(3)/4*(nL+mL)))
    e0=1-Kd/8+1/Kd
    print(' E0', mpf(3)/4*(S+T)-Ad-(e0-Phi))
    L=x*(x+2*z*H)/(4*S*S)+z*h/S*f(h)/H
    print(' floor', F(z/S,h)-mpf(3)/4-L)
    print(' m-n', S*Z*(mL-nL)-(Kd*(S*T-Kd)+H*(S**4-Kd**2+Kd*S*S*(T-S))))
