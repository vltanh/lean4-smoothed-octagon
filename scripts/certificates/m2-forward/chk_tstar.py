from phys import *
import random, sympy as sp
import norm
random.seed(1)
for _ in range(5):
    a=mpf(random.uniform(0.5,0.8)); c=a+mpf(random.uniform(0.1,1)); d=a+mpf(random.uniform(0.1,1)); r=a+mpf(random.uniform(0,1)); v=mpf(random.uniform(0.75,0.9))
    bs=bStar(a,c); us=uRoot(a,bs,c,d,r,v); hs=h_(a,bs,c,us,v)
    ts=Next(a,c,d,r,us,v,hs)
    T=a+c; tt=a/T; xx=(d-a)/T; kk=(a**2+4)/T**2; qq=(c+d)*(d+r)/(d**2+4)
    sub={norm.t:tt,norm.x:xx,norm.k:kk,norm.q:qq,norm.v:v,norm.L:log(qq)}
    val=norm.Tstar.subs(sub)
    print(ts, sp.N(val,30))
