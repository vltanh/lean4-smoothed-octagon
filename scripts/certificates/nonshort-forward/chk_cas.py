from phys import *
import random
random.seed(3)
for _ in range(4):
    a=mpf(random.uniform(0.5,0.8)); b=a+mpf(random.uniform(0.2,1)); c=a+mpf(random.uniform(0.1,0.5)); d=a+mpf(random.uniform(0.1,1)); r=a+mpf(random.uniform(0,1)); v=mpf(random.uniform(0.75,0.9))
    u=uRoot(a,b,c,d,r,v); h=h_(a,b,c,u,v); w=wOf(a,c,d,u,v,h)
    cas=Cas(a,u,v,h)
    T=a+c; t=a/T; x=(d-a)/T; k=(a**2+4)/T**2; q=(c+d)*(d+r)/(d**2+4)
    W=1+x; p=t+x; B=k+2*t*x+x**2; Z=q*B/W; L=log(q)
    Sd=(1-t)+Z-p**2/W-p**2/Z+p**3/B-p*L
    Hd=(B/p)*(W*v+Z*w-Sd)
    G=(4*B**2*v*w-Hd**2)/(16*(k-t**2)**2)
    print(cas, G)
