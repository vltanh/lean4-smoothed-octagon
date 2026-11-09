import numpy as np
from numchk import Nfun, Sec, F, U
rng = np.random.default_rng(3)
n=4_000_000
def run(tlo,thi, scale, label):
    t=rng.uniform(tlo,thi,n); x=rng.uniform(0,2.5,n)
    k=np.maximum(1,scale*t**2)
    kmax=2*t+2*x+x**2
    ok = k<kmax
    W=1+x; p=t+x
    q=1+(W/p-1)*rng.uniform(0,1,n)**2
    v=Sec(t,x)
    ok &= v<=U(t); ok &= v>=1-(1-t)*p/W**2
    with np.errstate(all='ignore'):
        ok &= v>=F(p/W,q)
        N=Nfun(t,x,k,q,v,np.log(q))
    j=np.argmin(np.where(ok,N,np.inf))
    print(label, ok.sum(), 'min N', N[j], 't,x,k,q', t[j],x[j],k[j],q[j], 'neg',(N[ok]<0).sum())
run(0.4,0.5,7,'highT 7')
run(0.4,0.5,20/3,'highT 20/3')
run(0.38,0.5,20/3,'highT 20/3 from .38')
