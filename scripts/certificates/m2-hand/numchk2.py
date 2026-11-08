import numpy as np
from numchk import Nfun, Sec, F, U
rng = np.random.default_rng(2)
n=4_000_000
def run(tmax, scale, label, order=True, k_face=None):
    t=rng.uniform(0,tmax,n); x=rng.uniform(0,7/3,n)
    ok = x<7/3-10/3*t
    kmin=np.maximum(1,scale*t**2)
    if order: kmin=np.maximum(kmin,2*t+x)
    kmax=2*t+2*x+x**2
    ok &= kmin<kmax
    k=kmin if k_face else kmin+(kmax-kmin)*rng.uniform(0,1,n)**3
    W=1+x; p=t+x
    q=1+(W/p-1)*rng.uniform(0,1,n)**2
    v=Sec(t,x)
    ok &= v<=U(t); ok &= v>=1-(1-t)*p/W**2
    with np.errstate(all='ignore'):
        ok &= v>=F(p/W,q)
        N=Nfun(t,x,k,q,v,np.log(q))
    j=np.argmin(np.where(ok,N,np.inf))
    print(label, ok.sum(), 'min N', N[j], 't,x,k,q', t[j],x[j],k[j],q[j], 'neg',(N[ok]<0).sum())
run(0.4, 29/4, 'rev 29/4', k_face=True)
run(0.4, 0, 'rev noscale', k_face=True)
run(0.4, 20/3, 'rev 20/3', k_face=True)
run(0.5, 20/3, 'rev 20/3 t<.5', k_face=True)
run(0.5, 7, 'rev 7 t<.5', k_face=True)
run(0.5, 0, 'rev none t<.5', k_face=True)
