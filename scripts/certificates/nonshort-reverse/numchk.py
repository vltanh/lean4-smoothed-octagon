import numpy as np
rng = np.random.default_rng(1)
def Nfun(t,x,k,q,v,L):
    W=1+x; X=x+2; p=t+x; Y=x*X; B=k+2*t*x+x**2; Z=q*B/W
    H0=k/t*(v-1+t**2)+t*(2-t)
    wU=(k**2-k*t+t**2+H0*Y+v*Y**2)/B**2
    R=(1-t)+Z-p**2/W-p**2/Z+p**3/B-p*L-W*v-Z*wU+p*(H0+2*v*Y)/B
    return t*B*q*W*R
def Sec(t,x):  # Sec(t,1-t,t+x) normalized
    W=1+x
    return 1+(1-t)**2/W-(1-t)*np.log1p(x)/x
def F(eta,q): return 1+eta**2*q-eta*q*np.log(q)/(q-1)
def U(t): return 1-t+t*t
n=4_000_000
# reverse domain (12)
t=rng.uniform(0,0.4,n); x=rng.uniform(0,7/3,n)
ok = x<7/3-10/3*t
kmin=np.maximum.reduce([np.ones(n),2*t+x,29/4*t**2]); kmax=2*t+2*x+x**2
ok &= kmin<kmax
k=kmin+(kmax-kmin)*rng.uniform(0,1,n)**3
W=1+x; p=t+x
q=1+(W/p-1)*rng.uniform(0,1,n)**2
v=Sec(t,x)
ok &= v<=U(t)
ok &= v>=F(p/W,q)
N=Nfun(t,x,k,q,v,np.log(q))
print('reverse: pts',ok.sum(),'min N',N[ok].min(), 'neg', (N[ok]<0).sum())
# lowscale
t=rng.uniform(0,0.5,n); x=rng.uniform(0,3,n)
kmin=np.maximum(1,17*t**2); kmax=2*t+2*x+x**2
ok = kmin<kmax
k=kmin+(kmax-kmin)*rng.uniform(0,1,n)**3
W=1+x; p=t+x
q=1+(W/p-1)*rng.uniform(0,1,n)**2
v=Sec(t,x)
ok &= v<=U(t); ok&= v>=1-(1-t)*p/W**2
ok &= v>=F(p/W,q)
N=Nfun(t,x,k,q,v,np.log(q))
print('lowscale(no order): pts',ok.sum(),'min N',N[ok].min(), 'neg', (N[ok]<0).sum())
idx = ok & (N<0)
if idx.sum(): 
    j=np.argmin(N[ok]); 
    print(t[ok][j],x[ok][j],k[ok][j],q[ok][j])
