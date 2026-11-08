from mpmath import mp, mpf, log
mp.dps = 40
def U(x): return 1-x+x**2
def g(a,b): return (a*a+a*b+b*b)/(a+b)**2
def Sec(A,B,P):
    if A==P: return g(A,B)
    return 1+B**2/((A+B)*(P+B)) - B/(P-A)*log((P+B)/(A+B))
def F(x,q):
    if q==1: return U(x)
    return 1+x**2*q - x*q*log(q)/(q-1)
def Stat(p,a,n):
    return p+a+n - a**2*(1/(p+a)+1/(a+n)) + a**3/(a**2+4) - a*log((p+a)*(a+n)/(a**2+4))
def h_(a,b,c,u,v): return (a**2+4)/(16*a)*((a+b)*u+(a+c)*v-Stat(b,a,c))
def Y_(a,c,d): return (c+d)**2-(a+c)**2
def hd(a,c,d,v,h): return h+v*Y_(a,c,d)/8
def wOf(a,c,d,u,v,h): return ((a**2+4)**2*u+16*h*Y_(a,c,d)+v*Y_(a,c,d)**2)/(d**2+4)**2
def Root(a,c,d,r,u,v,h): return Stat(c,d,r)-(c+d)*v-(d+r)*wOf(a,c,d,u,v,h)+16*d*hd(a,c,d,v,h)/(d**2+4)
def Next(a,c,d,r,u,v,h): return ((d**2+4)**2*v-16*hd(a,c,d,v,h)*(d+r)**2+wOf(a,c,d,u,v,h)*(d+r)**4)/(r**2+4)**2
def Cas(a,u,v,h): return u*v*(a**2+4)**2/64-h**2
def RootAt(a,b,c,d,r,v,u): return Root(a,c,d,r,u,v,h_(a,b,c,u,v))
def uRoot(a,b,c,d,r,v):
    R0=RootAt(a,b,c,d,r,v,0); R1=RootAt(a,b,c,d,r,v,1); return -R0/(R1-R0)
def bStar(a,c): return (a**2+4)/(a+c)-a
