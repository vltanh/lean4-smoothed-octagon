from sympy import *
a,c,d,r,v,u,b,T,t,x,k,q,L,LQ = symbols('a c d r v u b T t x k q L LQ', positive=True)
# physical
K=a**2+4
def Stat(p,a_,n): return p+a_+n-a_**2*(1/(p+a_)+1/(a_+n))+a_**3/(a_**2+4) - a_*LQ_(p,a_,n)
# we treat logs symbolically: log((p+a)(a+n)/K) 
def m2h(a,b,c,u,v,logCa): 
    Ca = b+a+c-a**2*(1/(a+b)+1/(a+c))+a**3/(a**2+4) - a*logCa
    return (a**2+4)/(16*a)*((a+b)*u+(a+c)*v-Ca)
def Y(a,c,d): return (c+d)**2-(a+c)**2
def wOf(a,c,d,u,v,h): return ((a**2+4)**2*u+16*h*Y(a,c,d)+v*Y(a,c,d)**2)/(d**2+4)**2
def hd(a,c,d,v,h): return h+v*Y(a,c,d)/8
def Root(a,c,d,r,u,v,h,logq):
    Cd = c+d+r-d**2*(1/(c+d)+1/(d+r))+d**3/(d**2+4)-d*logq
    return Cd-(c+d)*v-(d+r)*wOf(a,c,d,u,v,h)+16*d*hd(a,c,d,v,h)/(d**2+4)
bstar = K/(a+c)-a
U = lambda z: 1-z+z**2
ustar = U(a*(a+c)/K)
# log(K/(S*T)) at b*: S*T = K -> log 1 = 0 ; Stat uses -a*log((p+a)(a+n)/K) = -a*log(S T/K)=0
h0 = m2h(a,bstar,c,ustar,v,0)
G = Root(a,c,d,r,ustar,v,h0,L)  # L = log q
# normalized substitution
subsd = {a:t*T, c:(1-t)*T, d:(t+x)*T}
# 4 = (k - t^2) T^2 ; we need to express K = k T^2. Replace number 4: do by setting T from k: T^2 = 4/(k-t^2)
W=1+x; p=t+x; B=k+2*t*x+x**2; Z=q*B/W; Yn=x*(x+2)
H0 = k/t*(v-1+t**2)+t*(2-t)
wU = (k**2-k*t+t**2+H0*Yn+v*Yn**2)/B**2
Rn = (1-t)+Z-p**2/W-p**2/Z+p**3/B-p*L-W*v-Z*wU+p*(H0+2*v*Yn)/B
# r physical = Z*T - d
Gs = G.subs(r, Z*T-(t+x)*T).subs(subsd)
Gs = Gs.subs(T, sqrt(4/(k-t**2)))
Tn = sqrt(4/(k-t**2))
print(simplify(Gs/Tn - Rn))
