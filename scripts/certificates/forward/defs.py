from mpmath import mp, mpf, log, sqrt, pi
mp.dps=30
def f(r): return (r-1/r)/2-log(r)
def F(x,r): return 1+x*x*r-x*r*log(r)/(r-1)
def g2(U,x,y): return 3*x*y-U-(x*x+y*y)*log(x+y)+(x*x*log(x*x+U)+y*y*log(y*y+U))/2
def q(U,z,w): return (1+z)*(1+w)/(1+U)
def A(U,z,w): return 1+z+w-1/(1+z)-1/(1+w)+1/(1+U)-log(q(U,z,w))
def B(U,z,h): return (z*z+U)*h/(1+z)+1-z*z*(1+z)/((z*z+U)*h)-z*z/(1+z)+z**3/(z*z+U)-z*log(h)
def al(U,z,h): return (1+U)*(h*(1+z)-z)/(z*z+U)
def n(U,z,h): return (1+z)**2*(U-z)*(h-1)/(z*z+U)
def m(U,z,w,h): return (1+U)**2/((1+z)*(z*z+U))*(q(U,z,w)-1+(h-1)*(q(U,z,w)*(1+z)-1))
def cas(U,u,v,E): return (1+U)**2*(4*u*v-E*E)/(16*U*U)
def Phi(U,z,w): return f((1+z)/2)+f((1+w)/2)+f(4/(1+U))
def e0(U): return 1-(1+U)/8+1/(1+U)
def r(U,z,w,h):
    d=3-U;x=z-1;H=h-1
    P=d*d*(x*x+4*x+2)+8*d*x*z+2*x*x*(8+4*x-x*x)
    return (d*x*(d+2*x)+H*P)/(8*(1+z)*(z*z+U))+H*H*z*(d+4*x+x*x)/(2*h*(z*z+U))+(1+U)*(1+(1+z)*H)/(z*z+U)*Phi(U,z,w)-z*f(h)
def L(z,h): return (z-1)*((z-1)+2*z*(h-1))/(4*(1+z)**2)+z*h/(1+z)*(f(h)/(h-1))
def resS(U,z,w,h): return r(U,z,w,h)-n(U,z,h)/35-(m(U,z,w,h)-n(U,z,h))*L(w,(1+w)**2/(w*w+U))
def resV(U,z,w,h): return r(U,z,w,h)-n(U,z,h)*L(z,h)-m(U,z,w,h)/64
def resN(U,z,w,h): return al(U,z,h)*A(U,z,w)-B(U,z,h)-n(U,z,h)*F(z/(1+z),h)-m(U,z,w,h)*F(w/(1+w),(1+w)**2/(w*w+U))
Aoct=2*sqrt(3)*(8-4*sqrt(2)-log(2))/(2*sqrt(2)-1)
