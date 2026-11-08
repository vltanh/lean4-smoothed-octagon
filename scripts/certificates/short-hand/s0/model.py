# exact sympy model of the Lean definitions (Basic.lean)
from sympy import *
x, al, be = symbols('x al be', positive=True)
def Dg(x,be,al): return al**2+2*al*be+1+2*x-2*be*x
def RA(al,be): return al/(al+be)
def Qc(x,al): return al**2/(x*(x+2)+al**2)
def E0(x,u): return (1+x)*(u-1)+1/(1+x)
def A1(x,be,al,u): return 2*(1-1/al**2)+(1+x)/al**2+Dg(x,be,al)/al**2*E0(x,u)
def A2(x,be,al,u):
    e=1-1/al**2; n=(1+x)/al**2; De=Dg(x,be,al)/al**2
    return e**2+e*n+n**2+De**2*u+De*e*E0(x,u)-De*(2*(1+x)-1)/al**2
def A3(x,be,al,u):
    De=Dg(x,be,al)/al**2; e=1-1/al**2
    return 2*De*u+e*E0(x,u)-(2*(1+x)-1)/al**2
def Ws(x,be,al,u,q): return 1-q*A1(x,be,al,u)+q**2*A2(x,be,al,u)
def ELs(x,be,al,u,q): return -E0(x,u)+q*A3(x,be,al,u)
def F(x,be,al,u,q,tau,l,m):
    w=Ws(x,be,al,u,q)
    return (w-1)*tau+1/tau+(u-1)/RA(al,be)+RA(al,be)+1-q-ELs(x,be,al,u,q)+l+m*(w-Rational(3,4))
def Ubar(x,be): return Rational(3,4)+(2*(x-1)**3/((x+1)*(35*x+13))+(be-x)**3/(48*x**2))/(be-1)
def Uhat(x,be): return Rational(3,4)+2*(x-1)**2/((x+1)*(35*x+13))*(x-1+(be-x)/8)/(be-1)
h=Rational(1,2)  # floor weight m = 1/2
def central_two(x,al,be):
    q=Qc(x,al); T=RA(al,be)/q
    return F(x,be,al,Uhat(x,be),q,Integer(2),5/(2*T)-Rational(11,9),h)
def central_T(x,al,be):
    q=Qc(x,al); T=RA(al,be)/q
    return F(x,be,al,Uhat(x,be),q,T,0,h)
def central_8(x,al,be):
    q=Qc(x,al); T=RA(al,be)/q
    return F(x,be,al,Uhat(x,be),q,8*T/9,Rational(-1,9),h)
def outer(x,al,be,k):
    q=Rational(1,7); T=7*RA(al,be)
    if k=='T': return F(x,be,al,Ubar(x,be),q,T,0,h)
    if k=='8': return F(x,be,al,Ubar(x,be),q,8*T/9,Rational(-1,9),h)
    return F(x,be,al,Ubar(x,be),q,Integer(2),5/(2*T)-Rational(11,9),h)
def bmax(x,al): return x+x*(7*x+1)*(al-1)/(4*x**2+11*x+1)
def bmin_o(x,al): return x+4*x*(al-1)/(5*x+4)
