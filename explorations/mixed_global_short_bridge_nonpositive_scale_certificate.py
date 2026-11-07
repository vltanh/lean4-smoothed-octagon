"""Exact identities for a conditional nonpositive-bridge scale sign.

No endpoint value or M2 closure claim; see the companion hand note.
"""
import sympy as s

r,t,rho,u,w,EL,lam,L,sigma,tau,alpha,F=s.symbols(
    'r t rho u w EL lam L sigma tau alpha F', positive=True)
U=lambda z:1-z+z*z
checks=0
def check(name,a,b=0):
    global checks
    assert s.simplify(a-b)==0,name
    checks+=1

E=1+r+t-rho+s.log(rho/(r*t))-(1-u)/r-(1-w)/t
upper=-1+2*r+2*t-rho+s.log(rho/(r*t))
check('upper norm corner',E.subs({u:U(r),w:U(t)}),upper)
check('strict ratio defect',4*r*t-(-1+2*r+2*t),(1-2*r)*(1-2*t))
z=s.symbols('z',positive=True)
check('product derivative',s.diff(4*z-rho+s.log(rho/z),z),4-1/z)
check('product lower endpoint',(4*z-rho+s.log(rho/z)).subs(z,rho),3*rho)
check('outer scale inequality',1-4*alpha*alpha*lam*rho,
      lam*(1-rho-3*alpha*alpha*rho)
      +(1-lam*(1+rho*(alpha*alpha-1))))
d=-lam*rho*L
check('outer E transport',d*u-F,-lam*rho*L*u-F)
base=(1+lam)*(1-rho)/rho-2*tau*sigma*w
deriv=(1+lam+lam*rho*L*tau)*(1/rho-1+L*u)-(sigma-tau*L)*F-2*tau*sigma*w
check('first coefficient branch',deriv-base,
      (1+lam)*L*u+lam*tau*L*(1-rho+rho*L*u)-(sigma-tau*L)*F)
bound=deriv.subs(F,-lam*rho*(L*u+3*alpha*alpha))
check('second coefficient branch',bound,
      base+(1+lam)*L*u+lam*tau*L*(1-rho-3*alpha*alpha*rho)
      +lam*sigma*rho*(L*u+3*alpha*alpha))
check('positive base numerator',(1+lam)*(1-rho)-lam,
      1-rho*(1+lam))
H,v=s.symbols('H v',real=True)
lr=1/(1+rho*sigma)
Fr=lr*(H+s.log(rho)-rho+rho*L*u)
dr=-lr*rho*L
wr=lr*lr*v-dr*Fr
ELr=dr*u-Fr
P=1/rho+sigma
outer_h=s.log(P/(sigma+1))-1+(sigma+1)/P
envelope=tau*s.diff(wr,rho)-s.diff(outer_h,rho)-s.diff(ELr,rho)
check('actual scale envelope',envelope,
      lr*((1+lr+lr*rho*L*tau)*(1/rho-1+L*u)
          -(sigma-tau*L)*Fr-2*tau*sigma*wr))
f=lambda x:x-1/x-s.log(x)
root_E=w/t-f(1/t)+u/r-f(1/r)-(s.log(1/rho)-1+rho)
check('outer root is the reverse equation',s.expand_log(root_E-E,force=True))
check('truncated derivative floor',s.diff(f(tau),tau)-s.Rational(3,4),
      (tau-2)**2/(4*tau*tau))
legendre=s.log(tau)-1+2/tau
check('continuous maximum slope',s.diff(legendre,tau),
      tau*s.diff(f(tau),tau,2))
print(f'All {checks} exact conditional nonpositive-scale identities passed.')
