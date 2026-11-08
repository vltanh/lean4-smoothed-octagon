#!/usr/bin/env python3
"""Finite symbolic checks for docs/VERTEX_EVENT_ESCAPE.md.

Run: python explorations/vertex_event_certificate.py
Requires SymPy. Exact rational/symbolic algebra, no samples or solver.
The inequalities, PMP interface and global consequence are hand arguments
in the note; this checker does not constitute independent peer review.
"""
from fractions import Fraction
import platform
import sympy as s


def main():
    checks=[]
    def zero(name,value):
        assert s.simplify(value)==0,name
        checks.append(name)
    u,c,W,mu,p0,n0,k0=s.symbols('u c W mu p0 n0 k0',positive=True)
    q=s.sqrt(3)/3;x=q-W/u;w=u*u/W;S=u-c
    E=c*c*p0+W*(mu-q*q)*(u-c)+2*q*W*W*s.log(u/c)+W**3*(1/u-1/c)
    pw=E/u**2
    zero('edge numerator derivative',s.diff(E,u)-W*(mu-x*x))
    zero('state covector equation',s.diff(pw,u)*u*u/W+2*pw/(q-x)-(mu-x*x))
    Q=1+(x*x-mu)*w+(W+1)*u**3*pw/W**2
    n=n0-k0*S+(1+mu)*S*S
    B=n-Q
    zero('third gap second derivative',s.diff(B,u,2)-(s.Rational(8,3)-2*q*(W+1)/u))
    C=s.Rational(3,2)*((1+W)*W*(1/c-1/u)+s.Rational(4,3)*(u-c)-2*q*W*s.log(u/c))
    zero('physical cost derivative',s.diff(C,u)-s.Rational(3,2)*(W/u**2+1+x*x))
    r,R=s.symbols('r R',positive=True)
    psi=2-3/R+1/R**2-s.log(R)
    zero('escape shape derivative',s.diff(psi,R)+(R-1)*(R-2)/R**3)
    zero('exit shape identity',(R-1)**2-R*(R*s.log(R)-R+1)-R**2*psi)
    f=s.Rational(5,4);L=s.symbols('L',real=True);kap=s.Rational(448,803)
    a=5*q/61;w0=s.Rational(11163,22484);W0=s.Rational(112,803);c0=s.simplify(W0/(q-a))
    zero('M1 state W',(q-a)**2*w0-W0)
    zero('M1 exit ratio',(1+W0)/(2*q*c0)-s.Rational(15,4))
    P01=(711040*L-20548)*r*r+(55685-352800*L)*r-98000-294000*r*s.log(r)
    P02=-50176*r*r+(894720*L-247172)*r+387365-1289200*L+136640*r*s.log(r)
    at=lambda e:s.factor(e.subs(r,f).subs(s.log(f),L))
    zero('M1 edge tie',at(P02))
    zero('M1 third gap value',at(P01)-60500*(5*L-1))
    zero('M1 edge derivative',at(s.diff(P02,r))-(1031360*L-235972))
    zero('M1 mu-a^2',kap*at(s.diff(P02,r))/(200704*f*w0)-11*(23440*L-5363)/55815)
    zero('M1 B0',-4*kap*w0*at(P01/392000)/3+14884*(5*L-1)/261121)
    zero('M1 B1',-4*kap*w0/(3*c0)*at(2*P01/392000-r*s.diff(P01/392000,r))
         -61*s.sqrt(3)*(560*L-167)/20440)
    z=Fraction(11,21)
    lower=2*sum(z**(2*j+1)/Fraction(2*j+1) for j in range(4))
    target=Fraction(297,256)
    assert lower-target==Fraction(34560224369,16137753327360)>0
    assert 23440*Fraction(9,40)-5363==-89
    assert 560*Fraction(9,40)-167==-41
    assert 5*Fraction(2,9)-1==Fraction(1,9)>0
    assert Fraction(15,4)/(Fraction(9,8))==Fraction(10,3)>Fraction(16,5)
    print('Python',platform.python_version(),'SymPy',s.__version__)
    for name in checks:print('PASS',name)
    print('PASS 5 rational sign/threshold checks')
    print('Total:',len(checks),'symbolic identities and 5 exact rational checks.')

if __name__=='__main__':main()
