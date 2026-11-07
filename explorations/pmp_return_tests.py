#!/usr/bin/env python3
"""Independent canonical-adjoint residual checks for the explicit arc flow.
Run: python explorations/pmp_return_tests.py
Requires mpmath and pmp_return_probe.py. Numerical tests, not certificates.
"""
import mpmath as mp
from pmp_return_probe import regular_phase, VertexArc, settings, phi, fields, trace, norm


def main():
    mp.mp.dps=70
    ph,_=regular_phase(1)
    active=0
    for j in range(3):
        arc=VertexArc(ph,active,settings().zero)
        r=mp.mpf(11)/10;t=arc.at(r)
        def output(z):
            v=arc.at(z)
            return mp.matrix(list(v.g)+list(v.xy)+list(v.lam)+list(v.p)+[v.cost])
        num=mp.diff(output,r)*r/mp.sqrt(arc.W)
        X=phi(t.xy);gd=t.g*X;ld=t.lam*X-X*t.lam
        def H(x,y):
            xy=mp.matrix([x,y]);return trace(t.lam*phi(xy))+mp.fdot(t.p,fields(active,xy))-mp.mpf(3)/2*(1+x*x+y*y)/y
        pd=mp.matrix([-mp.diff(lambda x:H(x,t.xy[1]),t.xy[0]),-mp.diff(lambda y:H(t.xy[0],y),t.xy[1])])
        x,y=t.xy;rhs=mp.matrix(list(gd)+list(fields(active,t.xy))+list(ld)+list(pd)+[mp.mpf(3)/2*(1+x*x+y*y)/y])
        error=norm(num-rhs)
        assert error<mp.mpf('1e-60'),(active,error)
        print('PASS canonical state/frame/adjoint/cost RHS for vertex',active,'residual',mp.nstr(error,6))
        from pmp_return_probe import first_switch
        rs,nxt,status=first_switch(arc,settings());assert status=='SWITCH'
        ph=arc.at(rs);active=nxt

if __name__=='__main__':main()
