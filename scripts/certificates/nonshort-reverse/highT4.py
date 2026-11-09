from nsrN import *
from common import vbar, Lp, Fl, W, X
import numpy as np
fN = lambdify((t,x,k,q,v,L), nsrN(t,x,k,q,v,L))
fvb = lambdify((t,x), vbar); fFl = lambdify((t,x,q), Fl); fLp = lambdify(q, Lp)
for (tt,xx) in [(0.4,0.324),(0.4,0.3)]:
  for kk in [20/3*tt**2, 7*tt**2]:
    for yy in [0.1,0.2,0.34,0.5]:
        qq=1+yy
        vb=fvb(tt,xx); fl=fFl(tt,xx,qq)
        Nb=fN(tt,xx,kk,qq,vb,fLp(qq))
        g = 1-(1-tt)*(tt+xx)/(1+xx)**2
        vex = 1+(1-tt)**2/(1+xx)-(1-tt)*np.log1p(xx)/xx
        eta=(tt+xx)/(1+xx); F = 1+eta**2*qq-eta*qq*np.log(qq)/(qq-1)
        Nex=fN(tt,xx,kk,qq,vex,np.log(qq))
        print(tt,xx,round(kk,4),yy,'vb-Fl',round(vb-fl,5),'Nbar',round(Nb,5),'P/6..',round(Nb-yy*(vb-fl),5),'vex',round(vex,5),'g',round(g,5),'F',round(F,5),'Nex',round(Nex,5))
