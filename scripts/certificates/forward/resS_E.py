import sympy as sp, pickle
a,t=sp.symbols('a t',real=True)
LI,Lc=sp.symbols('LI Lc')
A0,A1,Dd=pickle.load(open('A01.pkl','rb'))
z=(1+a)/(1-a)
Hc=(2*(1-a**2)-t*(5+3*a+2*a**2))/(3*(1-a))
tc=Hc/(1+Hc); tt=t/(1+t)
tau=sp.Symbol('tau')
g=Dd*tau/2-tau**2/(3*(2-tau))
psi=A0*(1/tau-1)+A1+z*g
dpsi=sp.diff(psi,tau)
E3=psi.subs(tau,tc)
E4=E3+dpsi.subs(tau,tc)*(tt-tc)
res={}
for name,E in [('E3',E3),('E4',E4)]:
    E=sp.expand(E)
    cI=sp.factor(sp.together(E.coeff(LI)))
    cc=sp.factor(sp.together(E.coeff(Lc)))
    R=sp.factor(sp.together(E.subs({LI:0,Lc:0})))
    res[name]=(R,cI,cc)
    print(name,'cI=',cI)
    print(name,'cc=',cc)
pickle.dump(res,open('E34.pkl','wb'))
