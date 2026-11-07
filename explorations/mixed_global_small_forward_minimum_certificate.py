"""Exact interfaces for MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md.

The hand proof includes the genuine PMP gaps and scalar comparisons.
This supplementary checker verifies the displayed identities.
The full hard-face polynomial identity has its own fixed-table checker.
No Lean, Lake, typechecking, CI, or floating-point sampling.
"""
import sympy as sp
def reduced_model():
    """Rank-free two-equation centre-frame reduction and needle floors."""
    import sympy as sy
    a,b,c,h,k=sy.symbols('a b c h k', positive=True)
    Lh,Lq,Lk=sy.symbols('Lh Lq Lk', real=True)
    K=a*a+4;Kb=b*b+4;Kc=c*c+4;sm=a+b;sp=a+c;q=sm*sp/K
    A=b+a+c-a*a*(1/sm+1/sp)+a**3/K-a*Lq
    B=h*Kb/sm+a-b*b*(sm/(h*Kb)+1/sm)+b**3/Kb-b*Lh
    C=a+k*Kc/sp-c*c*(1/sp+sp/(k*Kc))+c**3/Kc-c*Lk
    M11=sm**2*(4-a*b)*(h-1)/(a*Kb)
    M12=K**2*(a*(q-1)+(h-1)*(sm*q-a))/(a*sm*Kb)
    M22=sp**2*(4-a*c)*(k-1)/(a*Kc)
    M21=K**2*(a*(q-1)+(k-1)*(sp*q-a))/(a*sp*Kc)
    RL=K*(h*sm-b)*A/(a*Kb)-B
    RR=K*(k*sp-c)*A/(a*Kc)-C
    Fh=1+(b/sm)**2*h-(b/sm)*h*Lh/(h-1)
    Fk=1+(c/sp)**2*k-(c/sp)*k*Lk/(k-1)
    DL=RL-M11*Fh-M12*Fk
    DR=RR-M21*Fh-M22*Fk
    return locals()




D=reduced_model()
a,b,c,h,k=(D[n] for n in ('a','b','c','h','k'))
K,Kb,Kc,s,t,q=(D[n] for n in ('K','Kb','Kc','sm','sp','q'))
u,v,E=sp.symbols('u v E',real=True)
checks=0

def check(name,lhs,rhs=0):
 global checks
 if sp.factor(lhs-rhs)!=0:
  raise AssertionError(name)
 checks+=1

R=sp.Matrix([[1,-1],[1,0]])
T=lambda z:sp.diag(z,1/z)
Uc=sp.Matrix([[K*E/16,-s*s*u/8],[K*K*v/(8*s*s),-K*E/16]])
P=T(h)*R
Ub=P*Uc*P.inv()
Pnext=T(q)*R
Un=Pnext.inv()*Uc*Pnext
Wb=2*sp.Matrix([[-b/Kb,h*h/s],[-s/(h*Kb),b/Kb]])
Wa=2*sp.Matrix([[-a/K,q*q/t],[-1/s,a/K]])
Wc=2*sp.Matrix([[-c/Kc,k*t/Kc],[-1/t,c/Kc]])
ha=s*u+t*v-a*E-D['A']
hb=4*sp.trace(Ub*Wb)-D['B']
hc=4*sp.trace(Un*Wc)-D['C']
check('central trace stationarity',4*sp.trace(Uc*Wa),s*u+t*v-a*E)
check('left positive row',hb+D['M11']*u+D['M12']*v-D['RL'],K*(h*s-b)*ha/(a*Kb))
check('right positive row',hc+D['M21']*u+D['M22']*v-D['RR'],K*(k*t-c)*ha/(a*Kc))
s0=h*Kb/s;p=s0-b
LM=2*sp.Matrix([[b*s0,-s0*s0],[Kb,-b*s0]])
GL=sp.trace(Ub*LM)+p*s0+Kb
check('left actual needle floor',GL,Kb*Kb*(h-1)*(u-D['Fh'])/4-h*Kb*Kb*hb/(4*s))
s1=k*Kc/t;d=s1-c
Uend=T(k).inv()*Un*T(k)
RM=2*sp.Matrix([[c*s1,-Kc],[s1*s1,-c*s1]])
GR=sp.trace(Uend*RM)+d*s1+Kc
check('right actual needle floor',GR,Kc*Kc*(k-1)*(v-D['Fk'])/4-k*Kc*Kc*hc/(4*t))
alpha=K*(h*s-b)/(a*Kb);beta=K*K*h/(s*Kb)
check('affine opposite coefficient',D['M12'],alpha*t-beta)
U=1-a/t+a*a/(t*t)
check('cost primitive derivative',sp.diff(D['A'].subs(D['Lq'],sp.log(q)),c),U)
EL=D['RL']-D['M11']*D['Fh']-D['M12']*U
check('opposite margin derivative',sp.diff(EL,c).subs(sp.diff(D['Lq'],c),0)+alpha*(-a/t),-D['M12']*a*(c-a)/t**3)
# Lq is an independent symbol in the algebra model; replace it for calculus.
EL=EL.subs({D['Lq']:sp.log(q),D['Lh']:sp.log(h)})
check('full opposite margin derivative',sp.diff(EL,c),-D['M12']*a*(c-a)/t**3)
Ppoly=(4-a*b)*h*h*(2*b*h-a-b)+a*Kb*h-2*a*b*s
check('own factor second derivative',sp.diff(EL,h,2),-b*Ppoly/(a*Kb*h**3))
check('increasing numerator derivative',sp.diff(Ppoly,h),2*(4-a*b)*h*(3*b*h-a-b)+a*Kb)
check('numerator at one',Ppoly.subs(h,1),b*(4-a*a-2*a*b))
check('q1 numerator nonnegative decomposition',Ppoly.subs(h,1)-b*(b*b-a*a),b*(K-s*s))
q1=sp.factor(EL.subs(c,K/s-a))
check('q1 residual at one',sp.limit(q1,h,1))
check('q1 derivative at one',sp.limit(sp.diff(q1,h),h,1))
x,z=sp.symbols('x z',positive=True)
F=1+x*x*z-x*z*sp.log(z)/(z-1)
check('floor factor derivative',sp.diff(F,z),x*x-x*((z-1)-sp.log(z))/(z-1)**2)
check('floor ratio derivative',sp.diff(F,x),z*(2*x-sp.log(z)/(z-1)))
check('floor at one',sp.limit(F,z,1),1-x+x*x)
H=t*t/Kc
check('minimum factor increasing',sp.diff(H,c),2*t*(4-a*c)/(Kc*Kc))
check('q1 opposite minimum factor',sp.factor((t*t-Kc).subs(c,K/s-a)),K*(a-b)/s)


# The easy symmetric face and the full hard-face normalization.
qs=s*s/K;rr=a/s
Fq=rr*(qs-1)+(1-rr)*(1-1/qs)-sp.log(qs)
sym=EL.subs(c,b)
check('easy symmetric initial value',sp.limit(sym,h,1),a*K*Fq/Kb)
Gq=Fq+(1-rr)*(qs-1)*(rr*qs-(1-rr))/qs
check('easy symmetric initial slope',sp.limit(sp.diff(sym,h),h,1),s*K*Gq/Kb)
r0,q0=sp.symbols('r0 q0',positive=True)
f0=r0*(q0-1)+(1-r0)*(1-1/q0)-sp.log(q0)
check('easy symmetric logarithmic derivative',sp.diff(f0,q0),(q0-1)*(r0*q0-(1-r0))/q0**2)
Vfun=sp.Function('V')(c)
strong=D['RL'].subs(D['Lq'],sp.log(q))-D['M11']*D['Fh']-D['M12']*Vfun
check('minimum-aware opposite derivative',sp.diff(strong,c),alpha*(U-Vfun)-D['M12']*sp.diff(Vfun,c))

scale,z0,LH=sp.symbols('scale z0 LH',positive=True)
H0=s*s/Kb
V0=1+(b/s)**2*H0-(b/s)*H0*LH/(H0-1)
strongsym=D['RL'].subs(c,b)-D['M11']*D['Fh']-D['M12'].subs(c,b)*V0
physical=sp.cancel((strongsym/s).subs(b,a*z0)).subs(a*a,4/scale)
t0=1/(1+z0);x0=z0/(1+z0);q0=(1+z0)**2/(1+scale);H0=(1+z0)**2/(scale+z0*z0)
AA=2-t0-2*t0*t0+t0**3*q0-t0*D['Lq']
BB=h/H0+t0-x0*x0*H0/h-x0*x0+x0**3*H0-x0*D['Lh']
Fh=1+x0*x0*h-x0*h*D['Lh']/(h-1)
FH=1+x0*x0*H0-x0*H0*LH/(H0-1)
normalized=H0*(h-x0)*AA/(t0*q0)-BB
normalized-=H0*(1-t0*q0)*(h-1)*Fh/(t0*q0)
normalized-=H0*(t0*(q0-1)+(h-1)*(q0-t0))*FH/(t0*q0*q0)
diff=sp.cancel(physical-normalized)
for lg in (D['Lq'],D['Lh'],LH):
 check('hard face log normalization '+str(lg),sp.diff(diff,lg))
check('hard face rational normalization',diff.subs({D['Lq']:0,D['Lh']:0,LH:0}))
print(f'All {checks} exact interface and boundary identities passed.')
