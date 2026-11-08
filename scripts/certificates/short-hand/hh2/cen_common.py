"""Central face (S2, hs2_central_sign): polynomials and Lean string helpers."""
import re
import sympy as sp
from fractions import Fraction as Fr
from bern import from_sympy
S,K,D,B,a,u=sp.symbols('S K D B a u')
x,t=sp.symbols('x t')
LBAR=sp.Rational(-296,1029)
def face_exprs():
    W=(S**2*(S**2-S+1)+D**2*u-D*(S**3*(u-1)+3*S-1))/K**2
    EL=(2*D*u-(S**3*(u-1)+3*S-1))/K
    q=a**2/K; rA=a/B; k=q/rA
    cc=(u-1)/rA+rA+1-q-EL
    tt=4*(2*k)/3-1
    LB=LBAR+tt-tt**2/2+tt**3/3
    G2=(W-1)*2+sp.Rational(1,2)+cc+LB+(2-7*2*k/4)*(W-sp.Rational(3,4))
    A=(1-7*k/4)*(W-sp.Rational(3,4))
    return G2,A
def stage1():
    G2,A=face_exprs()
    out={}
    for nm,F in [('G',G2),('A',A)]:
        Pi=sp.expand(sp.cancel(F*K**3*a*B))
        Pp=sp.Poly(Pi,u)
        out[nm]=(Pp.coeff_monomial(1),Pp.coeff_monomial(u))
    return out
bx=x+((24*x+51)/sp.Integer(128)-t)*(a-1)
SUBS={S:1+x,K:x*(x+2)+a**2,B:a+bx,D:a**2+2*a*bx+1+2*x-2*bx*x}
Ud=9600*(1+x)**2*(bx-1); Un=7200*(1+x)**2*(bx-1)+680*(x-1)**3+3*(1+x)**2*(bx-x)
def polys():
    st=stage1()
    NG=sp.expand(18522*(st['G'][0].subs(SUBS)*Ud+st['G'][1].subs(SUBS)*Un))
    NA=sp.expand(18522*(st['A'][0].subs(SUBS)*Ud+st['A'][1].subs(SUBS)*Un))
    ND=sp.expand(18522*((K**3*a*B).subs(SUBS))*Ud)
    return st,NG,NA,ND
def lean(e):
    s=sp.sstr(e).replace('**','^')
    s=re.sub(r'\^(\d+)', r' ^ (\1 : ℕ)', s)
    return s
LINES=[(Fr(0),Fr(0)),(Fr(0),Fr(97,500)),(Fr(-347,312500),Fr(1179,2500)),
       (Fr(9,196)+Fr(1,50000)-Fr(12197,10000)*Fr(9,196),Fr(12197,10000)),(Fr(-9,392)+Fr(1,50000),Fr(3,2))]
BPS=[Fr(0),Fr(1,250),Fr(3,250),Fr(9,196)]

_CACHE = {}
def polys_cached():
    if 'p' not in _CACHE:
        _CACHE['p'] = polys()
    return _CACHE['p']
