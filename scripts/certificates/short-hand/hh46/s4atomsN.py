"""Structured numerators of the S4 surrogates in high-level atoms."""
import sympy as sp
R_=sp.Rational
X,AL,A,Sg,S,U,D,Pn,nu,du,k,L0=sp.symbols('X AL A Sg S U D Pn nu du k L0')
c0=R_(1829,10000)
def NF(which):
    G=(4*nu*du*S**2*U-Pn**2)/(16*X**2*(X+2)**2*du**2)
    wc=(S**2*U*du+D**2*nu-D*Pn)/(Sg**2*du)
    EL=(2*D*nu-Pn)/(Sg*du)
    rest=(nu-du)*A/(AL*du)+AL/A-AL**2/Sg-EL
    h=(2*k*AL*A-Sg)/Sg
    Ls=L0+h-h**2/2+h**3/3
    if which=='Phi':
        F=G-(2*wc-R_(1,2)+rest+Ls)/7
    else:
        F=G-((Sg/(AL*A))*(wc-R_(3,4))+1+rest+Ls)/7
    M=16*42*X**2*(X+2)**2*du**2*Sg**3*AL*A
    N=sp.expand(sp.cancel(M*(F-c0)))
    return N,M
if __name__=='__main__':
    for w in ('Phi','Psi'):
        N,M=NF(w)
        P=sp.Poly(N,X,AL,A,Sg,S,U,D,Pn,nu,du,k,L0)
        print(w,len(P.terms()), sp.denom(sp.together(N)))
