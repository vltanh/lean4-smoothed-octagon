import sympy as sp
U,t=sp.symbols('U t')
def Lp(N,M): return 2*(N-M)/(N+M)+(N-M)**3/(6*N*M*(N+M))
xs=(5*U-8)/3
gbar_xs=3*xs-U-sp.Rational(1,2)*Lp(25*(U-1)**2,9*(1+U))-xs**2/2*Lp(25*(U-1)**2,(5*U-8)**2+9*U)
gbar_1=3-U-Lp(4,1+U)
D=2*gbar_xs+5*gbar_1-sp.Rational(2501,1384)*U
num,den=sp.fraction(sp.factor(sp.together(D)))
print('den',sp.factor(den))
P=sp.Poly(sp.expand(num),U)
print('deg',P.degree())
# Bernstein on [11/5,3]
l,r=sp.Rational(11,5),3
s=sp.symbols('s')
q=sp.Poly(sp.expand(num.subs(U,l+(r-l)*s)),s)
n=q.degree()
a=[q.coeff_monomial(s**i) for i in range(n+1)]
bs=[sum(sp.binomial(k,i)/sp.binomial(n,i)*a[i] for i in range(k+1)) for k in range(n+1)]
print([float(x) for x in bs])
# t-substitution check
c=sp.Poly(sp.expand(sp.simplify((1+t)**11*num.subs(U,(11+15*t)/(5+5*t)))),t)
print([x for x in c.all_coeffs()[::-1]][:3])
