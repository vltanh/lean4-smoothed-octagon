import sympy as sp
U=sp.symbols('U')
def Lp(N,M): return 2*(N-M)/(N+M)+(N-M)**3/(6*N*M*(N+M))
xs=(5*U-8)/3
gbar_xs=3*xs-U-sp.Rational(1,2)*Lp(25*(U-1)**2,9*(1+U))-xs**2/2*Lp(25*(U-1)**2,(5*U-8)**2+9*U)
gbar_1=3-U-Lp(4,1+U)
D=2*gbar_xs+5*gbar_1-sp.Rational(2501,1384)*U
num,den=sp.fraction(sp.factor(sp.together(D)))
num=sp.expand(num)
# express num = sum b_k (U-11/5)^k (3-U)^(11-k)
x,y=sp.symbols('x y')
l,r=sp.Rational(11,5),sp.Integer(3)
s=sp.symbols('s')
q=sp.Poly(sp.expand(num.subs(U,l+(r-l)*s)),s); n=11
a=[q.coeff_monomial(s**i) for i in range(n+1)]
bs=[sum(sp.binomial(k,i)/sp.binomial(n,i)*a[i] for i in range(k+1)) for k in range(n+1)]
# num(U) = sum_k bs_k C(n,k) s^k (1-s)^(n-k), s=(U-l)/(r-l) => = sum_k bs_k C(n,k) (U-l)^k (r-U)^(n-k)/(r-l)^n
coef=[bs[k]*sp.binomial(n,k)/(r-l)**n for k in range(n+1)]
chk=sp.expand(sum(coef[k]*(U-l)**k*(r-U)**(n-k) for k in range(n+1))-num)
print('identity',chk==0)
print('num=',num)
print('coef=',coef)
