import sympy as sp
U=sp.symbols('U')
K=1+U
e0=1-K/8+1/K
c=sp.Rational(1,35);b=sp.Rational(1,64)
target=sp.Rational(23,125)
def bernstein(p,l,r):
    # p polynomial in U; return Bernstein coeffs on [l,r]
    s=sp.symbols('s')
    q=sp.Poly(sp.expand(p.subs(U,l+(r-l)*s)),s)
    n=q.degree()
    a=[q.coeff_monomial(s**i) for i in range(n+1)]
    # bernstein coeff b_k = sum_{i<=k} C(k,i)/C(n,i) a_i
    bs=[sum(sp.binomial(k,i)/sp.binomial(n,i)*a[i] for i in range(k+1)) for k in range(n+1)]
    return n,bs
def check(name,expr,l,r):
    # expr: rational function > target needed; numerator after clearing positive denominators
    num,den=sp.fraction(sp.together(expr-target))
    num=sp.expand(num);den=sp.expand(den)
    # ensure den>0 on interval: check sign at midpoint
    mid=(l+r)/2
    sgn=sp.sign(den.subs(U,mid))
    num=num*sgn
    n,bs=bernstein(num,l,r)
    print(name,'deg',n,'min bern',float(min(bs)),'all pos',all(x>0 for x in bs), 'den sign',sgn)
    return num,bs
sA1=(5*U+1)/6
check('A1',K**2/(16*U**2)*(sp.Rational(327,140)-(e0+c*sA1)**2),sp.Rational(11,5),sp.Rational(13,5))
check('A2',K**2/(16*U**2)*(sp.Rational(327,140)-(e0+c*sp.Rational(7,3))**2),sp.Rational(13,5),3)
sig=2+5*(U-1)/3
QB0=4*(sp.Rational(3,4)+c-b)*(sp.Rational(3,4)+b)
check('B1',K**2/(16*U**2)*(QB0-(e0+(c-b)*sig+(2*b-c)*sp.Rational(7,3))**2),sp.Rational(11,5),sp.Rational(13,5))
check('B2',K**2/(16*U**2)*(QB0-(e0+c*sp.Rational(7,3))**2),sp.Rational(13,5),3)
