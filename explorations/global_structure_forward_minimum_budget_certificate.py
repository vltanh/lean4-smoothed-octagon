#!/usr/bin/env python3
"""Exact identities for the whole-forward minimum budget reduction.

The hand proof uses a global active minimum 4/3<a^2<20/11 and the actual
whole-period budget.  Its scalar seven-entry comparison is uniform for
every N>=7; it is not a catalogue or a claimed endpoint-preserving path.

Run: python explorations/global_structure_forward_minimum_budget_certificate.py
Dependency: SymPy.  No numerical samples, Lean, Lake, typechecking or CI.
"""

import sympy as S


def run():
    count = 0

    def check(condition, label):
        nonlocal count
        assert condition, label
        count += 1

    def zero(expr, label):
        check(S.simplify(S.expand_log(expr, force=True)) == 0, label)

    a,b,x,u,rho,d,y,v = S.symbols("a b x u rho d y v", positive=True)
    G = (3*a*b-4-(a*a+b*b)*S.log(a+b)
         +(a*a*S.log(a*a+4)+b*b*S.log(b*b+4))/2)
    zero(S.diff(G,a,b)-2*(1-a*b/(a+b)**2), "mixed derivative")
    zero(S.diff(G,a,b,b)-2*a*(b-a)/(a+b)**3, "mixed third derivative")
    Gbb = S.diff(G,b,b)
    diagonal = -S.log(4*rho)-S.Rational(3,2)+5*rho-2*rho*rho
    zero(Gbb.subs(a,b)-diagonal.subs(rho,b*b/(b*b+4)), "diagonal concavity expression")
    zero(S.diff(diagonal,rho)+(4*rho-1)*(rho-1)/rho, "diagonal monotonicity")
    zero(Gbb.subs(a,4/b)-(S.log(b*b/(b*b+4))+1-b*b/(b*b+4)),
         "strict-star concavity expression")
    star = 8-a*a*S.log(1+4/(a*a))/2-8*S.log(1+a*a/4)/(a*a)
    zero(G.subs(b,4/a)-star, "star edge value")

    g = (3*x-u-S.log((1+x)**2/(1+u))/2
         -x*x*S.log((1+x)**2/(x*x+u))/2)
    zero((G/a**2).subs({b:a*x})-g.subs(u,4/a**2), "dimensionless edge action")
    N = -4*u*u*x+3*u*u-2*u*x**3+11*u*x*x+6*x**4
    H = (1+x)**2/(x*x+u)
    zero((1+x)*S.diff(g,x,2)+S.diff(g,x)-N/(x*x+u)**2+(2*x+1)*S.log(H),
         "logarithmic-coordinate Hessian")
    polynomial = (2*y**4+4*y**3+(23-8*d)*y*y
                  +(12-2*d*d)*y+(24-15*d+2*d*d))
    zero((N-(2*x+1)*(1+2*x-u)*(x*x+u)).subs({u:3-d,x:1+y})-polynomial,
         "positive convexity polynomial")
    check(23-8*S.Rational(4,5)>0, "quadratic coefficient lower bound")
    check(12-2*S.Rational(4,5)**2>0, "linear coefficient lower bound")
    check(24-15*S.Rational(4,5)>0, "constant coefficient lower bound")

    U = (v-1)*(v*v+10*v+1)/(6*v*(v+1))
    zero(S.diff(U,v)-1/v-(v-1)**4/(6*v*v*(v+1)**2), "upper logarithm derivative")
    zero(U.subs(v,1), "upper logarithm base")
    lo7,hi7 = S.Rational(26457,10000),S.Rational(26458,10000)
    lo3 = S.Rational(1732,1000)
    check(lo7**2<7<hi7**2, "rational square-root-seven enclosure")
    check(lo3**2<3, "rational square-root-three lower bound")
    check(7/(11-2*hi7)==S.Rational(17500,14271), "H upper endpoint")
    lower = (3*lo7-6-U.subs(v,S.Rational(7,4))/2
             -S.Rational(13543,10000)*U.subs(v,S.Rational(17500,14271)))
    check(lower==S.Rational(7231126442093904703,5236815518550000000),
          "exact normalized lower cost")
    full_lower = 4*lo3*lower/3
    check(full_lower==S.Rational(3131077749426660736399,981902909728125000000),
          "exact physical lower cost")
    check(full_lower>S.Rational(313,100), "strict octagon-budget contradiction")
    zero(g.subs({u:3,x:S.sqrt(7)-1})
         -(3*S.sqrt(7)-6-S.log(S.Rational(7,4))/2
           -(4-S.sqrt(7))*S.log(7/(11-2*S.sqrt(7)))),
         "cutoff action identity")
    print(f"{count} exact identities/sign checks passed (SymPy {S.__version__}).")


if __name__ == "__main__":
    run()
