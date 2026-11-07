"""Supplement exact identities in GLOBAL_SPECTRAL_COST_CASIMIR.md.

Domain is stated in the hand proof: kappa>0, p>=1, p^-1<=r<=p,
z>=1, m_b>0, 2*kappa*r<=3. SymPy checks identities only; ordering,
PMP, continuous angle and global endpoints are hand obligations.
No Lean, Lake, typechecking, CI, sampling, or word enumeration.
"""
import sympy as s
p, r, z, mb, k = s.symbols('p r z mb k', positive=True)
checks = {
    'spectral factorization': p+1/p-r-1/r-(p-r)*(p*r-1)/(p*r),
    'whole-period improvement': (k+s.Rational(3,2))/3-4*k/(2*k+3)
        -(2*k-3)**2/(6*(2*k+3)),
    'exact pointwise defect': 3*mb-(k+s.Rational(3,2))*mb*(1+r)/(z+1)
        -((r+1)/(2*r)*(3*mb-2*k*r*mb)
          +s.Rational(3,2)*mb*(2*z-r-1/r))/(z+1),
    'completion coefficient improvement': k+s.Rational(3,2)-12*k/(2*k+3)
        -(2*k-3)**2/(2*(2*k+3)),
    'ratio derivative': s.diff(r/(r+1),r)-1/(r+1)**2,
}
for name, expression in checks.items():
    assert s.factor(expression) == 0, name
    print('PASS', name)
print('All exact identities passed. No M2 or F exclusion is asserted.')
