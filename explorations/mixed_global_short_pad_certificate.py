#!/usr/bin/env python3
"""Exact algebra for one asymmetric normal-PMP short-pad obstruction.

See docs/MIXED_GLOBAL_SHORT_PAD_OBSTRUCTION.md. All bounds use finite
rational logarithm enclosures. No floating-point sampling or ODE steps.
This is not a closure, geometry, or local/global minimality certificate.
"""
import sympy as s

L, M, N1, N2 = s.symbols('L M N1 N2')
q = s.sqrt(3)/3
checks = 0


def equal(lhs, rhs=0, label='identity'):
    global checks
    value = s.simplify(s.factor(lhs-rhs))
    if value != 0:
        raise AssertionError(f'{label}: {value}')
    checks += 1


def assert_positive(value, label='positive rational'):
    global checks
    if not bool(value > 0):
        raise AssertionError(f'{label}: {value}')
    checks += 1


def log_enclosure(argument, terms=16):
    """For positive rational argument >1, return strict rational bounds."""
    z = (argument-1)/(argument+1)
    partial = 2*sum(z**(2*j+1)/s.Rational(2*j+1)
                    for j in range(terms))
    tail = 2*z**(2*terms+1)/((2*terms+1)*(1-z*z))
    return partial,partial+tail


# Recorded decimal-rational bounds are convenient to reproduce by hand.
log_inputs = {
    L:(s.Rational(7,5),336472236621212930),
    M:(s.Rational(6,5),182321556793954626),
    N1:(s.Rational(251,250),3992021269537452),
    N2:(s.Rational(201,200),4987541511039073),
}
enclosures = {}
for symbol,(argument,numerator) in log_inputs.items():
    lower,upper = log_enclosure(argument)
    if numerator is None:
        numerator = s.floor(lower*10**18)
    lo,hi = s.Rational(numerator,10**18),s.Rational(numerator+1,10**18)
    assert_positive(lower-lo, f'{symbol} lower log bound')
    assert_positive(hi-upper, f'{symbol} upper log bound')
    enclosures[symbol] = (lo,hi)
    print(f'{symbol}: {numerator}/10^18 < log({argument}) < {numerator+1}/10^18')


def interval(expression):
    """Natural exact interval for a polynomial in the positive log bounds."""
    poly = s.Poly(s.expand(expression),L,M,N1,N2)
    lo=hi=s.Rational(0)
    for powers,coefficient in poly.terms():
        ml=mh=s.Rational(1)
        for symbol,power in zip((L,M,N1,N2),powers):
            ml *= enclosures[symbol][0]**power
            mh *= enclosures[symbol][1]**power
        if coefficient >= 0:
            lo += coefficient*ml
            hi += coefficient*mh
        else:
            lo += coefficient*mh
            hi += coefficient*ml
    return lo,hi


def bounded(expression, lower, upper, label):
    lo,hi=interval(expression)
    assert_positive(lo-lower, f'{label}: lower endpoint')
    assert_positive(upper-hi, f'{label}: upper endpoint')
    print(f'  {label}: ({lower}, {upper})')


v=s.Rational(19,10)
h=s.Rational(7,5)
inner=s.Rational(2,5)
za,zb=-s.Rational(1,2),s.Rational(4,7)
m0=s.Rational(12,5)-7*L
mu=m0/3
P=s.Rational(171,490)
Ta,Tb=-s.Rational(323,490),s.Rational(38,49)
Za=P*(s.Rational(7,3)*L-s.Rational(11,30)-2*M)
Zb=P*(s.Rational(16,21)-s.Rational(8,3)*L)
wa,wb=s.Rational(342,245),v
Qa=1+s.Rational(114,245)*(s.Rational(1,4)-m0)-s.Rational(547,735)*Za
Qb=1+s.Rational(19,30)*(s.Rational(16,49)-m0)+s.Rational(547,630)*Zb
K0=-(209265*L-98460*M-52562)/90650
n0=(139771961*L+11224440*M-11725086)/39976650

# Inner weighted moment and the two outer rational/log integrals.
equal(inner-2*L+(1-m0)*(1-1/h),label='inner zero moment')
equal(P,v*((1-inner)/(1+inner))**2,label='outer state invariant')
equal(Ta,-v*inner/(1+inner)+P*(1/(1-inner)-1/(1+za)),
      'left accumulated state')
equal(Tb,v*inner/(1+inner)+P*(1/(1-zb)-1/(1-inner)),
      'right accumulated state')
equal(Za,P*((m0-1)*(1/(1-inner)-1/(1+za))-2*M
             -((1+za)-(1-inner))), 'left moment integral')
equal(Zb,-P*((m0-1)*(1/(1-inner)-1/(1-zb))-2*L
              -((1-zb)-(1-inner))), 'right moment integral')
equal(K0,(1+mu)*(Ta+Tb)-3*(Qb-Qa)/(Tb-Ta),'two-tie k0')
equal(n0,Qb+K0*Tb/3-(1+mu)*Tb**2/3,'two-tie n0')
equal(n0-K0*Ta/3+(1+mu)*Ta*Ta/3,Qa,'left outer tie')
equal(n0-K0*Tb/3+(1+mu)*Tb*Tb/3,Qb,'right outer tie')


def qB_S(z,w,T,Z,sigma):
    rho=1+sigma*z
    return ((-K0+2*(1+mu)*T-2*z)/3
            -sigma*(z*z-m0)*(rho*w/9-1/(3*rho))
            -Z*(s.Rational(1,9)+1/(3*rho*rho*w)))


Da=(412041*L+31179*M-145313)/81585
Db=-(1735995*L+147690*M-611059)/407925
Bmid=-19*(985733*L-295380*M-238494)/19988325
equal(qB_S(za,wa,Ta,Za,1),Da,'left gap derivative')
equal(qB_S(zb,wb,Tb,Zb,-1),Db,'right gap derivative')
equal(n0-1+mu*v,Bmid,'middle gap')

# Bounds ensuring B<0 everywhere: outer arcs are concave and the two
# inner arcs convex, with the endpoint slopes and middle gap below.
bounded(mu,s.Rational(14,1000),s.Rational(15,1000),'core mu')
bounded(Da,-s.Rational(13,1000),-s.Rational(12,1000),'q B_S(left)')
bounded(Db,s.Rational(43,10**6),s.Rational(44,10**6),'q B_S(right)')
bounded(Bmid,-s.Rational(38,1000),-s.Rational(37,1000),'B(center)')
# Uniform outer-arc maxima and inner-arc minima of B_SS.
Wouter=P/3
Winn=v/3
leftmax=2*(1-s.Rational(1,3)/Wouter-za*(1+1/Wouter)/3)
rightmax=2*(1-s.Rational(1,3)/Wouter+zb*(1+1/Wouter)/3)
innermin=2*(1-s.Rational(1,3)/Winn-inner*(1+1/Winn)/3)
equal(leftmax,-s.Rational(91,171),'left concavity constant')
equal(rightmax,-s.Rational(10,133),'right concavity constant')
equal(innermin,s.Rational(74,285),'inner convexity constant')

# Physical negative-elliptic determinant and the necessary budget cap.
determinant=s.Rational(9,4)*((1+mu)*n0-K0*K0/12)
bounded(determinant,s.Rational(213,100),s.Rational(107,50),'physical determinant')

# Independent state and group-cotangent rotation at the right outer tie.
matK=lambda x:s.Matrix([[1,x],[0,1]])
R0=s.Matrix([[s.Rational(1,2),-s.sqrt(3)/2],
             [s.sqrt(3)/2,s.Rational(1,2)]])
b=zb*q
a=-15*q/547
X=s.sqrt(v)*s.Matrix([[b,-b*b-1/v],[1,-b]])
Xr=(R0.T*X*R0).applyfunc(s.factor)
W=s.Rational(236883,1824760)
cbar=s.Rational(1383363,3649520)
wplus=s.Rational(2692881,7299040)
exit_ratio=s.Rational(3769,843)
equal(Xr[0,0]/Xr[1,0],a,'rotated abscissa')
equal(Xr[1,0]**2,wplus,'rotated inverse square height')
equal(W,(q-a)**2*wplus,'outgoing W')
equal(q*cbar,W/(q-a),'outgoing c')
equal(exit_ratio,(1+W)/(2*q*q*cbar),'outgoing exit ratio')

k_b=q*(K0-2*(1+mu)*Tb)
Mb=s.Matrix([[k_b/2,-1-mu],[Qb,-k_b/2]])
Mr=(matK(-a)*R0.T*matK(b)*Mb*matK(-b)*R0*matK(a)).applyfunc(s.factor)
muplus=(1847098680*L+157142160*M-650041901)/498182985
delta=1064*(1735995*L+147690*M-611059)/498182985
B0=-299209*(7*L-2)/5882450
B1q=547*(4176250*L+1624590*M-2271733)/534925650
equal(muplus,-1-Mr[0,1],'outgoing mu')
equal(delta,muplus-a*a,'outgoing initial source')
equal(B0,Mr[1,0]-1+delta*wplus,'outgoing third gap')
equal(q*B1q,-2*Mr[0,0]-2*a-(W-1)*delta/(q-a),
      'outgoing gap derivative')
bounded(muplus,s.Rational(212,10**6),s.Rational(213,10**6),'outgoing mu')
bounded(delta,-s.Rational(39,10**6),-s.Rational(38,10**6),'outgoing mu-a^2')
bounded(B0,-s.Rational(19,1000),-s.Rational(18,1000),'outgoing B0')
bounded(B1q,-s.Rational(3,5),-s.Rational(1,2),'outgoing B1/q')
assert_positive(exit_ratio-s.Rational(16,5),'exit ratio beyond threshold')


def E_over_q(factor, logarithm):
    return (W*(muplus-s.Rational(1,3))*cbar*(factor-1)
            +2*W*W*logarithm+3*W**3/cbar*(1/factor-1))


r1,r2=s.Rational(251,250),s.Rational(201,200)
E1,E2=E_over_q(r1,N1),E_over_q(r2,N2)
bounded(E1,-s.Rational(5,10**10),-s.Rational(4,10**10),'E(251/250)/q')
bounded(E2,s.Rational(14,10**10),s.Rational(15,10**10),'E(201/200)/q')
x1_over_q=1-(1+ s.Rational(15,547))/r1
x2_over_q=1-(1+ s.Rational(15,547))/r2
assert_positive(-x2_over_q,'both event brackets before x=0')
bounded(muplus-x1_over_q*x1_over_q/3,
        s.Rational(3,10**5),s.Rational(4,10**5),'source at first bracket')

# Local cost only, not a complete-period endpoint assertion.
core_cost_over_sqrt3=((zb-za)+(1+mu)*(Tb-Ta)-(Zb-Za)/3)/2
pad_cost_over_q=(s.Rational(9,2)*(1+W)*W/cbar*(1-1/r2)
                +2*cbar*(r2-1)-3*W*N2)
bounded(core_cost_over_sqrt3,s.Rational(127,100),s.Rational(9,7),
        'core cost / sqrt(3)')
bounded(pad_cost_over_q,s.Rational(0),s.Rational(1,80),'outgoing pad cost / q')

assert_positive(s.Rational(7,4)**2-3,'sqrt(3) upper for local cost')
assert_positive(s.Rational(3,5)**2-s.Rational(1,3),'q upper for local cost')

# A strict lower bound on the actual octagon budget gives a strict lower
# bound on its Casimir threshold, using pi<22/7.
assert_positive(s.Rational(3)-s.Rational(433,250)**2,'sqrt(3) lower')
assert_positive(s.Rational(283,200)**2-2,'sqrt(2) upper')
_,log2_upper=log_enclosure(s.Rational(2),4)
assert_positive(s.Rational(347,500)-log2_upper,'log(2) upper')
oct_lower=2*s.Rational(433,250)*(8-4*s.Rational(283,200)
                               -s.Rational(347,500))/(2*s.Rational(283,200)-1)
assert_positive(oct_lower-s.Rational(311,100),'octagon cost lower bound')
cap_lower=3*s.Rational(311,100)/(2*(2*s.Rational(22,7)-s.Rational(311,100)))
equal(cap_lower,s.Rational(2177,1482),'Casimir cap lower bound')
assert_positive(cap_lower**2-s.Rational(107,50),'determinant below actual cap')

print(f'PASS: {checks} exact identities and rational sign checks.')
print('Scope: one actual local normal PMP six-piece window with short pads.')
print('No full period, geometric-sector eligibility, embedding, or minimality claim.')
