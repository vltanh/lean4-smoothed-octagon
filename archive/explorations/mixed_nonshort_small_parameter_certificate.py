#!/usr/bin/env python3
"""Exact coefficient and rational checks for the nonshort epsilon<=1/32 corner.

Premises: 0<a<=c, a^2<=3/4, ac<=9/8, c^2<=4,
0<=li<=1, H=4-a^2-2ac>=1, M=a(l0+l2)+c*l1.
For each nonpositive coefficient monomial, choose a square or cross pair
from its weight monomial. A square is at most M^2; a cross pair at most
M^2/4. Bound the residual a,c monomial using only the four premises.
Every exponent identity and comparison is exact rational arithmetic.
"""
from pathlib import Path
from itertools import product
from functools import lru_cache
import sympy as s
ns={}
source=Path(__file__).with_name('mixed_nonshort_completion_blowup_certificate.py').read_text()
exec(source.split('# The quadratic-log model')[0],ns)
a,c,l0,l1,l2=[ns[k] for k in ('a','c','l0','l1','l2')]
H=4-a*a-2*a*c
T=a+c
pol=ns['poly']
scales=[(1,0),(0,1),(1,0)]

@lru_cache(None)
def basic_bound(pa,pc):
    options=[]
    # (a/c)^r (a^2)^j (ac)^k (c^2)^l
    for r,j,k,l in product(range(9),repeat=4):
        if r+2*j+k==pa and -r+k+2*l==pc:
            options.append((s.Rational(3,4)**j*s.Rational(9,8)**k*4**l,(r,j,k,l)))
    return min(options) if options else None

def best_pair(weight,pa,pc):
    options=[]
    for i in range(3):
        for j in range(i,3):
            uses=tuple(int(k==i)+int(k==j) for k in range(3))
            if any(x>y for x,y in zip(uses,weight)): continue
            ba=pa-scales[i][0]-scales[j][0]
            bc=pc-scales[i][1]-scales[j][1]
            base=basic_bound(ba,bc)
            if base is None:continue
            factor=1 if i==j else s.Rational(1,4)
            options.append((factor*base[0],(i,j),base[1]))
    assert options,(weight,pa,pc)
    return min(options)

lines=[]
totals=[]
for degree in range(4,9):
    quotient,remainder=s.div(pol.nth(degree),T**3,a,c,l0,l1,l2)
    assert s.expand(remainder)==0
    total=s.Integer(0)
    lines.append('C'+str(degree))
    for weight,coef in s.Poly(quotient,l0,l1,l2).terms():
        hc,hr=s.div(coef,H,a,c)
        if hr==0 and all(x>=0 for x in s.Poly(hc,a,c).coeffs()):
            lines.append(str(weight)+': nonnegative multiple of H')
            continue
        parts=[]
        group=s.Integer(0)
        for (pa,pc),val in s.Poly(coef,a,c).terms():
            if val>=0: continue
            bound,pair,basic=best_pair(weight,pa,pc)
            result=-val*bound
            group+=result
            parts.append((str(-val*a**pa*c**pc),pair,basic,str(result)))
        if not parts:
            lines.append(str(weight)+': nonnegative polynomial')
            continue
        total+=group
        lines.append(str(weight)+': '+str(group)+'; '+str(parts))
    assert total<=128,(degree,total)
    totals.append(total)
    lines.append('B'+str(degree)+'='+str(total)+' < 128\n')
if '--table' in __import__('sys').argv:
    print('\n'.join(lines))
else:
    print('Exact coefficient bounds C4..C8:', ', '.join(map(str, totals)))
print('PASS: all five coefficient lower bounds have Bk<=128')

# C3 admits sharper estimates by retaining its elementary positive slacks.
# q=a^2, r=ac and s=c^2 here are shorthand, not new free variables.
q=a*a; r=a*c; cc=c*c
quotient,remainder=s.div(pol.nth(3),T**3,a,c,l0,l1,l2)
assert s.expand(remainder)==0
coeffs=dict(s.Poly(quotient,l0,l1,l2).terms())
slacks={
    (2,1,0):(s.Rational(25,4)*a*c,
             a*a*(4-q)+3*a*c*(s.Rational(3,4)-q)),
    (2,0,1):(s.Rational(11,4)*a*a,
             a*a*(3*(s.Rational(3,4)-q)+4*(s.Rational(9,8)-r))),
    (0,3,0):(s.Rational(41,4)*c*c,
             c*(c-a)*(r+4)+2*c*c*(s.Rational(9,8)-r)),
    (0,2,1):(s.Rational(41,2)*a*c,
             a*c*(6*(s.Rational(3,4)-q)+8*(4-cc))+c*c*(12-15*q)),
    (0,1,2):(s.Rational(3,2)*a*c,
             a*T*(5*(s.Rational(3,4)-q)+8*(s.Rational(9,8)-r))
             +s.Rational(3,4)*a*(c-a)),
}
for weight,(loss,slack) in slacks.items():
    assert s.expand(coeffs[weight]+loss-slack)==0
positive={(1,2,0):2*a*c*H,(1,1,1):6*a*T*H,
          (1,0,2):2*a*a*H,(0,0,3):a*a*(a*a+4)}
assert set(coeffs)==set(slacks)|set(positive)
for weight,value in positive.items():
    assert s.expand(coeffs[weight]-value)==0
B3=sum([s.Rational(25,16),s.Rational(11,16),s.Rational(41,4),
        s.Rational(41,8),s.Rational(3,8)])
assert B3==18
print('PASS: C3 >= -18 M^2 by five explicit nonnegative slacks')

# Exact arithmetic behind the geometry and analytic remainder estimates.
qmax=s.Rational(12,17)
assert 9-10*qmax-3*qmax*qmax==s.Rational(129,289)>0
assert s.Rational(81,64)-s.Rational(7,4)*qmax==s.Rational(33,1088)>0
assert qmax<s.Rational(3,4)
assert qmax<s.Rational(17,20)**2
assert qmax+4<s.Rational(11,5)**2
eta=s.Rational(1,32)
assert s.Rational(17,20)+s.Rational(11,5)*eta==s.Rational(147,160)<1

# H(z)=integral_0^1 t^2/(1+zt) dt lies in [0,1/3] for z>=0.
# The hand proof bounds the two negative remainders after clearing the
# positive denominator by the last term below. All omitted polynomial
# powers are bounded by the displayed geometric series.
margin=1-B3*eta-128*eta**2/(1-eta) \
       -s.Rational(20,3)*eta*(1+eta/2)*(1+eta)**3
assert margin==s.Rational(39743703,520093696)
assert margin>s.Rational(3,40)
print('PASS: geometry and remainder budget; exact margin',margin,'> 3/40')
print('PASS: all max-chart points with epsilon<=1/32 satisfy Phi>0')
