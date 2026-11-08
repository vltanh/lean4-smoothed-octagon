import sympy as sp
from fractions import Fraction as Fr
from math import comb
from bern import poly_coeffs, shift_scale_1d, bern_1d

def lnum(q):
    q=Fr(q)
    if q.denominator==1: return f"{q.numerator}"
    return f"{q.numerator} / {q.denominator}"
def lean_expr(e):
    """sympy expr -> lean string (polynomial/rational)"""
    s=sp.sstr(e, order='lex')
    s=s.replace('**','^')
    return s
def lean_poly(p, vars_):
    """polynomial with rational coeffs -> lean string in expanded form"""
    P=sp.Poly(sp.expand(p),*vars_)
    terms=[]
    for mon,c in P.terms():
        c=Fr(int(sp.Rational(c).p),int(sp.Rational(c).q))
        parts=[]
        for v,e in zip(vars_,mon):
            if e==1: parts.append(f"{v}")
            elif e>1: parts.append(f"{v} ^ {e}")
        mono=" * ".join(parts)
        ac=abs(c)
        cs=lnum(ac)
        if mono=="":
            body=f"({cs})" if ac.denominator!=1 else cs
        elif ac==1: body=mono
        else: body=f"({cs}) * {mono}" if ac.denominator!=1 else f"{cs} * {mono}"
        terms.append(('-' if c<0 else '+', body))
    if not terms: return "0"
    out=("-" if terms[0][0]=='-' else "")+terms[0][1]
    for sg,b in terms[1:]: out+=f" {sg} {b}"
    return out

def bern_coeffs2(p, x, y, box):
    (x0,x1),(y0,y1)=box
    d,(m,n)=poly_coeffs(p,(x,y))
    A=[[Fr(0)]*(n+1) for _ in range(m+1)]
    for (i,j),c in d.items(): A[i][j]=c
    B=[[Fr(0)]*(n+1) for _ in range(m+1)]
    for j in range(n+1):
        col=bern_1d(shift_scale_1d([A[i][j] for i in range(m+1)],Fr(x0),Fr(x1)-Fr(x0)))
        for i in range(m+1): B[i][j]=col[i]
    C=[bern_1d(shift_scale_1d(B[i],Fr(y0),Fr(y1)-Fr(y0))) for i in range(m+1)]
    return C,m,n

def bern_lemma2(name, p, x, y, box, hyps_names=('hx0','hx1','hy0','hy1'), doc=""):
    """Lean theorem: 0 <= p on box, via Bernstein. Returns string or raises if a coefficient negative."""
    (x0,x1),(y0,y1)=box
    C,m,n=bern_coeffs2(p,x,y,box)
    mn=min(min(r) for r in C)
    if mn<0: raise ValueError(f"{name}: negative Bernstein coefficient {float(mn)}")
    X0,X1,Y0,Y1=map(Fr,(x0,x1,y0,y1))
    dx=X1-X0; dy=Y1-Y0
    def fx(v): return lnum(v)
    u1=f"({x} - {fx(X0)})" if X0!=0 else f"{x}"
    u2=f"({fx(X1)} - {x})"
    v1=f"({y} - {fx(Y0)})" if Y0!=0 else f"{y}"
    v2=f"({fx(Y1)} - {y})"
    terms=[]
    for i in range(m+1):
        for j in range(n+1):
            c=C[i][j]*comb(m,i)*comb(n,j)/(dx**m*dy**n)
            if c==0: continue
            parts=[]
            for base,e in ((u1,i),(u2,m-i),(v1,j),(v2,n-j)):
                if e==1: parts.append(base)
                elif e>1: parts.append(f"{base} ^ {e}")
            cs=lnum(c)
            terms.append(f"({cs}) * " + " * ".join(parts) if parts else f"({cs})")
    rhs=" +\n      ".join(terms) if terms else "0"
    P=lean_poly(p,(x,y))
    s=f"""{doc}theorem {name} {{{x} {y} : ℝ}} ({hyps_names[0]} : {fx(X0)} ≤ {x}) ({hyps_names[1]} : {x} ≤ {fx(X1)})
    ({hyps_names[2]} : {fx(Y0)} ≤ {y}) ({hyps_names[3]} : {y} ≤ {fx(Y1)}) :
    0 ≤ {P} := by
  have e1 : 0 ≤ {u1} := by linarith
  have e2 : 0 ≤ {u2} := by linarith
  have e3 : 0 ≤ {v1} := by linarith
  have e4 : 0 ≤ {v2} := by linarith
  have key : {P} =
      {rhs} := by ring
  rw [key]; positivity
"""
    return s, float(mn)

def bern_1d_coeffs(coeffs, x0, x1):
    return bern_1d(shift_scale_1d(coeffs, Fr(x0), Fr(x1)-Fr(x0)))

def uni_lean(name_q, q_coeffs, x, x0, x1):
    """returns (lean poly string of q, lean bernstein rhs string) for univariate q given power coeffs"""
    X0,X1=Fr(x0),Fr(x1)
    m=len(q_coeffs)-1
    b=bern_1d_coeffs(q_coeffs,X0,X1)
    dx=X1-X0
    u1=f"({x} - {lnum(X0)})" if X0!=0 else f"{x}"
    u2=f"({lnum(X1)} - {x})"
    terms=[]
    for i in range(m+1):
        c=b[i]*comb(m,i)/dx**m
        if c==0: continue
        parts=[]
        for base,e in ((u1,i),(u2,m-i)):
            if e==1: parts.append(base)
            elif e>1: parts.append(f"{base} ^ {e}")
        terms.append(f"({lnum(c)}) * "+" * ".join(parts) if parts else f"({lnum(c)})")
    return min(b), (" + ".join(terms) if terms else "0")

def upoly_str(coeffs, x):
    terms=[]
    for i,c in enumerate(coeffs):
        if c==0: continue
        ac=abs(c)
        mono = "" if i==0 else (x if i==1 else f"{x} ^ {i}")
        cs=lnum(ac)
        if mono=="": body=f"({cs})"
        elif ac==1: body=mono
        else: body=f"({cs}) * {mono}"
        terms.append(('-' if c<0 else '+',body))
    if not terms: return "0"
    out=("-" if terms[0][0]=='-' else "")+terms[0][1]
    for sg,bd in terms[1:]: out+=f" {sg} {bd}"
    return out

def bern_lemma2n(name, p, x, y, box, doc="", eps=0):
    """nested version: 0 <= p - eps on box"""
    (x0,x1),(y0,y1)=box
    X0,X1,Y0,Y1=map(Fr,(x0,x1,y0,y1))
    d,(m,n)=poly_coeffs(p,(x,y))
    A=[[Fr(0)]*(n+1) for _ in range(m+1)]
    for (i,j),c in d.items(): A[i][j]=c
    A[0][0]-=Fr(eps)
    # y-bernstein: for each power of x, convert column in y
    dy=Y1-Y0
    # Q_j(x) power coeffs: Q[j][i]
    Q=[[Fr(0)]*(m+1) for _ in range(n+1)]
    for i in range(m+1):
        b=bern_1d_coeffs([A[i][j] for j in range(n+1)],Y0,Y1)
        for j in range(n+1): Q[j][i]=b[j]*comb(n,j)/dy**n
    v1=f"({y} - {lnum(Y0)})" if Y0!=0 else f"{y}"
    v2=f"({lnum(Y1)} - {y})"
    u1=f"({x} - {lnum(X0)})" if X0!=0 else f"{x}"
    u2=f"({lnum(X1)} - {x})"
    lines=[]
    qs=[]
    gmin=None
    for j in range(n+1):
        if all(c==0 for c in Q[j]): qs.append(None); continue
        mn,rhs=uni_lean(f"q{j}",Q[j],x,X0,X1)
        if mn<0: raise ValueError(f"{name}: neg coeff at j={j}: {float(mn)}")
        gmin = mn if gmin is None else min(gmin,mn)
        qstr=upoly_str(Q[j],x)
        lines.append(f"  have q{j} : 0 ≤ {qstr} := by\n    have k : {qstr} = {rhs} := by ring\n    rw [k]; positivity")
        qs.append(qstr)
    terms=[]
    for j in range(n+1):
        if qs[j] is None: continue
        parts=[f"({qs[j]})"]
        for base,e in ((v1,j),(v2,n-j)):
            if e==1: parts.append(base)
            elif e>1: parts.append(f"{base} ^ {e}")
        terms.append(" * ".join(parts))
    P=lean_poly(p,(x,y))
    epsS = "" if eps==0 else f" + {lnum(Fr(eps))}" if Fr(eps)>0 else f" - {lnum(-Fr(eps))}"
    gens="\n".join(f"    generalize {qs[j] and '('+qs[j]+')'} = r{j} at q{j} ⊢" for j in range(n+1) if qs[j] is not None)
    s=f"""{doc}theorem {name} {{{x} {y} : ℝ}} (hx0 : {lnum(X0)} ≤ {x}) (hx1 : {x} ≤ {lnum(X1)})
    (hy0 : {lnum(Y0)} ≤ {y}) (hy1 : {y} ≤ {lnum(Y1)}) :
    {('0' if eps==0 else lnum(Fr(eps)))} ≤ {P} := by
  have e1 : 0 ≤ {u1} := by linarith
  have e2 : 0 ≤ {u2} := by linarith
  have e3 : 0 ≤ {v1} := by linarith
  have e4 : 0 ≤ {v2} := by linarith
""" + "\n".join(lines) + f"""
  have key : {P}{'' if eps==0 else ' - ('+lnum(Fr(eps))+')'} =
      {(' +'+chr(10)+'      ').join(terms)} := by ring
  have : 0 ≤ {(' + ').join(terms)} := by
{gens}
    positivity
  linarith
"""
    return s, float(gmin)
