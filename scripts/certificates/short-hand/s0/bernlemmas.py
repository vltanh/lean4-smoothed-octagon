# generic Bernstein lemmas hh0_bern{n} and the positive-form lemmas hh0_bpos{n}
from math import comb
def pw(v,e):
    if e==0: return None
    if e==1: return v
    return f"{v} ^ ({e} : ℕ)"
def prod(*fs):
    fs=[f for f in fs if f is not None]
    return " * ".join(fs) if fs else "1"
def bpos(n):
    cs=[f"c{k}" for k in range(n+1)]
    terms=[prod(f"c{k}",pw("p",k),pw("r",n-k)) for k in range(n+1)]
    s=" + ".join(terms)
    hyps=" ".join(f"(h{k} : 0 < c{k})" for k in range(n+1))
    rest_last=" + ".join(terms[:-1]); rest_first=" + ".join(terms[1:])
    return f"""/-- A Bernstein form of degree {n} with positive coefficients is positive. -/
theorem hh0_bpos{n} {{p r {' '.join(cs)} : ℝ}} (hp : 0 ≤ p) (hr : 0 ≤ r) (hpr : 0 < p ∨ 0 < r)
    {hyps} :
    0 < {s} := by
  rcases hpr with h | h
  · have h' : 0 < {terms[-1]} := by positivity
    have h'' : 0 ≤ {rest_last} := by positivity
    linarith
  · have h' : 0 < {terms[0]} := by positivity
    have h'' : 0 ≤ {rest_first} := by positivity
    linarith
"""
def combo(n,k):
    # sum_{i<=k} C(n-i,k-i) c_i gn^i gd^(k-i)
    ts=[]
    for i in range(k+1):
        c=comb(n-i,k-i)
        f=[None if c==1 else str(c), f"c{i}", pw("gn",i), pw("gd",k-i)]
        ts.append(prod(*f))
    return " + ".join(ts)
def poly(n, cname="c", y="y"):
    ts=[]
    for i in range(n+1):
        ts.append(prod(f"{cname}{i}", pw(y,i)))
    return " + ".join(ts)
def bern(n):
    cs=[f"c{k}" for k in range(n+1)]
    hyps="\n    ".join(f"(h{k} : 0 < {combo(n,k)})" for k in range(n+1))
    P=poly(n)
    rhs=" + ".join(prod(f"({combo(n,k)})", pw("y",k), pw("(gn - gd * y)",n-k)) for k in range(n+1))
    hargs=" ".join(f"h{k}" for k in range(n+1))
    return f"""/-- Bernstein positivity of degree {n} on `[0, gn/gd]`, with abstract coefficients: the
polynomial `∑ cᵢ yⁱ` is positive when its scaled Bernstein coefficients
`∑_{{i ≤ k}} C({n} - i, k - i) cᵢ gnⁱ gd^(k - i)` are. -/
theorem hh0_bern{n} {{y gn gd {' '.join(cs)} : ℝ}} (hy : 0 ≤ y) (hyg : gd * y ≤ gn) (hgd : 0 < gd)
    {hyps} :
    0 < {P} := by
  have hgn : 0 ≤ gn := le_trans (mul_nonneg hgd.le hy) hyg
  rcases hgn.eq_or_lt with h | h
  · have hy0 : y = 0 := by nlinarith
    subst hy0
    simpa using h0
  · have e : gn ^ ({n} : ℕ) * ({P}) =
        {rhs} := by ring
    have hpr : 0 < y ∨ 0 < gn - gd * y := by
      rcases hy.eq_or_lt with h' | h'
      · right; rw [← h']; simpa using h
      · left; exact h'
    have hpos := hh0_bpos{n} hy (by linarith) hpr {hargs}
    rw [← e] at hpos
    exact pos_of_mul_pos_right hpos (by positivity)
"""
def module(ns):
    s="""module

public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Basic

/-!
# Hand proof of the smaller-short case, heavy S0 signs: Bernstein lemmas

Positivity of a polynomial `∑ cᵢ yⁱ` on an interval `0 ≤ y ≤ gn/gd` from its (scaled) Bernstein
coefficients, with abstract coefficients `cᵢ`, `gn`, `gd` (so that the certificates of
`Heavy/S0*` apply them to polynomial coefficients without expanding them).

## Main API

* `hh0_bpos{n}`: a Bernstein form with positive coefficients is positive.
* `hh0_bern{n}`: Bernstein positivity on `[0, gn/gd]`, degrees """+", ".join(map(str,ns))+""".
-/

@[expose] public section

namespace SmoothedOctagon

"""
    for n in ns: s+=bpos(n)+"\n"
    for n in ns: s+=bern(n)+"\n"
    s+="end SmoothedOctagon\n"
    return s
if __name__=="__main__":
    import sys
    p=sys.argv[1]
    open(p,'w').write(module([4,5,6,7,8]))
