from genS import *
from collections import Counter
exec(open('genS6.py').read().split("out=[]")[0].split("info=pickle.load")[0])
P1s='(2 - 2 * a ^ 2 - t * (5 + 3 * a + 2 * a ^ 2))'
P2s='(5 - 3 * a - 2 * a ^ 2 - t * (5 + 3 * a + 2 * a ^ 2))'
P3s='(8 - 6 * a - 2 * a ^ 2 - t * (5 + 3 * a + 2 * a ^ 2))'
lin=pickle.load(open('S_lin.pkl','rb'))
def prod_lean(cnt, extra=None):
    parts=([extra] if extra else [])+[ln if e==1 else f"{ln} ^ {e}" for ln,e in sorted(cnt.items()) if e>0]
    return " * ".join(parts) if parts else "1"
def fr(num, cnt): return f"({L(num)}) / ({prod_lean(cnt)})"
def linform(name, LIn='LI', Lcn='Lc'):
    p=lin[name]
    return f"{fr(*p['R'])} + {fr(*p['cI'])} * {LIn} + {fr(*p['cc'])} * {Lcn}"
defs=f"""/-- `A₀ = 𝓔_Σ(h = 1)` (SYMMETRIC_SUM_REDUCTION (3), (7)) in the coordinates `a = (z - 1)/(z + 1)`,
`t = I - 1`, with `LI = log I`, `Lc = log(1 - aI)` kept as atoms. -/
noncomputable def fs_SA0 (a t LI Lc : ℝ) : ℝ := {linform('A0')}

/-- `A₁` (SYMMETRIC_SUM_REDUCTION (15)): `𝓔_Σ = A₀ + A₁H + z(DH²/(2h) - f(h))`. -/
noncomputable def fs_SA1 (a t LI Lc : ℝ) : ℝ :=
  -({L(sp.expand(N1:=35*a**5*t**2 + 70*a**5*t + 35*a**5 + 35*a**4*t**2 - 35*a**4 - 70*a**3*t**2 - 210*a**3*t - 105*a**3 - 70*a**2*t**2 + 70*a**2*t + 105*a**2 + 35*a*t**2 + 206*a*t - 4*a + 35*t**2 - 4*t + 4))}) / (70 * (1 - a) ^ 2) -
    ({L(a**3*t**2 + 2*a**3*t + a**3 + a**2*t**2 - a**2 - 3*a*t**2 - 6*a*t - 2*a - t**2)}) / (t * (1 - a)) * LI +
    2 * (1 - a * (1 + t)) / (1 - a) * Lc

/-- `Ψ(τ) = A₀(1/τ - 1) + A₁ + z(Dτ/2 - τ²/(3(2 - τ)))`: the Padé upper bound of `𝓔_Σ/H`, `τ = H/h`. -/
noncomputable def fs_Spsi (A0 A1 D z τ : ℝ) : ℝ :=
  A0 * (1 / τ - 1) + A1 + z * (D * τ / 2 - τ ^ 2 / (3 * (2 - τ)))

/-- `Ψ'(τ)`. -/
noncomputable def fs_Sdpsi (A0 D z τ : ℝ) : ℝ :=
  -A0 / τ ^ 2 + z * (D / 2 - (4 * τ - τ ^ 2) / (3 * (2 - τ) ^ 2))
"""
def eqlemma(name, lhs):
    return f"""theorem fs_S{name}_eq {{a t LI Lc : ℝ}} (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 7) (ht0 : 0 < t) (ht1 : t ≤ 1 / 4) :
    {lhs} =
      {linform(name)} := by
  have hb : 0 < 1 - a := by linarith
  have hP1 : 0 < {P1s} := by nlinarith [mul_nonneg ha0 ht0.le, mul_nonneg (mul_nonneg ha0 ha0) ht0.le]
  have hP2 : 0 < {P2s} := by nlinarith [mul_nonneg ha0 ht0.le, mul_nonneg (mul_nonneg ha0 ha0) ht0.le]
  have hP3 : 0 < {P3s} := by nlinarith [mul_nonneg ha0 ht0.le, mul_nonneg (mul_nonneg ha0 ha0) ht0.le]
  have e2 : 2 - {P1s} / {P2s} = {P3s} / {P2s} := by
    rw [eq_div_iff hP2.ne', sub_mul, div_mul_cancel₀ _ hP2.ne']; ring
  unfold fs_Spsi{' fs_Sdpsi' if name=='E4' else ''} fs_SA0 fs_SA1
  rw [e2]
  generalize hq1 : {P1s} = p1 at *
  generalize hq2 : {P2s} = p2 at *
  generalize hq3 : {P3s} = p3 at *
  field_simp
  rw [← hq1, ← hq2, ← hq3]
  ring
"""
tc=f"{P1s} / {P2s}"
E3lhs=f"fs_Spsi (fs_SA0 a t LI Lc) (fs_SA1 a t LI Lc) (a + t + a * t) ((1 + a) / (1 - a))\n      ({tc})"
E4lhs=(f"fs_Spsi (fs_SA0 a t LI Lc) (fs_SA1 a t LI Lc) (a + t + a * t) ((1 + a) / (1 - a))\n      ({tc}) +\n"
       f"      fs_Sdpsi (fs_SA0 a t LI Lc) (a + t + a * t) ((1 + a) / (1 - a)) ({tc}) *\n      (t / (1 + t) - {tc})")
open('Sdefs.lean','w').write(defs)
open('Seq.lean','w').write(eqlemma('E3',E3lhs)+"\n"+eqlemma('E4',E4lhs))
print('ok')
