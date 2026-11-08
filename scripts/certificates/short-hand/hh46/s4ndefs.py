from s4nstruct import STRUCT
def emit(which):
    return f"""/-- The cleared numerator of `{which}_r - 1829/10000` in the atoms `X = x`, `AL = α`, `A = α + β`,
`Sg = Σ`, `S = 1 + x`, `U = S² - S + 1`, `D`, `Pn = S³(nu - du) + (3S - 1)du` (`u = nu/du`), `k = 1/y₀`,
`L0`; denominator `hh46S4M` (`SMALL_SHAPE_CASIMIR_FLOOR` (10)-(11) with the logarithm surrogate). -/
noncomputable def hh46S4N{which} (X AL A Sg S U D Pn nu du k L0 : ℝ) : ℝ :=
  {STRUCT[which]}
"""
if __name__=='__main__':
    import sys
    open(sys.argv[1],'w').write(emit('Phi')+"\n"+emit('Psi'))
