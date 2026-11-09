from sympy import *
from gen import *
import pickle
h,s = symbols('h s')
P = pickle.load(open('ofaceP.pkl','rb'))
R=Rational
hdr = """module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Reverse.Bernstein

/-!
# Case M2, reverse successor: sign certificate for the reverse order face

The polynomial `P(h, s)` of the reverse order face
(`h = 1 - 2t`, `s = k - 1`, on the face `k = 2t + x`), positive on the domain (11)
`1/5 < h < 1`, `0 ≤ s < 4/3`, `h + s > 1/4`, covered by the pieces
`h ∈ [1/5, 1/4], s ∈ [1/4 - h, 4/3]` and `h ∈ [1/4, 1], s ∈ [0, 4/3]`. Bernstein-form
certificates of degree seven in `s` with univariate Bernstein bounds for the coefficients
(generated; every identity is checked by `ring`). Route: one Bernstein certificate on the face.

## Main API

* `nsrOP h s`; `nsrOP_pos_a`, `nsrOP_pos_b`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The order-face polynomial `P(h, s)`). -/
noncomputable def nsrOP (h s : ℝ) : ℝ :=
  """ + lpoly(P,[h,s],['h','s']) + "\n"
out=[hdr]
for tag,(lo,hi,S0f,S1f) in [('a',(R(1,5),R(1,4),lambda a,b: R(1,4)-h, lambda a,b: R(4,3))), ('b',(R(1,4),Integer(1),lambda a,b: Integer(0), lambda a,b: R(4,3)))]:
    pl = plan_biv(P, s, h, lo, hi, S0f, S1f)
    assert len(pl)==1
    code, nl = emit_biv_piece(f"nsrOP_pos_{tag}", P, s, h, 's', 'h', pl[0], stmt="nsrOP h s", unfold="nsrOP")
    out.append(code)
out.append("end SmoothedOctagon\n")
open('/home/vltanh/Documents/lean4-reinhardt-conjecture/SmoothedOctagon/Exclusion/Mixed/Nonshort/Reverse/OrderFace/Signs.lean','w').write("\n".join(out))
