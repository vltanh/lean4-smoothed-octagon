from sympy import *
from gen import *
import pickle
h,s = symbols('h s')
P = pickle.load(open('ofaceP.pkl','rb'))
R=Rational
hdr = """module

public import SmoothedOctagon.Exclusion.Mixed.Hand.Bern

/-!
# Case M2 by hand: generated sign certificate for the reverse order face

The polynomial `P(h, s)` of `MIXED_NONSHORT_REVERSE_ORDER_FACE_REDUCTION` (13)-(14)
(`h = 1 - 2t`, `s = k - 1`, on the face `k = 2t + x`), positive on the domain (11)
`1/5 < h < 1`, `0 ≤ s < 4/3`, `h + s > 1/4`, covered by the pieces
`h ∈ [1/5, 1/4], s ∈ [1/4 - h, 4/3]` and `h ∈ [1/4, 1], s ∈ [0, 4/3]`. Bernstein-form
certificates of degree seven in `s` with univariate Bernstein bounds for the coefficients
(generated; every identity is checked by `ring`). Route: in place of the hand estimates (15)-(18).

## Main API

* `nhOP h s`; `nhOP_pos_a`, `nhOP_pos_b`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The order-face polynomial `P(h, s)` (`MIXED_NONSHORT_REVERSE_ORDER_FACE_REDUCTION` (13)). -/
noncomputable def nhOP (h s : ℝ) : ℝ :=
  """ + lpoly(P,[h,s],['h','s']) + "\n"
out=[hdr]
for tag,(lo,hi,S0f,S1f) in [('a',(R(1,5),R(1,4),lambda a,b: R(1,4)-h, lambda a,b: R(4,3))), ('b',(R(1,4),Integer(1),lambda a,b: Integer(0), lambda a,b: R(4,3)))]:
    pl = plan_biv(P, s, h, lo, hi, S0f, S1f)
    assert len(pl)==1
    code, nl = emit_biv_piece(f"nhOP_pos_{tag}", P, s, h, 's', 'h', pl[0], stmt="nhOP h s", unfold="nhOP")
    out.append(code)
out.append("end SmoothedOctagon\n")
open('/home/vltanh/Documents/lean4-reinhardt-conjecture/SmoothedOctagon/Exclusion/Mixed/Hand/CertOrder.lean','w').write("\n".join(out))
