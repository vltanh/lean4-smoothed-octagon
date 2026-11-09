import pickle
from gen4 import lemma0g, lemmaI, lemma_pos
from gen5 import lemma_tr
from fractions import Fraction as Fr
from mk5 import DOC, LEAN, OUT
from writer import write_cert
s = """module

public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Bernstein

/-!
# Case M2, forward successor: further Bernstein lemmas

The generic lemmas of `Nonshort/Forward/Bernstein` used only by the small-gap certificates (same conventions).
-/

@[expose] public section

namespace SmoothedOctagon

""" + "\n".join([lemma_pos(2), lemma_pos(3), lemma0g(7), lemmaI(2, Fr(0), Fr(1,30)), lemmaI(3, Fr(0), Fr(1)), lemma_tr('zgen', 3)]) + "\nend SmoothedOctagon\n"
open(LEAN + 'Bernstein/LowDegree.lean', 'w').write(s.replace('\\\\n', '\\n'))
for X in ['nsfCChi','nsfCQD','nsfCQC','nsfCEn','nsfCPn']:
    n = write_cert(X)
    p = LEAN + OUT[X]
    t = open(p).read().replace('public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Bernstein\n', 'public import SmoothedOctagon.Exclusion.Mixed.Nonshort.Forward.Bernstein.LowDegree\n')
    open(p, 'w').write(t)
    print(X, n)
