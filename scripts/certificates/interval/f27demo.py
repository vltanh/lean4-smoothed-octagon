import pickle, random, sys
import run_ss, smaller, expr, fx
res = pickle.load(open('../res_ss_lp.pkl','rb'))
prob = run_ss.make(True)
f, fn = smaller.build(); f27 = f[27].i
B0 = smaller.root_box()
hits = []; checked = 0
random.seed(3)
def walk(c, B):
    global checked
    if len(hits) >= 60: return
    if c[0] == 'split':
        j = c[1]; lo, hi = B[j]; m = (lo + hi) >> 1
        BL = list(B); BL[j] = (lo, m); BR = list(B); BR[j] = (m, hi)
        walk(c[2], BL); walk(c[3], BR); return
    if random.random() > 0.05: return
    checked += 1
    r = expr.evalR(B, f27, {})
    if r is not None and r[1] < 0:
        hits.append((B, ('R', 27))); return
    s = expr.evalS(B, f27, {})
    if s is not None and expr.slope_hi(B, s) < 0:
        hits.append((B, ('S', [(27, 1)])))
for p, ok, c, st in res:
    if not ok: continue
    B = B0
    for bit in p:
        j = prob.split_axis(B); lo, hi = B[j]; m = (lo + hi) >> 1
        B = list(B); B[j] = (lo, m) if bit == 0 else (m, hi)
    walk(c, B)
print('checked', checked, 'f27 rejects', len(hits), [h[1][0] for h in hits][:20], file=sys.stderr)
pickle.dump(hits, open('../f27hits.pkl', 'wb'))
