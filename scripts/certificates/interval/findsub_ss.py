import pickle, sys, collections
import run_ss, smaller, fx
res = pickle.load(open(sys.argv[1], 'rb'))
lo_l, hi_l = int(sys.argv[2]), int(sys.argv[3])
prob = run_ss.make(True)
names = prob.names
B0 = smaller.root_box()
cands = []
def info(c):
    if c[0] == 'split':
        a = info(c[2]); b = info(c[3])
        return (a[0] + b[0], a[1] + b[1])
    cnt = collections.Counter()
    if c[0] == 'R': cnt['R'] += 1
    elif len(c[1]) == 1:
        cnt['S'] += 1
        if names[c[1][0][0]] == 'f27': cnt['S27'] += 1
    else:
        cnt['L'] += 1
        if any(names[k] == 'f27' for k, _ in c[1]): cnt['L27'] += 1
    return (1, cnt)
def walk(c, B, path):
    n, cnt = info(c)
    if lo_l <= n <= hi_l:
        cands.append((n, dict(cnt), path, B, c))
        return
    if c[0] == 'split' and n > hi_l:
        j = c[1]; lo, hi = B[j]; m = (lo + hi) >> 1
        BL = list(B); BL[j] = (lo, m); BR = list(B); BR[j] = (m, hi)
        walk(c[2], BL, path + (0,)); walk(c[3], BR, path + (1,))
import os
onlyp = os.environ.get('ONLYP')
for p, ok, c, st in res:
    if not ok: continue
    if onlyp and ''.join(map(str, p)) != onlyp: continue
    B = B0
    for bit in p:
        j = prob.split_axis(B); lo, hi = B[j]; m = (lo + hi) >> 1
        B = list(B); B[j] = (lo, m) if bit == 0 else (m, hi)
    walk(c, B, p)
cands.sort(key=lambda x: -(min(x[1].get('S27', 0) + x[1].get('L27', 0), 300) + min(x[1].get('L', 0), 300)))
for cd in cands[:8]:
    print(cd[0], cd[1], [(round(l / fx.U, 4), round(h / fx.U, 4)) for l, h in cd[3]])
pickle.dump(cands[:8], open(os.environ.get('OUT', '../subcands_ss.pkl'), 'wb'))
