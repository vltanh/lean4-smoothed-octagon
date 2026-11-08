import pickle, sys, collections
import run, nonshort, fx
res = pickle.load(open(sys.argv[1], 'rb'))
allowed = set(sys.argv[2].split(','))
lo_l, hi_l = int(sys.argv[3]), int(sys.argv[4])
prob = run.make(1, False)
names = prob.names
B0 = nonshort.root_box()
cands = []
def info(c):
    """returns (leaves, set of residual names, counts R/S)"""
    if c[0] == 'split':
        a = info(c[2]); b = info(c[3])
        return (a[0] + b[0], a[1] | b[1], a[2] + b[2], a[3] + b[3])
    if c[0] == 'R':
        return (1, {names[c[1]]}, 1, 0)
    return (1, {names[k] for k, _ in c[1]}, 0, 1)
def walk(c, B, path):
    n, used, nr, ns = info(c)
    if used <= allowed and lo_l <= n <= hi_l:
        cands.append((n, nr, ns, sorted(used), path, B, c))
        return
    if c[0] == 'split' and n > lo_l:
        j = c[1]; lo, hi = B[j]; m = (lo + hi) >> 1
        BL = list(B); BL[j] = (lo, m); BR = list(B); BR[j] = (m, hi)
        walk(c[2], BL, path + (0,)); walk(c[3], BR, path + (1,))
for p, ok, c, st in res:
    # recompute box of task path
    B = B0
    for bit in p:
        j = prob.split_axis(B); lo, hi = B[j]; m = (lo + hi) >> 1
        B = list(B); B[j] = (lo, m) if bit == 0 else (m, hi)
    walk(c, B, p)
cands.sort(key=lambda x: -x[2])
for cnd in cands[:10]:
    print(cnd[0], 'R', cnd[1], 'S', cnd[2], cnd[3], [(round(l/fx.U, 6), round(h/fx.U, 6)) for l, h in cnd[5]])
pickle.dump(cands[:10], open('../subcands.pkl', 'wb'))
