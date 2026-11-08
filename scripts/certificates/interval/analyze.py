import pickle, sys, collections
import run, expr
res = pickle.load(open(sys.argv[1], 'rb'))
chart = int(sys.argv[2])
prob = run.make(chart, False)
cnt = collections.Counter()
depths = collections.Counter()
def walk(c, d):
    if c[0] == 'split':
        walk(c[2], d+1); walk(c[3], d+1)
    elif c[0] == 'R':
        cnt[('R', prob.names[c[1]])] += 1
    elif c[0] == 'S':
        if len(c[1]) == 1:
            cnt[('S', prob.names[c[1][0][0]])] += 1
        else:
            cnt[('L', len(c[1]))] += 1
    else:
        cnt[('FAIL',)] += 1
for p, ok, c, st in res:
    if ok:
        walk(c, len(p))
for k, v in sorted(cnt.items(), key=lambda kv: -kv[1]):
    print(k, v, 'cost', prob.cost[prob.names.index(k[1])] if len(k) > 1 and k[0] in 'RS' else '')
