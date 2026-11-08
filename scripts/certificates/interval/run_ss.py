import sys, time, pickle, os, multiprocessing as mp
import fx, expr, smaller, bnb

import math

def _xl(b):
    return 1 / b[0][1] - 1

# (residual index, axis, side, new-bound function of the float box) from the C++ `contract`
CONTRACTORS = [
    (16, 3, 'hi', lambda b: b[0][1] ** 2),                                   # rho <= r^2
    (16, 0, 'lo', lambda b: math.sqrt(b[3][0])),                             # r >= sqrt rho
    (17, 2, 'hi', lambda b: 1 / b[0][0] - 1),                                # al <= x
    (9, 2, 'hi', lambda b: math.sqrt(3 * (1 - b[3][0]) / (17 * b[3][0]))),   # rhoA <= 3/20
    (17, 0, 'hi', lambda b: 1 / (1 + b[2][0])),                              # x >= al
    (18, 2, 'lo', lambda b: 1 + b[1][0] * (1 + 2 * _xl(b) / 7)),             # al >= 1 + delta(..)
    (18, 1, 'hi', lambda b: (b[2][1] - 1) / (1 + 2 * _xl(b) / 7)),
    (19, 3, 'hi', lambda b: 1 / (b[2][0] ** 2 + 2 * b[2][0] * (1 + b[1][0]) * _xl(b) + 1)),
    (20, 3, 'hi', lambda b: 1 / (1 + (1 + b[1][0]) * _xl(b) ** 2)),
    (2, 4, 'hi', lambda b: 1 - b[3][0] / b[0][1] + (b[3][0] / b[0][1]) ** 2),
    (13, 5, 'hi', lambda b: 3 * b[3][1]),
]

def make(lp):
    f, nm = smaller.build()
    sc = [lambda lo, s=s: s * fx.U for s in smaller.SCALES]
    p = bnb.Problem(f, nm, sc, lp=lp, maxdepth=int(os.environ.get('MAXDEPTH', '70')))
    if os.environ.get('CONTRACT', '0') == '1':
        p.contractors = CONTRACTORS
    return p

def top_split(prob, B, D):
    out = [((), B)]
    for _ in range(D):
        nxt = []
        for path, b in out:
            j = prob.split_axis(b); lo, hi = b[j]; m = (lo + hi) >> 1
            bl = list(b); bl[j] = (lo, m); br = list(b); br[j] = (m, hi)
            nxt.append((path + (0,), bl)); nxt.append((path + (1,), br))
        out = nxt
    return out

def work(args):
    lp, path, B, limit = args
    prob = make(lp)
    t = time.time()
    try:
        cert, st = bnb.solve(prob, B, depth=len(path), limit=limit)
        ok = True
    except RuntimeError:
        cert, st, ok = None, {'nodes': limit}, False
    st['time'] = time.time() - t
    return path, ok, cert, st

if __name__ == '__main__':
    lp = sys.argv[1] == 'lp'; D = int(sys.argv[2]); limit = int(sys.argv[3]); out = sys.argv[4]
    prob = make(lp)
    tasks = [(lp, p, b, limit) for p, b in top_split(prob, smaller.root_box(), D)]
    t0 = time.time(); res = []
    with mp.Pool(int(os.environ.get('NPROC', '18'))) as pool:
        for r in pool.imap_unordered(work, tasks):
            res.append(r); p, ok, c, st = r
            print(len(res), p, ok, st, flush=True)
            if len(res) % 16 == 0:
                pickle.dump(res, open(out, 'wb'))
    tot = {}
    for p, ok, c, st in res:
        for k, v in st.items():
            if isinstance(v, (int, float)) and k != 'maxdepth':
                tot[k] = tot.get(k, 0) + v
    tot['maxdepth'] = max(st.get('maxdepth', 0) for _, _, _, st in res)
    tot['unresolved_tasks'] = sum(1 for r in res if not r[1])
    print('TOTAL', tot, 'wall', time.time() - t0)
    pickle.dump(res, open(out, 'wb'))
