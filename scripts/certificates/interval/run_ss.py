import sys, time, pickle, os, multiprocessing as mp
import fx, expr, smaller, bnb

def make(lp):
    f, nm = smaller.build()
    sc = [lambda lo, s=s: s * fx.U for s in smaller.SCALES]
    return bnb.Problem(f, nm, sc, lp=lp, maxdepth=int(os.environ.get('MAXDEPTH', '70')))

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
