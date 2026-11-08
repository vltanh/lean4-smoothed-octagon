import sys, time, pickle, os, multiprocessing as mp
import fx, expr, nonshort, bnb

SCALES = [lambda lo: 0.5 * fx.U, lambda lo: 1.0 * fx.U, lambda lo: fx.U + lo, lambda lo: 1.0 * fx.U]


def make(chart, lp):
    g, nm = nonshort.build(chart, int(os.environ.get('BRANCH', '0')))
    p = bnb.Problem(g, nm, SCALES, lp=lp, maxdepth=int(os.environ.get('MAXDEPTH', '60')))
    p.smart = os.environ.get('SMART', '0') == '1'
    return p


def top_split(prob, B, D):
    """Split D levels with the same rule; return list of (path, box)."""
    out = [((), B)]
    for _ in range(D):
        nxt = []
        for path, b in out:
            j = prob.split_axis(b)
            lo, hi = b[j]
            m = (lo + hi) >> 1
            bl = list(b); bl[j] = (lo, m)
            br = list(b); br[j] = (m, hi)
            nxt.append((path + (0,), bl)); nxt.append((path + (1,), br))
        out = nxt
    return out


def work(args):
    chart, lp, path, B, limit = args
    prob = make(chart, lp)
    t = time.time()
    try:
        cert, st = bnb.solve(prob, B, depth=len(path), limit=limit)
        ok = True
    except RuntimeError:
        cert, st, ok = None, {'nodes': limit}, False
    st['time'] = time.time() - t
    return path, ok, cert, st


if __name__ == '__main__':
    chart = int(sys.argv[1]); lp = sys.argv[2] == 'lp'; D = int(sys.argv[3]); limit = int(sys.argv[4])
    out = sys.argv[5]
    prob = make(chart, lp)
    B = nonshort.root_box()
    tasks = [(chart, lp, p, b, limit) for p, b in top_split(prob, B, D)]
    only = os.environ.get('ONLY')
    if only:
        keep = [tuple(int(ch) for ch in o) for o in only.split(',')]
        tasks = [t for t in tasks if t[2] in keep]
    t0 = time.time()
    res = []
    with mp.Pool(int(os.environ.get('NPROC', '18'))) as pool:
        for r in pool.imap_unordered(work, tasks):
            res.append(r)
            p, ok, c, st = r
            print(len(res), p, ok, st, flush=True)
    tot = {}
    for p, ok, c, st in res:
        for k, v in st.items():
            if isinstance(v, (int, float)) and k != 'maxdepth':
                tot[k] = tot.get(k, 0) + v
    tot['maxdepth'] = max(st.get('maxdepth', 0) for _, _, _, st in res)
    tot['unresolved_tasks'] = sum(1 for r in res if not r[1])
    print('TOTAL', tot, 'wall', time.time() - t0)
    pickle.dump(res, open(out, 'wb'))
