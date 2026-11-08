import sys, time, pickle, os, multiprocessing as mp
import run_ss, smaller
if __name__ == '__main__':
    paths = sys.argv[1].split(','); D = int(sys.argv[2]); limit = int(sys.argv[3]); out = sys.argv[4]
    prob = run_ss.make(True)
    tasks = []
    for ps in paths:
        p = tuple(int(ch) for ch in ps)
        B = smaller.root_box()
        for bit in p:
            j = prob.split_axis(B); lo, hi = B[j]; m = (lo + hi) >> 1
            B = list(B); B[j] = (lo, m) if bit == 0 else (m, hi)
        for q, b in run_ss.top_split(prob, B, D):
            tasks.append((True, p + q, b, limit))
    t0 = time.time(); res = []
    with mp.Pool(int(os.environ.get('NPROC', '18'))) as pool:
        for r in pool.imap_unordered(run_ss.work, tasks):
            res.append(r); p, ok, c, st = r
            print(len(res), p, ok, st, flush=True)
    tot = {}
    for p, ok, c, st in res:
        for k, v in st.items():
            if isinstance(v, (int, float)) and k != 'maxdepth':
                tot[k] = tot.get(k, 0) + v
    tot['unresolved_tasks'] = sum(1 for r in res if not r[1])
    print('TOTAL', tot, 'wall', time.time() - t0)
    pickle.dump(res, open(out, 'wb'))
