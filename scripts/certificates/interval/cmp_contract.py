import os, sys, time
os.environ['CONTRACT'] = sys.argv[2]
import run_ss, smaller, bnb
prob = run_ss.make(True)
B = smaller.root_box()
for ch in sys.argv[1]:
    j = prob.split_axis(B); lo, hi = B[j]; m = (lo + hi) >> 1
    B = list(B); B[j] = (lo, m) if ch == '0' else (m, hi)
t = time.time()
c, st = bnb.solve(prob, B, depth=len(sys.argv[1]), limit=600000)
print(sys.argv[1], 'CONTRACT', sys.argv[2], st, round(time.time() - t, 1), flush=True)
