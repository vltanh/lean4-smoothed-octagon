"""Kernel-time estimate of a search result from measured per-leaf costs (seconds)."""
import sys, pickle, collections, os
import run
S_COST = {'g7': 0.16, 'g10': 0.047, 'g9': 0.009, 'g8': 0.009, 'tau': 0.324, 'negExcess': 0.28,
          'negEndpointExcess': 0.36}
R_COST = {'g7': 0.048, 'tau': 0.06, 'negExcess': 0.055, 'negEndpointExcess': 0.07, 'g10': 0.015}
def s_cost(n): return S_COST.get(n, 0.01)
def r_cost(n): return R_COST.get(n, 0.003)
res = pickle.load(open(sys.argv[1], 'rb')); chart = int(sys.argv[2])
prob = run.make(chart, True)
tot = collections.Counter(); cnt = collections.Counter()
def walk(c):
    if c[0] == 'split':
        walk(c[2]); walk(c[3]); return
    if c[0] == 'R':
        n = prob.names[c[1]]; cnt['R'] += 1; tot['R'] += r_cost(n)
    elif len(c[1]) == 1:
        n = prob.names[c[1][0][0]]; cnt['S'] += 1; tot['S'] += s_cost(n)
    else:
        cnt['L'] += 1; tot['L'] += sum(s_cost(prob.names[k]) for k, _ in c[1]) + 0.02
nodes = 0; unresolved = 0
for p, ok, c, st in res:
    nodes += st.get('nodes', 0)
    if ok: walk(c)
    else: unresolved += 1
leaves = sum(cnt.values())
T = sum(tot.values())
print(f'{sys.argv[1]}: nodes {nodes} leaves {leaves} (R {cnt["R"]}, S {cnt["S"]}, L {cnt["L"]}), '
      f'unresolved tasks {unresolved}; est kernel {T:.0f} s = {T/3600:.2f} h '
      f'(R {tot["R"]:.0f}, S {tot["S"]:.0f}, L {tot["L"]:.0f}); {T/max(leaves,1)*1000:.0f} ms/leaf')
