import sys, pickle, random, collections
import run_ss, smaller, expr, fx, certemit
res = pickle.load(open(sys.argv[1], 'rb')); per = int(sys.argv[2])
prob = run_ss.make(True)
B0 = smaller.root_box()
found = collections.defaultdict(list)
anyboxes = []
def walk(c, B):
    if c[0] == 'split':
        j = c[1]; lo, hi = B[j]; m = (lo + hi) >> 1
        BL = list(B); BL[j] = (lo, m); BR = list(B); BR[j] = (m, hi)
        walk(c[2], BL); walk(c[3], BR); return
    key = 'R' if c[0] == 'R' else ('S' if len(c[1]) == 1 else 'L')
    if len(found[key]) < 2000: found[key].append((B, c))
    if len(anyboxes) < 20000: anyboxes.append(B)
for p, ok, c, st in res:
    if not ok: continue
    B = B0
    for bit in p:
        j = prob.split_axis(B); lo, hi = B[j]; m = (lo + hi) >> 1
        B = list(B); B[j] = (lo, m) if bit == 0 else (m, hi)
    walk(c, B)
f, fn = smaller.build()
roots = [x.i for x in f]
random.seed(1)
out = ['module', '', 'public import SmoothedOctagon.Interval.Bench.SsRes', '', '@[expose] public section', '',
       'namespace SmoothedOctagon.Interval.Bench', 'set_option profiler true']
for k in ['R', 'S', 'L']:
    sel = random.sample(found[k], min(per, len(found[k])))
    for B, c in sel: assert certemit.pycheck(roots, B, c)
    items = ', '.join(f'({certemit.lean_box(B)}, {certemit.lean_cert(c)})' for B, c in sel)
    out.append(f'noncomputable def LT_{k} : List (List Ival × Cert) := [{items}]')
    out.append(f'theorem TT_{k} : (LT_{k}.all fun p => check ss_fs [] p.1 p.2) = true := by decide +kernel')
    print(k, len(found[k]), file=sys.stderr)
# forced f27 slope evaluations on boxes where it is defined
f27 = roots[27]
ok = [B for B in anyboxes if expr.evalS(B, f27, {}) is not None]
print('f27 defined on', len(ok), 'of', len(anyboxes), file=sys.stderr)
sel = random.sample(ok, min(per, len(ok)))
out.append('noncomputable def LT_f27 : List (List Ival) := [' + ', '.join(certemit.lean_box(B) for B in sel) + ']')
out.append('theorem TT_f27 : (LT_f27.all fun B => (ss_f27.evalS B).elim false fun s => zle (Slope.bound B s).lo (Slope.bound B s).hi && zle s.r.lo s.r.hi) = true := by decide +kernel')
out.append('theorem TT_f27R : (LT_f27.all fun B => (ss_f27.evalR B).elim false fun I => zle I.lo I.hi) = true := by decide +kernel')
out.append('end SmoothedOctagon.Interval.Bench')
print('\n'.join(out))
