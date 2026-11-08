"""Regenerate every generated module of the heavy leaves `hs4_floor_box` and `hs6_B_endpoint`.

usage: python3 gen_all.py OUTDIR   (then compare with SmoothedOctagon/Exclusion/Mixed/ShortHand/Heavy/)
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bern_lemmas, s6gen, s4gen, s4face, s4claims, s4ndefs
import sympy as sp

def main(out):
    here = os.path.dirname(os.path.abspath(__file__))
    s = bern_lemmas.module([14, 24], "", "Heavy H-S leaves: generic Bernstein lemmas (degrees 14, 24)")
    open(f"{out}/S6Bern.lean", "w").write(s)
    s = bern_lemmas.module([5, 6, 7, 8, 9, 10, 19], "", "Heavy H-S leaves: generic Bernstein lemmas (degrees 5-10, 19)")
    s = s.replace("public import Mathlib.Basic.Real.Basic\n",
                  "public import SmoothedOctagon.Exclusion.Mixed.ShortHand.Heavy.S6Bern\n", 1)
    s = s.replace("Degrees: 5, 6, 7, 8, 9, 10, 19.", "Degrees: 5, 6, 7, 8, 9, 10, 19 (degrees 14 and 24 are in `S6Bern`).")
    open(f"{out}/S4Bern.lean", "w").write(s)
    for e in (sp.Rational(13, 5), sp.Rational(3)):
        M, C, ny, nd = s6gen.coeffs(e)
        t = s6gen.tag(e)
        open(f"{out}/S6Id{t}.lean", "w").write(s6gen.emit_id(e, M, C, ny, nd))
        open(f"{out}/S6Pos{t}.lean", "w").write(s6gen.emit_pos(e, M, C, ny, nd))
    nd = s4ndefs.emit('Phi') + "\n" + s4ndefs.emit('Psi')
    open(f"{out}/S4Surr.lean", "w").write(open(f"{here}/S4Surr_head.lean.in").read() + nd +
                                          open(f"{here}/S4Surr_tail.lean.in").read())
    for face in ('A', 'B'):
        for which in ('Phi', 'Psi'):
            C, nx, nw, n_, d_, kk, LL = s4gen.face_poly(face, which)
            tag = f"{which}{face}"
            open(f"{out}/S4Id{tag}.lean", "w").write(s4gen.emit_id(face, which, C, nx, nw, n_, d_, kk, LL))
            open(f"{out}/S4Pos{tag}.lean", "w").write(s4gen.emit_pos(face, which, C, nx, nw))
    out_face = [s4face.HEAD]
    for face in ('A', 'B'):
        for which in ('Phi', 'Psi'):
            out_face.append(s4face.face_thm(face, which))
    out_face.append("end SmoothedOctagon\n")
    open(f"{out}/S4Face.lean", "w").write("\n".join(out_face))
    s4claims.emit(f"{out}/S4Beta1.lean")

if __name__ == "__main__":
    main(sys.argv[1])
