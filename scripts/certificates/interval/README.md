# Branch-and-bound search for the kernel-checked interval certificates

Python mirror of the Lean evaluator of `SmoothedOctagon/Interval/` (same fixed-point outward
rounding, natural and slope forms, LP-weight leaves): it searches subdivisions and writes
certificates that the Lean checker (`SmoothedOctagon.Interval.Check`, theorem `check_sound`)
verifies by kernel reduction. The scripts are not trusted; only the Lean check is.
