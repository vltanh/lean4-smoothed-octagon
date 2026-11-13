# Smaller-nonshort forward certificates

These Python scripts (sympy, fractions) generate the remaining certificate modules in
`SmoothedOctagon/Exclusion/Mixed/Nonshort/Forward`. Lean checks the identities with `ring`,
`linear_combination` and `field_simp`.

The small-gap estimates are proved analytically: the ratio bound uses concavity and endpoint
estimates in `SmallGap/Chi*.lean`; the event comparison uses the boundary gap in
`EventFactor/Barrier.lean`; and the envelope bound uses the order imbalance in
`SmallGap/EnvelopeBound.lean`.

* `model.py`, `qe.py`: the normalized residual, transport and event-factor quantities.
* `lr.py`: the remaining low-ratio polynomials, written as pickles.
* `plan3.py`, `plan4.py`, `gen4.py`, `gen5.py`: nested Bernstein certificates for gap and ratio
  intervals, with abstract coefficients and univariate subdivision.
* `mk5.py`, `writer.py`: plan and emit the remaining low-ratio order-face certificate.
* `nums.py`, `links.py`: cleared numerators and helpers for the link identities.
* `phys.py`, `norm.py`, `chk_*.py`: numerical checks of the normalization identities.

For the low-ratio order face, run from this directory, in order:
`python3 lr.py; python3 nums.py; python3 mk5.py nsfCLRb; python3 writer.py nsfCLRb`.
