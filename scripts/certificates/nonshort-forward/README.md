# Generators of the certificates for the forward successor of case M2

These Python scripts (sympy, fractions) generate the Lean files
`SmoothedOctagon/Exclusion/Mixed/Nonshort/Forward/{Bernstein,Bernstein/LowDegree,*Signs}.lean` and the
link identities of `Nonshort/Forward/SmallGap/EnvelopeCasimir.lean` for
`m2_forward_exclusion`; `LowRatio.lean`, `LargeGap.lean`, and the analytic
`SmallGap/NormDerivative.lean` are written by hand. The small-gap ratio bound follows from
concavity and elementary endpoint estimates in `SmallGap/Chi*.lean`. The event-factor comparison
uses the boundary-gap inequality in `EventFactor/Barrier.lean` and completion of a square.
Lean re-checks every identity
(`ring`, `linear_combination`, `field_simp`); nothing computed here is trusted.

* `model.py`, `qe.py`: the normalized residual `N`, the cleared transport part and the combined
  residual; the event-factor elimination quantities.
* `lr.py`, `sg2.py`: the polynomials to certify (written as pickles).
* `plan3.py`, `plan4.py`, `gen4.py`, `gen5.py`: nested Bernstein certificates for gap and ratio
  intervals, using generic lemmas with abstract coefficients and univariate subdivision.
* `mk5.py` plans/emits a certificate job; `writer.py`, `writer2.py` write `Bernstein*.lean` and the `*Signs.lean` certificate modules.
* `nums.py`, `nums2.py`: cleared numerators used by the link proofs.
* `links.py`: helpers for the link identities. `mk_env_file.py` updates the Casimir-excess
  link identity in `SmallGap/EnvelopeCasimir.lean`.
* `phys.py`, `norm.py`, `chk_*.py`: numerical checks of the normalization identities (transport
  identity for `𝒯_*`, Casimir on the stationary line, slope and diagonal identities).

Run from this directory, in order:
`python3 lr.py; python3 sg2.py; python3 nums.py; python3 nums2.py;`
`python3 mk5.py nsfCLRb nsfCPn; python3 writer.py nsfCLRb;`
`python3 writer2.py; python3 mk_env_file.py`.
