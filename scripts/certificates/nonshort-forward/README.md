# Generators of the certificates for the forward successor of case M2

These Python scripts (sympy, fractions) generated the Lean files
`SmoothedOctagon/Exclusion/Mixed/Nonshort/Forward/{Bernstein,Bernstein/LowDegree,*Signs}.lean` and the
region files with link identities `Nonshort/Forward/{LowRatio,LargeGap,SmallGap/Chi,EventFactor,
SmallGap/EnvelopeCasimir}.lean` for `m2_forward_exclusion`. Lean re-checks every identity
(`ring`, `linear_combination`, `field_simp`); nothing computed here is trusted.

* `model.py`, `qe.py`: the normalized residual `N`, the cleared transport part and the combined
  residual; the event-factor elimination quantities.
* `lr.py`, `lg.py`, `sg.py`, `sg2.py`, `qe2.py`: the polynomials to certify (written as pickles).
* `plan3.py`, `plan4.py`, `gen4.py`, `gen5.py`: nested Bernstein certificates (event-factor level
  and gap level through generic lemmas with abstract coefficients, ratio level by univariate
  certificates with subdivision).
* `mk5.py` plans/emits a certificate job; `writer.py`, `writer2.py` write `Bernstein*.lean` and the `*Signs.lean` certificate modules.
* `nums.py`, `nums2.py`: cleared numerators used by the link proofs; `links.py`,
  `mk_*_file.py`: the region files.
* `phys.py`, `norm.py`, `chk_*.py`: numerical checks of the normalization identities (transport
  identity for `𝒯_*`, Casimir on the stationary line, slope and diagonal identities).

Run from this directory, in order:
`python3 lr.py; python3 lg.py; python3 sg.py; python3 sg2.py; python3 qe2.py; python3 nums.py;`
`python3 nums2.py; python3 mk5.py nsfCLRa nsfCLRb nsfCLGa nsfCLGb nsfCLGc nsfCLGd nsfCChi nsfCQD nsfCQC`
`nsfCEn nsfCPn; python3 writer.py nsfCLRa,nsfCLRb,nsfCLGa,nsfCLGb,nsfCLGc,nsfCLGd; python3 writer2.py;`
`python3 mk_lr_file.py; python3 mk_lg_file.py; python3 mk_chi_file.py; python3 mk_qe_file.py;`
`python3 mk_env_file.py`.
