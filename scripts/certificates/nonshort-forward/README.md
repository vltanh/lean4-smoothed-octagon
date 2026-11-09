# Generators of the certificates for the M2 forward-successor hand theorem

These Python scripts (sympy, fractions) generated the Lean files
`SmoothedOctagon/Exclusion/Mixed/FwdHand/{Bern,Bern2,Cert*}.lean` and the region files with link
identities `FwdHand/{LowRatio,LargeGap,LargeGapLink,Chi,QElim,Envelope}.lean` for
`MIXED_NONSHORT_FORWARD_HAND_EXCLUSION` (`m2_forward_hand`). Lean re-checks every identity
(`ring`, `linear_combination`, `field_simp`); nothing computed here is trusted.

* `model.py`, `qe.py`: the normalized residual `N`, the cleared transport part and the combined
  residual; the event-factor elimination quantities.
* `lr.py`, `lg.py`, `sg.py`, `sg2.py`, `qe2.py`: the polynomials to certify (written as pickles).
* `plan3.py`, `plan4.py`, `gen4.py`, `gen5.py`: nested Bernstein certificates (event-factor level
  and gap level through generic lemmas with abstract coefficients, ratio level by univariate
  certificates with subdivision).
* `mk5.py` plans/emits a certificate job; `writer.py`, `writer2.py` write `Bern*.lean`, `Cert*.lean`.
* `nums.py`, `nums2.py`: cleared numerators used by the link proofs; `links.py`,
  `mk_*_file.py`: the region files.
* `phys.py`, `norm.py`, `chk_*.py`: numerical checks of the normalization identities (transport
  identity for `𝒯_*`, Casimir on the stationary line, slope and diagonal identities).

Run from this directory, in order:
`python3 lr.py; python3 lg.py; python3 sg.py; python3 sg2.py; python3 qe2.py; python3 nums.py;`
`python3 nums2.py; python3 mk5.py fhCLRa fhCLRb fhCLGa fhCLGb fhCLGc fhCLGd fhCChi fhCQD fhCQC`
`fhCEn fhCPn; python3 writer.py fhCLRa,fhCLRb,fhCLGa,fhCLGb,fhCLGc,fhCLGd; python3 writer2.py;`
`python3 mk_lr_file.py; python3 mk_lg_file.py; python3 mk_chi_file.py; python3 mk_qe_file.py;`
`python3 mk_env_file.py`.
