# A smaller competitive Casimir ceiling (no large coefficients)

Date: 2026-11-08 UTC. **New independent analytic lemma**, intended to
provide additional slack for future low-coefficient replacements of S1.
It changes no premise of the already accepted hand proof and is not
claimed to replace any existing coefficient sign.

## Theorem

For every **actual competitive noncircular normal period** to which
the [spectral cost--Casimir theorem](GLOBAL_SPECTRAL_COST_CASIMIR.md)
applies, let `C` be its whole-period physical cost and write
\[
\kappa=\sqrt{12\Gamma_{\mathrm{actual}}}.
\]
Then
\[
\boxed{\Gamma_{\mathrm{actual}}<\frac{9191}{50000}
       <\frac{9193}{50000}.}
\tag{1}
\]
The upper bound belongs to the **original conserved common covector**,
not to the scalar Casimir at a shape or scale comparison point.

## Proof with small integers

The exact expression for the octagon cost and the independent
elementary rational bounds in Section 7 of
[the small-shape cost note](MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION.md)
give
\[
A_{\rm oct}<\frac{3126055}{10^6}
           <\frac{312606}{10^5},
\qquad
\pi>\frac{314159265}{10^8}
    >\frac{314159}{10^5}.
\tag{2}
\]
Only those rational estimates for the universal constants are
invoked; this lemma does **not** invoke the small-shape theorem or
its conditional cost conclusion.

For an actual competitive noncircular period,
the cited spectral theorem gives
\[
\frac\pi3(\kappa+3/2)<C\le A_{\rm oct}.
\]
Consequently
\[
\kappa<
\frac{3(312606)}{314159}-\frac32
=\frac{933159}{628318}
<\frac{14852}{10000}.
\tag{3}
\]
The last strict comparison is exactly
\[
14852\cdot628318-933159\cdot10000=188936>0.
\]

As \(\kappa>0\), squaring (3) yields
\[
\Gamma_{\rm actual}
=\frac{\kappa^2}{12}
<\frac{13786369}{75000000}
<\frac{9191}{50000},
\]
where the last positive numerator difference over the common
denominator \(75000000\) is just \(131\). This proves (1).

Compared with the ceiling \(9193/50000\) used by the existing
lower-ratio signs, (1) adds exactly \(1/25000\) of slack. The new
ceiling can be used at the *original* S1 contradiction point.
It is **not** licensed for a deformed scalar endpoint.

## Dependency boundary

This is an independent strengthening of
[HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md), Section 1,
not a replacement for its valid weaker bound. It reuses the spectral
theorem and elementary arithmetic constants, without any of the
S1--S7 ratio, displacement, shear, cost-exclusion, or coefficient
certificates. Its domain is noncircular actual competitive periods,
which includes the smaller-short H-S period being excluded.

For the ongoing low-coefficient rewriting effort, the target at both
S1 terminal scale faces may be weakened from
\[
\Gamma_*-\frac7{96}R_\tau^* >\frac{9193}{50000}
\quad\text{to}\quad
\Gamma_*-\frac7{96}R_\tau^* >\frac{9191}{50000}.
\]
The existing proof already establishes the stronger scalar inequality,
but **its large expansions are not removed by this observation alone**.
An actual replacement needs a new, separately checked proof of the
terminal inequalities with small rational bounds.
