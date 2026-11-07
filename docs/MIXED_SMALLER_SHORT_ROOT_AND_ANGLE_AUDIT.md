# Independent hand review of the short-side root and angle reduction

Date: 2026-11-07 UTC. Internal mathematical review of
[MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md).
The displayed analytic reductions are accepted. The four resulting
boundary faces remain unexcluded.

## Root comparison and determinant control

The fixed actual outer root has the same geometry, incoming norm and
root parameter throughout. Its coefficient of the opposite norm is
strictly positive on the full comparison interval. Implicit
differentiation therefore gives each of the four displayed derivative
identities. In particular, the opposite pairing increases and the
outer norm decreases; its descending-root ceiling survives.

The upper bound for the outer pairing follows from the fixed root
identity and the two preserved incident ceilings. Its positive bracket
proves that the squared Casimir decreases. No sign of the bridge
diagonal or of `1-tau*d` is assumed.

The review specifically checked ellipticity rather than inferring it
from the upper cap. The initial lower bound `E>-23/16`, the monotonicity
of E, and the central upper bound `E<=3rho<3/7` imply the displayed
strict determinant lower bound while both norms stay at least `3/4`.
Thus no missing zero-determinant stopping face is needed. The stronger
whole-period lower Casimir bound is deliberately dropped after the
comparison. The four listed stopping faces are exhaustive because the
root solution is smooth on a compact interval and `t=r` is one of
its endpoints.

## Physical matrix and circle formula

The positive-matrix decomposition agrees entry by entry with the
physical endpoint trace formulas: its numerator has entries
`-3*h21`, `-sqrt(3)*h11`, and `h12`. The two vector columns have
determinant `-2sqrt(3)(1-rho)`; the Gram determinant and
`kappa^2=12Gamma` give `det H=1`. Positive definiteness follows from
the separately established determinant lower bound and positive u.

The chosen unit vector annihilates the second column and gives exactly
`s=3u/(2kappa U(r))`. Every positive determinant-one matrix with that
entry has the displayed one-real-parameter form. Maximizing over the
entire real parameter is an enlargement of the actual covector domain.

Multiplication of the triangular matrix gives the exact complex quotient
in the theorem. Its image is the stated circle except possibly its
limiting point, which suffices for the supremal angle bound. The
identity `Re(V conjugate(D0))=1-|V|^2` follows directly from `det M=1`.
It proves that each filled disk, and the limiting disk containing all
of them, avoids the origin.

The common branch is fixed by the initial actual angle in `(0,pi/3)`.
The disk centres differ by exactly the difference of radii, giving
nested disks and a nondecreasing supremal angle as s increases. This
handles possible principal-argument cuts without assigning an artificial
point an actual-period angle condition.

## Necessary cost bound and limitations

The physical bridge geometry, equal-secant norm, cost and relative
frame are fixed along the comparison. The new angle bound keeps the
actual incoming norm and positive Casimir and maximizes over the other
matrix parameter. Its relaxed completion cost is nondecreasing with
kappa, so the decreasing-Casimir root comparison preserves its
necessary upper cost inequality as well as the upper Casimir cap.

The argument constructs a scalar relaxation, not a competing physical
trajectory or a new PMP lift for the whole period. It does not preserve
all middle-switch constraints or the original lower Casimir bound.
Before any face is excluded, its full enlarged domain must be checked;
the reduction by itself does not assert that those face domains are
empty or supply a hand proof of H-S.
