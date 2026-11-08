# Independent audit of nonpositive-diagonal scale continuation

Date: 2026-11-07 UTC. Reviewer: root agent, independently of the author.

I read the full nonpositive-diagonal note and checked its exact identities.
All thirteen exact checks pass. The argument includes the truncated
maximum for w<=3/4, including negative auxiliary w, and passes the hand
audit without correction.

The maximum on [2,T] is unique and lies below T whenever it is positive
and R(T)<0. Its ordinary and truncated formulas have matching first
derivatives at w=3/4. A root between the maximum and T therefore supplies
r,t<1/2, rho_A<rt, and w<=U(t) in both norm branches. The reverse-centre
upper bound E_L<3rho_A follows from the exact root equation; it is not an
extra condition that could fail during continuation.

The bound rho_A<1/4 is exactly equivalent to
1-rho-3alpha^2 rho>0. The lower bound on F consequently has the stated
sign. In the derivative split, the coefficient of F determines which
bound is allowed, and both branches are handled with the correct
inequality direction. The common positive base estimate uses
Q>2alpha^2>2sigma; negative w only strengthens its first inequality.

The upper-endpoint theorem applies on the actual strengthened-order
path. It excludes a maximum at T throughout the comparison. Strict
increase of the positive maximum excludes an exit through zero, and
T=2 would itself make the maximum R(T)<0. Thus only the central value
is required to complete this sign branch. The central value is proved
separately; this note does not silently assume a trajectory-preserving
variation or full endpoints at intermediate scalar points.

No Casimir division, endpoint rank, Lean, Lake, typechecking, CI, floating
sign assertion, or growing word-length catalogue is used in this audit.
