# Independent audit of the all-sign central convex-chord face

Date: 2026-11-07 UTC. Reviewer: `normality_audit`.

The theorem in `MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL_FACE.md` passes independent
review. This replaces the earlier positive-diagonal chord face with
the strengthened genuine two-secant order; the norm and root interval
scope remain as stated.

The convex chord, nonpositive logarithm coefficient, cubic logarithm
lower bound and resulting rational upper bound are unchanged from the
previously audited central-face calculation. I rechecked that raising
the norms occurs only after obtaining an affine scalar upper bound;
the raised point need not remain in the original root interval. For
`d<=0`, the newly added physical-norm coefficient is positive term by
term. For `d>0`, the earlier `d_max` calculation and its strict sign
continue to apply. The other norm coefficient is positive for either
diagonal sign.

I independently checked the strengthened-order integration and its
new parametrization. The identity `G=B(P-2Q)` has exactly the
claimed positive clearing factor. Thus the polynomial multiplier in
the new certificate uses only the actual central `T>=2` constraint;
there is no hidden condition on `D`.

All ten exact checks pass. I additionally read all 13,348 unique
positive entries in the literal CSV and checked both strict reserve
coefficients, 29720334827520 at `j^3` and 6129819058176 at `j^3*z^5`.
The three displayed negative coefficients of the independently
reconstructed numerator are exactly -75621740838912,
-41938694701056, and -59431496712192 at the stated monomials.
The complete integer identity with its two displayed `G` multipliers
holds, and all remainder coefficients are positive.

The upper strengthened-order boundary remains strict: after dividing
by `z^5`, the generator term is nonnegative, the second reserve gives
a positive numerator, and `B^5/z^5` tends to `(7+2x)^5>0`. The
`alpha=1` branch is already covered at `z=0`. The scalar face is not
claimed to preserve the original trajectory or its covector; the
same-lift transport identities are used correctly at actual data.

No mathematical correction was required. The theorem covers the
central zero-factor face with `3/4<=w<=U(1/T)`, for both signs of
the bridge diagonal. It does not cover the truncated `w<3/4` central
value, and the text explicitly prevents extrapolating the chord into
that region. No complete short-bridge or M2 exclusion is asserted.

No Lean, Lake, typechecking, CI, floating sign test, or growing
word-length catalogue was used in this audit.
