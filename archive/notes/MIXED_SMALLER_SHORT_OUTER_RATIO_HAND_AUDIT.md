# Audit of the outer terminal sign for the short upper-ratio bound

Date: 2026-11-08 UTC. **Result:** the
[OUTER_RATIO_HAND_SIGN](MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_SIGN.md)
proves the whole outer scalar face for \(13/6\le x\le12/5\),
including every duration and boundary. The reconstruction and the
independent mathematical reading below are accepted. Together
with the central sign it supplies the two scalar endpoints needed by
the accepted variable-floor reduction.

## 1. Actual-to-scalar scope

The starting shape is the actual ordered equal-secants shape with
\(a=\alpha\), \(b=\beta\), \(a^2\ge x(x+2)/6\), and the
strong lower / 9/8 upper order strip. This squared condition is exactly
\(1/7\le q_c\) on the outer endpoint \(q=1/7\).

The simplified w and \(E_L\) formulas are obtained from the original
outer transport by substituting

\[
\rho=\frac1{6a^2+1},\qquad
\lambda=\frac{6a^2+1}{7a^2},\qquad d=\frac D{7a^2}.
\]

For example, \(\lambda^2U(\rho S)\) is precisely
\((M^2-MS+S^2)/(49a^4)\), with \(M=6a^2+1\), and the
transported pairing numerator is the displayed N. No new covector is
introduced.

The incoming norm is raised only after reaching the endpoint with the
original shape fixed, by the positive coefficient proved in the
[variable-floor reduction](MIXED_SMALLER_SHORT_VARIABLE_FLOOR_REDUCTION.md).
The two replacement ceilings are proved for the actual norm. Neither
an incident norm ceiling nor a physical cost or competitive upper
Casimir cap is claimed after replacing that norm or changing shape.

## 2. Duration and the shape split

The exact derivative of the combined scalar is integrated to an upper
linear function in \(\tau-2\). Both possible endpoint values of this
linear function are retained as \(H_0,H_1\). Thus the outgoing
comparison norm may be either above or below 3/4; its actual floor is
not silently transported to a new endpoint.

The split \(a\le3/2\) and \(a\ge3/2\) is exhaustive, including
its common boundary. On the smaller branch the strong order gives
\((b-x)/x<1/5\). The positive incoming integral tail is consequently
at most \((b-x)/1200\), and the Gauss-based bound for \(V(x)\)
gives exactly the stated \(u_s\). On the larger branch, the already
accepted uniform incoming ceiling \(u_v\) is used. No additional
assumption on the small short-gap strip is introduced.

The outer cap gives the affine alpha floor \(a_f=(36x+25)/84\)
by the displayed concave quadratic with endpoint values 46 and 258/5.
The original beta strip lies between the two simple linear-in-a
endpoints established in the central theorem. All shape domains used
later have \(b\le ax\), hence
\(0<2k\le34/35<1\) and \(T>35/17>2\). This checks every logarithm
and duration ordering, including artificial endpoints.

## 3. Smaller-shape comparisons

The alpha derivative is taken at fixed x and
\(c=(b-x)/(a-1)\), with the norm \(u_s\) treated as its full
explicit rational function. Thus it includes all changes of b and
of the incoming ceiling. Its sign is proved on
\(6/5\le a\le3/2\), which contains the entire motion from the
actual smaller alpha down to \(a_f(x)\).

Only after alpha has reached this floor is c increased to
\(c_+(x)=(24x+51)/128\). The proof establishes the c derivative
on that floor exactly; it does not claim beta monotonicity at all
larger alpha values. This avoids a false global monotonicity claim:
the beta derivatives can change sign before alpha is lowered.

Both comparisons use the exact logarithm derivative. The logarithm
majorant is inserted only after the two shape comparisons. The final
two polynomials in x have degrees 14 and 13. Their positive clearing
denominators and all their coefficients after \(x=13/6+X\) are
printed. The sum of all negative coefficients in absolute value is
smaller than the positive constant coefficient; \(0\le X<1\)
therefore proves both signs directly.

## 4. Larger-shape comparisons

On the larger branch the proof directly treats the enlarged rectangle
\(3/2\le a\le12/5\), retaining the whole c interval
\([5/8,7/8]\). It does not move alpha or c while asserting any
physical hypothesis. The simple cubic upper bound for \(\log y\)
is valid throughout by \(y=2k<1\).

After positive denominator clearing, the two polynomials have alpha
degrees six and five. Their exact Bernstein coefficient polynomials
are specified by one finite binomial identity. A centered coefficient
norm in x and c gives thirteen explicit positive lower coefficients,
all printed. At the ends of the alpha interval the Bernstein weights
still sum to one and at least one is one, so strictness includes
\(a=3/2,12/5\). The proof has no unhandled equality or duration
boundary.

## 5. Arithmetic reconstruction and hand-proof boundary

A fresh exact reconstruction started with the original transport
\(\lambda^2v+d^2u-d\lambda E\) and \(2du-\lambda E\), rather
than the simplified numerators used in the construction. It verified:

1. Both alpha derivative polynomial identities and every coefficient
   in their two printed lower polynomials.
2. Both c derivative identities at the affine alpha floor and every
   coefficient in their printed lower polynomials.
3. Both smaller-shape terminal identities and their complete
   one-variable coefficient arrays.
4. Both larger-shape polynomial identities and every one of the
   thirteen printed Bernstein norm lower bounds.
5. Every final integer sign comparison and all existing local links.

All identities agreed exactly. These are transcription checks; the
published proof consists of the displayed factor specifications,
complete finite lower-polynomial arrays and elementary sign arguments.
It does not depend on running a script. In particular, the previous
assertion of bounds on 62,010 transformed coefficients is not a premise.
No Lean, Lake, typechecking or CI was run.

## 6. Consequence

A separate second reading checked the complete transport formulas,
both incoming ceilings and their exact equal-secant scope, the affine
alpha floor, the two duration alternatives, and the enlarged domains
of all four derivatives. The norm rules and all explicit terminal
sign arguments have the required directions. The logarithm is
replaced only where its upper bound is valid; no physical constraint
is transferred to an added shape. This accepts the complete outer
scalar theorem, including every equality boundary.

Every outer positive endpoint from the
variable-floor reduction is excluded on \(x\ge13/6\). Together
with the separately proved central sign, this permits the actual-period
upper-ratio assembly. This audit by itself does not mark H-S or H-A
complete.
