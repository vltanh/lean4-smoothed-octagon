# Independent review of the factor-free forward Casimir sign

Date: 2026-11-08 UTC. Internal independent mathematical review of
[MIXED_NONSHORT_FORWARD_ENVELOPE_CASIMIR_SIGN](MIXED_NONSHORT_FORWARD_ENVELOPE_CASIMIR_SIGN.md).
No Lean, Lake, typechecking, CI or interval cover was run.

**Acceptance:** the displayed scalar theorem is proved on its complete
closed domain

\[
1/3\le t\le2/5,\qquad0\le j\le1/30,
\qquad1\le k\le31/30,
\qquad3/4\le v\le V.
\]

The calculus directions, positive denominator multipliers, complete
coefficient parts, weighted bounds, concavity variable, both endpoint
identities, and strict signs are accepted. The comparison does not
transfer a physical Casimir cap to an artificial central ceiling.
Its application to every actual forward window remains conditional on
the required ratio bounds and actual Casimir monotonicity hypotheses.

## 1. Scalar definitions and the norm direction

I reconstructed the function from the displayed definitions of
\(p,W,Y,B,s,V,g,H,w_U,a_q,b_q,h_1\), without using a stored
polynomial from the author. In particular the function being compared is

\[
N(v)=4B^2v w_U-[B(h_1+v-g)]^2.
\]

Writing \(P_v=Y(k/t+Y)>0\) and \(D(v)=B(h_1+v-g)\), direct
differentiation gives precisely

\[
D'(v)=B(1+W/p)+P_v/(pW),
\qquad N''(v)=8P_v-2[D'(v)]^2.
\]

All summands of \(D'(v)\) are positive. The AM--GM comparison is
strict in the needed direction:

\[
[D'(v)]^2\ge4B(1+W/p)P_v/(pW)>4P_v,
\]

because \(B=p^2+(k-t^2)>p^2\), and
\(p^2(1+W/p)/(pW)=1+p/W>1\). Thus \(N''<0\) throughout the
whole domain. Once \(N'(3/4)<0\) is proved, N strictly decreases
for every \(v\ge3/4\). Raising the incoming norm to its explicit
upper bound V therefore lowers N, with no missing upper-endpoint or
clipping case. If a parameter choice has \(V<3/4\), the stated
v interval is empty; no implication is inferred from such a point.

The bound \(v<V\) for the original incoming secant uses the displayed
one-variable logarithm derivative, not a numerical fit.

## 2. The norm-derivative sign

The factor
\(2t^2p^2W^3\) in the definition of E is strictly positive and
clears all denominators. After
\(t=2/5-A\), \(x=1/5+2A+J\), \(k=1+Z\), the additional
factor \(5^{10}\) produces exactly the integer polynomial stated
in the note. Its constant is 6465474.

The first Appendix A table is the entire absolute negative coefficient
part of that polynomial, including all rows involving Z and Z squared.
Its weighted sums at \(A=1/15,J=Z=1/30\) are the three fractions
printed in Section 2. Their total is exactly

\[
787831672153/787320<6465474.
\]

Since \(A,J,Z\) are nonnegative, every negative monomial is bounded
below by its negative coefficient times
\(15^{-i}30^{-m-n}\), while every omitted monomial is nonnegative.
This gives E>0 at every point, including the boundary. Consequently
\(N'(3/4)<0\) and \(N(v)\ge N(V)\) have the correct directions.
There is no required interval replay or unlisted coefficient sign.

## 3. The cleared Casimir difference and its concavity

The multiplier

\[
3125t^2p^2W^4(x^2+6x+6)^2
\]

is positive and clears all denominators in
\(N(V)-16(k-t^2)^2(9193/50000)\). Thus positivity of P is
equivalent to the desired squared-Casimir comparison. The subsequent
\(5^{16}\) normalization and the simultaneous substitutions in
A,J,Z are correct.

The constant coefficient of \(\widehat P_{AA}\) is
\(-20842670556105750\). The second Appendix A table is its entire
positive nonconstant coefficient part. Its three weighted sums agree
with those in Section 3 and are, respectively, less than
\(1/7,1/25,1/50000\) of the absolute constant. The sum of these
three bounds is less than one fifth. Dropping the negative
nonconstant terms consequently proves strict concavity throughout
the closed box.

The derivative is with respect to A at fixed J,Z. It therefore follows
the necessary relation \(x=1-2t+j\), rather than varying t while
silently fixing x. A concave polynomial in A on \([0,1/15]\)
is bounded below by the smaller of its two endpoint values; no
stationary A minimum remains to be checked.

## 4. Both complete endpoint signs

I independently reconstructed both endpoint identities, including the
positive multiplier
\(129140163/305175781250\) in the \(A=1/15\) identity.
Both tables contain all fourteen powers of J, and all three powers
of Z that occur. Their coefficients agree with the defining polynomial.

Every constant-in-Z coefficient a is strictly positive. Every linear
coefficient b is nonnegative. For each negative quadratic coefficient c,
the printed integers satisfy \(30b+c>0\). Because
\(0\le Z\le1/30\), the inequality

\[
cZ^2\ge cZ/30\qquad(c<0)
\]

has the direction used in the proof. Hence every row is strictly
positive, and the constant-in-J row remains strictly positive even
at J=0. The proof covers Z=0, Z=1/30 and both A endpoints without
an appeal to continuity from an open subdomain.

It follows that P>0 on the entire domain. The strict sign survives
all positive multipliers and the preceding lowering of N, proving
the scalar conclusion above the exact cap \(9193/50000\).

## 5. The actual-period interface remains explicit

The scalar formula uses the diagonal from the forward stationary line
at the central upper-envelope norm. The actual diagonal at that norm
must not be replaced by the central ceiling diagonal merely because
both use \(w_U\). The note keeps these quantities distinct.

The [factor-elimination theorem](MIXED_NONSHORT_FORWARD_Q_ELIMINATION.md)
supplies the separate inequality

\[
h(q)-h(1)\le F_{p/W}(q)-g
\]

on its stated ratio domain. It uses the original incoming floor to
bound h at the comparison norm. To square that upper bound in the
physical application, the diagonal at \(w_U\) must be positive.
The cited actual Casimir-monotonicity result supplies this through its
positive-diagonal conclusion and the increasing stationary diagonal.
Those hypotheses still have to hold for the actual original data.

Once the common order gives \(k<1+j\), a proved \(j\le1/30\)
would supply the shape interval here. This audit does not prove the
missing t or j restrictions or the additional ratio hypothesis in
actual Casimir monotonicity. It therefore accepts the scalar result
and its stated conditional role, without declaring H-N-forward closed.

## 6. Supplementary identity reconstruction

As a transcription safeguard, exact symbolic reconstruction checked
the two differentiation identities, the denominator-clearing factors,
both integer normalizations, both complete coefficient parts, all six
weighted sums, both endpoint identities and all twenty-eight endpoint
row inequalities. These checks match the hand expressions above.
They are supplementary: the sign proof consists of the displayed
finite identities, a single rational power bound, concavity, and
\(Z^2\le Z/30\), not an executable sign verdict.
