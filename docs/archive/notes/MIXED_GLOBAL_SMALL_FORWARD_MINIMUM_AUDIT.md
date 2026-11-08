# Audit of the small forward-minimum theorem

Date: 2026-11-07 UTC. Independent reconstruction and internal hand
review of
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md).
No Lean, Lake, typechecking, or CI. This is not kernel validation or
outside peer review.

## Verdict and precise scope

The theorem passes. In an actual finite normal closed period, five
consecutive active margins \((p,b,a,c,d)\), with all four intervening
switches forward and the three interior indices distinct, cannot satisfy

\[
0<a\le\min(p,b,c,d),\qquad a^2\le4/3
\]

when the three interior arcs have positive durations. The proof uses
the actual same normal primary multiplier, the common cyclic action,
and the two genuine exterior missing-control inequalities. It requires
neither ellipticity, a Casimir or cost bound, endpoint-rank inversion,
nor an implicit-function argument.

The proof now bounds the full hard-face residual directly. A proposed
monotonicity in its own factor was found to be false near the star
boundary and is not used in the final note or certificate.

## 1. Actual normal multiplier and the three stationarity equations

I checked the prefix-frame conjugations, the three forward frame
columns, and their contractions with the same unrestricted real
traceless primary multiplier. In the middle frame its coordinates are

\[
U_a=\begin{pmatrix}KE/16&-s^2u/8\\
K^2v/(8s^2)&-KE/16\end{pmatrix}.
\]

This is a linear parametrization, not an assumption on its determinant
or component. The central equation is exactly
\(su+tv-aE=A\). Eliminating \(E\) gives both displayed rows
of (7), including the identities (9) and its reflection. The four
coefficients \(M_{ij}\) are positive by the actual strict-star
inequalities and positive factors. Only one row is used after
reflection; its determinant is never inverted.

The cyclic-action stationarity identity being used is the normal PMP
boundary identity from the state-closed margin family. Its initial
state and final state terms cancel by actual twisted transversality,
and the remaining frame term uses the actual primary covector. Using
that identity does not require the later ellipticity conclusion of
the source note. A window crossing the seam is handled by rebasing
the same period and conjugating the same covector.

## 2. Exterior gaps: independent physical sign check

I reconstructed the left missing Hamiltonian from the physical state
and vector fields, separately from the reduced algebra. Rotate the
new active control at \(p\to b\) to zero and write \(s_0=p+b\).
In triangular coordinates the state matrix is

\[
X^{\rm tri}=\begin{pmatrix}
-b/2&s_0/2\\-K_b/(2s_0)&b/2
\end{pmatrix}.
\]

With the common physical normal normalization \(\lambda=-1\), the
group part and running cost combine to

\[
H_{\rm common}=-\frac{\sqrt3}{2s_0}G_L.
\]

Solving the two incident zero-Hamiltonian equations gives

\[
H_1=\frac8{4-pb}H_{\rm common}
=-\frac{4\sqrt3}{(p+b)(4-pb)}G_L.
\]

Thus maximizing PMP gives exactly \(G_L\ge0\). All denominators
are positive at this actual exterior switch. The right endpoint has
the reflected identity with \(c,d\) and the same normal lift.

The exact elimination of the left stationarity residual is

\[
G_L=-\frac{hK_b^2}{4s}H_b
 +\frac{K_b^2(h-1)}4\{u-F_{b/s}(h)\}.
\]

Since \(H_b=0\), this proves the stated norm floor without dividing
by a costate component or assuming an inactive gap is strict. The
right floor follows by the same calculation. Missing-control triple
ties are therefore retained.

The exterior state inequalities \(pb<4\), \(cd<4\) are essential
here and also give \(h<(a+b)/b\), \(k<(a+c)/c\). They are now
explicit in (2a), together with the interior inequalities \(ab<4\),
\(ac<4\). The exterior comparisons \(p,d\ge a\) separately
give the lower factor bounds in (3).

## 3. The positive row and reduction of the larger neighbor

The derivatives of \(F_x\), including their continuous limits at
factor one, have the stated signs for \(1/2\le x<1\). Consequently
the opposite floor

\[
V(a,c)=F_{c/(a+c)}\!\left(\max\{1,(a+c)^2/(c^2+4)\}\right)
\]

is continuous and nondecreasing, and dominates
\(U(a/(a+c))\). Positivity of the row coefficients then makes
\(\mathcal E\ge0\) a necessary consequence of PMP.

Reflection exchanges the two exact scalar rows, so choosing \(b\le c\)
does not introduce a different multiplier. I checked
\(M_{12}=\alpha(a+c)-\beta\) and

\[
\partial_c\mathcal E
=\alpha(U-V)-M_{12}\partial_cV\le0.
\]

The scalar comparison remains in \(c\ge b\ge a\), \(ac<4\),
and \(q\ge1\), until either \(q=1\) or \(c=b\).
The coefficient \(M_{12}\) remains positive on the zero-central-factor
face because \(h>1\). The possible nondifferentiable transition
in the maximum defining \(V\) is continuous and has monotone pieces.
No intervening scalar point is asserted to be a PMP trajectory.

## 4. The two elementary boundary signs

On the \(q=1\) comparison face, \((a+c)^2/K_c\le1\), so
\(V=U\). I checked both zero initial values
\(\mathcal E(1)=\mathcal E_h(1)=0\). Also

\[
\mathcal E_{hh}=-\frac{bP(h)}{aK_bh^3},\qquad
P'(h)=2(4-ab)h(3bh-a-b)+aK_b>0.
\]

Here \(P(1)\ge b(b^2-a^2)\ge0\), proving strict negativity
for every actual \(h>1\).

On \(c=b\) with \(H=s^2/K_b\le1\), set \(r=a/s\).
The restriction gives \(q\le1/(2r)\le(1-r)/r\). The function
\(F(q)\) in (19) is therefore nonpositive, and negative for
\(q>1\). I separately derived the two identities (20); both
initial residual and initial slope are nonpositive. The same
strict second-derivative argument proves the result, including
the possible \(q=1\) endpoint.

## 5. Full hard-face rational certificate and displayed tables

I independently substituted \(a=2/\sqrt u\), \(b=c=2z/\sqrt u\)
into the original reduced-model residual. Division by \(a+b\)
gives exactly (H2), with the opposite floor held at \(F_x(H)\).
The coefficient of \(\log q\) is negative; those of \(\log h\)
and \(\log H\) are positive. Both derivative identities (H3)
give the required logarithm bounds, so the displayed rational
replacement is an upper bound throughout the domain.

The change of variables (H4) covers the full hard face, with
\(Y\ge0\), \(R>0\), and \(T\ge0\). Its inverse formulas
are correct. In particular it includes the centroid equality
\(a^2=4/3\) and exterior minimum equality \(h=H\).
The strict exterior star inequality is exactly what makes the
upper endpoint \((1+z)/z\) strict. Every denominator in the
rational bound and in its clearing factors is positive.

An independent regeneration gives the stated degrees and 3,369
negative nonzero coefficients before the final positive factors
are removed. More importantly, I parsed the five actual displayed
tables from the note, retained every row factor, and reconstructed
(H5) from them. Its difference from the regenerated polynomial is
identically zero. The table checks give:

| Polynomial | Degree in \(Y\) | Degree in \(R\) | Positive nonzero coefficients |
|---|---:|---:|---:|
| \(Q_0\) | 7 | 15 | 122 |
| \(Q_1\) | 9 | 18 | 187 |
| \(Q_2\) | 9 | 17 | 178 |
| \(Q_3\) | 9 | 16 | 170 |
| \(Q_4\) | 8 | 14 | 135 |

All omitted coefficients are zero. The coefficient of \(R^3\) in
\(Q_0(0,R)\) is \(1,966,080\). Thus (H5) is strictly negative
even at \(Y=T=0\), since \(R>0\). The full integer tables,
rational expressions, and exact identity supply the finite arithmetic
certificate; a count of sampled signs or coefficients alone is not
the argument.

## 6. Boundaries and the resulting global statement

The actual factors \(h,q,k\) are strictly greater than one.
Factor-one values are used only as continuous scalar comparison
faces. No assertion of a PMP extension through a zero-duration arc
is needed. State-star denominators are strictly positive at every
actual switch. Missing Hamiltonian gaps may vanish, exterior active
margins may equal the middle margin, and the scale may equal
\(a^2=4/3\); those cases are included. No uniform gap or duration
lower bound is inferred as factors approach one.

For a pure-forward period in the remaining domain, the global
minimum therefore has square strictly greater than \(4/3\).
For a mixed period, a reverse centre gives a margin with square
strictly below \(4/3\). The earlier minimum-structure theorem
places any global minimum either in four consecutive forward
switches or at a strict reverse centre. The new result excludes
the former placement, so every mixed global minimum is a reverse
centre, including when the minimum crosses the twisted seam.

This does not place such a centre next to a long forward run,
exclude chains of short bridges, or prove a constrained negative
variation. F and M2 remain open. The completed comparison is a
new necessary global minimum principle with its stated scope.

The supplementary scripts are
`explorations/mixed_global_small_forward_minimum_certificate.py`
and `explorations/global_structure_forward_small_minimum_certificate.py`.
The former checks the common-lift interface and elementary faces;
the latter checks the full hard-face identity against the fixed
integer tables. Their role is exact reproducibility of the
displayed hand certificate.
