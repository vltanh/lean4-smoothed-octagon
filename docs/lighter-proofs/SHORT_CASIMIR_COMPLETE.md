# Completed extended Casimir derivative replacement (S4)

This assembles the replacements for the six derivative dependencies in
[the original extended Casimir derivative note](../../archive/notes/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md),
equations (4)--(30). The actual
[extended-floor caller](../../archive/notes/MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md)
retains its original conclusion
\[
 \Gamma_{\mathrm{actual}}>1829/10000
 \qquad(2\le x\le13/6,\ 0\le d\le1/19).
\]
Five signs are proved on their original stated domains. The third is
proved after the caller has fixed e=13/5, exactly where that sign is
used. Its former statement on unused e values is not claimed.

## 1. The six signs and their exact comparison domains

Use the unchanged central source functions Phi and Psi, incoming upper
value, and shape substitution
\[
 a=1+ed,\qquad b=x(1+d),\qquad
 2\le x\le13/6,\quad0\le d\le1/19,\quad13/5\le e\le3.
\]
The symbol e is the eta of the archived caller. The new proofs establish:

| Original dependency | Proved sign | Comparison domain | Small replacement |
|---|---|---|---|
| W1 | −Phi_d>27/5000 | Full original box | [First derivatives](SHORT_CASIMIR_FIRST_DERIVATIVES.md), Sections 1--3 |
| W2 | Psi_e/(xd)>0 | Full original box, with its continuous extension at d=0 | [First derivatives](SHORT_CASIMIR_FIRST_DERIVATIVES.md), Sections 4--5 |
| W3 | −Psi_x>11/14000 | e=13/5; all original x,d | [Ratio derivative](SHORT_CASIMIR_RATIO_DERIVATIVE.md) |
| W4 | −Phi_x>1/1750 | d=1/19; all original x,e | [Boundary derivatives](SHORT_CASIMIR_BOUNDARY_DERIVATIVES.md), Sections 1--3 |
| W5 | −Phi_e>0 | x=13/6,d=1/19; all original e | [Boundary derivatives](SHORT_CASIMIR_BOUNDARY_DERIVATIVES.md), Section 4 |
| W6 | −Psi_dd>81/1000 | x=13/6,e=13/5; all original d | [Terminal concavity](SHORT_CASIMIR_TERMINAL_CONCAVITY.md) |

For W2, the identity Psi_e=d Psi_a holds because the incoming ceiling
is independent of e. Hence the quotient is Psi_a/x for d>0 and has the
same positive limit at d=0. The unnormalized derivative is zero there;
no division by d is made at that boundary.

## 2. The unchanged caller closes in its original order

Sections 1--2 of the original floor caller prove, at the original
common covector and actual period,
\[
 \Gamma_{\mathrm{actual}}\ge\min\{\Phi,\Psi\}.
\]
They also justify increasing the original incoming norm to the same
rational upper value used in every replacement above. Those earlier
analytic reductions are unchanged.

For Phi, apply W1 to increase d to 1/19, W4 to increase x to 13/6,
and W5 to increase e to 3. Thus
\[
 \Phi(x,d,e)\ge\Phi(13/6,1/19,3).
\]
For Psi, W2 first decreases e to 13/5. At that fixed e, W3 increases
x to 13/6. W6 then gives concavity in d, so
\[
 \Psi(x,d,e)\ge
 \min\{\Psi(13/6,0,13/5),\Psi(13/6,1/19,13/5)\}.
\]
This is the precise reason that the restricted W3 statement suffices.
The comparisons are between scalar lower bounds. They do not move a
competitive cap, physical cost, genuine root or common covector to an
artificial shape.

## 3. The same three scalar endpoints, with small directed bounds

Each endpoint is Z−log(y)/7, where Z is the rational part of the
unchanged Phi or Psi source. Since 0<y<1 and z=(y−1)/(y+1)<0,
\[
 \log y<2(z+z^3/3+z^5/5).
\]
This follows by integrating the finite geometric identity for
1/(1−z²); the omitted remainder has the sign dictated by z<0.
Put L=−2(z+z³/3+z⁵/5)/7. Direct substitution into the separate source
fractions gives the following directed bounds, each with denominator
100000000:

| Endpoint | y | Strict lower numerator for Z | Strict lower numerator for L | Lower bound minus 1829/10000 |
|---|---|---:|---:|---|
| Phi(13/6,1/19,3) | 103488/134749 | 14527385 | 3770827 | 2053/25000000 |
| Psi(13/6,0,13/5) | 12/19 | 11745465 | 6564620 | 4017/20000000 |
| Psi(13/6,1/19,13/5) | 2524608/3353029 | 14236332 | 4053971 | 303/100000000 |

These are scalar rational evaluations of the printed transport source,
not new polynomial sign certificates. In particular the three margins
are greater than 1/12500, 1/5000 and 3/1000000, respectively, as in the
original caller. This proves the unchanged strict floor for the original
actual covector.

## 4. Expansion and validation boundary

The first proof removes beta through derivative signs and scalar norm
bounds. Its remaining high-degree source is differentiated before
expansion. The boundary proof fixes displacement first, follows a lower
norm curve, and uses two separately concave derivatives and four scalar
corners. The ratio proof first fixes e to its already justified endpoint;
it differentiates its degree-nine and degree-ten sources before any
expansion, then removes displacement before expanding the final boundary.
The last proof specializes both x and e, and separates six elementary
rational terms before bounding their third derivatives.

Every expanded sign identity in these replacements has at most fifty
monomials and total degree at most eight in at most two variables. The
original three-variable D is kept as a degree-two source. Every printed
coefficient and every individually expanded source contribution satisfies
the twelve-digit bound; explicit cancellation or normalization precedes
the expansions where required. All necessary sign polynomials and
rational bounds are printed. The only rational splits are a=11/10
in the first shape-derivative bound and x=25/12 in the boundary Gamma estimate.

Independent source reconstructions check the derivatives, domains,
caller order, printed identities, elementary sign bounds, scalar endpoint
roundings, and individual contribution sizes. Exact symbolic arithmetic
checks transcription; it is not a proof premise. No numerical sampling,
old coefficient table, Lean, Lake, typechecking or CI run establishes any
sign here. Lean source and existing formal certificates are unchanged.
