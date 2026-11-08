# Central upper-ratio caller: duration tangent assembly

**Complete hand replacement for S2.1.** Independent source, sign,
domain and size reviews accept the beta comparison, x comparison,
four terminal signs and their assembly below. The original duration
test satisfies the stronger uniform bound \(G_\tau<-1/6000\).

The source obligation is equation (5) of
[the central-ratio note](../../archive/notes/MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_SIGN.md):
\[
G_\tau<0\qquad(13/6\le x\le12/5,\quad 2\le\tau\le T)
\]
on its original central-cap domain and incoming ceiling. The transport
notation \(R,k,T,h\) below is exactly that of
[the beta proof](SHORT_RATIO_CENTRAL_BETA.md), equations (2)--(3).
In particular the incoming norm retains its beta dependence.

## 1. Original statement and harmless shape enlargement

The original domain is
\[
13/6\le x\le12/5,\qquad a\ge1,\qquad a^2\le x(x+2)/6,
\]
\[
x+\frac{8x(a-1)}{9x+8}\le b\le
x+\frac{x(7x+1)(a-1)}{4x^2+11x+1}.
\]
Source Section 2 proves, by a cubic and a quadratic, that it lies in
\[
1\le a\le4/3,\qquad
x+5(a-1)/8\le b\le b_+(x,a):=x+(24x+51)(a-1)/128,
\]
and that \(K-2aB\ge25/36\) on the enlarged rectangle. Consequently
\(T>2\) throughout the scalar comparisons.

The exact source duration expression is
\[
G_\tau=R+(w-1)\tau+\tau^{-1}+\log(\tau k)
                  +(2-7\tau k/4)h,\qquad h=w-3/4.
\tag{1}
\]
The original variable-floor reduction proves incoming-norm
monotonicity before substitution at the actual central endpoint.
The Gauss incoming estimate and the original shape order supply
the rational ceiling used in the beta proof. These elementary
source dependencies and the original actual caller are unchanged.

## 2. A tangent to the duration-dependent sum

The function \(L(\tau)=\log\tau+1/\tau\) is concave on \([2,\infty)\),
since
\[
L''(\tau)=(2-\tau)/\tau^3\le0.
\]
For any chosen \(t\ge2\), its tangent therefore gives
\[
L(\tau)\le\log t+2/t-1+\tau(t-1)/t^2.
\tag{2}
\]
Inserting (2) in (1) leaves an affine function of \(\tau\).
Its maximum on \([2,T]\) occurs at an endpoint, regardless of
the sign of \(h\). Thus
\[
G_\tau\le\max\{F_0,F_1\},                            \tag{3}
\]
where
\[
F_0=R+(4-7k/2)h+4/t-2/t^2-3/2+\log(tk),
\tag{4}
\]
\[
F_1=R+(T+1/4)h+T\{(t-1)/t^2-1/4\}+2/t-1+\log(tk).
\tag{5}
\]
The tangent need not lie in the physical interval \([2,T]\): its
validity follows from concavity on the larger interval \([2,\infty)\).
Choose the continuous piecewise affine tangent location
\[
t(a)=
\begin{cases}
20/3-4a,&1\le a\le7/6,\\
2,&7/6\le a\le4/3.
\end{cases}                                         \tag{6}
\]
It always lies in \([2,8/3]\). There is one rational shape split.

## 3. Beta reduction

The [beta proof](SHORT_RATIO_CENTRAL_BETA.md) proves that both tests
(4)--(5), with the original moving norm, strictly increase in beta
on the whole enlarged rectangle. They can therefore be evaluated
at \(b=b_+(x,a)\). The proof retains the norm pole and differentiates
before expansion; its largest identity has 43 monomials and degree
eight. No original high-degree derivative certificate is a premise.

## 4. The x comparison

After setting \(b=b_+(x,a)\), retain the original incoming ceiling
as a function of x and a. The [x proof](SHORT_RATIO_CENTRAL_X.md)
establishes the two total derivatives
\[
G_x<-1/250,\qquad H_x<-1/2000,
\quad G=R+(4-7k/2)h+\log(2k),
\quad H=R+(T+1/4)h+\log(2k).                         \tag{7}
\]
Its domain is the full rectangle \(13/6\le x\le12/5\),
\(1\le a\le4/3\). In particular it does not require the central
cap to remain true while x decreases.

For (4), the added terms relative to G depend only on a, so
\((F_0)_x=G_x\). For (5), write
\[
F_1=H+T\phi(t)+2/t-1+\log(t/2),\qquad
\phi(t)=-\frac{(t-2)^2}{4t^2}\le0.
\]
The x proof also gives \(T_x>0\). It follows that
\[
(F_1)_x=H_x+T_x\phi(t)\le H_x<0.                    \tag{8}
\]
This applies to both choices in (6), including their common endpoint.
Both tests are therefore bounded above by their values at \(x=13/6\).

The two x estimates use small printed source polynomials, a fully
printed degree-eight comparison polynomial for each derivative, and
an explicit geometric-series remainder. Their finite coefficient
comparisons and remainder bounds are supplied in the
[algebra companion](SHORT_RATIO_CENTRAL_X_ALGEBRA.md).

## 5. Four terminal signs and the original caller

The [terminal proof](SHORT_RATIO_CENTRAL_TERMINALS.md) establishes
\[
F_0(13/6,a),F_1(13/6,a)<-1/6000
\quad(1\le a\le4/3),                                \tag{9}
\]
with the same split and tangent choices in (6). It first raises the
original norm curve to its two explicit affine upper bounds
\[
\widehat u=
\begin{cases}
(38269-288a)/50000,&1\le a\le7/6,\\
(38206-234a)/50000,&7/6\le a\le4/3.
\end{cases}
\]
The direction is legitimate at these scalar points: equation (16)
of the beta proof gives \((F_0)_u=G_u>0\) and
\((F_1)_u=H_u>0\). The terminal proof derives the norm bounds from
convexity of the original reciprocal affine pole and three rational
endpoint comparisons.

It then uses a quadratic upper bound for \(\log(tk)\) and four
printed nine-term polynomials. A scalar recurrence checks each
coefficient rounding, and a positive geometric-series majorant bounds
the analytic remainder. Concavity, convexity or a negative quadratic
proves the signs of the printed polynomials. The coefficient-rounding
error and analytic tail are included before asserting the uniform
margin (9). Every source polynomial and comparison polynomial is
printed in the [terminal algebra](SHORT_RATIO_CENTRAL_TERMINAL_ALGEBRA.md).

The beta comparison, (7)--(9), and (3) now give
\[
\boxed{G_\tau<-1/6000<0}
\]
on the original central-cap domain, with the source's unchanged
incoming ceiling and every \(2\le\tau\le T\). This proves the
original scalar statement (5). The original variable-floor incoming
monotonicity and proved incoming ceiling then exclude exactly the
same actual central endpoint as the source caller.

## 6. Size and verification boundary

The duration and norm comparisons use one shape split at \(a=7/6\),
and no ratio subdivision. The lower first terminal polynomial's
curvature check distinguishes the two signs of its centered coordinate,
equivalently the two sides of \(a=13/12\).
The beta identities have at most 43 monomials; each x comparison
polynomial has 45; each terminal comparison polynomial has nine.
All expanded polynomials have degree at most eight in one or two
variables, with coefficient sizes within the requested twelve-digit
boundary. The Taylor coefficient recurrences are finite scalar
arithmetic on printed small sources; no unprinted exact polynomial
or numerical sample supplies a sign premise.

No outgoing physical norm floor, upper Casimir cap or equal-secant
relation is asserted at the continued scalar points. No Lean source,
compilation, Lake, typechecking or CI is part of this hand argument.
