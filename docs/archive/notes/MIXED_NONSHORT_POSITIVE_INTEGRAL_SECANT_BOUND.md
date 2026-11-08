# A positive-integral rational upper bound for the incoming secant

Date: 2026-11-08 UTC. Standalone hand lemma. This note does not close
any of the remaining forward-successor ratio or Casimir signs.

For the normalized common nonshort geometry put
\[
c=1-t,\qquad p=t+x,\qquad W=1+x,\qquad x>0,
\]
\[
v=1+\frac{c^2}{W}-\frac{c\log W}{x},\qquad
g=1-\frac{cp}{W^2}.
\]
Assume \(0<t<1\), so \(c>0\). The exact identity
\[
v-g=\frac{cx}{W^2}\{T_0(x)-t\},\qquad
T_0(x)=2+\frac1x-\frac{(1+x)^2\log(1+x)}{x^2}
\tag{1}
\]
will be used only at these original incoming coordinates.

## The rational upper bound

For every \(x>0\),
\[
\boxed{T_0(x)<T_G(x):=
\frac{90-19x^2}{12(x^2+10x+15)}.}
\tag{2}
\]
Consequently
\[
\boxed{
 v<v_G:=1-\frac{cp}{W^2}
 +\frac{cx}{W^2}\left\{
       \frac{90-19x^2}{12(x^2+10x+15)}-t\right\}.
}
\tag{3}
\]
This has a quadratic auxiliary denominator. In particular it can replace
an atanh-series upper bound in a scalar expression already proved to be
decreasing in the incoming norm. Such a replacement still requires the
corresponding scalar monotonicity; (3) alone makes no assertion about a
new PMP covector or an artificial endpoint Casimir.

## Proof by an explicit nonnegative integral

Define
\[
 I(x)=\int_0^1\frac{(1-u)^2}{1+xu}\,du,
 \quad P(u)=u^2-\frac23u+\frac1{15},
 \quad Q(x)=1+\frac23x+\frac{x^2}{15}.
\]
Elementary integration gives
\[
T_0(x)=\frac12-xI(x).
\tag{4}
\]
The needed weighted moments are
\[
\int_0^1(1-u)^2\,du=\frac13,\quad
\int_0^1u(1-u)^2\,du=\frac1{12},\quad
\int_0^1u^2(1-u)^2\,du=\frac1{30},\quad
\int_0^1u^3(1-u)^2\,du=\frac1{60}.
\]
They show directly that
\[
\int_0^1(1-u)^2P(u)\,du=0,
\qquad
\int_0^1u(1-u)^2P(u)\,du=0.
\tag{5}
\]
Set \(a=-1/x\). Since
\[
 P(u)-P(a)=(u-a)(u+a-2/3),\qquad
 1+xu=x(u-a),\qquad P(a)=\frac{Q(x)}{x^2},
\]
(5) first gives
\[
\int_0^1\frac{(1-u)^2P(u)^2}{1+xu}\,du
=P(a)\int_0^1\frac{(1-u)^2P(u)}{1+xu}\,du.
\tag{6}
\]
A second use of the same division identity gives
\[
\int_0^1\frac{(1-u)^2P(u)}{1+xu}\,du
=P(a)I(x)-\frac1{3x^2}-\frac5{36x}.
\tag{7}
\]
Combining (6) and (7), and dividing by the positive \(P(a)^2\), yields
\[
\boxed{
I(x)-\frac{1/3+5x/36}{Q(x)}
=\frac{x^4}{Q(x)^2}
 \int_0^1\frac{(1-u)^2P(u)^2}{1+xu}\,du>0.
}
\tag{8}
\]
Strictness follows because the integrand is continuous, nonnegative,
and not identically zero. Substitution into (4) gives
\[
T_0(x)<\frac12-x\frac{1/3+5x/36}{Q(x)}
=\frac{90-19x^2}{12(x^2+10x+15)},
\]
which proves (2), and (1) proves (3).

For applications needing a polynomial rather than a rational bound, the
finite identity
\[
\frac1{1+xu}=1-xu+\frac{x^2u^2}{1+xu}
\]
likewise gives the simpler, weaker strict upper bound
\[
T_0(x)<\frac12-\frac x3+\frac{x^2}{12}
\qquad(x>0),
\tag{9}
\]
using only \(I(x)>1/3-x/12\). Both (2) and (9) are hand inequalities;
no numerical quadrature or coefficient certificate is a premise.
