# A sharp rational incoming ceiling for the smaller short branch

Date: 2026-11-08 UTC. Hand corollary of the accepted
[positive-integral secant bound](MIXED_NONSHORT_POSITIVE_INTEGRAL_SECANT_BOUND.md).
Its substitution and remainder are reviewed in the
[variable-floor reconstruction audit](MIXED_SMALLER_SHORT_VARIABLE_FLOOR_AUDIT.md).
No new scalar exclusion is asserted here.

For 1<x<=beta put

\[
u=\operatorname{Sec}(1,x,\beta),\qquad S=1+x,
\qquad z=\frac{\beta-1}{S}>0,
\]

and define

\[
T_G(z)=\frac{90-19z^2}{12(z^2+10z+15)}.
\]

Then the following strict rational bound holds:

\[
\boxed{
u<u_G:=1-\frac{x\beta}{(x+\beta)^2}
 +\frac{x(\beta-1)}{(x+\beta)^2}
          \left(T_G\!\left(\frac{\beta-1}{1+x}\right)
                         -\frac1{1+x}\right).}
\tag{1}
\]

The substitution in the cited standalone identity is

\[
c=\frac{x}{1+x},\qquad t=\frac1{1+x},
\qquad p=\frac\beta{1+x},\qquad W=1+z.
\]

It gives exactly

\[
u=1+\frac{c^2}{W}-\frac{c\log W}{z},
\qquad g=1-\frac{cp}{W^2}=1-\frac{x\beta}{(x+\beta)^2},
\]

and c*z/W^2=x(beta-1)/(x+beta)^2. The hypotheses c>0,
0<t<1 and z>0 hold. Thus the existing positive-integral identity
proves (1) directly, with no new logarithm estimate.

For clarity, its exact remainder here is also explicit. Set

\[
Q(z)=1+\frac23z+\frac{z^2}{15},\qquad
P(s)=s^2-\frac23s+\frac1{15}.
\]

Then

\[
\boxed{
u_G-u=\frac{c z^6}{(1+z)^2Q(z)^2}
  \int_0^1\frac{(1-s)^2P(s)^2}{1+zs}\,ds>0.}
\tag{2}
\]

The integral is positive because its continuous integrand is
nonnegative and not identically zero. Its elementary moment gives

\[
\int_0^1(1-s)^2P(s)^2\,ds=\frac1{1575},
\]

so, if an explicit error bound is useful,

\[
0<u_G-u<\frac{c z^6}{1575(1+z)^2Q(z)^2}.
\tag{3}
\]

All variables in (1)--(3) are those of the original incoming secant.
Replacing u by u_G in a later scalar expression still requires that
expression's monotonicity in u. The bound does not carry a norm
ceiling or a Casimir cap to an artificial covector.
