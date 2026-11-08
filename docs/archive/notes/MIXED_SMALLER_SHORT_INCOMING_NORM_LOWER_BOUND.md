# A positive-integral lower bound for the incoming short norm

Date: 2026-11-08 UTC. Hand lemma, accepted in the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md),
Section 10.
This is a bound for the unchanged incoming secant. It does not supply
the remaining short-domain or completion-cost exclusion.

Suppose 1<x<=beta, and put
\[
u=\operatorname{Sec}(1,x,\beta),\qquad
\theta=\frac{x-1}{2x}\in(0,1/2),
\]
\[
J_2(\theta)=
\frac{5(34\theta^2-105\theta+90)}
 {6(6\theta^2-20\theta+15)^2}.
\]
Then
\[
\boxed{u>\frac34+
 \frac{(x-1)^3}{16x^2(\beta-1)}J_2(\theta)
 +\frac{(\beta-x)^3}{12(\beta+x)^2(\beta-1)}.}
\tag{1}
\]
All quantities in this bound are rational functions of the original
short geometry. No second-secant equality is needed.

## 1. An explicit positive remainder

Define
\[
P(z)=z^2-\frac43z+\frac25,\quad
Q(\theta)=1-\frac43\theta+\frac25\theta^2,
\quad A(\theta)=\frac13-\frac7{36}\theta.
\]
Direct integration gives
\[
\int_0^1z^2P(z)\,dz=0,
\qquad \int_0^1z^3P(z)\,dz=0.
\tag{2}
\]
Let
\[
I(\theta)=\int_0^1\frac{z^2}{1-\theta z}\,dz.
\]
The following identity has a positive remainder:
\[
\boxed{I(\theta)-\frac{A(\theta)}{Q(\theta)}
 =\frac{\theta^4}{Q(\theta)^2}
   \int_0^1\frac{z^2P(z)^2}{1-\theta z}\,dz.}
\tag{3}
\]
For a direct algebraic proof, use
\[
Q(\theta)-\theta^2P(z)
 =(1-\theta z)(1+\theta z-4\theta/3).
\]
Subtracting the two integrands after multiplication by Q^2 leaves
\[
z^2(1+\theta z-4\theta/3)
       [Q(\theta)+\theta^2P(z)].
\]
Its P part integrates to zero by (2). The remaining part integrates
to Q times (1/3-7theta/36), proving (3).

For 0<=theta<=1/2, Q>=Q(1/2)=13/30>0 and Q'<0.
The integral on the right of (3) is positive and nondecreasing in
theta; its derivative is an integral with a nonnegative integrand.
Thus the full remainder and its derivative are strictly positive
when theta>0. Applying the operator 1+theta*d/dtheta to (3) gives
\[
\int_0^1\frac{z^2}{(1-\theta z)^2}\,dz
 >\frac{A}{Q}+\theta\left(\frac A Q\right)'
 =J_2(\theta).
\tag{4}
\]
The last equality is the displayed rational identity defining J_2.
Differentiation under the integral is justified by the positive
uniform denominator 1-theta*z>=1/2 on this compact interval.

## 2. Apply the bound to the two parts of the secant

The exact positive integral is
\[
u-\frac34=\frac1{4(\beta-1)}
 \int_1^\beta\frac{(s-x)^2}{(s+x)^2}\,ds.
\tag{5}
\]
On [1,x], set z=(x-s)/(x-1). This part becomes
\[
\frac{(x-1)^3}{16x^2(\beta-1)}
 \int_0^1\frac{z^2}{(1-\theta z)^2}\,dz.
\]
Equation (4) gives the first strict contribution in (1).

On [x,beta], s+x<=beta+x. Hence the remaining part is at least
\[
\frac1{4(\beta-1)(\beta+x)^2}
 \int_x^\beta(s-x)^2\,ds
 =\frac{(\beta-x)^3}{12(\beta+x)^2(\beta-1)}.
\]
This includes beta=x, when the tail is zero. Adding the two parts
proves (1), with strictness supplied by the first part since x>1.

Using this lower bound inside a later cost expression requires that
expression's appropriate monotonicity or endpoint argument. No such
comparison, scale change or physical admissibility assertion is
contained in the present lemma.
