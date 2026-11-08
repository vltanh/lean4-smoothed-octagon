# A compact rational upper bound for the incoming short norm

Date: 2026-11-08 UTC. Hand lemma, accepted in the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md),
Section 3. This note does not close the smaller-short exclusion.

For the exact incoming secant write
\[
u=\operatorname{Sec}(1,x,\beta)
 =1+\frac{x^2}{(1+x)(x+\beta)}
 -\frac{x}{\beta-1}\log\frac{x+\beta}{1+x},
\qquad 1<x\le\beta.
\tag{1}
\]
Then
\[
\boxed{
u\le\frac34+
 \frac{1}{\beta-1}\left\{
 \frac{2(x-1)^3}{(x+1)(35x+13)}
 +\frac{(\beta-x)^3}{48x^2}\right\}.}
\tag{2}
\]
The bound uses only this secant and its short ordering. In particular,
it does not require the other secant equality, a scale comparison or
an upper bound on beta/x.

## 1. The secant ending at the minimum

Put
\[
V(x)=\operatorname{Sec}(1,x,x),\qquad
z=\frac{x-1}{x+1}\in(0,1).
\]
We first prove
\[
V(x)-\frac34
 \le\frac{z^2}{12+11z/2}
 =\frac{2(x-1)^2}{(x+1)(35x+13)}.
\tag{3}
\]
Indeed
\[
V(x)-\frac34
 =\frac12+\frac z4-\frac{1+z}{2z}\log(1+z).
\]
Consequently (3) is equivalent to
\[
\log(1+z)\ge L(z):=
 \frac{z}{1+z}\left(1+\frac z2
                    -\frac{4z^2}{24+11z}\right).
\tag{4}
\]
Let G(z)=log(1+z)-L(z). A direct differentiation gives the small
rational identity
\[
G'(z)=\frac{z^3(32-33z)}
 {2(1+z)^2(24+11z)^2}.
\tag{5}
\]
Thus G increases on [0,32/33] and decreases on [32/33,1]; its
minimum on [0,1] is at an endpoint. At zero it vanishes. At one,
L(1)=97/140, whereas the first three positive terms of the
atanh series, or their direct positive-integral remainder, give
\[
\log2
 =2\int_0^{1/3}\frac{ds}{1-s^2}
 >2\left(\frac13+\frac1{81}+\frac1{1215}\right)
 =\frac{842}{1215}
 =\frac{97}{140}+\frac1{6804}.
\tag{6}
\]
This proves (4), hence (3), without a numerical logarithm estimate.

## 2. Add the tail after the minimum

The positive integral identity associated with (1) is
\[
u-\frac34
 =\frac1{4(\beta-1)}
  \int_1^\beta\frac{(s-x)^2}{(s+x)^2}\,ds.
\tag{7}
\]
Its part over [1,x] equals
\((x-1)[V(x)-3/4]/(\beta-1)\). For the remaining part, s>=x
gives (s+x)^2>=4x^2, and therefore
\[
\frac14\int_x^\beta\frac{(s-x)^2}{(s+x)^2}\,ds
 \le\frac1{16x^2}\int_x^\beta(s-x)^2\,ds
 =\frac{(\beta-x)^3}{48x^2}.
\tag{8}
\]
Combining (3), (7) and (8) proves (2).

This is an upper bound for the original incoming norm. Replacing u
by its right side in another expression still requires the relevant
monotonicity in u; no other domain hypothesis is transported by this
replacement.
