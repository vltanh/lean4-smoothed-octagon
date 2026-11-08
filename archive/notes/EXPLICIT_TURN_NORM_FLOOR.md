# A stronger explicit lower bound for a turn norm

Date: 2026-11-07. Hand proof, accepted in independent internal review.
See [HAND_FURTHER_REFINEMENTS_AUDIT](HAND_FURTHER_REFINEMENTS_AUDIT.md).

This strengthens the elementary turn-norm floor used in
[HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md). It is a scalar
inequality, not a completed forward or mixed-period exclusion.

For \(1/2\le\eta\le1\) and q>1, define

\[
f_\eta(q)=1+\frac{\eta^2}{q}
                 -\eta\frac{\log q}{q-1}.
\]

Then

\[
\boxed{f_\eta(q)>\Phi(\eta):=
1-\eta^2-\frac43\eta+\frac{2\eta}{3}\sqrt{12\eta-2}.}
\tag{1}
\]

The logarithm inequality already proved in the hand refinements is

\[
\frac{\log q}{q-1}
<\frac{q^2+10q+1}{6q(q+1)}.
\]

Put \(z=1/q\), \(B=\eta(\eta-1/6)>0\), and \(C=4\eta/3>0\).
Substitution and one collection of fractions give

\[
f_\eta(q)>1-\eta/6+Bz-C+\frac C{1+z}
\]
\[
=1-\eta/6-B-C+
       \left[B(1+z)+\frac C{1+z}\right]
\ge1-\eta/6-(\sqrt C-\sqrt B)^2=\Phi(\eta).
\]

The last inequality is AM--GM for two positive numbers. Thus every step
and its strictness is explicit. The expression in (1) is the exact
infimum of this rational logarithm relaxation when q>=1: equality in
AM--GM requires \(1+1/q=\sqrt{C/B}\), which is in (1,2] for
1/2<=eta<=1. Equality for the original logarithm comparison is still
strict when q>1.

The floor is at least 3/4 and increases with eta. To see both facts
without estimating a radical, write \(h=\sqrt{12\eta-2}\), so
\(2\le h\le\sqrt{10}<2+\sqrt2<4\). Direct factorization gives

\[
\Phi(\eta)-\frac34
=\frac{h(4-h)(h-2)^2}{144}\ge0.
\tag{2}
\]

The derivative of the right side with respect to h is

\[
-\frac{(h-2)(h^2-4h+2)}{36}>0
\qquad(2<h\le\sqrt{10}).
\]

Indeed \(h^2-4h+2=(h-2)^2-2<0\) on this interval. The inequality
\(\sqrt{10}<2+\sqrt2\) follows from \(4<4\sqrt2\) after squaring
positive numbers. Therefore Phi is strictly increasing for eta>1/2.

For a genuine turn with previous margin 0<a<b and successor p>a,

\[
\operatorname{Sec}(a,b,p)
=f_{b/(a+b)}\left(\frac{p+b}{a+b}\right)
>\Phi\left(\frac b{a+b}\right).
\tag{3}
\]

In particular, at a reverse centre whose smaller adjacent turn is c<=b,
put t=a/(a+c). The two actual incident norms both exceed
\(\Phi(1-t)\): apply (3) to c, and to b use
\(b/(a+b)\ge c/(a+c)=1-t\) and the proved monotonicity.
This is an actual-data lower bound. Its preservation under any later
artificial comparison must be checked separately; (3) does not supply
that preservation by itself.
