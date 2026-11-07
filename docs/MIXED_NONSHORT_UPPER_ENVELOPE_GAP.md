# Three upper-envelope lemmas and a uniform nonshort gap

Date: 2026-11-07 UTC. Hand proofs, accepted in the
[independent review](MIXED_NONSHORT_UPPER_ENVELOPE_GAP_AUDIT.md).

These lemmas use the actual nonshort-side data and scalar boundary
comparison of [MIXED_SMALLER_TURN_CONTINUATION](MIXED_SMALLER_TURN_CONTINUATION.md).
No interval cover, sampled minimum or computer-generated sign verdict is
a premise. The rational identity in Lemma 2 is displayed with all five
coefficients factored, so ordinary multiplication verifies its sign
certificate. The lemmas supply necessary restrictions; the remaining
reverse and forward exclusions still require separate hand arguments.

Use a<c<=b, d>a, K=a^2+4, T=a+c, S=a+b, Q=d^2+4,
W=c+d, Y=W^2-T^2, and the actual incoming norm
v=Sec(a,c,d). Put U(s)=1-s+s^2. The actual central stationary formula is

\[
h=\frac K{16a}(Su+Tv-C_a),
\quad C_a=b+a+c-a^2(S^{-1}+T^{-1})+a^3/K+a\log(K/(ST)),
\]

and its transported outgoing norm is

\[
w=\frac{K^2u+16hY+vY^2}{Q^2}.
\]

The genuine actual switch supplies u<U(a/S) and w>g_d(r), where
q=W(d+r)/Q>1 and g_d(r)=1-dr/(d+r)^2. These are the same actual
normal multiplier and actual first forward event as in the continuation
note.

The first two lemmas require a<b, a<c and the positive central factor
K/(ST)>1; their proofs do not use c<=b. The smaller-turn ordering is
used for c<2 and T^2<=K in the stated corollaries. Thus the strict
inequality d^2+2cd>4 also applies when the nonshort side was not chosen
by size.

## Lemma 1. The upper incident envelope preserves the outgoing floor

For fixed a,c,d,v, substitute u=U(a/S) in the two formulas above and
call the resulting values h_U(b), w_U(b). Then, for b>a,

\[
(h_U)_b=\frac{K(b-a)}{16S^2}>0,
\qquad
(w_U)_b=\frac{K(b-a)(aK+SY)}{S^3Q^2}>0.
\tag{1}
\]

Indeed C_a,b=U(a/S) and [U(a/S)]_b=a(b-a)/S^3. Differentiating h_U
cancels the U term and gives the first formula; differentiating w_U
gives the second. All factors have their indicated signs because Y>0.

The coefficient of u in w, with central stationarity imposed, is

\[
w_u=\frac{K(aK+SY)}{aQ^2}>0.
\]

Thus at the actual b one has w<w_U(b). Increase b to the already
justified zero-factor boundary b*=K/T-a>b. Formula (1) gives

\[
\boxed{w_U(b_*)>w>g_d(r)\ge3/4.}
\tag{2}
\]

This is a comparison for the envelope obtained by imposing the upper
norm. It does not assert an outgoing floor for the solved boundary root
w*, which can be smaller than w.

## Lemma 2. The first forward centre satisfies d^2+2cd>4

Under the same actual hypotheses,

\[
\boxed{d^2+2cd>4.}
\tag{3}
\]

In particular c<2 implies

\[
d>\sqrt8-2>4/5.
\tag{4}
\]

**Proof.** Suppose e=4-d^2-2cd>=0. Put x=d-a>0, so W=T+x, and
r0=Q/W-d. Then r0>=d and q>1 gives r>r0. The function g_d is
increasing on [d,infinity), hence g_d(r)>=g_d(r0).

Strict turn log-concavity gives ad<c^2. For a<=s<=d, direct
subtraction gives the pointwise chord identity

\[
\frac{(d-s)g_c(a)+(s-a)g_c(d)}{d-a}-g_c(s)
=\frac{c(s-a)(d-s)
 [c^2(a+d+2c)+(c^2-ad)s]}
 {(a+c)^2(c+d)^2(c+s)^2}.
\]

Its right side is strictly positive for interior s because every
factor has the displayed sign. Integrating it over [a,d] yields

\[
v< V_{\rm ch}:=1-\frac12\left(\frac{ac}{T^2}+\frac{cd}{W^2}\right).
\]

At b*, the coefficient of v in w_U is

\[
\frac{Y(KT/a+Y)}{Q^2}>0.
\]

Consequently w_U(b*) is bounded above by the same envelope evaluated at
V_ch. Call that rational quantity w_U,ch. At the boundary
C_a=4/T+4c/K and U(a/S)=U(aT/K), so every term is explicit.

Clear the positive denominators. Direct substitution and collection by
powers of x give the identity

\[
Q^2[w_{U,\rm ch}-g_d(r_0)]
=-\frac{cx}{2aT^2W^2}\,[P_0(x)+eP_e(x)],
\tag{5}
\]

where

\[
\begin{aligned}
P_0(x)={}&2aT^5x
 +2T^3(5a^2+3ac+2c^2)x^2\\
 &+2T^2(9a^2+5ac+2c^2)x^3\\
 &+T(2a+c)(7a+c)x^4+a(4a+3c)x^5,
\end{aligned}
\]
\[
P_e(x)=T[2aT^3+2T^3x+4aT^2x+T^2x^2+6aTx^2+3ax^3].
\]

For clarity, (5) is obtained from

\[
Q^2w_{U,\rm ch}
=K^2U(aT/K)+\frac Ka
 [ (K/T)U(aT/K)+TV_{\rm ch}-4/T-4c/K]Y
 +V_{\rm ch}Y^2,
\]
\[
Q^2g_d(r_0)=Q^2-dWQ+d^2W^2,
\]

by setting d=a+x and 4=d^2+2cd+e. Thus the displayed five coefficients
and the coefficient of e give a complete elementary expansion check.
Every summand of P_0 and P_e is positive for a,c,x>0. Therefore
w_U,ch<g_d(r0)<=g_d(r), contradicting (2). This proves (3).

Finally c<2 and (3) imply d^2+4d>4, giving d>sqrt8-2. The comparison
sqrt8-2>4/5 follows by squaring 14/5: 196/25<8.

## Lemma 3. An actual incoming turn satisfies d<5c/2

The genuine turn inequalities v<g_c(a) and v>g_c(d), together with a<c,
imply

\[
\boxed{d<\frac52c.}
\tag{6}
\]

**Proof.** The function g_c decreases on [0,a]. Hence its average over
[0,a] is at least g_c(a)>v. Extending the actual secant average from
[a,d] to [0,d] therefore increases it:

\[
v<\operatorname{Sec}(0,c,d)
=1+\frac1{1+t}-\frac{\log(1+t)}t,\qquad t=d/c.
\]

Since v>g_c(d)=1-t/(1+t)^2, it follows that

\[
\log(1+t)<\frac{t(1+2t)}{(1+t)^2}.
\tag{7}
\]

The difference between the left and right sides has derivative

\[
\frac{t(t-1)}{(1+t)^3},
\]

which is positive for t>1. At t=5/2, use

\[
\log(7/2)
>2\left(\frac59+\frac{(5/9)^3}{3}\right)
=\frac{2680}{2187}>\frac{60}{49}.
\]

The first strict inequality follows by integrating the first two
positive terms of 1/(1-z^2) from 0 to 5/9. The last is the integer
comparison 2680*49-60*2187=100>0. But 60/49 is exactly the right side
of (7) at t=5/2. Monotonicity then excludes every t>=5/2, proving (6).

## Corollary. A uniform duration-ratio gap without a coefficient table

Assume the [sharpened hand scale bound](HAND_PROOF_REFINEMENTS.md), Section 2,
a^2<2/3 and the smaller-turn
shape inequality T^2<=K. Then

\[
\boxed{\delta_1:=\frac{d-a}{a+c}>\frac1{10}.}
\tag{8}
\]

Indeed put z=a^2 and G=4-a^2-2ac. The shape bound gives
c<=sqrt(z+4)-a and hence

\[
G\ge4+z-2\sqrt{z(z+4)}>1.
\]

To verify the last strict inequality, both sides of
3+z>2sqrt(z(z+4)) are positive, and their squared difference is

\[
9-10z-3z^2\ge9-10(2/3)-3(2/3)^2=1>0.
\]

On the other hand Lemma 2 is exactly

\[
T^2\delta_1(\delta_1+2)>G>1.
\]

Because T^2<=K<14/3, it follows that

\[
\delta_1(\delta_1+2)>\frac3{14}>\frac{21}{100}.
\]

The last strict rational comparison is 300>294 after multiplying by
1400. If delta1<=1/10 its product with delta1+2 would be at most
21/100, a contradiction.

This directly excludes every epsilon=max(delta1,delta2)<=1/10 after
the b-boundary comparison, and every original three-parameter corner
with maximum at most 1/10. In particular the previously isolated
1/32 corner needs no polynomial-coefficient table for the actual
nonshort problem once these hand lemmas and the sharpened scale are
retained. The original delta0 may be largest; delta1 itself is still
unchanged by the comparison and satisfies the strict gap (8).

## Additional preserved restrictions for the reverse-next branch

If the next switch is reverse, put s=Sec(a,r,d). The actual inequalities
w<=s, w>g_d(r), and w>=F_{d/(d+r)}(q) imply the unchanged-coordinate
conditions

\[
s>g_r(d),\qquad s\ge F_{d/(d+r)}(q).
\]

They remain legitimate after the b-comparison because a,d,r and q are
held fixed. They do not assert that w* satisfies the original outgoing
floor or missing-control inequality.

For completeness, r^2>=ad>a^2 implies a<r, and for a<x<d the exact
identity

\[
g_r(a)-g_r(x)=
\frac{r(x-a)(r^2-ax)}{(r+a)^2(r+x)^2}>0
\]

shows s<g_r(a), even when r^2=ad. Lemma 3 therefore also applies to
this extended secant and gives the additional reverse-only d<5r/2.
