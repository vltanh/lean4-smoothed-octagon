# Concavity in scale of the nonshort boundary Casimir

Date: 2026-11-07 UTC. Hand reduction, accepted in independent internal review.
The remaining forward endpoint signs are not asserted proved.
See [HAND_ENDPOINT_REDUCTIONS_AUDIT](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).

The lower endpoint in the
[forward successor comparison](MIXED_NONSHORT_FORWARD_BOUNDARY_REDUCTION.md)
has a simple additional concavity. At fixed normalized turn geometry
and first-event factor, its Casimir is a concave quadratic in the
squared physical scale. This gives a further endpoint reduction without
transferring the original Casimir cap to a scalar comparison point.

## 1. Normalized coordinates and two exact identities

Use the boundary b*=(a^2+4)/(a+c)-a and write
\[
\ell=a+c,\quad t=a/\ell,\quad x=(d-a)/\ell,\quad
k=(a^2+4)/\ell^2,\quad s=k-t^2=4/\ell^2.
\]
Keep \(t,x,q\) and the exact incoming norm
\[
v=\operatorname{Sec}(t,1-t,t+x)
 =1+\frac{(1-t)^2}{1+x}
       -(1-t)\frac{\log(1+x)}x
\]
fixed while varying k. Put
\[
c=1-t,\quad p=t+x,\quad W=1+x,\quad Y=x(x+2),
\quad J=t+Y,
\]
\[
B=k+2tx+x^2=s+p^2,\quad e=q/W,\quad Z=eB,\quad r=Z-p.
\]
The physical margins are \(\ell(t,c,p,r)\); here c and r denote
normalized margins. The needed algebraic domain is
\[
0<t<1/2,\quad x>0,\quad 1<q<W/p,\quad k\ge1.
\tag{1}
\]
Define
\[
\theta=1-pe>0,\qquad D=eJ-p>0,\qquad U_t=1-t+t^2.
\tag{2}
\]
For D, observe that \(J-pW=x(1-t)>0\), and q>1.
All subsequent denominators are therefore positive.

Let u*, w* and the diagonals be the uniquely solved boundary root.
Use the dimensionless diagonals
\[
h_c=16h/\ell^2,\qquad h_d=16h_d^{\rm physical}/\ell^2.
\]
The exact central stationarity and transport equations imply
\[
\boxed{
J h_d=B^2w_*+v(s+J^2)-s(s+U_t).
}
\tag{3}
\]
For a direct derivation, they say
\[
t h_c=k^2u_*+kv-ks-sc,\qquad
B^2w_*=k^2u_*+Yh_c+vY^2,\qquad h_d=h_c+2vY.
\]
Eliminate u* and then use \(k=s+t^2\). This gives (3) by
ordinary multiplication.

Define the k-independent number
\[
L=\log q+\frac{Wv-c+p^2/W}{p}.
\tag{4}
\]
The first forward stationary equation is equivalently
\[
\boxed{
h_d=BL+\frac ep B^2(w_*-1)+\frac{p\theta}{e}.
}
\tag{5}
\]
Indeed its normalized scalar cost is
\[
C_d=c+Z-\frac{p^2}W-\frac{p^2}Z+\frac{p^3}B-p\log q,
\]
and stationarity is \(C_d-Wv-Zw_*+p h_d/B=0\).
Substitution of \(Z=eB\) gives (5).

## 2. The solved root has only two inverse powers of B

Solving (3)--(5) gives
\[
\boxed{w_*=1+\frac AB+\frac C{B^2},\qquad
h_d=\alpha B+\beta,}
\tag{6}
\]
where every coefficient is independent of k:
\[
A=\frac pD\{2p^2-U_t+v-JL\},
\]
\[
C=\frac pD\{-p^4+(U_t-v)p^2+vJ^2-Jp\theta/e\},
\]
\[
\alpha=L+\frac ep A,\qquad
\beta=\frac ep C+\frac{p\theta}{e}.
\tag{7}
\]
To check (6), substitute (5) in (3) and use \(s=B-p^2\).
The coefficient of \(B^2w_*\) is D/p. Its quadratic term gives
exactly the leading constant one in w*, and its linear and constant
terms give A and C. Formula (5) then gives the displayed affine
diagonal. No logarithm approximation has been made.

The boundary determinant, in the physical normalization used by the
actual-period cap, is
\[
\Gamma_*(k)=
\frac{4B^2v w_*-h_d^2}{16s^2}.
\tag{8}
\]
This is the scalar determinant of the boundary solution. Its
identification with (8) is an algebraic transport identity, not a
claim that the boundary solution is a physical period.

## 3. A negative square proves concavity

Put
\[
X=\frac1s=\frac{\ell^2}{4},\qquad
c_0=4v-\alpha^2,
\]
\[
c_1=2p^2c_0+4vA-2\alpha\beta,\qquad
M=\alpha p^2+\beta-2vJ.
\tag{9}
\]
Then the exact identity is
\[
\boxed{16\Gamma_*=c_0+c_1X-M^2X^2.}
\tag{10}
\]

Here is a short proof of the square coefficient. By (6), the numerator
of (8) is
\[
(4v-\alpha^2)B^2+(4vA-2\alpha\beta)B+4vC-\beta^2.
\]
With \(B=s+p^2\), its constant term in s can be found from (3).
That identity is polynomial after (6), so it may be evaluated
algebraically at s=0, without assigning that value a geometric meaning.
It gives
\[
p^4+Ap^2+C=J(\alpha p^2+\beta)-vJ^2.
\]
Consequently the constant numerator is
\[
4v\{p^4+Ap^2+C\}-(\alpha p^2+\beta)^2
=-(\alpha p^2+\beta-2vJ)^2=-M^2.
\]
The other two coefficients are exactly (9). This proves (10).

Thus \(\Gamma_*\) is concave in X for every fixed t,x,q,v in (1).
It is strictly concave unless M=0; the affine exceptional case also
has its minimum on an interval at an endpoint. No sign of
\(\Gamma_*\), \(c_0\), \(c_1\) or M is assumed.

In particular, if \(1\le k_L\le k\le k_U<\infty\), then
\[
\boxed{\Gamma_*(k)\ge
\min\{\Gamma_*(k_L),\Gamma_*(k_U)\}.}
\tag{11}
\]
The reciprocal scale X reverses the order of the interval endpoints,
but preserves their set, so the usual concave-function inequality
gives exactly (11).

## 4. The next norm and a continuous threshold

The transported next norm at the boundary is
\[
\mathcal T_*(k)=
\frac{B^2v-h_dZ^2+w_*Z^4}{(r^2+s)^2}.
\]
Since
\[
r^2+s=B\{e^2B+j_0\},\qquad j_0=1-2pe,
\]
equation (6) gives
\[
\boxed{
\mathcal T_*=
\frac{e^4B^2+(e^4A-e^2\alpha)B+v-e^2\beta+e^4C}
     {(e^2B+j_0)^2}.
}
\tag{12}
\]
The denominator is positive, because \(r^2+s>0\) and B>0.

For a fixed threshold m, the condition \(\mathcal T_*\ge m\)
is equivalent to the quadratic inequality
\[
e^4(1-m)B^2
 +\{e^4A-e^2\alpha-2me^2j_0\}B
 +v-e^2\beta+e^4C-mj_0^2\ge0.
\tag{13}
\]
A stronger argument permits a threshold which varies continuously with k;
no polynomial form or monotonicity is needed.

**Endpoint lemma.** Let \(m(k)\) be any continuous function on a finite
interval \([k_L,k_U]\subset[1,\infty)\), and set
\[
\mathcal A=\{k\in[k_L,k_U]:\mathcal T_*(k)\ge m(k)\}.
\]
Suppose \(\mathcal A\) contains a point with \(\Gamma_*<g\).
Then a point with both \(\Gamma_*<g\) and \(\mathcal T_*\ge m\)
exists on at least one of the faces
\[
\boxed{k=k_L,\qquad k=k_U,\qquad \mathcal T_*=m(k).}
\tag{14}
\]

Indeed \(\mathcal A\) is nonempty and compact, so let
\(k_-=\min\mathcal A\), \(k_+=\max\mathcal A\). If they agree,
that single point is either an interval endpoint or satisfies
\(\mathcal T_*=m\) by continuity. Otherwise concavity in X gives
\[
\Gamma_*(k)\ge
\min\{\Gamma_*(k_-),\Gamma_*(k_+)\}
\quad(k\in\mathcal A).
\]
At least one of these two endpoints therefore has determinant below g.
An extreme of \(\mathcal A\) in the interior of \([k_L,k_U]\)
cannot have \(\mathcal T_*>m\), since continuity would give an eligible
neighborhood on both sides. Thus it has equality. This proves (14).

The argument does not assume that \(\mathcal A\) is an interval.
Concavity is used on its whole spanning interval, on which the scalar
determinant is defined; intermediate points need not be eligible.

## 5. Retain the stronger outgoing-turn floor

Impose the affine lower bound \(r\ge t>0\) on the compared k interval.
Then
\[
\eta(k)=\frac{rZ}{r^2+s}\in(0,1).
\]
The upper bound follows from
\[
s-pr=B(1-pe)=B\theta>0.
\]
In fact
\[
\eta=1-\frac{\theta}{e^2B+j_0},
\]
so eta is continuous. Define the continuous threshold
\[
m_\Phi(k)=
\begin{cases}
1-\eta+\eta^2,&0<\eta\le1/2,\\
\Phi(\eta),&1/2\le\eta<1,
\end{cases}
\]
\[
\Phi(\eta)=1-\eta^2-\frac{4\eta}{3}
                 +\frac{2\eta}{3}\sqrt{12\eta-2}.
\tag{15}
\]
The two definitions agree at \(\eta=1/2\), with value 3/4.

This is a proved lower bound for the original actual next forward norm.
For \(\eta\le1/2\), use the trapezoid logarithm argument in
[HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md), Section 3.
For \(\eta\ge1/2\), use the scalar inequality of
[EXPLICIT_TURN_NORM_FLOOR](EXPLICIT_TURN_NORM_FLOOR.md).
The missing-control substitution at the actual next forward switch is
the same one displayed in Section 4 of the hand refinements. It yields
a strict actual norm bound above \(m_\Phi\).
The original b-comparison fixes d,r, hence eta, so its transported
boundary norm satisfies \(\mathcal T_*>m_\Phi\).

For completeness, along the first-forward stationary line at a fixed
k the next norm has derivative
\[
\frac{d\mathcal T}{dw}=-\mathcal B,\qquad
\mathcal B=\frac{Z^3(s-pr)}{p(r^2+s)^2}>0.
\tag{16}
\]
The scalar value with next norm \(m_\Phi(k)\) is therefore
\[
w_\Phi(k)=w_*(k)+
             \frac{\mathcal T_*(k)-m_\Phi(k)}{\mathcal B(k)}.
\tag{17}
\]
At a cut face \(\mathcal T_*=m_\Phi\), it equals w*. Its determinant
is exactly
\[
\Gamma(w_\Phi)=\Gamma_*.
\tag{18}
\]

Thus the third face in the endpoint lemma joins the corresponding
stronger upper-w endpoint problem. This preserves the varying floor
by choosing extreme eligible points; it does not claim that the floor
is monotone along a shape path, or that every intermediate k satisfies
it.

## 6. Application and remaining signs

The incident-upper residual numerator is affine and strictly increasing
in k by
[MIXED_NONSHORT_SHAPE_MONOTONICITY](MIXED_NONSHORT_SHAPE_MONOTONICITY.md).
Write \(N(k)=A_Nk+B_N\), with \(A_N>0\), and
\(k_{\rm top}=-B_N/A_N\). Actual data have \(k<k_{\rm top}\).
The hand scale bound a<4/5 gives \(k>(29/4)t^2\).
The global-minimum condition \(r\ge t\) is exactly
\[
k\ge\frac{W(2t+x)}q-2tx-x^2.
\]
Accordingly a convenient closed enlarged interval for (15) is
\[
\boxed{
k_L=\max\left\{1,\frac{29}{4}t^2,
       \frac{W(2t+x)}q-2tx-x^2\right\},\qquad
k_U=k_{\rm top}.
}
\tag{19}
\]
It is nonempty whenever the original actual point exists.
The exact incoming secant and its derivative and missing-control
inequalities are independent of k. The root upper-norm condition
persists weakly on this entire interval, since \(N(k)\le0\).

Other restrictions which change with k are not automatically retained.
For example the centre gap is the affine upper bound
\(k<2t+x(x+2)\); intersecting (19) with this bound replaces k_U by
the smaller explicit endpoint. Compact state bounds require their own
incorporation if they are to be used at every comparison endpoint.
No additional such bound is assumed in the argument above.

The actual forward successor, the proved b-comparison and concavity
of the determinant in w give the exhaustive stronger alternative
\[
\Gamma_*<9193/50000
\quad\hbox{or}\quad
\Gamma(w_\Phi)<9193/50000,
\qquad \mathcal T_*>m_\Phi.
\tag{20}
\]
For the first alternative, apply Section 4 with \(m=m_\Phi\).
It produces a point below the same cap on k=k_L, k=k_U, or the
joining face (18). In each case the threshold condition is retained
at that selected point. The joining face belongs to the second
alternative in (20), now with weak equality in the threshold.
No original physical Casimir is assigned to an arbitrary intermediate
shape.

The remaining endpoint inequalities have not been proved here.
The contribution is the exact scale concavity and the justified
retention of the stronger next-norm condition. These facts use no
numerical sampling, interval execution or omitted polynomial sign.
