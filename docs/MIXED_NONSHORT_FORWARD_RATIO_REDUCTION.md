# A monotone rational reduction for the low-ratio forward successor

Date: 2026-11-07 UTC. Hand reduction, accepted in the
[endpoint audit](HAND_ENDPOINT_REDUCTIONS_AUDIT.md), Section 17.
The final unit-shape sign in Section 6 is not proved here.
In particular this note does not yet claim \(t>1/3\).

This gives a scalar reduction for the forward-next eligibility condition
\(\mathcal T_*\ge3/4\). It preserves the incoming floor at its original
coordinates and uses no artificial Casimir cap. All identities and signs
proved below are independent of numerical discovery.

## 1. The common ratio starts above one quarter

The unit-shape part, Sections 2--6, of
[MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION](MIXED_NONSHORT_LOW_SCALE_HAND_EXCLUSION.md)
has a useful common consequence:
\[
\boxed{t>1/4.}
\tag{1}
\]
Indeed, suppose \(t\le1/4\). The
[common-order corollary](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md),
Section 5, gives \(k<2t+x\), while \(k\ge1\).
Thus \(x>1-2t\ge1/2\). The common duration bound gives \(x<7/3\),
and the actual derivative floor gives \(t<T(x)\), with \(T\)
as in the low-scale note.
These are exactly that note's unit-shape domain (3).
Lowering \(k\) to one preserves the exact incoming norm and its floor.
The already proved unit-shape sign contradicts \(N_k<0\).

No low-\(a\) assumption is used in this application: that assumption was
needed for the other shape face in the full low-scale theorem.

For the proposed exclusion of \(t\le1/3\), it is therefore enough to use
the closed enlarged domain
\[
\frac14\le t\le\frac13,\quad
1-2t\le x\le1,\quad
1\le k\le o:=2t+x,\quad
1\le q\le\frac{W}{o},\qquad W=1+x.
\tag{2}
\]
Actual first-event data have strict inequalities where appropriate.
The bound \(x<1\) follows from \(t<T(x)\) and \(T(1)=19/81<1/4\).
For actual data the incoming floor and boundary root give
\(v\ge F_{p/W}(q)\) and \(N<0\), where \(p=t+x\).

## 2. A combination of the residual and the next norm

Put
\[
c=1-t,\quad X=x+2,\quad Y=x(x+2),\quad J=t+Y,
\]
\[
s=k-t^2,\quad B=s+p^2,\quad e=q/W,\quad
D=eJ-p,\quad E=e^2B+1-2pe.
\]
These quantities use the normalized conventions of
[MIXED_NONSHORT_FORWARD_SHAPE_CASIMIR](MIXED_NONSHORT_FORWARD_SHAPE_CASIMIR.md).
Both D and E are positive:
\[
D\ge J/W-p=xc/W>0,\qquad
BE=r^2+s>0,\quad r=eB-p.
\]

Let \(u_U=U(t/k)\) be the central incident ceiling at the boundary,
and let \(\mathcal T_U\) be the transported next norm obtained by
using this upper incident norm. Explicitly,
\[
H_U=\frac{k}{t}(v-1+t^2)+t(2-t),\qquad
w_U=\frac{k^2-kt+t^2+H_UY+vY^2}{B^2},
\]
\[
\mathcal T_U=
\frac{v-e^2(H_U+2vY)+e^4B^2w_U}{E^2}.
\tag{3}
\]
Use \(N=tBqWR(u_U)\), the original incident-upper residual numerator.

The root equation is affine in the central incident norm, with
\[
N_u=-qWk^2D.
\]
Hence its solved root satisfies
\[
u_*-u_U=\frac{N}{qWk^2D}.
\]
The derivative of the transported next norm with respect to this
incident norm is
\[
\mathcal T_u=\frac{k^2e^2(Je^2-1)}{tE^2}.
\]
Multiplication gives the exact identity
\[
\boxed{
\mathcal T_*=\mathcal T_U+
       \frac{e(Je^2-1)}{tW^2DE^2}\,N.
}
\tag{4}
\]

Define the positive factor and combined residual
\[
C_*=\frac{tW^2DE^2}{e},\qquad
F=6N+C_*(3/4-\mathcal T_*).
\]
Then (4) gives
\[
\boxed{F=(7-Je^2)N+C_*(3/4-\mathcal T_U).}
\tag{5}
\]
An eligible actual boundary point, with \(N<0\) and
\(\mathcal T_*\ge3/4\), has \(F<0\).

At fixed \(t,x,q,v,\log q\), F is a concave quadratic in k.
Its quadratic coefficient is
\[
-\frac{tW^2De^3}{4}<0.
\tag{6}
\]
For a direct verification, the solved-root formula in the cited shape
note writes \(\mathcal T_*=V(B)/E^2\), where V is a quadratic with
leading coefficient \(e^4\). Thus
\[
C_*(3/4-\mathcal T_*)=\frac{tW^2D}{e}
 \{(3/4)E^2-V(B)\}.
\]
Its quadratic coefficient in \(B=k+p^2-t^2\) is
\(-tW^2De^3/4\). The other term \(6N\) is affine in k.

## 3. The two substitutions have justified signs

In this section v and \(\log q\) are treated as independent scalar
arguments of F. Put
\[
I_0=k+tx+tW(k-2t),\qquad I_1=kX+txX^2,
\]
\[
A=-N_v=xq\{I_0+I_1(q-1)\}>0.
\]
Since \(k\ge1>2t\), one has \(A\ge xeWk\).
The coefficient calculation from (3) is
\[
(\mathcal T_U)_v
 =\frac{(1-e^2Y)\{1-e^2(Y+k/t)\}}{E^2}.
\]
Consequently
\[
F_v=-(7-Je^2)A-\frac{tW^2D}{e}
 (1-e^2Y)\{1-e^2(Y+k/t)\}.
\tag{7}
\]

The following coarse bounds suffice:
\[
Je^2\le J/o^2\le10/3,\qquad
\frac{WD}{x}\le\frac{2cW}{o}\le\frac94.
\tag{8}
\]
For the second, use \(x\ge1-2t\) in
\[
\frac Dx\le
\frac{t(1-2t)/x+2-3t}{o}\le\frac{2c}{o},
\]
and \(W/o=1+(1-2t)/o\le3/2,\ c\le3/4\).

If the product in (7) is nonnegative, its contribution is nonpositive.
If it is negative, write \(a=e^2Y\), \(b=e^2k/t>0\).
Then \(0<1-a<1\) and
\[
-(1-a)(1-a-b)=(1-a)(a+b-1)<b.
\]
Its positive contribution to (7) is therefore less than \(W^2Dek\),
which is at most \(9A/4\) by (8).
In both cases
\[
\boxed{F_v<-\frac{17}{12}A<0.}
\tag{9}
\]
Also
\[
F_{\log q}=(7-Je^2)N_{\log q}<0,
\quad N_{\log q}=-tpBqW<0.
\tag{10}
\]

Use the three positive atanh terms to define
\[
v_3=1+\frac{c^2}{W}
-\frac{2c}{X}\left(1+\frac{x^2}{3X^2}
                          +\frac{x^4}{5X^4}\right)>v,
\]
and retain the familiar bounds
\[
L_+=\frac{(q-1)(q^2+10q+1)}{6q(q+1)}>\log q,
\]
\[
F_\ell=1+\frac{p^2q}{W^2}
-\frac pW\frac{q^2+10q+1}{6(q+1)}
<F_{p/W}(q)\le v.
\]
Thus \(\bar F:=F(v_3,L_+)<F(v,\log q)\).
Set
\[
\rho=\frac34(q+o-1)>0,\qquad
v_{\rm eff}=v_3+\rho(v_3-F_\ell),\qquad
G=F(v_{\rm eff},L_+).
\tag{11}
\]
F is affine in v, so \(G=\bar F+\rho F_v(v_3-F_\ell)<\bar F\).
Therefore an actual eligible point necessarily has
\[
G<0.
\tag{12}
\]
All quantities in G are rational; no logarithm remains.

## 4. A ceiling for the effective norm

The following bound holds throughout the enlarged rectangle (2),
even where no incoming floor is assumed:
\[
\boxed{v_{\rm eff}<U(t).}
\tag{13}
\]

Write \(g=1-cp/W^2\), and let \(v_2\) denote the same secant upper
bound with only the first two atanh terms.
Since \(p/W\ge1/2\), direct subtraction gives
\[
F_\ell-g
=\eta(\eta-\tfrac12)(q-1)
 +\frac{\eta(q-1)^2}{3(q+1)}\ge0,\qquad \eta=p/W.
\tag{14}
\]
Further,
\[
U(t)+2g-3v_2
=\frac{cx}{W^2X^3}
 \{3x^3+7x^2+2x-4+t(1-x)X^3\}>0.
\tag{15}
\]
Indeed \(x\le1\), \(t\ge(1-x)/2\), and substitution of this
lower t in the brace gives exactly
\[
\frac{x^2W(x^2+3x+4)}2>0.
\]
Thus \(3v_3-2g<3v_2-2g<U(t)\).
Also
\[
U(t)-g=\frac{cx}{W^2}\{1-t(2+x)\}\ge0
\]
on (2), so \(v_3<U(t)\).

Finally
\[
\rho\le\frac34\left(o+\frac{1-2t}{o}\right)
\le\frac34\left(\frac53+\frac12\right)=\frac{13}{8}<2.
\]
If \(v_3\ge g\), equations (11), (14) give
\(v_{\rm eff}\le v_3+\rho(v_3-g)\le3v_3-2g<U(t)\).
If \(v_3<g\), they give \(v_{\rm eff}<v_3<U(t)\).
This proves (13).

## 5. The rational lower bound strictly increases in shape

The effective norm, rho and \(L_+\) are independent of k.
Hence
\[
G_k=F_k(v_{\rm eff},L_+).
\]
We prove
\[
\boxed{G_k>0\quad\hbox{on (2)}.}
\tag{16}
\]

Differentiate (7). With
\[
A_k=qx\{1+tW+X(q-1)\}\ge xeW,
\]
one obtains
\[
F_{kv}=-(7-Je^2)A_k+W^2De(1-e^2Y)
<-\frac{17}{12}A_k<0
\tag{17}
\]
by the same two bounds (8).
Also \(F_{k,\log q}<0\).
Since \(v_{\rm eff}<U(t)\) and \(L_+<q-1\),
\[
G_k>F_k(U(t),q-1).
\]
The strict inequality \(L_+<q-1\) follows from
\[
1-\frac{L_+}{q-1}
=\frac{(q-1)(5q+1)}{6q(q+1)}>0
\]
for \(q>1\), with the endpoint understood continuously.
By (6), \(F_k\) decreases with k, so it is enough to evaluate this
last lower bound at \(k=o\).

Put \(y=q-1\), so \(0\le y\le1/2\). Exact collection gives
\[
F_k(U(t),y)\big|_{k=o}
=\frac{tq}{2W^2}\{d_0+d_1y+d_2y^2+d_3y^3\},
\tag{18}
\]
where
\[
d_0=xc\{1-2t+x(-2t^2+14t-1)+24tx^2+12tx^3\}>0,
\qquad d_3=xWJ>0,
\]
\[
\begin{aligned}
d_1={}&t-2t^2+(16-27t+8t^2)x\\
&+(51-68t+10t^2+4t^3)x^2\\
&+(63-80t+16t^2)x^3+(24-28t+4t^2)x^4,
\end{aligned}
\]
\[
\begin{aligned}
d_2={}&-6t^2+(-16t-6t^2)x+(-5-27t+2t^3)x^2\\
&+(-7-19t+8t^2)x^3+(-4-2t+2t^2)x^4<0.
\end{aligned}
\]
Every coefficient of \(d_2\) is negative for \(1/4\le t\le1/3\).
For \(d_0\), \(-2t^2+14t-1\ge19/8>0\).
Finally
\[
\begin{aligned}
2d_1+d_2={}&2t-10t^2+(32-70t+10t^2)x\\
&+(97-163t+20t^2+10t^3)x^2\\
&+(119-179t+40t^2)x^3+(44-58t+10t^2)x^4>0.
\end{aligned}
\tag{19}
\]
Its constant is at least \(-4/9\), its linear coefficient is at
least \(26/3\), and \(x\ge1/3\). These two terms already total
at least \(22/9\). The remaining three coefficients are at least
\(128/3,178/3,74/3\), respectively.
As \(d_2<0\) and \(y\le1/2\),
\[
d_1+d_2y\ge d_1+d_2/2>0.
\]
This proves positivity in (18), hence (16).

Thus any eligible actual point with \(t\le1/3\) would force
\[
G(t,x,q,1)<0.
\tag{20}
\]
The entire shape variable has been removed by a proved monotonicity.
No condition at an arbitrary intermediate switch is imported.

## 6. The remaining unit-shape target

The accepted
[quantitative swap bound](MIXED_NONSHORT_QUANTITATIVE_SWAP_BOUND.md)
further gives
\[
q<\frac{W}{4t+2x-1}.
\]
Write
\[
h=1-2t,\qquad j=2t+x-1.
\]
Its domain gives \(1/3\le h\le1/2\) and \(0\le j\le h\).
The closed enlarged unit-shape problem is therefore parametrized by
\[
t=(1-h)/2,\quad x=h+j,\quad
q=1+z\,\frac{h-j}{1+2j},\quad k=1,
\]
\[
\frac13\le h\le\frac12,\qquad
0\le j\le h,\qquad0\le z\le1.
\tag{21}
\]
Equivalently set \(j=ha\), with \(a,z\in[0,1]\).

A sufficient remaining hand theorem is positivity of the single
rational function G from (11) on (21).
That sign is not proved in this note.
No numerical observation is needed for any reduction above.
