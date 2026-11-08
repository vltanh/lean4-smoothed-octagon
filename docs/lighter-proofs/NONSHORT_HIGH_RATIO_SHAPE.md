# Remove the high-ratio upper-shape certificate by monotonicity

This replaces the use of the upper face `k = 1 + j` in
`SmoothedOctagon/Exclusion/Mixed/FwdHand/LargeGap.lean`, theorem
`fh_LGB_core`. It retains the lower-face sign at `k = 29t²/4` as an
explicit dependency. It does **not** replace that lower-face sign.

The relevant scalar proof already appears in Section 2 of
[the high-ratio note](../../archive/notes/MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_EXCLUSION.md).
Here it is reconstructed with stronger elementary bounds and a staged
algebra interface. The four endpoint derivative identities have 11, 15,
12 and 5 monomials, respectively, in the two variables `t,x`; their
total degrees are at most six. No three-variable residual expansion,
coefficient table, or subdivision is required.

## 1. Exact replacement statement and caller

Assume

\[
\frac38\le t\le\frac25,\quad h=1-2t,\quad
\frac1{30}\le j\le\frac{5h}{7},\quad x=h+j,
\quad 1\le q\le\frac{1+x}{1+2j}.
\]

Set \(k_+=1+j=2t+x\). For the rational function \(G_4\) in equation
(6) of the high-ratio note,

\[
\boxed{\partial_kG_4(t,x,q,k)>0\quad(1\le k\le k_+).}
\tag{1}
\]

The actual caller has

\[
k_0:=29t^2/4<k<k_+.
\]

In particular \(k_0\ge261/256>1\), and every point between \(k_0\)
and \(k\) lies in the interval in (1). Therefore the retained lower-face
sign gives

\[
G_4(t,x,q,k)>G_4(t,x,q,k_0)>0,
\]

contradicting the unchanged necessary condition \(G_4<0\).

In `fh_LGB_core`, retain the substitution proof through `hG` and the
lower endpoint proof `hA` using `fhCLGc_pos_y` and `fh_LGc_link`.
Replace `hB` and `fh_comb_pos_of_ends` by (1) integrated on
\([29t^2/4,k]\). The Lean expression `fhComb 4 1 ...` is
\(4q(1+x)^2G_4\); its positive multiplier is independent of shape.
Thus the caller still closes without `fhCLGd_pos_y` or `fh_LGd_link`.

This is a deliberately weaker interface than asserting the upper-face
sign on every point of its enlarged certificate box. Where
\(k_0>k_+\), that box has no actual caller. No sign is claimed there
by this replacement.

## 2. Factor-preserving definitions

Write

\[
c=1-t,\quad p=t+x,\quad W=1+x,\quad Y=x^2+2x,
\quad J=t+x^2+2x,\quad B=k+2tx+x^2,\quad e=q/W.
\]

Use precisely the incoming and logarithm bounds of the original note:

\[
T_G(x)=\frac{90-19x^2}{12(x^2+10x+15)},\qquad
V=1-\frac{cp}{W^2}+\frac{cx}{W^2}(T_G(x)-t),
\]

\[
L(q)=\frac{(q-1)(q^2+10q+1)}{6q(q+1)},\qquad
F_\ell=1+\frac{p^2q}{W^2}
        -\frac pW\frac{q^2+10q+1}{6(q+1)}.
\]

For free scalar arguments \(v,\ell\), put

\[
Z=v-1+t^2,\qquad H=kZ+t^2(2-t),
\qquad Q=t(k^2-kt+t^2)+HY+tvY^2,
\quad E_0=q^2B+W^2-2pqW,
\]

\[
\begin{aligned}
N={}&tBqWc+tq^2B^2-tBqp^2-tp^2W^2+tqWp^3\\
 &-tBqWp\ell-tBqW^2v-q^2Q+qWp(H+2tvY),\\
\mathcal T={}&3tE_0^2-4tvW^4
                 +4q^2W^2(H+2tvY)-4q^4Q,\\
F_4(v,\ell,k)={}&(5-Je^2)N
                 +\frac{qJ-pW}{4qW^2}\mathcal T.
\end{aligned}
\]

Then \(G_4=F_4(V,L,k)+F_\ell-V\). The last two terms are independent
of \(k\). These definitions are retained as products. The sign proof
below uses only the printed derivative polynomials, not a fully
expanded numerator for \(G_4\).

## 3. Small bounds for the scalar substitutions

Here \(1/5\le h\le1/4\), \(x>0\), and \(0\le y:=q-1\le h\le1/4\).
Also \(qJ-pW>0\), since

\[
J-pW=x(1-t)=xc>0.
\]

The following quadratic identity proves \(Je^2<15/16\):

\[
\begin{aligned}
\frac{15}{16}(1+2j)^2-J
&=\frac7{16}-\frac32h-h^2+\frac74j-2hj+\frac{11}{4}j^2\\
&=(1/4-h)(h+7/4+2j)+\frac54j+\frac{11}{4}j^2>0.
\end{aligned}
\tag{2}
\]

It has six monomials and degree two in \(h,j\). Moreover,

\[
J-p(1+2j)=hW-j^2=x(1+h)-j(1+j),
\]

\[
(1+h)(1+2j)-W=j+2hj\ge0.
\]

The expanded polynomials in the first equality are
\(h+h^2+hj-j^2\) (four monomials), and in the second equality
\(j+2hj\) (two monomials). The duration bound therefore gives

\[
\frac{qJ-pW}{x}
\le\frac{W(1+h)}{1+2j}\le(1+h)^2\le\frac{25}{16}.
\tag{3}
\]

Let \(U(t)=1-t+t^2\). One has \(V<U(t)\). In fact,

\[
U(t)-V=\frac{cx}{W^2}\{1-tW-T_G(x)\}.
\]

Since \(x\ge1/5\),

\[
\frac7{16}-T_G(x)=
\frac{97x^2+210x-45}{48(x^2+10x+15)}>0;
\]

the numerator increases on \([1/5,\infty)\), and at \(1/5\) equals
\(22/25\). The domain also gives

\[
tW\le\frac{(1-h)(1+12h/7)}2\le\frac{361}{672}<\frac{11}{20},
\]

using the three-monomial quadratic identity

\[
\frac{361}{672}-\frac{(1-h)(1+12h/7)}2
=\frac{576h^2-240h+25}{672}
=\frac{(24h-5)^2}{672}.
\]

Thus \(1-tW-T_G(x)>1/80\). Finally,

\[
y-L(q)=\frac{(q-1)^2(5q+1)}{6q(q+1)}\ge0.
\tag{4}
\]

Its numerator is \(5q^3-9q^2+3q+1\), four monomials of degree three.
The single logarithm majorant used here, \(\log q\le L(q)\) for
\(q\ge1\), is the original one; no replacement logarithm estimate is
needed for the shape argument.

## 4. Monotonicity of the shape derivative in the scalar arguments

Differentiate the displayed product formulas before substituting
\(V,L\). Since \(N\) is affine in \(k\),

\[
A_k:=-N_{kv}
 =xq\{1+tW+(x+2)y\}\ge xq>0.
\tag{5}
\]

In \(t,x,q\) the expanded polynomial is

\[
A_k=tx^2q+txq+x^2q^2-x^2q+2xq^2-xq.
\]

It has six monomials and total degree four in three variables. The
transport contribution gives, with no expansion of its products,

\[
(F_4)_{kv}=-(5-Je^2)A_k+q(qJ-pW)(1-Ye^2).
\]

Because \(Y\ge0\), equations (2), (3), and (5) imply

\[
(F_4)_{kv}
< -\frac{65}{16}A_k+\frac{25}{16}A_k
=-\frac52 A_k<0.
\tag{6}
\]

The other mixed derivative is

\[
(F_4)_{k\ell}=-(5-Je^2)tpqW<0.
\tag{7}
\]

Hence (4), (6), and \(V<U(t)\) yield

\[
\partial_kG_4=(F_4)_k(V,L,k)>(F_4)_k(U(t),y,k).
\tag{8}
\]

Also

\[
(F_4)_{kk}=-\frac{tq^3(qJ-pW)}{2W^2}<0.
\tag{9}
\]

This follows by differentiating only the two quadratic terms in
\(\mathcal T\): their second derivatives are \(6tq^4\) and
\(-8tq^4\). Consequently the right side of (8) is at least its
value at \(k=k_+\).

## 5. Endpoint derivative: four bivariate identities

At \(v=U(t),\ell=y,k=k_+\), collect the derivative in the single
variable \(y\), keeping the following bivariate coefficients opaque:

\[
\begin{aligned}
A_0&=tx^2-t^2x^2,&
A_1&=2x^2+x-2tx^2-tx,\\
b_0&=1-2t-x,&
b_1&=-8tx^2-10tx-6t+4x^2,\\
b_2&=5x^2+3x-4tx^2-2tx,\\
e_0&=5-t+8x+4x^2,&
e_1&=-2t-4x-2x^2,&
e_2&=-t-2x-x^2,\\
r_0&=x-tx,&r_1&=t+2x+x^2.
\end{aligned}
\tag{10}
\]

These have respectively 2, 4, 3, 4, 4, 4, 3, 3, 2 and 3 monomials;
their degrees are at most four. Differentiation of the product
definitions gives the two small univariate expressions

\[
\frac{N_k}{tq}=A_0+A_1y,
\qquad
\frac{\mathcal T_k}{2tq^2}=b_0+b_1y+b_2y^2.
\]

The first identity can be checked coefficient by coefficient from
\[
\begin{aligned}
\frac{N_k}{tq}={}&Wc+2qB-p^2-Wpy-W^2U(t)\\
&-q\{2k-t+(2t-1)Y\}+Wp(2t-1),
\end{aligned}
\]
and the second from
\[
\frac{\mathcal T_k}{2tq^2}
=3E_0+2W^2(2t-1)-2q^2\{2k-t+(2t-1)Y\}.
\]

Each coefficient check is an identity in \(t,x\) only. Multiplication
of the resulting univariate polynomials gives

\[
\left.(F_4)_k(U(t),y,k)\right|_{k=k_+}
=\frac{tq}{2W^2}\{d_0+d_1y+d_2y^2+d_3y^3\}.
\tag{11}
\]

Here all four polynomials are printed:

\[
\begin{aligned}
d_0={}&x(1-t)\{1-2t+(-2t^2+10t-1)x+16tx^2+8tx^3\},\\
d_1={}&t-2t^2+(12-23t+8t^2)x\\
 &+(35-52t+10t^2+4t^3)x^2
 +(43-60t+16t^2)x^3+(16-20t+4t^2)x^4,\\
d_2={}&-6t^2+(-16t-6t^2)x+(-5-27t+2t^3)x^2\\
 &+(-7-19t+8t^2)x^3+(-4-2t+2t^2)x^4,\\
d_3={}&x(1+x)(t+x^2+2x).
\end{aligned}
\tag{12}
\]

For direct checking, the four coefficient identities are

\[
\begin{aligned}
d_0&=2e_0A_0+r_0b_0,\\
d_1&=2(e_0A_1+e_1A_0)+r_0b_1+r_1b_0,\\
d_2&=2(e_1A_1+e_2A_0)+r_0b_2+r_1b_1,\\
d_3&=2e_2A_1+r_1b_2.
\end{aligned}
\tag{13}
\]

These are the only expansions needed for (11). Their expanded
polynomials have 11, 15, 12 and 5 monomials and degrees 6, 6, 6 and 4,
all in \(t,x\); their coefficients have absolute value at most 60.
In particular, do not verify (11) by expanding the entire original
three-variable residual in one ring call.

## 6. The cubic has a positive sign without a table

The factorizations in (12) show \(d_0,d_3>0\): for example,

\[
-2t^2+10t-1\ge-8/25+15/4-1=243/100>0.
\]

Each coefficient of \(d_2\), considered as a polynomial in \(x\), is
negative. For its last three coefficients it suffices to use

\[
-5-27t+2t^3<-5+16/125<0,
\]
\[
-7-19t+8t^2<-7+32/25<0,
\qquad -4-2t+2t^2<-4+8/25<0.
\]

Finally, the complete 15-monomial polynomial of degree six is

\[
\begin{aligned}
4d_1+d_2={}&4t-14t^2+(48-108t+26t^2)x\\
&+(135-235t+40t^2+18t^3)x^2\\
&+(165-259t+72t^2)x^3+(60-82t+18t^2)x^4.
\end{aligned}
\tag{14}
\]

Its constant and linear coefficients satisfy

\[
4t-14t^2+16/25=(2/5-t)(14t+8/5)\ge0,
\]

\[
48-108t+26t^2-224/25
=(2/5-t)(488/5-26t)\ge0.
\]

These are three-term univariate quadratics. Since \(x\ge1/5\),
the constant and linear terms of (14) together are at least
\(144/125\). Its remaining coefficients exceed
\(41,307/5,136/5\), respectively, by dropping their positive terms
and using \(t\le2/5\). Thus \(4d_1+d_2>0\).

Because \(d_2<0\) and \(0\le y\le1/4\),

\[
d_1+d_2y\ge d_1+d_2/4>0,
\]

and so

\[
d_0+y(d_1+d_2y)+d_3y^3>0.
\]

Equations (8)--(11) prove (1), including \(q=1\). Section 1 then
removes the upper-shape certificate from the actual high-ratio caller.

## Validation and remaining boundary

The four identities (13), the coefficient collections (10), and all
displayed factorizations have been checked with exact rational symbolic
arithmetic. Their displayed algebra is the proof; the computation is
only a transcription check. No Lean compilation or CI was run, and
this note does not claim a measured time or memory improvement.

The lower-face certificate `CertLGc` remains required until its own
replacement is proved. The low-t and low-ratio signs, and all requested
S1--S6 replacements, are separate obligations.
