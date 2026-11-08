# Outer upper-ratio tests: reciprocal-shape convexity

This note replaces the large shape-derivative and three-variable
expansions in (11)--(18) of
[the archived outer-ratio sign](../../archive/notes/MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_SIGN.md).
It is a reduction lemma. The [assembly](SHORT_RATIO_OUTER_COMPLETE.md)
supplies its terminal signs and records the actual caller.

We use the archive's exact transport and duration tests (3),(6), with
\(H_0,H_1\) retaining their exact logarithm. Put

\[
S=x+1,\quad b=x+c(a-1),\quad r=1/a,\quad
e=x-c,\quad d=1+c,\quad Z=d+er=(a+b)/a.
\]

The fixed-norm result is

\[
\boxed{(H_j)_{rr}>\frac12\quad(j=0,1)}
\tag{1}
\]

on the rectangle with a moving lower edge

\[
\frac{13}{6}\le x\le\frac{12}{5},\quad
\frac58\le c\le\frac78,\quad
\frac1x\le r\le\frac56,\quad
\frac34\le u\le\frac45.
\tag{2}
\]

The incoming norm used for smaller shapes is

\[
u_s=\frac34+
\frac{17(x-1)^3/(240S^2)+(b-x)/1200}{b-1}.
\tag{3}
\]

On \(2/3\le r\le5/6\), the moving-norm version satisfies

\[
\boxed{\frac{d^2}{dr^2}H_j(x,r,c;u_s(r))>\frac25.}
\tag{4}
\]

Thus a maximum in reciprocal shape occurs at an endpoint. No strict
outgoing floor, Casimir cap or equal-secant relation is used at the
continued scalar points.

## 1. Keep the transport quartic before expanding

Define

\[
\begin{aligned}
d_0&=1+2c,&d_1&=2(x-cS),&d_2&=1+2x-2x^2+2cx,\\
D_r&=d_0+d_1r+d_2r^2,&
E_0&=S(u-1)+S^{-1},&J_2&=Su+S-1+S^{-1}.
\end{aligned}
\]

The original formulas give

\[
49w=W(r)=\sum_{i=0}^4W_ir^i,
\qquad 7E_L=2uD_r-6E_0-J_2r^2,
\tag{5}
\]

where the complete coefficient formulas are

\[
\begin{aligned}
W_0&=36+ud_0^2-6d_0E_0,\\
W_1&=d_1(2ud_0-6E_0),\\
W_2&=12-6S+u(d_1^2+2d_0d_2)-6d_2E_0-d_0J_2,\\
W_3&=d_1(2ud_2-J_2),\\
W_4&=(S-d_2)(S-1+S^{-1}-ud_2)
     =x(2x-1-2c)(S-1+S^{-1}-ud_2).
\end{aligned}
\tag{6}
\]

In particular, the tests are

\[
H_j=\frac67+(u-1)Z+Z^{-1}-E_L+
m_j(W/49-3/4)+\log(2Z/7),
\quad m_0=4-Z/2,\quad m_1=7/Z+1/4.
\tag{7}
\]

All differentiations in \(r\) below keep \(x,c,u\) fixed. Norm affinity
allows every polynomial sign to be checked at \(u=3/4,4/5\) before
expanding in \(x,c\). In particular (5)--(7) are not expanded as a
polynomial in four variables.

Direct endpoint bounds in (2) give

\[
\frac54<e<\frac95,\quad 3<S\le\frac{17}{5},\quad
\frac94\le d_0\le\frac{11}{4},\quad
-\frac54<d_1\le\frac{11}{20},\quad
-3<d_2\le-\frac{19}{72},
\]
\[
-\frac35<E_0<0,\qquad \frac{14}{3}<J_2<6.
\tag{8}
\]

For \(E_0,J_2\), use their monotonicity in \(S,u\), with
\(19/6\le S\le17/5\). The derivatives of \(d_2\) have fixed signs.
These bounds imply

\[
-50<W_2<-16,\qquad W_3>-6,\qquad W_4>7.
\tag{9}
\]

For the upper bound on \(W_2\), discard its two negative terms involving
\(d_2\): the remaining upper bound is
\(-7+5/4-21/2=-65/4\). For the lower bound, discard \(ud_1^2\)
and use
\(-42/5-66/5-54/5-33/2=-489/10>-50\).
When \(d_1\le0\), \(W_3\ge0\); otherwise
\(W_3>-(11/20)(6+24/5)>-6\).
Finally \(W_4=S^2-S+1+ud_2^2-J_2d_2>7\).

## 2. The first test

Differentiating (7) three times gives the small identity

\[
(H_0)_{rrr}=
\frac{\{3(7-c)-12er\}W_3-3eW_2+
       \{12(7-c)r-30er^2\}W_4}{49}
 +\frac{2e^3(Z-3)}{Z^4}.
\tag{10}
\]

Here \(5/12\le r\le5/6\), \(Z\ge2\),

\[
0<3(7-c)-12er<13,
\qquad 12(7-c)r-30er^2>21.
\]

For the second bound, the concave quadratic
\((147/2)r-54r^2\) has endpoint values \(85/4,95/4\).
Equations (9),(10) therefore give

\[
(H_0)_{rrr}>\frac{-78+60+147}{49}-\frac{729}{1000}>0.
\tag{11}
\]

It remains to check the second derivative at \(r=1/x\).
Write \(Z_b=2+c-c/x\), and let

\[
Q_0=\frac{2(J_2-2ud_2)}7+
 \frac{(4-Z_b/2)W''(1/x)-eW'(1/x)}{49}.
\tag{12}
\]

The two degree-eight identities A in the
[algebra companion](SHORT_RATIO_OUTER_RECIPROCAL_ALGEBRA.md)
prove \(Q_0>5/8\). Since

\[
(H_0)_{rr}(1/x)=Q_0+e^2\frac{2-Z_b}{Z_b^3},
\qquad \frac{Z_b-2}{Z_b^3}\le\frac1{27},
\]

the pole contribution is greater than \(-3/25>-1/8\).
Together with (11), this proves (1) for \(j=0\).

## 3. The second test

Set

\[
\xi=-d/e,\quad R=W(\xi)/7-17/4,\quad L=e^4R.
\tag{13}
\]

This residue has a small source identity. With

\[
T=-(3+2c)x^2+(2+8c+4c^2)x+1+2c,
\]

one has \(e^2D_\xi=T\), and

\[
\begin{aligned}
28SL={}&25Se^4+4(12-6S)Sd^2e^2+4S(S^2-S+1)d^4+4SuT^2\\
&-4T\{6[S^2(u-1)+1]e^2+[S^2u+S^2-S+1]d^2\}.
\end{aligned}
\tag{14}
\]

The two degree-seven identities B in the companion prove \(L>0\).
Polynomial division only in \(r\), with the coefficients (6) retained,
gives

\[
(H_1)_{rrr}=A(r)-\frac{6e^3R}{Z^4}+\frac{2e^3}{Z^3},
\quad
A(r)=\frac{3W_3}{98}+\frac{6W_4r}{49}+\frac{6W_4}{7e}.
\tag{15}
\]

By (9), \(A>0\) and \(A'>0\). Consequently

\[
\{Z^4(H_1)_{rrr}\}'=A'Z^4+4eAZ^3+2e^4>0.
\tag{16}
\]

At the lower edge, \(7/3<Z_b<8/3\). The two degree-seven
identities D prove

\[
\mathcal D=W_4(7/3)^4-7L-(3e/14)(7/3)^4>0.
\tag{17}
\]

Indeed \(6W_4/(7e)-9/49>0\), so (15) at \(1/x\) gives

\[
Z_b^4(H_1)_{rrr}(1/x)
>\frac6{7e}\mathcal D>0.
\]

Equation (16) proves \((H_1)_{rrr}>0\) everywhere in (2).

For the initial second derivative, division by the same linear factor
gives

\[
\begin{aligned}
(H_1)_{rr}={}&\frac{2(J_2-2ud_2)}7+\frac{W''}{196}
 +\frac{6W_4r}{7e}+\frac{2W_3}{7e}-\frac{2dW_4}{7e^2}
 +\frac{2e^2R}{Z^3}-\frac{e^2}{Z^2}.
\end{aligned}
\tag{18}
\]

At \(r=1/x\), use

\[
\frac{W''}{196}>-\frac{65}{98}>-\frac23,
\quad -\frac{e^2}{Z_b^2}>-\frac35,
\quad \frac{2e^2R}{Z_b^3}>\frac{27L}{256e^2}.
\]

The two degree-seven identities C prove

\[
\mathcal C=
\frac{2(J_2-2ud_2)}7-\frac23+
\frac{6W_4}{7ex}+\frac{2W_3}{7e}-\frac{2dW_4}{7e^2}
+\frac{27L}{256e^2}-\frac35-\frac12>0.
\tag{19}
\]

Thus \((H_1)_{rr}(1/x)>1/2\), and its increasing derivative proves
(1) for \(j=1\).

## 4. Moving the smaller-shape norm

For this section restrict to \(2/3\le r\le5/6\). Set

\[
f=x-c-1>0,\quad
k(x)=\frac{17(x-1)^3}{240S^2}-\frac{x-1}{1200}.
\]

Equation (3) becomes

\[
u_s=\frac{901}{1200}+\frac{k r}{c+fr},\qquad
u_s'>0,\qquad
-u_s''=\frac{2kcf}{(c+fr)^3}.
\tag{20}
\]

Here \(0<k<1/50\). Positivity follows from
\(85(x-1)^2>S^2\); the positive first term is increasing and its
value at \(12/5\) is \(343/20400<1/50\).
For \(v=fr/c\), the elementary maximum
\(v/(1+v)^3\le4/27\) gives

\[
0<-u_s''\le\frac{8k}{27cr}<\frac{16}{1125}<\frac1{60}.
\tag{21}
\]

The norm remains within (2): it is at least \(3/4\), and (20) gives
\(u_s<901/1200+(1/50)(5/6)/(5/8)<4/5\).

The necessary norm coefficients can be bounded without expanding a
three-variable derivative. Put

\[
N_u=S(6+r^2),\qquad j=N_u-2D_r,\qquad
t=D_r(N_u-D_r).
\]

On this smaller rectangle, \(D_r\) decreases in \(x,c,r\), so

\[
\frac{53}{72}\le D_r\le\frac{154}{81}<2,
\qquad D_r'<0.
\tag{22}
\]

In detail, \((D_r)_c=2(1-r)(1-xr)<0\) and
\((D_r)_x=2r\{1-c+(1-2x+c)r\}<0\).
For \((D_r)_r=d_1+2d_2r\), it is enough to check the two c endpoints:
at \(7/8\) both coefficients are negative; at \(5/8\) use
\(d_1\le11/20,d_2\le-97/72,r\ge2/3\).
The two extreme values then give (22).

Consequently

\[
19<N_u<23,\quad15<j<23,\quad
\frac{901}{72}<t<50,\quad
\frac52<Z<\frac{19}{6},\quad
\frac{12}{5}<m_j<\frac{13}{4}.
\tag{23}
\]

Norm affinity in (7) gives the exact identities

\[
(H_j)_u=Z+j/7-m_jt/49,
\]
\[
(H_j)_{ru}=e+j'/7-m_j't/49-m_jt'/49.
\tag{24}
\]

The lower bound in (23) gives \((H_j)_u>1\), while

\[
(H_j)_u<\frac{19}{6}+\frac{23}{7}-\frac{901}{1470}<6.
\]

Also \(j'=2Sr-2D_r'>0\), \(m_j'<0\), and
\(t'=D_r'j+2SrD_r<34/3\). Hence

\[
(H_j)_{ru}>\frac54-\frac{13}{4}\frac{34}{147}>0.
\tag{25}
\]

Finally the chain rule, norm affinity, (1), and (21)--(25) give

\[
\frac{d^2}{dr^2}H_j(x,r,c;u_s(r))
=(H_j)_{rr}+2(H_j)_{ru}u_s'+(H_j)_u u_s''
>\frac12-\frac6{60}=\frac25.
\]

This proves (4) on the entire smaller-shape comparison interval.

## Expansion boundary

The [companion](SHORT_RATIO_OUTER_RECIPROCAL_ALGEBRA.md) prints every
polynomial used in A--D and its elementary positive lower bound.
Each has 26 or 29 monomials after the rational shift, in two variables,
and degree at most eight. The source quartic is differentiated before
substitution; norm affinity removes \(u\) before any bivariate expansion.
The identity \(W_4=x(2x-1-2c)(S-1+S^{-1}-ud_2)\) removes its displayed
factor \(x\) before the initial-edge denominators are cleared.
No coefficient-table oracle, interval search, or enlarged three-variable
polynomial is a premise of this proof.
