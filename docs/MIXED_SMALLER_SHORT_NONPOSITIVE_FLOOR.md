# The opposite norm floor is redundant in the short-root comparison

Date: 2026-11-07. Hand proof, accepted in independent internal review.
The original nonpositive-diagonal lemma is reviewed in
[HAND_FURTHER_REFINEMENTS_AUDIT](HAND_FURTHER_REFINEMENTS_AUDIT.md).
The endpoint reductions and complete positive-diagonal exclusion are
reviewed in [HAND_ENDPOINT_REDUCTIONS_AUDIT](HAND_ENDPOINT_REDUCTIONS_AUDIT.md).

This removes the separate v=3/4 stopping face in
[MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION](MIXED_SMALLER_SHORT_ROOT_AND_ANGLE_REDUCTION.md).
For a nonpositive short diagonal, that face is impossible or already
lies on w=3/4. For a positive diagonal, Sections 6--11 exclude it.
The three other faces t=r, U(t)-v=0 and w=3/4 remain open.
Every sign below is a displayed scalar inequality; no runtime
certificate or large coefficient table is used.

## 1. Statement

Use the actual short-bridge geometry, retained throughout the scalar
comparison:

\[
1\le\alpha<x\le\beta\le\alpha x,\qquad
\alpha\ge\frac\beta x+\frac27(\beta-x),\qquad
r=\frac1{1+x},\quad 0<\rho\le rt,\quad 0<t\le r.
\]

Its fixed incoming norm satisfies

\[
\tfrac34<u\le V(x):=\operatorname{Sec}(1,x,x).
\]

The order and the bound u<=V(x) use only the integral/secant arguments
in Sections 1--2 of
[MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL](MIXED_GLOBAL_SHORT_BRIDGE_CENTRAL.md).
The later polynomial comparison in that note is not used here.

Define

\[
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,\quad
\lambda=[1+\rho(\alpha^2-1)]^{-1},\quad d=\lambda\rho D,
\]
\[
E=\frac{u-1}{r}+\frac{v-1}{t}
 +1+r+t-\rho+\log\frac{\rho}{rt},
\qquad w=\lambda^2v+d^2u-d\lambda E.
\]

**Lemma.** If D<=0 and v=3/4, then

\[
\boxed{E-\rho Du<0,\qquad w\le\tfrac34.}
\tag{1}
\]

The last inequality is strict if D<0, or if alpha>1. In particular,
within a comparison retaining w>=3/4, the face v=3/4 with D<=0 is
either impossible or already belongs to the face w=3/4.

Neither the upper Casimir cap nor the outer root is needed for this
lemma.

## 2. A short rational bound for the incoming norm

The secant integral gives

\[
V(x)-\frac34
=\frac1{4(x-1)}\int_1^x\frac{(s-x)^2}{(s+x)^2}\,ds
\le\frac{(x-1)^2}{12(x+1)^2}.
\]

Indeed \(s+x\ge1+x\), and the remaining integral of \((s-x)^2\)
is \((x-1)^3/3\). Put

\[
S=1+x,\qquad \bar u=\frac34+\frac{(x-1)^2}{12S^2}.
\tag{2}
\]

Thus u<=ubar by a single integral bound.

## 3. Move the central scalar expression to its upper endpoint

Write \(F_0=E-\rho Du\) and set v=3/4. At fixed rho,

\[
\frac{\partial F_0}{\partial t}
=\frac{(t-1/2)^2}{t^2}>0\qquad(0<t\le r<1/2).
\]

Raise t to r; this preserves rho<=rt. Then, holding t=r,

\[
\frac{\partial F_0}{\partial\rho}
=\frac1\rho-1-Du>0\qquad(0<\rho\le r^2<1/4, D\le0).
\]

Raise rho to r^2. These are comparisons of a scalar expression, with
all short-bridge ratios and u fixed. They yield

\[
F_0\le u\left(S-\frac D{S^2}\right)
       -\frac54S+1+\frac2S-\frac1{S^2}.
\tag{3}
\]

Since D<=0, the coefficient of u in (3) is positive. We may therefore
replace u by ubar from (2) when obtaining an upper bound.

## 4. One quadratic shape bound and one univariate sign

Put \(k=\beta/x\ge1\). The strengthened short order says

\[
\alpha\ge \frac{(7+2x)k-2x}{7}.
\]

D is strictly increasing in alpha, because its alpha derivative is
\(2(\alpha+\beta)>0\). Substituting this lower endpoint gives

\[
D\ge A k^2+B k+C,
\]
\[
A=\frac{(2x+7)(16x+7)}{49}>0,
\quad B=-\frac{2x(67x+14)}{49},
\quad C=1+2x+\frac{4x^2}{49}.
\tag{4}
\]

First, D<=0 forces x>2. If 1<x<=2, the derivative of the quadratic
in (4) is positive for k>=1: at k=1 it is

\[
2A+B=\frac{2(-35x^2+112x+49)}{49}>0.
\]

The numerator is a concave quadratic, positive at x=1 and x=2, hence
positive throughout [1,2]. The minimum over k>=1 is then at k=1,
where the quadratic is \(2+4x-2x^2\ge2>0\), a contradiction.

For x>=2, complete the square in (4):

\[
D\ge C-\frac{B^2}{4A}.
\tag{5}
\]

Insert (2) and (5) into the right side of (3). Collecting the displayed
quadratic expressions gives the following single-variable identity:

\[
\bar u\left(S-\frac{C-B^2/(4A)}{S^2}\right)
 -\frac54S+1+\frac2S-\frac1{S^2}
=-\frac{P(x)}{12S^4(2x+7)(16x+7)},
\tag{6}
\]
\[
\begin{aligned}
P(x)={}&160x^7+284x^6+1003x^5-141x^4\\
       &-4310x^3-5566x^2-2653x-441.
\end{aligned}
\]

The sign of this polynomial does not require a coefficient table. Divide
it by x^5:

\[
\frac{P(x)}{x^5}
=160x^2+284x+1003-\frac{141}x-\frac{4310}{x^2}
 -\frac{5566}{x^3}-\frac{2653}{x^4}-\frac{441}{x^5}.
\]

Every nonconstant term is strictly increasing on x>0. At x=2 its value
is \(6005/32>0\). Hence P(x)>0 for all x>=2. The denominator in (6)
is positive, so (3)--(6) prove \(F_0<0\).

Finally the exact transport identity is

\[
w=\lambda^2v-d\lambda F_0.
\]

For D<0, both d and F0 are negative, so
\(w<\lambda^2v\le v=3/4\). For D=0,
\(w=\lambda^2v\le v\), with strictness when alpha>1. This proves
(1) and the stated stopping-face consequence.

## 5. The remaining positive-diagonal floor question

In the root-preserving comparison, if \(1-\tau d\le0\), then
\(v'\ge0\), so the path cannot reach v=3/4 from an actual v>3/4.
Combined with the lemma above, a separate v-floor endpoint could only
remain when

\[
D>0,\qquad 0<\tau d<1.
\]

Use \(f(s)=s-s^{-1}-\log s\) and
\(h(s)=\log s-1+s^{-1}\), as in the reverse-root interface. Writing
\(C_0=-f(\tau)+u/r_A-f(1/r_A)-h(1/\rho_A)\), the fixed-root
equation gives

\[
(1-\tau d)w=\lambda^2v-d^2u+dC_0.
\]

Thus a sufficient further face-collapse inequality would be

\[
\tfrac34(1-\tau d-\lambda^2)+d^2u-dC_0\ge0.
\]

Sections 6--11 establish the needed exclusion on the remaining
positive-diagonal domain. The other three stopping faces remain open.

## 6. A simple localization of the remaining positive-diagonal face

At a remaining v=3/4 endpoint, retain D>0, the fixed outer root and
its norm ceilings, and the sharper reverse scale rho_A<1/7. The outer
central-pairing bound gives E_L<=3rho_A. Consequently

\[
E=2\rho Du-E_L/\lambda
\ge2\rho Du-3\alpha^2\rho> -\frac12,
\]

because \(\rho_A<1/7\) is equivalent to
\(\rho<1/(6\alpha^2+1)\), and hence
\(3\alpha^2\rho<1/2\).

On the other hand, raising t to r and then rho to r^2 increases E
when v=3/4. Applying (2) gives

\[
E\le(u-5/4)S+1+2/S-1/S^2
\le-\frac{5S}{12}+\frac23+\frac7{3S}-\frac1{S^2}
=:B(S).
\]

For S>2, the derivative
\(B'(S)=-5/12+(6-7S)/(3S^3)\) is strictly negative. At S=41/10,

\[
B(41/10)+\frac12=-\frac{431}{13448}<0.
\]

Thus the remaining positive-diagonal v-floor face necessarily satisfies
\(\boxed{x<31/10}\). This excludes its large-ratio tail by hand;
it does not exclude the entire remaining face.

## 7. A three-endpoint scalar target for the positive-diagonal remainder

Retain D>0 and \(c=1-\tau d>0\), and put

\[
q=1/\rho,\quad \sigma=\alpha^2-1,\quad
Q=\alpha(\alpha+\beta),\quad T_B=(\alpha+\beta)/\alpha.
\]

The root and w>=3/4 imply

\[
L_\tau:=\tfrac34(1-\lambda^2)+d^2u
 -d[\varphi(\tau)+uT_B-f(T_B)-h(1/\rho_A)]
=c(3/4-w)\le0,
\]

where \(\varphi(\tau)=3\tau/4-f(\tau)\). Its derivative is
\(-(\tau-2)^2/(4\tau^2)\le0\), and \(\varphi(2)=\log2\).
Since d>0 and tau>2, the expression L2 obtained by replacing tau by 2
is strictly smaller than L_tau, hence L2<0.

Multiplying L2 by the positive factor \((q+\sigma)^2\) gives the
explicit expression

\[
\begin{aligned}
\ell(q)={}&\tfrac34(2q\sigma+\sigma^2)+D^2u+D\alpha^2\\
&-D(q+\sigma)\left[(u-1)T_B+T_B^{-1}+1
                  +\log\frac{2Q}{q+\sigma}\right].
\end{aligned}
\tag{8}
\]

Thus ell(q)<0 is necessary at the floor face. But this scalar expression
is strictly increasing whenever q+sigma>=2Q. Indeed

\[
\ell'(q)=\tfrac32\sigma-D\left[(u-1)T_B+T_B^{-1}
                         +\log\frac{2Q}{q+\sigma}\right]>0.
\tag{9}
\]

The actual incident ceiling \(u\le U(1/T_B)\) makes the first two
terms inside brackets at most \(-1+2/T_B<0\); the logarithm is
nonpositive on the stated interval. Thus the sign in (9) needs no
secant approximation.

The retained central duration, outer scale and root interval give

\[
q\ge q_{\min}:=\max\{S^2,\ 6\alpha^2+1,\ 2Q-\sigma\}.
\]

The whole comparison interval from q_min to q lies in the domain of
(9). Consequently a remaining positive-diagonal floor point must satisfy

\[
\boxed{\ell(q_{\min})<0.}
\tag{10}
\]

This removes both the opposite-turn variable and the descending-root
parameter from the remaining floor question. At least one of the three
displayed lower bounds is an equality at q_min. The same short shape,
equal secants and x<31/10 are retained. No actual trajectory, root or
Casimir cap is asserted at this artificial scale endpoint. The following sections remove the T=2 alternative and prove positivity
on both remaining correctly enlarged endpoint domains.

## 8. One easy region of the outer-scale endpoint

Suppose the maximum in q_min is \(6\alpha^2+1\), and suppose
\(\alpha\ge4/3\). This region is excluded by a short quadratic
bound. Since q_min+sigma>=2Q, one has \(2<T_B\le7/2\).
Also x<31/10 and (2) imply

\[
u\le\frac34+\frac{147}{6724}<\frac{31}{40}.
\]

At this endpoint q+sigma=7alpha^2. Write
\(\delta=D/\alpha^2>0\) and

\[
B=(u-1)T_B+T_B^{-1}+1+\log(2T_B/7).
\]

The elementary inequality log z<=z-1 gives

\[
B\le(u-5/7)T_B+T_B^{-1}<\frac{87}{140}.
\]

Indeed the rational expression on the right is convex in T_B, so its
maximum on [2,7/2] is at an endpoint. Using u<31/40, its endpoint
values are at most 87/140 and 279/560, respectively.

Dividing (8) by alpha^4 now gives

\[
\frac{\ell(6\alpha^2+1)}{\alpha^4}
=\frac34(13-12\alpha^{-2}-\alpha^{-4})
                       +u\delta^2+(1-7B)\delta.
\]

For delta>0, completion of one square gives

\[
u\delta^2+(1-7B)\delta
>\frac34\delta^2-\frac{67}{20}\delta
\ge-\frac{4489}{1200}.
\]

The first term increases with alpha. At alpha=4/3 it is 4557/1024.
Consequently

\[
\boxed{\frac{\ell(6\alpha^2+1)}{\alpha^4}
>\frac{4557}{1024}-\frac{4489}{1200}
=\frac{54479}{76800}>0,}
\]

contrary to (10). Thus a surviving outer-scale endpoint must have
alpha<4/3. The following sections treat the remaining smaller-alpha
outer-scale region and the central-duration endpoint. The apparent T=2
endpoint is removed by the next hand lemma.

## 9. The T=2 endpoint cannot dominate

On the remaining positive-diagonal floor domain, the exact short
secants force

\[
\boxed{T_B<\frac72.}
\tag{11}
\]

Consequently
\(2Q-\sigma=\alpha^2(2T_B-1)+1<6\alpha^2+1\): the third
entry in q_min is redundant. This statement concerns the fixed short
geometry. It does not assert that an artificial comparison endpoint is
an actual reverse root.

Here is a two-step convexity proof of (11). We use the slightly sharper
elementary incoming-norm bound

\[
u\le V(x)\le\overline V(x)
:=\frac34+\frac{R^2}{12+5R},\qquad R=\frac{x-1}{x+1}.
\tag{12}
\]

For completeness, this is equivalent to

\[
\log(1+R)\ge\frac{R}{1+R}
 \left(1+\frac R2-\frac{2R^2}{12+5R}\right).
\]

The difference vanishes at R=0 and has derivative
\(R^3(16-5R)/[2(1+R)^2(12+5R)^2]>0\) for 0<R<1.
Thus (12) has a short independent proof; the coefficient certificate
later in the earlier short-upper-endpoint note is not used. Both R and
\(R^2/(12+5R)\) increase with x.

Suppose, to obtain a contradiction, that T_B>=7/2, equivalently
beta>=5alpha/2. The order beta<=alpha*x implies x>=5/2.
The other equal secant has the integral representation

\[
u=\frac1{x-\alpha}\int_\alpha^x
       \left(1-\frac{\beta s}{(\beta+s)^2}\right)\,ds.
\]

The integrand has second derivative
\(2\beta(2\beta-s)/(\beta+s)^4>0\) on
\([\alpha,x]\), because x<=beta. Jensen's inequality and
\(g(z)=1-z/(1+z)^2\) therefore give

\[
u\ge g\left(\frac{\alpha+x}{2\beta}\right)
 =g\left(\frac{2\beta}{\alpha+x}\right),
\tag{13}
\]

where g increases on [1,infinity), and 2beta/(alpha+x)>1.

First use x<31/10 from Section 6. Formula (12) gives

\[
u<\frac34+\frac{441}{24477}<\frac{77}{100}
 <\frac{151}{196}=g(9/5).
\]

By (13), beta<9(alpha+x)/10. Combining this with
beta>=5alpha/2 gives alpha<9x/16. Since alpha<x, the coefficient
of beta in D is negative, so

\[
D\le 6\alpha^2-5\alpha x+1+2x.
\tag{14}
\]

For fixed x, the right side is a convex quadratic in alpha. On
\([1,9x/16]\), its maximum is at an endpoint, with values

\[
7-3x,\qquad 1+2x-\frac{117x^2}{128}.
\]

If x>=8/3, the first is at most -1, and the second is at most its
value -1/6 at x=8/3, since its derivative is negative for x>=8/3.
That contradicts D>0. Hence x<8/3.

Apply (12) once more at this improved endpoint:

\[
u<\frac34+\frac{25}{1727}<\frac34+\frac1{64}
 =\frac{49}{64}=g(5/3),
\]

where the middle inequality is exactly 1600<1727. Formula (13)
now gives beta<5(alpha+x)/6. Together with beta>=5alpha/2, this
implies alpha<x/2. The maximum of the convex quadratic in (14)
on \([1,x/2]\) is again at an endpoint, now with values

\[
7-3x,\qquad 1+2x-x^2.
\]

For x>=5/2, these are at most -1/2 and -1/4, respectively.
Both decrease thereafter. This final contradiction with D>0 proves
(11), and therefore removes the T=2 endpoint entirely.

The positive-diagonal floor question is now reduced to
\(q_{\min}=\max\{(1+x)^2,6\alpha^2+1\}\), with
\(T_B<7/2\), and with alpha<4/3 whenever the outer-scale entry
dominates. The next section excludes this last outer-scale region.

## 10. The entire outer-scale endpoint is positive

**Status:** accepted in independent internal review. The argument and the
seven displayed polynomial coefficients were checked independently.

We now prove

\[
\boxed{q_{\min}=6\alpha^2+1
       \quad\Longrightarrow\quad\ell(q_{\min})>0.}
\tag{15}
\]

Section 8 treats alpha>=4/3, so assume 1<=alpha<4/3. Scale
dominance gives

\[
x\le\sqrt{6\alpha^2+1}-1<\sqrt{35/3}-1<5/2.
\]

By (12), as already used in Section 9, this implies u<49/64.
Recall the notation

\[
\delta=D/\alpha^2>0,\qquad
B=(u-1)T_B+T_B^{-1}+1+\log(2T_B/7),
\]
\[
\frac{\ell(6\alpha^2+1)}{\alpha^4}
=A(\alpha)+u\delta^2+(1-7B)\delta,
\quad
A(\alpha)=\frac34(13-12\alpha^{-2}-\alpha^{-4}).
\tag{16}
\]

### A uniform bound on the logarithmic bracket

Replace u by 49/64 in B. On T_B>2, the resulting function has
derivative

\[
-\frac{15}{64}-T_B^{-2}+T_B^{-1}
=-\frac{15(T_B-8/5)(T_B-8/3)}{64T_B^2}.
\]

Its maximum is therefore at T_B=8/3, with value
3/4+log(16/21). The first two positive terms of the atanh series
give

\[
\log\frac{21}{16}
>\frac{10}{37}+\frac{250}{3\cdot37^3}
=\frac{19}{70}+\frac{5179}{10637130}
>\frac{19}{70}.
\]

Consequently B<67/140. With u>3/4 and delta>0, (16) yields

\[
\frac{\ell(6\alpha^2+1)}{\alpha^4}
>A(\alpha)+\frac34\delta^2-\frac{47}{20}\delta.
\tag{17}
\]

### The interval alpha>=10/9

The quadratic in (17) is at least -2209/1200. Also A increases
with alpha. Thus, for alpha>=10/9,

\[
\frac{\ell(6\alpha^2+1)}{\alpha^4}
>A(10/9)-\frac{2209}{1200}
=\frac{78717}{40000}-\frac{2209}{1200}
=\frac{15251}{120000}>0.
\]

### The interval 1<=alpha<=10/9

Here the short order supplies the needed positive lower bound on D.
Since alpha<x and beta<=alpha*x,

\[
D\ge(\alpha^2+1)(1+2x)-2\alpha x^2.
\]

The right side decreases with x for x>=alpha, since its x derivative
is at most 2(1-alpha^2)<=0. Insert the largest allowed x,
namely sqrt(6alpha^2+1)-1. With S_*=sqrt(6alpha^2+1), this gives

\[
D\ge(\alpha+1)^2(2S_*-1)-2\alpha(6\alpha^2+1).
\tag{18}
\]

The function sqrt(6alpha^2+1) is strictly convex in alpha. Its
value and derivative at alpha=1 satisfy

\[
\sqrt7>\frac{37}{14},\qquad
\frac6{\sqrt7}>\frac94;
\]

these follow by squaring, from 1372>1369 and 576>567. Its tangent
line at 1 therefore implies

\[
S_*>\frac{37}{14}+\frac94(\alpha-1)
     =\frac{63\alpha+11}{28}.
\]

Substitution into (18) yields

\[
\delta>\delta_0(\alpha)
:=\frac{-105\alpha^3+123\alpha^2+29\alpha-3}
          {14\alpha^2}.
\tag{19}
\]

This lower bound decreases on alpha>=1: its derivative is
\(-15/2-29/(14\alpha^2)+3/(7\alpha^3)<0\).
Consequently, on the interval under consideration,

\[
\delta_0(\alpha)\ge\delta_0(10/9)
=\frac{9001}{4200}>\frac{47}{30}.
\]

The quadratic \(3\delta^2/4-47\delta/20\) increases above
47/30, so (17) may be bounded below by substituting delta_0.
The remaining calculation is the following single polynomial identity.
Put z=alpha-1>=0. Then

\[
\begin{aligned}
3920\alpha^4
 \left[A(\alpha)+\frac34\delta_0(\alpha)^2
                   -\frac{47}{20}\delta_0(\alpha)\right]
={}&165375z^6+673890z^5+981696z^4+592762z^3\\
 &+114624z^2-2064z+88.
\end{aligned}
\tag{20}
\]

All terms of degree at least three are nonnegative. The remaining
quadratic is explicitly positive:

\[
114624z^2-2064z+88
=114624\left(z-\frac{43}{4776}\right)^2
  +\frac{15663}{199}>0.
\]

Thus (17)--(20) give ell(6alpha^2+1)>0 on this final interval.
Together with the preceding cases, this proves (15) by hand. There is
no runtime sign check or unlisted coefficient assertion in this proof.

Combining Sections 7--10, any still-possible positive-diagonal
v=3/4 endpoint must have

\[
\boxed{q_{\min}=(1+x)^2>6\alpha^2+1,\qquad
       \ell((1+x)^2)<0.}
\tag{21}
\]

Section 11 resolves the central-duration scalar sign in (21).
The other root-comparison faces remain outside the scope of this note.

## 11. The central-duration endpoint is positive

**Status:** accepted in independent internal review. The derivative,
endpoint and constrained-minimum arguments were checked independently.

We prove the last scalar sign from (21):

\[
\boxed{q=(1+x)^2\ge6\alpha^2+1
       \quad\Longrightarrow\quad\ell(q)>0.}
\tag{22}
\]

All hypotheses retained above remain in force, including D>0,
x<31/10 and 2<T_B<7/2. This is a comparison of explicit scalar
expressions; no artificial endpoint is assigned a physical trajectory
or an original Casimir cap.

### Normalize the remaining scale parameter

Put

\[
K=\frac{q+\alpha^2-1}{\alpha^2}\ge7,\qquad
\varepsilon=1-\alpha^{-2},\qquad \delta=D/\alpha^2>0,
\]
\[
A_K=\frac34(2K\varepsilon-\varepsilon^2),\qquad
B_K=(u-1)T_B+T_B^{-1}+1+\log(2T_B/K).
\]

Then (8) becomes the exact identity

\[
\frac{\ell(q)}{\alpha^4}
=A_K+u\delta^2+(1-KB_K)\delta.
\tag{23}
\]

Notice that \(A_K\ge A_7=A(\alpha)\) from (16). Also

\[
B_K=B_7+\log(7/K).
\tag{24}
\]

### First reduce alpha to the interval [1,10/9)

The bound x<31/10 and (12) give u<77/100. For 0<z<=1,
the elementary atanh inequality gives
\(\log z\le2(z-1)/(z+1)\). Apply it with z=2T_B/7,
which is less than one. Writing y=T_B-2>0, direct subtraction gives

\[
-\frac{23}{100}T_B+T_B^{-1}+1
       +\frac{2(2T_B-7)}{2T_B+7}-\frac12
=-\frac{12+y(46y^2-63y+46)}
       {100T_B(2T_B+7)}<0.
\tag{25}
\]

The quadratic in the numerator is positive: its discriminant is
\(63^2-4\cdot46^2=-4495<0\). Hence \(B_7<1/2\).
The function \(K[1/2-\log(K/7)]-1\) strictly decreases for
K>=7 and equals 5/2 at K=7. Consequently (23)--(24) give

\[
\frac{\ell(q)}{\alpha^4}
>A_7+\frac34\delta^2-\frac52\delta
\ge A_7-\frac{25}{12}.
\]

For alpha>=9/8 the last expression is positive, since A_7 increases
with alpha and

\[
A_7(9/8)-\frac{25}{12}
=\frac{18989}{8748}-\frac{25}{12}
=\frac{191}{2187}>0.
\]

Thus only alpha<9/8 remains. Since beta>=x and alpha<x,

\[
D\le\alpha^2+2\alpha x+1+2x-2x^2
<\frac{145}{64}+\frac{17x}{4}-2x^2.
\]

The last quadratic is decreasing for x>=8/3, and at 8/3 its value
is -359/576. Therefore D>0 forces x<8/3. Formula (12) now gives
u<49/64.

The sharper bracket bound of Section 10 applies:
\(B_7<67/140\). The function
\(K[67/140-\log(K/7)]-1\) also strictly decreases for K>=7,
with value 47/20 at K=7. Hence

\[
\frac{\ell(q)}{\alpha^4}
>A_7+\frac34\delta^2-\frac{47}{20}\delta.
\]

The completed-square estimate in Section 10 excludes alpha>=10/9
with the same positive surplus 15251/120000. It remains to prove
(22) when \(1\le\alpha\le10/9\).

### A lower bound for the diagonal, as a function of K

Fix alpha in this last interval and define

\[
\sigma=\alpha^2-1,\quad C=(\alpha+1)^2,\quad
S_K=\sqrt{(K-1)\alpha^2+1}.
\]

Because q=(1+x)^2, one has x=S_K-1. The short order
beta<=alpha*x and the negative beta coefficient in D imply

\[
\delta\ge\delta_*(K):=
\frac{C(2S_K-1)}{\alpha^2}
             -2\alpha(K-1)-\frac2\alpha.
\tag{26}
\]

This is the same elementary lower bound for D used in (18);
here its dependence on K is retained. In particular,

\[
\delta_*'(K)=\frac C{S_K}-2\alpha<0,\qquad
\delta_*''(K)=-\frac{\alpha^2C}{2S_K^3}.
\tag{27}
\]

For the strict first sign, \(S_K\ge S_7>\alpha+1\), because
\(S_7^2-(\alpha+1)^2=\alpha(5\alpha-2)>0\).

Set

\[
b(K)=K[67/140-\log(K/7)]-1,\qquad
\mathcal H(K)=\delta_*(K)-\frac43b(K).
\]

The bracket estimate and (23) give

\[
\frac{\ell(q)}{\alpha^4}
>A_K+\frac34\delta^2-b(K)\delta.
\tag{28}
\]

The key elementary fact is

\[
\boxed{\mathcal H'(K)>0\qquad(K\ge7).}
\tag{29}
\]

Indeed \(b'(K)=67/140-1-\log(K/7)<0\) and
\(b''(K)=-1/K\), so

\[
\mathcal H''(K)
=-\frac{\alpha^2C}{2S_K^3}+\frac4{3K}>0.
\]

For the last strict inequality, multiply by positive factors and use
\(\alpha^2K=S_K^2+\sigma\). It is equivalent to

\[
3C(1+\sigma/S_K^2)<8S_K.
\]

Here \(C\le361/81<9/2\), \(\sigma\le19/81<1/4\),
and \(S_K\ge\sqrt7>5/2\). The left side is therefore less than
\(3(9/2)(1+1/25)=351/25<20\), while the right side exceeds 20.

It remains to check the initial derivative. The function

\[
\alpha\longmapsto
\frac{(\alpha+1)^2}{\sqrt{6\alpha^2+1}}-2\alpha
\]

strictly decreases for alpha>=1: differentiating gives

\[
\frac{2(\alpha+1)}{\sqrt{6\alpha^2+1}}
-\frac{6\alpha(\alpha+1)^2}{(6\alpha^2+1)^{3/2}}-2<0,
\]

since the first term is less than 2. At alpha=10/9,
\(\sqrt{6\alpha^2+1}=\sqrt{681}/9<29/10\). Therefore

\[
\mathcal H'(7)
>\frac{3610}{2349}-\frac{20}{9}+\frac{73}{105}
=\frac{809}{82215}>0.
\]

Together with the positive second derivative, this proves (29).

### The constrained quadratic minimum remains positive

If b(K)<=0, the right side of (28) is positive because delta>0
and A_K>=0. Suppose b(K)>0. Minimize the displayed quadratic
over its valid enlarged domain
\(\delta\ge\max\{0,\delta_*(K)\}\). Its minimum is

\[
M(K)=
\begin{cases}
A_K+\frac34\delta_*(K)^2-b(K)\delta_*(K),
       &\delta_*(K)\ge2b(K)/3,\\[2mm]
A_K-b(K)^2/3,&\delta_*(K)\le2b(K)/3.
\end{cases}
\tag{30}
\]

The branches agree, including their first derivatives, at the displayed
transition.

If \(\mathcal H(K)\ge0\), then
\(\delta_*(K)\ge4b(K)/3\); the quadratic is nonnegative on its
entire permitted interval, and hence M(K)>=A_K>=0. The strict
inequality (28) already proves ell(q)>0 in this case.

Consider instead the interval where \(\mathcal H(K)<0\).
By (29), this is either empty or an initial interval starting at K=7.
On the first branch of (30), write

\[
M=A_K+\frac34\delta_*\mathcal H.
\]

Then

\[
M'=A_K'+\frac34
       [\delta_*'\mathcal H+\delta_*\mathcal H']>0.
\]

Both terms in brackets are strictly positive: delta_*'<0,
\(\mathcal H<0\), and delta_*>=2b/3>0, while
\(\mathcal H'>0\). Also \(A_K'=3\varepsilon/2\ge0\).
On the second branch of (30),

\[
M'=A_K'-\frac23bb'>0.
\]

Consequently M is strictly increasing throughout this initial interval.

Its initial value is positive by the already displayed algebra in
Section 10. More precisely, (19) gives
\(\delta_*(7)>\delta_0(\alpha)>47/30=2b(7)/3\),
and (20), with its completed square, gives

\[
M(7)
=A_7+\frac34\delta_*(7)^2-\frac{47}{20}\delta_*(7)>0.
\]

This use of K=7 is solely a comparison of explicit scalar functions.
No physical trajectory, reverse root or Casimir condition is asserted
there. Thus M>0 wherever \(\mathcal H<0\), completing all cases
in (30). Equation (28) proves (22).

### Consequence for the root-preserving comparison

Sections 8--11 exclude both possible maxima in q_min. Therefore no
positive-diagonal v=3/4 endpoint satisfying the retained root and norm
bounds exists. For D<=0, Sections 1--4 show that such an endpoint is
either impossible or is also on w=3/4.

The separate opposite-norm floor face is therefore redundant:
the root-preserving comparison need only stop on

\[
\boxed{t=r,\qquad U(t)-v=0,\qquad w=3/4.}
\]

Those three other faces still require hand exclusions. This conclusion
does not claim that the smaller-short branch, or the global hand proof,
is complete.
