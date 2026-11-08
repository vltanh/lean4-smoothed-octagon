# Central displacement: a small shape derivative proof

This replaces Section 2, equations (4)–(10), of
[`MIXED_SMALLER_SHORT_DISPLACEMENT_CENTRAL_FACE`](../../archive/notes/MIXED_SMALLER_SHORT_DISPLACEMENT_CENTRAL_FACE.md).
It proves the derivative sign needed by the actual caller. The larger
rectangle in that note is unnecessary: the comparison path already has
`a >= a_min(x)` and the central square cap. The beta comparison in Section 1
and the final one-variable signs in Section 3 of that source are separate,
unchanged dependencies. In particular this note does not claim to replace
Section 3's large endpoint numerators.

## 1. Domain, definitions, and the derivative to bound

Throughout,

\[
2\le x\le13/6,\qquad a_m=(15x+511)/475\le a,
\qquad a^2\le x(x+2)/6,
\]
\[
C=(15x+36)/25,\qquad B=x/C,\qquad b=x+B(a-1).
\tag{1}
\]

Use the source definitions

\[
S=1+x,\quad K=x(x+2)+a^2,\quad q=a^2/K,\quad p=a/(a+b),
\quad T=p/q,\quad k=5a-1,
\]
\[
D=a^2+2ab+1+2x-2bx,\quad d=D/K,\quad \lambda=S^2/K,
\quad v=1-S^{-1}+S^{-2},
\]
\[
g=\frac{(x-1)^2(71x^2+48x+1)}{96xS(13x^2+14x+3)},
\quad
u=\frac34+\frac{(x-1)g+(b-x)/5808}{b-1},
\]
\[
E=S(u-1)+3/S-1/S^2,\quad
w=\lambda^2v+d^2u-d\lambda E,\quad E_L=2du-\lambda E.
\]

The incoming ceiling is the same as in the source. Put

\[
y=2/T,\quad n_0=2+4(4-3y)/k,\quad n_1=T+4/k,
\]
\[
J=(u-1)/p+p+1-q-E_L+\log y,\qquad F_i=J+n_i(w-3/4).
\]

All hypotheses of the
[central beta lemma](../../archive/notes/MIXED_SMALLER_SHORT_DISPLACEMENT_CENTRAL_BETA.md)
hold on (1), as shown in the source's Section 1. We use its already small
bounds

\[
\frac34+\frac{13}{2000}<u<\frac{19}{25},\quad
\frac16<d<\frac13,\quad \frac{20}{7}<\lambda S<\frac{19}{6},
\quad E_L<\frac3{10},
\]
\[
\frac13\le p<\frac12,\quad \frac34<y\le\frac67,
\quad \frac73\le T<\frac83,\quad
3<n_i<\frac{53}{15},\quad k\ge\frac{89}{19}.
\tag{2}
\]

Set

\[
L=2a/K,\quad A=1+2B+(x-B-Bx)/a,
\quad z=2/a-L-(x-B)/(a(a+b)),
\]
\[
N_0=-12yz/k-20(4-3y)/k^2,
\qquad N_1=-Tz-20/k^2.
\]

The source's chain-rule identity, with \(e=LA\), is

\[
\begin{aligned}
H_i:=\frac{d}{da}F_i(x,a,b(x,a))
={}&\frac{x-B}{a^2}\{1-p+p^2-u\}
+\frac{2(1-q)^2}{a}\\
&+LA(n_iE_L-2u)+L(E_L-2n_iw)\\
&+Bu_b\{p^{-1}+\lambda S-2d+n_i d(d-\lambda S)\}
+N_i(w-3/4),
\end{aligned}
\tag{3}
\]

where \(u_b=-(x-1)(g-1/5808)/(b-1)^2\). For a direct derivation use
\(q'=L(1-q)\), \(\lambda'=-L\lambda\), \(d'=LA-Ld\),
\(u'=Bu_b\), and \(p'=(x-B)/(a+b)^2\). The product rule gives
\(E_L'=2uLA-LE_L+(2d-\lambda S)u'\) and
\(w'=LAE_L-2Lw+d(d-\lambda S)u'\). Differentiating the first four
terms of \(J\), together with \(\log y\), gives
\(u'/p+(x-B)(1-p+p^2-u)/a^2+2(1-q)^2/a\).
These identities establish (3) without clearing its composite rational
numerator. This identity retains
\(\log y\) exactly. In particular the positive term
\(2(1-q)^2/a\) is included. The proof below groups it with the next two
terms; estimating these three terms independently is too weak.

## 2. Small geometric bounds

Write \(h=x-2\in[0,1/6]\), \(r=8a-9\), \(j=5x+12\), and
\(Z=40ax+36a+15x^2+11x=3j(a+b)\).
The following useful shape bounds follow from (1):

\[
a\ge\frac{x+23}{22}\ge\frac{25}{22}>\frac98,
\qquad a\le a_+:=\frac{13(3x+2)}{90}\le\frac{221}{180}<\frac54.
\tag{4}
\]

For the lower affine bound, the difference from \(a_m\) is
\((317-145x)/10450>0\). The upper bound is the elementary square-root
bound (9) in the beta lemma. In particular \(r\ge1/11\).

### The grouped derivative multiplier

The four-term identity

\[
66aj(A-25/11)=127h-220h^2+85hr+44r
\]

shows \(A\ge25/11\). Also \(z>1/a-L>0\), because
\(x-B<a+b\) and \(a^2<x(x+2)\). For an upper bound,

\[
2560aKZ(6/5-z)=Q_z(h,r),
\]
\[
\begin{aligned}
Q_z={}&(30h+87)r^4+(90h^2+1506h+3624)r^3\\
&+(1920h^3+20118h^2+77690h+103390)r^2\\
&+(5760h^4+70784h^3+353566h^2+876742h+892064)r\\
&+13440h^4+69376h^3+10466h^2-214768h+45715.
\end{aligned}
\tag{5}
\]

All terms except the displayed linear term are nonnegative, and
\(45715-214768/6>0\). Hence \(0<z<6/5\). It follows that
\(N_i<0\). Moreover

\[
-N_0\le\frac{1091512}{277235}<4<\frac{21}{5},
\qquad
-N_1\le\frac{16}{5}+\frac{7220}{7921}<\frac{21}{5}.
\tag{6}
\]

For the first inequality, substitute \(z\le6/5\) and
\(1/k\le19/89\) in the two positive terms defining \(-N_0\).
The resulting affine function of \(y\) is increasing, so use
\(y\le6/7\). For the second use \(T\le8/3\).

### A lower bound on both duration multipliers

Both \(n_i\) decrease along the same straight line as \(a\) increases
to \(a_+\). The formulas for \(N_i\) establish this without any norm
hypothesis. Indeed on the slight extension to \(a_+\), \(b/a\le2\),
\(a^2<x(x+2)/5\), and hence \(y<1\) and \(z>0\).
The square bound here follows from
\(99x^2+1212x-676>0\).

At \(a=a_+\), direct one-variable identities give

\[
n_0-19/6=\frac{P_0(h)}{6j(39x+8)(9621x^2+18228x+676)},
\]
\[
n_1-19/6=\frac{P_1(h)}{78(3x+2)(39x+8)(1455x^2+1717x+468)},
\]
\[
\begin{aligned}
P_0={}&125999488-633236320h-655622604h^2
                 -179084736h^3-13132665h^4,\\
P_1={}&72261472-304916812h-443055600h^2
                 -187091181h^3-25163190h^4.
\end{aligned}
\tag{7}
\]

They decrease on \([0,1/6]\), and their values at \(1/6\) are
\(67638389/48\) and \(98991893/12\), respectively. Thus
\(n_i>19/6\).

### Bounds for \(q,d,p\)

Inserting the lower affine shape in \(q\) gives

\[
q-63/500\ge
\frac{29189-161102h-30055h^2}{500(x+1)(485x+529)}>0.
\tag{8}
\]

The numerator decreases and remains positive at \(h=1/6\).
Together with the central cap this proves
\(63/500<q\le1/7\).

For \(d\),

\[
30jK(3/10-d)=P_d(x,a),
\]
\[
P_d=-605a^2x-252a^2+200ax^2-220ax
           +345x^3+118x^2-654x-360.
\]

Its derivative in \(a\) is
\(-2a(605x+252)+200x^2-220x<0\), using (4).
At \(a_+\),

\[
3/10-d=
\frac{2576295h^3+14499138h^2+20348776h+225008}
{30j(9621x^2+18228x+676)}>0.
\tag{9}
\]

Finally \(p^{-1}\ge17/6\). The equivalent shape bound is
\(a\le 2x(15x+11)/(5x+132)\); its square follows from the central cap
and the positive four-degree identity

\[
\left(\frac{2x(15x+11)}{5x+132}\right)^2-\frac{x(x+2)}6
=\frac{x(5375h^3+38800h^2+73540h+32)}{6(5x+132)^2}>0.
\tag{10}
\]

## 3. The incoming ceiling, its derivative, and the small positive term

Let \(R=13x^2+14x+3\), \(Q=465x^2+58x-648\), and
\(u_0=757/1000+h/150\). Both \(u\) and \(-u_b\) decrease as
\(b\) increases, so their lower bounds are obtained by using
\(a=a_+\) in \(b\). On that one-variable endpoint,

\[
u-u_0=\frac{P_u(h)}{726000xSRQ},\qquad
-u_b-3/500=\frac{3P_b(h)}{121000xSRQ^2},
\tag{11}
\]
\[
\begin{aligned}
P_u={}&70764042+544147561h+703021883h^2-544043387h^3\\
&-1587453649h^4-1086331448h^5-300939850h^6-29257800h^7,\\
P_b={}&8496963156+2200521664h-100718737143h^2\\
&-269487341827h^3-312488173018h^4-189579248676h^5\\
&-62001148349h^6-10298395365h^7-680243850h^8.
\end{aligned}
\]

All denominators are positive: \(Q(2)=1328\) and \(Q'>0\).
For explicit short signs, bound all negative terms at \(h=1/6\).
Their sum in \(P_u\) is less than four million, while its constant
exceeds seventy million. Also

\[
P_b/10^9\ge8-101h^2-270h^3-313h^4-190h^5-63h^6-11h^7-h^8>3.
\]

The final inequality follows by substitution of \(1/6\). Consequently
\(u\ge u_0\) and \(-u_b\ge3/500\).

Now \(1-p+p^2-u\le187/9000-h/150\), by \(p\ge1/3\),
and \((x-B)/a^2\le484x(15x+11)/[(15x+36)(x+23)^2]\).
The right side of the first inequality is positive. The exact identity

\[
\frac1{48}-
\frac{484x(15x+11)}{(15x+36)(x+23)^2}
\left(\frac{187}{9000}-\frac h{150}\right)
=\frac{876825h^3+1714440h^2-3336451h+625438}
{54000(x+23)^2j}>0
\tag{12}
\]

has a positive numerator, already by
\(625438-3336451/6>0\). Hence the first term in (3) is less than
\(1/48\).

For the coefficient of \(Bu_b\), use \(n_i\le53/15\),
\(p^{-1}\ge17/6\), \(d\le3/10\), and the bounds on \(\lambda S\).
Write \(m=53/15\). The expression is at least

\[
17/6-2d+md^2+(1-md)\lambda S.
\]

For \(d\le1/m\), insert \(\lambda S\ge20/7\); for
\(d\ge1/m\), insert \(\lambda S\le19/6\). Each resulting quadratic
is decreasing on its indicated interval. Their minima are at least
\(17/6-15/53\) and \(1771/750\), both larger than \(9/4\).
Since \(B\ge3/4\), the entire term in (3) is less than
\(-81/8000<-1/100\).

## 4. Two correlated transport bounds

The remaining two estimates retain the correlation with \(q\):

\[
E_L\le5q-83/200,\qquad
w\ge w_b:=901/1000-6q/5.
\tag{13}
\]

### The pairing bound

Since \((E_L)_u=2d-\lambda S<0\), first lower \(u\) to
\(3/4+13/2000\). At that value,

\[
6000jK(5q-83/200-E_L)=P_E(x,a),
\]
\[
\begin{aligned}
P_E={}&-59140a^2x+221184a^2+60520ax^2-66572ax\\
&-7305x^4+38883x^3-63499x^2-106923x+17532.
\end{aligned}
\tag{14}
\]

The coefficient of \(a^2\) and the coefficient of \(a\) are positive,
so \(P_E\) increases in \(a\). At \(a=25/22\), the difference is

\[
5q-83/200-E_L=
\frac{22068-202106h+2551153h^2-788799h^3-294635h^4}
{500j(484x^2+968x+625)}.
\tag{15}
\]

The numerator exceeds \(22000-203000h+2400000h^2>0\).
For the last sign, the leading coefficient is positive and
\(4(2400000)(22000)-203000^2=169991000000>0\).
This proves the first inequality in (13).

### The norm bound

Since \(w_u=d(d-\lambda S)<0\), first raise \(u\) to \(19/25\);
denote the resulting norm by \(w_*\). Then

\[
1000j^2K^2(w_*-w_b)=Q_w(h,r)/36864,
\tag{16}
\]

where the complete polynomial is

\[
\begin{aligned}
Q_w={}&(3278275h^2+16992820h+22245004)r^4\\
&+(-15808000h^3+31803500h^2+466210640h+728151984)r^3\\
&+(14976000h^5+60016000h^4-691610880h^3-2567450318h^2\\
&\hspace{24mm}+816470712h+6535942600)r^2\\
&+(-36864000h^6+135628800h^5+1618338560h^4-5043517440h^3\\
&\hspace{24mm}-37422983124h^2-43214024624h+7365531312)r\\
&-442368000h^7-5902848000h^6-28361948160h^5\\
&-60905292416h^4-71564445952h^3-86648243805h^2\\
&-76691490124h+16148237836.
\end{aligned}
\]

Bound negative powers of \(h\) in each coefficient of
\(\partial_r Q_w\) at \(h=1/6\), and discard positive nonconstant
powers. The four resulting explicit lower bounds give

\[
\partial_r Q_w\ge
-\frac{72874391221}{81}
+\frac{116305607401}{9}r
+\frac{19658127568}{9}r^2+88980016r^3>0.
\tag{17}
\]

Indeed \(r\ge1/11\), and the first two terms already sum to at least
\(245132163178/891>0\). This proves monotonicity of the *numerator*
in (16); no monotonicity of its denominator is being assumed.

It remains to check \(Q_w(h,1/11)>0\). Write \(H_j(h)\) for the
coefficient of \(r^j\) printed in (16). The same bounds used in (17)
give \(H_1>-900000000\) and \(H_2,H_3,H_4>0\). Directly from the
printed constant coefficient,

\[
\frac{H_0}{10^8}\ge
161-767h-867h^2-716h^3-610h^4-284h^5-60h^6-5h^7>5.
\tag{18}
\]

The last polynomial decreases and its value at \(1/6\) is
\(1472467/279936>5\). Therefore
\(Q_w(h,1/11)>500000000-900000000/11>0\). This proves the second
inequality in (13), without expanding the specialization at \(r=1/11\).

## 5. The derivative sign is a single quadratic comparison

In (3), combine the second, third and fourth terms before estimating.
Since \(L=2q/a\), their sum is

\[
\frac2a\left[(1-q)^2+q\{A(n_iE_L-2u)+E_L-2n_iw\}\right].
\tag{19}
\]

By (2), \(n_iE_L-2u<0\), so use \(A\ge25/11\). Then use
\(u\ge3/4\), the two bounds (13), and \(n_i\ge19/6\).
The last substitution has the correct direction because
\((25/11)(5q-83/200)-2w_b<0\) on the indicated q interval.
Thus the bracket in (19) is at most

\[
\mathcal R(q)=\frac{16363}{330}q^2-\frac{87103}{6000}q+1<0.
\tag{20}
\]

For its strict sign, use convexity on \([63/500,1/7]\) and the values
\(-2307467/55000000\), \(-66777/1078000\) at its two endpoints.
Since \(a<5/4\), (19) is at most \((8/5)\mathcal R(q)\).
Also \(w_b<3/4\) on this q interval, so (6) and (13) imply
\(N_i(w-3/4)\le(21/5)(3/4-w_b)\), including when \(w\ge3/4\).
Equations (12), (13), and the bound on the \(Bu_b\) term now give

\[
H_i<\frac1{48}-\frac1{100}
+\frac85\mathcal R(q)+\frac{21}{5}(3/4-w_b)
=\frac{65452}{825}q^2-\frac{68203}{3750}q+\frac{29299}{30000}<0.
\tag{21}
\]

The final quadratic is convex. Its values at \(63/500\) and \(1/7\)
are \(-11437177/206250000\) and \(-40087/16170000\).
This proves both required derivatives, without a logarithm approximation
or any large cleared derivative numerator.

## 6. Caller and size audit

The original candidate has \(a>a_m\) and \(b\) as in (1) after the
source's beta comparison. Decreasing a to \(a_m\) keeps the central cap,
all beta-lemma hypotheses, and every inequality used here. By (21) it
raises both tests. At the endpoint,

\[
a=(15x+511)/475,\qquad b=20x/19,
\]

exactly the endpoint (10) in the source. Thus its Section 3 and conclusion
can consume this replacement unchanged. No root, cost, or outgoing floor
has been transported to an artificial shape. The larger rectangle in old
(4) is neither needed nor claimed.

The reductions precede expansion: b is the prescribed straight line;
the incoming norm is bounded separately; all incoming-ceiling expansions
are one-variable endpoint calculations. The only subdivision is the
single split at \(d=15/53\) for the signed coefficient in Section 3.

All polynomial numerators used above are fully printed. Their maximum
total degree is eight (the one-variable \(P_b\)); the largest genuinely
two-variable check is the degree-seven, 28-monomial \(Q_w\).
The other two-variable numerators have 4, 19, 8 and 9 monomials
(the multiplier bound, \(Q_z\), \(P_d\), and \(P_E\)). Each one-variable
check has at most nine monomials. All printed and separately expanded
source numerator coefficients are at most twelve digits; the largest
coefficient after distributing the harmless factor 3 in (11) is
937464519054. The proof uses the printed small polynomials and elementary
rational bounds, with no extracted coefficient table as a premise.

For the coefficient-height audit, use (16) in exactly its displayed
normalization: the four separately expanded contributions
\(\lambda^2v\), \((19/25)d^2\), \(-d\lambda E\), and \(-w_b\),
after multiplication by \(1000j^2K^2\), have degrees 6, 6, 7, 6
and respectively 7, 25, 21, 23 monomials in h,r. Their reduced rational
coefficients have numerators and denominators within twelve digits;
the largest numerator is 182935448045. Do not multiply this identity
by the unnecessary integer 36864. In the first identity (11), cancel
3/4 from u and u_0 before expansion. In its second identity, multiply
by \((121000/1089)xSRQ^2\), so the target is \(P_b/363\).
Each of its two source contributions then has degree at most eight,
at most nine monomials, and reduced coefficient numerator at most
566940157875. These normalization choices keep the individual source
checks, as well as their collected answers, within the stated budget.

This is a hand proof. No Lean source is changed and no Lean, Lake,
typechecking, or CI check is used for this replacement.
