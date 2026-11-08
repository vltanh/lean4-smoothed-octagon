# A floor-weighted envelope for the large short-ratio question

Date: 2026-11-08 UTC. Hand reductions, accepted in the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md),
Section 8. The positive-scale endpoint sign is not asserted in this note.

Use the actual smaller-short notation of the
[outer-envelope theorem](MIXED_SMALLER_SHORT_OUTER_ENVELOPE.md).
Throughout this note 12/5<=x<=9, and the actual two short secants are
equal. Write S=1+x, Q=alpha(alpha+beta), r=1/S,
r_A=alpha/(alpha+beta), q=rho_A, and

\[
G_\tau(t,v)=R_\tau(t,v)+\frac12(w(t,v)-3/4).
\tag{1}
\]

At the actual root, R_tau=0 and w>3/4, so G_tau>0. The floor is
incorporated in this actual scalar expression before any comparison
is made.

## 1. The same upper-envelope comparison is valid for G

For z=tau+1/2 put B_z(t)=1+z(lambda*t-d). Then

\[
G_v=\frac\lambda t B_z(t),\qquad
\frac{d}{dt}G_\tau(t,U(t))
 =\frac{\lambda(2t-1)}t B_z(t).
\tag{2}
\]

Both signs follow from B_z>0. If D<=S, then t>=rho*S implies
lambda*t-d>=0. If D>S, the minimum is at t=t0=rho*S and
tau=T=(lambda*rho*Q)^(-1). Because T>=2,

\[
\begin{aligned}
B_z(t)&\ge1-\frac{D-S}{Q}-\frac{\lambda\rho(D-S)}2\\
&\ge1-\frac{5(D-S)}{4Q}
 =\frac{4Q-5(D-S)}{4Q}>0.
\end{aligned}
\]

The last numerator has the elementary bound

\[
4Q-5(D-S)=\beta(10x-6\alpha)-\alpha^2-5x
 \ge x(3x-5)>0,
\tag{3}
\]

using alpha<=x and beta>=x. Thus raising v to U(t), then decreasing
t to t0, gives

\[
\boxed{0<G_\tau(t,v)\le G_\tau^*
 :=R_\tau^*+\tfrac12(w_*-3/4).}
\tag{4}
\]

This is valid for either sign of D-S. No outgoing floor is separately
transported to w_*, and no upper Casimir cap is used.

## 2. A simple shape bound on the large-ratio range

The exact equal secants imply

\[
\boxed{\alpha/\beta<3/4,\qquad r_A<3/7.}
\tag{5}
\]

Suppose instead alpha>=3beta/4. The second secant, as an average of
1-βs/(β+s)^2 on [alpha,x] contained in [alpha,beta], has

\[
u-3/4\le\frac{(\beta-\alpha)^2}
 {4(\beta+\alpha)^2}\le\frac1{196}.
\tag{6}
\]

For the first secant, put a=x-1 and z=x-s on [1,x]. The elementary
convex-tangent inequality for 1/y^2, averaged with weight z^2, gives

\[
\int_0^a\frac{z^2}{(2x-z)^2}\,dz
 \ge\frac{a^3/3}{(2x-3a/4)^2}
 =\frac{16(x-1)^3}{3(5x+3)^2}.
\tag{7}
\]

To verify the averaging step directly, use
1/y^2>=1/c^2-2(y-c)/c^3 with c=2x-3a/4;
the weighted integral of y-c vanishes. This tangent inequality itself
is equivalent to (y-c)^2(2y+c)>=0.

The hypothesis alpha>=3beta/4 and alpha<=x gives beta<=4x/3.
Retaining only the nonnegative first part of the incoming integral
therefore yields

\[
u-3/4\ge
 \frac{4(x-1)^3}{3(\beta-1)(5x+3)^2}
 \ge F(x):=\frac{4(x-1)^3}{(4x-3)(5x+3)^2}.
\tag{8}
\]

Its derivative is

\[
F'(x)=\frac{12(x-1)^2(23x-15)}
 {(4x-3)^2(5x+3)^3}>0.
\]

At x=12/5,

\[
F(12/5)=\frac{1372}{185625}
 =\frac1{196}+\frac{83287}{36382500}>\frac1{196},
\]

contradicting (6). This proves (5).

## 3. A diagonal ratio bound on the enlarged ordered shape domain

In fact, merely beta>=max(x,4alpha/3) and 1<=alpha<=x imply

\[
\boxed{\frac DQ\le\frac{3(1+x)^2}{7x^2}<1.}
\tag{9}
\]

For fixed alpha and x, D/Q decreases with beta: the numerator of its
beta derivative is alpha(alpha^2-2alpha*x-1-2x)<0. Thus only the two
possibilities for the lower endpoint max(x,4alpha/3) matter.

If alpha<=3x/4, set beta=x and C=1+2x-2x^2. The alpha derivative of
D/Q has numerator

\[
-\alpha^2x-(2\alpha+x)C>0.
\]

Indeed -C>=x^2/2 on x>=12/5, and the resulting lower bound is
x[alpha(x-alpha)+x^2/2]>0. Its maximum on this interval is at
alpha=3x/4.

If 3x/4<=alpha<=x, set beta=4alpha/3. Then

\[
\frac DQ=\frac{11}7-\frac{8x}{7\alpha}
                 +\frac{3(1+2x)}{7\alpha^2}
\]

is convex as a function of 1/alpha, so its maximum is at an endpoint.
The value at alpha=x is 3(1+x)^2/(7x^2); it exceeds the value at
alpha=3x/4 because their difference is

\[
\frac{8x^2-14x-7}{21x^2}>0
\]

for x>=12/5. Finally 4x^2-6x-3>0 on that interval proves the strict
last inequality in (9).

## 4. Increasing the incoming norm is a valid scalar comparison

The coefficient of u in G_* is

\[
(G_*)_u=\frac1{r_A}+\lambda S-2d
 +(\tau+1/2)d(d-\lambda S).
\tag{10}
\]

It is strictly positive for the actual fixed geometry. For D<0, this
is immediate after grouping the terms as
1/r_A-2d+(tau+1/2)d^2+[1-(tau+1/2)d]lambda*S.
For D>=0, (9) and tau<=T give tau*d<1, so (10) is strictly larger
than

\[
\frac1{r_A}-d(2+\lambda S/2).
\tag{11}
\]

For x>=5/2, the identity and order estimate

\[
D-2\alpha^2\le1+2x-x^2-(x-\alpha)^2\le0
\]

give d=qD/alpha^2<=2/7. Since S<=10, the amount subtracted in
(11) is at most 2, whereas 1/r_A>2. For 12/5<=x<=5/2, the same
estimate gives D/alpha^2<=51/25 and S<=7/2; that amount is at most
153/140<2. This proves positivity in all cases.

Accordingly the rational incoming upper bound in
[MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND](MIXED_SMALLER_SHORT_INCOMING_NORM_BOUND.md)
may be substituted into G_*, with the geometry and root parameter
fixed. This statement is a scalar comparison, not a transport of any
incident ceiling after the substitution.

## 5. The zero-scale endpoint is strictly negative

Keep the actual shape and its fixed incoming norm u. At fixed
p=tau*q in (0,r_A], the established scale formulas give

\[
G_*(q)=C(p)+qL(p)+\frac18-\frac{qA_1}2+\frac{q^2A_2}2.
\tag{12}
\]

We prove its value at q=0 is strictly negative. The elementary bound
log(p/r_A)<=p/r_A-1 makes C(p)+1/8 at most the affine expression

\[
E_0+\frac{u-1}{r_A}+r_A+\frac18
       +p(1/r_A-A_1).
\tag{13}
\]

At p=0 this is at most

\[
-\frac3{16}\left(\frac{17}5+\frac73\right)
 +\frac5{17}+\frac37+\frac18
 =-\frac{541}{2380}<0.
\tag{14}
\]

Here u<=13/16, S>=17/5, r<=5/17, and r_A<=3/7 were used.
At p=r_A, (13) is exactly

\[
E_0(1-D/Q)+\frac{u-1}{r_A}+\frac98-r_A
                              -\frac{r_A(x-1)}{\alpha^2}.
\tag{15}
\]

For the actual short incoming norm, the secant comparison and the
rational estimate for V(x) give

\[
u\le V(x)\le\overline V(x)
 :=\frac34+\frac{2(x-1)^2}{(x+1)(35x+13)}.
\tag{16}
\]

In particular E_0<0. Set c=(4x^2-6x-3)/(7x^2)>0 and
E_V=S(overline V-1)+1/S. Equations (9), (16), and alpha<=x bound
(15) above by

\[
cE_V+\frac{\overline V-1}{r_A}
       +\frac98-r_A\left(1+\frac{x-1}{x^2}\right).
\tag{17}
\]

The last expression increases with r_A on 0<r_A<=3/7. To check
this, its derivative is at least zero if

\[
1-\overline V-\frac9{49}\left(1+\frac{x-1}{x^2}\right)>0.
\]

Its numerator over the positive denominator
196x^2(x+1)(35x+13) is

\[
N(x)=63x^4+148x^3-691x^2+1260x+468.
\]

With z=5x-12>=0 the explicit identity

\[
625N(x)=63z^4+3764z^3+63797z^2+498036z+2279988
\]

proves the sign. Substituting r_A=3/7 in (17) now gives

\[
(15)\le-\frac{P(x)}{168x^2(x+1)(35x+13)}<0,
\tag{18}
\]

where

\[
P(x)=648x^5-237x^4-2290x^3-305x^2+450x-90.
\]

Its positive expansion on the same interval is

\[
3125P(x)=648z^5+37695z^4+818990z^3+8074475z^2
                    +33628170z+35346726.
\]

Both endpoints of the affine majorant (13) are strictly negative,
so (13) is strictly negative throughout 0<=p<=r_A. This closes the
q=0 endpoint in (12), without an artificial cap or a computed sign
premise.
