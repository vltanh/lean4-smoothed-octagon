# Symmetric all-forward sum residual: initial value and the low-D region

Date: 2026-11-07 UTC. Complete hand proof of the initial-value lemma
and the low-D region. The complementary region is proved in
[HAND_FORWARD_SYMMETRIC_SUM_HIGH_D](HAND_FORWARD_SYMMETRIC_SUM_HIGH_D.md);
together they establish the entire sum bound.

Use the symmetric domain and the residual \(\mathcal E_\Sigma\) from
[HAND_FORWARD_CONDITIONAL_NORM_BOUNDS](HAND_FORWARD_CONDITIONAL_NORM_BOUNDS.md):
\[
1\le z\le4/3,\quad 1+6z/5\le U<3,\quad
\frac{S^2}{Z}\le h\le\frac{S(5U-2-3z)}{3Z},
\quad S=1+z,\ Z=z^2+U,\ K=1+U.
\tag{1}
\]
Write
\[
d=3-U,\quad x=z-1,\quad H=h-1,\quad
I=\frac{S^2}{Z},\quad q=\frac{S^2}{K},\quad L_v=L(z,I).
\]
The exact functions \(f,L,n,m,r\) are those displayed in the linked
note. In particular
\[
\mathcal E_\Sigma=r-\frac n{35}-(m-n)L_v.
\tag{2}
\]
The value at \(h=1\) means the continuous algebraic extension of (2);
the actual exterior factor still satisfies (1).

## 1. The exact initial value is nonpositive

**Lemma.** On (1),
\[
\boxed{A_0:=\mathcal E_\Sigma(1)\le0.}
\tag{3}
\]
It is zero when \(z=1\), and strictly negative when \(z>1\).

Put
\[
a=\frac{z-1}{z+1}\in[0,1/7],\qquad
t=\frac z{1+z}=\frac{1+a}{2},\qquad
S=\frac2{1-a}.
\]
The lower factor \(I=S^2/Z\) satisfies
\[
1\le I\le\frac54.
\tag{4}
\]
For the upper bound, use \(U\ge1+6z/5\) and the identity
\[
5(z^2+1+6z/5)-4(z+1)^2=(z-1)^2\ge0.
\]
Moreover
\[
q=\frac I{1-aI}.
\tag{5}
\]
All denominators in (5) are positive, since \(aI\le5/28<1\).

Define
\[
F_z(q)=\frac{q-1}{S}+t(1-q^{-1})-\log q,
\]
\[
\Delta=t\frac a2(I-1)+tI\frac{f(I)}{I-1}.
\tag{6}
\]
At \(I=1\), the second expression uses its continuous value zero.
Since
\[
L(z,I)=\frac{a^2}{4}+\Delta,
\]
direct substitution in the centered stationary residual gives
\[
\boxed{\frac ZK A_0
 =J:=F_z(q)-\frac{S(q-1)}q\,\Delta.}
\tag{7}
\]
This identity uses the exact logarithms; no rational upper estimate of
\(A_0\) is substituted.

We prove that \(J\) is nonincreasing as \(I\) increases from 1 to 5/4
with \(a\) fixed. By (5), \(q\) increases with \(I\). Differentiating
(6)--(7), with \(e=I-1\), and collecting the logarithmic terms gives
\[
q^2J_q=
\frac{(q-1)(q-z)}S
 +St^2-2St^3I^2+Ste
 +St\,aI^2\frac{e-\log I}{e^2}.
\tag{8}
\]
The continuous extension applies at \(e=0\). The elementary inequality
\(\log I\ge2(I-1)/(I+1)\) yields
\[
\frac{e-\log I}{e^2}\le\frac1{I+1}.
\tag{9}
\]
The coefficient of this fraction in (8) is nonnegative.

After substituting (5) and \(t=(1+a)/2\), the resulting rational upper
bound in (8) has positive denominator
\[
2(1-a)(I+1)(1-aI)^2
\]
and numerator
\[
N=aQ_1(e)+a^2Q_2(e)+a^3Q_3(e)+a^4Q_4(e)+a^5Q_5(e),
\tag{10}
\]
where the five polynomials are
\[
\begin{aligned}
Q_1(e)&=-5e-4e^2+3e^3+2e^4,\\
Q_2(e)&=-4-e+14e^2+14e^3+2e^4-e^5,\\
Q_3(e)&=6+20e+20e^2+e^3-8e^4-3e^5,\\
Q_4(e)&=-5e-18e^2-24e^3-14e^4-3e^5,\\
Q_5(e)&=-2-9e-16e^2-14e^3-6e^4-e^5.
\end{aligned}
\tag{11}
\]
Equations (8)--(11) are polynomial identities after multiplication by
the stated positive denominator, so they can be checked by ordinary
expansion.

By (4), \(0\le e\le1/4\). Dropping negative terms and bounding the
positive powers of \(e\) gives
\[
Q_1(e)\le-\frac{153}{32}e,\qquad
Q_2(e)\le-\frac{371}{128},\qquad
Q_3(e)\le\frac{785}{64},\qquad
Q_4(e),Q_5(e)\le0.
\tag{12}
\]
For example the first bound uses
\(3e^3+2e^4\le(3/16+1/32)e\);
the second uses
\(14e^2+14e^3+2e^4\le14/16+14/64+2/256\).
Since \(a\le1/7\), (10)--(12) imply
\[
N\le-\frac{153}{32}ae
 -\left(\frac{371}{128}-\frac{785}{448}\right)a^2
 =-\frac{153}{32}ae-\frac{1027}{896}a^2\le0.
\tag{13}
\]
Thus \(J_q\le0\).

At \(I=1\), \(\Delta=0\) and \(q=1/(1-a)=S/2\in[1,z]\).
The derivative
\[
F_z'(q)=\frac{(q-1)(q-z)}{Sq^2}
\]
is nonpositive on that interval and \(F_z(1)=0\). Therefore the initial
value of \(J\) is nonpositive, and it is strictly negative if \(a>0\).
Monotonicity then proves (3). For \(a=0\), the same formulas give
\(J_q=0\) and \(J=0\).

## 2. A scalar decomposition of the positive-duration residual

Let
\[
n=n_1H,\qquad
n_1=\frac{S^2(U-z)}Z,
\]
\[
m=m_0+m_1H,\qquad
m_0=\frac{K^2(q-1)}{SZ},\qquad
m_1=\frac{K^2(Sq-1)}{SZ}.
\]
The coefficient difference is
\[
m_1-n_1=\frac{S^4-K^2}{SZ}>0.
\tag{14}
\]
Set
\[
P=d^2(x^2+4x+2)+8dx(x+1)+2x^2(8+4x-x^2),
\]
\[
\Phi=2f(S/2)+f(4/K),\qquad
r_1=\frac P{8SZ}+\frac{KS}{Z}\Phi,
\]
\[
A_1=r_1-\frac{n_1}{35}-(m_1-n_1)L_v,\qquad
D=\frac{d+4x+x^2}{Z}.
\tag{15}
\]
Then the exact residual is
\[
\boxed{\frac{\mathcal E_\Sigma}{H}
 =\frac{A_0}{H}+A_1+zg(H),\qquad
g(H)=\frac{DH}{2(1+H)}-\frac{f(1+H)}H.}
\tag{16}
\]
Put \(\tau=H/(1+H)\). The elementary lower bound
\[
f(h)\ge\frac{(h-1)^3}{3h(h+1)}
\]
follows from equality at one and the exact derivative
\[
\frac d{dh}\left\{f(h)-\frac{(h-1)^3}{3h(h+1)}\right\}
=\frac{(h-1)^4}{6h^2(h+1)^2}\ge0.
\]
It gives
\[
g(H)\le\frac{D\tau}{2}-\frac{\tau^2}{3(2-\tau)}
 \le\frac{D\tau}{2}-\frac{\tau^2}{6}
 \le\frac{3D^2}{8}.
\tag{17}
\]
The last inequality is the maximum of a quadratic on the real line.

## 3. The entire region D <= 38/243 is closed by hand

**Proposition.** If, in addition to (1),
\[
D\le\frac{38}{243},
\tag{18}
\]
then \(\mathcal E_\Sigma<0\).

First, \(38/243<1/6\) and (15) imply
\[
7d+22x+5x^2<4.
\]
Consequently
\[
d\le4/7,\quad x<1/5,\quad z<6/5,\quad
U-z>6/5,\quad K>10/3,\quad Z<9/2.
\tag{19}
\]
The original domain also gives \(0\le x\le1/3\) and
\(0\le d\le(4-6x)/5\).

An exact polynomial comparison is
\[
\begin{aligned}
P-2(d+4x+x^2)^2
={}&dx\{d(x+4)-8+4x\}\\
&-4x^2(4+2x+x^2)\le0.
\end{aligned}
\tag{20}
\]
Indeed
\[
d(x+4)-8+4x
 \le-\frac{24}{5}-\frac65x^2<0
\]
on the original triangular domain. Thus \(P\le2D^2Z^2\).

Divide (16) by the positive \(n_1\), use \(A_0\le0\) from Section 1,
and drop the nonpositive term
\(-(m_1-n_1)L_v/n_1\). Equations (17), (19)--(20) give
\[
\begin{aligned}
\frac{\mathcal E_\Sigma}{n_1H}
&\le-\frac1{35}
 +\frac{P}{8S^3(U-z)}
 +\frac{K}{S(U-z)}\Phi
 +\frac{zZ}{S^2(U-z)}\frac{3D^2}{8},\\
\frac{P}{8S^3(U-z)}
&\le\frac{135}{256}D^2,\\
\frac{zZ}{S^2(U-z)}\frac{3D^2}{8}
&\le\frac{27}{64}D^2.
\end{aligned}
\tag{21}
\]
Here \(S\ge2\), and the two displayed constants follow respectively
from \(Z\le9/2,\ U-z\ge6/5\) and
\(z\le6/5,\ Z\le9/2,\ U-z\ge6/5\).
Their sum is \(243/256<1\).

For the logarithmic remainder, the elementary bound
\[
f(1+t)\le\frac{t^3}{6(1+t)}\le\frac{t^3}{6}
\quad(t\ge0)
\tag{22}
\]
follows from equality at \(t=0\) and
\[
\frac d{dt}
 \left\{\frac{t^3}{6(1+t)}-f(1+t)\right\}
 =\frac{t^3}{3(1+t)^2}\ge0.
\]
It yields
\[
\Phi\le\frac{x^3}{24}+\frac{d^3}{6K^3}.
\]
By \(x\le DZ/4,\ d\le DZ\) and (19),
\[
\begin{aligned}
\frac{K}{S(U-z)}\Phi
&\le
\frac53\left(\frac92\right)^3
 \left(\frac1{1536}+\frac9{2000}\right)D^3\\
&=\frac{80109}{102400}D^3<D^3
\qquad(D>0).
\end{aligned}
\tag{23}
\]
Combining (21)--(23),
\[
\frac{\mathcal E_\Sigma}{n_1H}
 <-\frac1{35}+D^2+D^3<0.
\tag{24}
\]
For the final strict comparison, \(D^2+D^3\) increases for \(D\ge0\),
and
\[
\left(\frac{38}{243}\right)^2+
\left(\frac{38}{243}\right)^3
 =\frac{405764}{14348907}<\frac1{35},
\]
because \(14348907-35\cdot405764=147167>0\).
The case \(D=0\) has the immediate bound \(-1/35\) in (21);
actual \(U<3\) already gives \(D>0\).
This proves the proposition.

## 4. The high-D region and its hand upper envelope

For the complementary region \(D\ge38/243\), put
\[
H_c=\frac{S(5U-2-3z)}{3Z}-1>0.
\]
The concave function
\[
\frac{D\tau}{2}-\frac{\tau^2}{3(2-\tau)}
\]
has tangent at \(\tau=1/5\)
\[
\frac2{243}+\left(\frac D2-\frac{19}{243}\right)\tau.
\]
Since the slope is nonnegative when \(D\ge38/243\), (3), (16), and
\(H\le H_c\) give the exact upper bound
\[
\frac{\mathcal E_\Sigma}{H}
\le\frac{A_0}{H_c}+A_1
 +z\left\{\frac2{243}
  +\left(\frac D2-\frac{19}{243}\right)
       \frac{H_c}{1+H_c}\right\}.
\tag{25}
\]
The hand proof in
[HAND_FORWARD_SYMMETRIC_SUM_HIGH_D](HAND_FORWARD_SYMMETRIC_SUM_HIGH_D.md)
starts from (25). It keeps an exact cancellation between \(A_0\) and
\(A_1\), proves a quantitative upper bound on \(A_0\), and bounds the
remaining rational expression by a quadratic in \(1-4(I-1)\). One
explicit quartic sign then proves strict negativity. Thus (18) and
the high-D proof cover the whole symmetric domain, including their
common boundary.
