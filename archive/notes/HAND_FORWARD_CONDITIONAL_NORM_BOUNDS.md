# Two scalar norm bounds sufficient for the all-forward Casimir contradiction

Date: 2026-11-07 UTC. Complete hand implication and symmetric reductions.
The scalar signs identified here are proved in the linked companion notes,
and the actual-period consequence is assembled in
[HAND_FORWARD_PERIOD_EXCLUSION](HAND_FORWARD_PERIOD_EXCLUSION.md).

This note strengthens the conditional Casimir reductions in
[HAND_FORWARD_LEMMAS](HAND_FORWARD_LEMMAS.md). The hand minimum and
neighbor bounds, together with the physical cost budget, are the only
geometric inputs. The sufficient norm bounds are
\(\delta u+\delta v\le1/35\) and \(\delta v\le1/64\), where the right
neighbor is the larger one. Section 2 proves that these imply the
strict inequality \(\gamma^2>23/125\). Sections 3--4 reduce both
norm bounds to explicit scalar signs with equal adjacent margins. The
[sum reduction](HAND_FORWARD_SYMMETRIC_SUM_REDUCTION.md), its
[high-D completion](HAND_FORWARD_SYMMETRIC_SUM_HIGH_D.md), and the
[larger-norm proof](HAND_FORWARD_LARGER_NORM_HAND_PROOF.md) establish them.

## 1. Domain, centered norms, and central pairing

Use the notation and exact stationary formulas of
[HAND_FORWARD_OPEN_TARGET](HAND_FORWARD_OPEN_TARGET.md):
\[
11/5\le U<3,\qquad 1\le z\le w\le4/3,\qquad
z+w\le5(U-1)/3.
\tag{1}
\]
Put
\[
S=1+z,\quad T=1+w,\quad K=1+U,\quad
Z=z^2+U,\quad W=w^2+U.
\]
The actual norm increments \(\delta u,\delta v\) are nonnegative. The
central Casimir identity is
\[
\gamma^2=\frac{K^2}{16U^2}
 \left\{4(3/4+\delta u)(3/4+\delta v)
 -(E_0+S\delta u+T\delta v)^2\right\},
\tag{2}
\]
where
\[
E_0=e_0-\Phi,\qquad e_0=1-K/8+K^{-1},
\]
\[
\Phi=f(S/2)+f(T/2)+f(4/K),\qquad
f(a)=\frac{a-a^{-1}}2-\log a.
\]
The elementary estimates in Section 2.1 of
[HAND_FORWARD_LEMMAS](HAND_FORWARD_LEMMAS.md) give
\[
0<E_0\le e_0,\qquad 3/4\le e_0\le73/80.
\tag{3}
\]

## 2. Conditional Casimir theorem

**Theorem.** On (1), suppose in addition that
\[
\boxed{\delta u+\delta v\le\frac1{35},\qquad
       \delta v\le\frac1{64}.}
\tag{4}
\]
Then
\[
\boxed{\gamma^2>\frac{23}{125}.}
\tag{5}
\]

The proof below uses only elementary differentiation and the displayed
rational comparisons.

### 2.1. Reduction to two norm vertices

Let \(c=1/35\), \(b=1/64\), and define
\[
G(u,v)=\frac{K^2}{16U^2}
 \left\{4(3/4+u)(3/4+v)-(e_0+Su+Tv)^2\right\}.
\tag{6}
\]
Equations (2)--(3) imply \(\gamma^2\ge G(\delta u,\delta v)\).
The Hessian of the bracket in (6) is
\[
\begin{pmatrix}
-2S^2&4-2ST\\
4-2ST&-2T^2
\end{pmatrix}.
\]
Its diagonal entries are negative and its determinant is
\(16(ST-1)>0\), so \(G\) is strictly concave.

It is also nonincreasing in either variable on the nonnegative quadrant.
For example, the derivative of the bracket with respect to \(u\) is
\[
3+4v-2S(e_0+Su+Tv)
 \le3-4e_0-8u-4v\le0.
\tag{7}
\]
The analogous inequality holds with \(u,v\) interchanged.

The polygon \(u,v\ge0,\ u+v\le c,\ v\le b\) has vertices
\[
(0,0),\quad(c,0),\quad(c-b,b),\quad(0,b).
\]
Concavity reduces its minimum to these vertices, and (7) shows that it
suffices to consider
\[
A=(c,0),\qquad B=(c-b,b)=(29/2240,1/64).
\tag{8}
\]

### 2.2. Exact scalar minimum for vertex A

Define
\[
s_*(U)=\min\left\{\frac73,\frac{5U+1}{6}\right\}.
\]
Ordering and (1) give \(S\le s_*(U)\). Hence
\[
G(A)\ge\phi(U):=
\frac{K^2}{16U^2}
 \left\{\frac{327}{140}-(e_0+s_*(U)/35)^2\right\}.
\tag{9}
\]
The exact minimum of this scalar function occurs at \(U=13/5\):
\[
\boxed{\phi(U)\ge\phi(13/5)
       =\frac{348293}{1892800}
       =\frac{23}{125}+\frac{89}{9464000}.}
\tag{10}
\]

Here is a direct derivative proof of (10). Write
\[
A_*=\frac{327}{140},\qquad
F=K(e_0+s_*/35)=1+aK-b_*K^2,
\]
\[
G_*=F-(K-1)F'=1+a+b_*K^2-2b_*K,\qquad
J=FG_*-A_*K.
\]
Then
\[
\phi'(U)=\frac{J}{8U^3},\qquad
J''(K)=6b_*(K-1)F'(K).
\tag{11}
\]

For \(16/5\le K\le18/5\), the constants are
\[
a=\frac{103}{105},\qquad b_*=\frac{17}{168},\qquad
F'\ge\frac{53}{210}>0.
\]
Thus \(J\) is convex. Its endpoint values are
\[
J(16/5)=-\frac{3736}{30625},\qquad
J(18/5)=-\frac{4019}{26250}.
\tag{12}
\]
A convex function lies below its endpoint chord, so \(J<0\) throughout
this interval and \(\phi\) decreases there.

For \(18/5\le K\le4\), the constants are
\[
a=\frac{16}{15},\qquad b_*=\frac18,\qquad F'\ge\frac1{15}>0.
\]
Equation (11) again gives \(J''>0\). The left endpoint values are
\[
J(18/5)=\frac{7409}{13125}>0,\qquad
J'(18/5)=\frac{13969}{63000}>0.
\tag{13}
\]
Therefore \(J>0\) on this interval and \(\phi\) increases there.
At the joining point, \(e_0+s_*/35=161/180\) and
\(K^2/(16U^2)=81/676\), which gives (10).

### 2.3. The mixed vertex B retains a positive rational margin

The budget and ordering yield
\[
\frac{S+T}{2}\le s_*(U),\qquad 0\le T-S\le\frac13.
\]
Consequently, with \(\varepsilon=1/2240\),
\[
(c-b)S+bT
 =c\frac{S+T}{2}+(b-c/2)(T-S)
 \le c s_*+\varepsilon,
\tag{14}
\]
because \(b-c/2=3/2240\).

The product term at \(B\) exceeds the product term at \(A\) by
\[
4b(c-b)=\frac{29}{35840}.
\]
Set \(E_A=e_0+c s_*\). Since
\[
E_A\le\frac{73}{80}+\frac1{15}=\frac{47}{48},\qquad
\frac{K^2}{16U^2}\le\frac{16}{121},
\]
equation (14) gives
\[
\begin{aligned}
G(B)
&\ge\phi(U)-
 \frac{16}{121}
 \left\{2\frac{47}{48}\varepsilon+\varepsilon^2
                         -\frac{29}{35840}\right\}\\
&=\phi(U)-\frac{983}{113836800}.
\end{aligned}
\tag{15}
\]
The expression in braces is positive, so the use of the upper
prefactor is in the stated direction. Finally,
\[
\frac{89}{9464000}-\frac{983}{113836800}
 =\frac{73961}{96192096000}>0.
\tag{16}
\]
Equations (10), (15)--(16) prove (5) at both vertices (8), and hence
throughout the polygon. This completes the conditional theorem.

## 3. Two sufficient stationary residual inequalities

Let \(h\) be the actual left exterior factor. The cost budget and the
right exterior lower factor give
\[
\frac{S^2}{Z}\le h\le\frac{S(5U-2-3w)}{3Z}.
\tag{17}
\]
Put \(H=h-1>0\), \(q=ST/K\), and \(I=T^2/W\). The first exact centered
stationary row is
\[
n\,\delta u+m\,\delta v=r,
\tag{18}
\]
where
\[
n=\frac{S^2(U-z)H}{Z},\qquad
m=\frac{K^2}{SZ}\{q-1+H(Sq-1)\}.
\tag{19}
\]
For \(d=3-U,\ x=z-1\), define
\[
P(d,x)=d^2(x^2+4x+2)+8dx(x+1)+2x^2(8+4x-x^2).
\]
The residual is
\[
\begin{aligned}
r={}&\frac{dx(d+2x)+HP(d,x)}{8SZ}
 +\frac{H^2z(d+4x+x^2)}{2hZ}\\
&+\frac{K(1+SH)}Z\Phi-zf(h).
\end{aligned}
\tag{20}
\]
The genuine exterior floor is
\[
L(z,h)=\frac{x(x+2zH)}{4S^2}
       +\frac{zh}{S}\frac{f(h)}H.
\tag{21}
\]
Actual data satisfy
\[
\delta u\ge L(z,h),\qquad \delta v\ge L(w,I).
\tag{22}
\]

The coefficient difference has the positive form
\[
SZ(m-n)
 =K(ST-K)+H\{S^4-K^2+KS^2(T-S)\}>0,
\tag{23}
\]
since \(U<3\), \(T\ge S\ge2\), and \(K<4\).

Define the two scalar residuals
\[
\mathcal E_\Sigma
 =r-\frac n{35}-(m-n)L(w,I),
\tag{24}
\]
\[
\mathcal E_v=r-nL(z,h)-\frac m{64}.
\tag{25}
\]
If \(\delta u+\delta v\ge1/35\), then (18), (22)--(23) imply
\(\mathcal E_\Sigma\ge0\). If \(\delta v\ge1/64\), then
(18), (22) imply \(\mathcal E_v\ge0\). Therefore the strict signs
\[
\mathcal E_\Sigma<0,\qquad \mathcal E_v<0
\tag{26}
\]
prove the two bounds required in Section 2, with room to spare.

## 4. Both residual signs reduce exactly to equal neighbors

Fix \(U,z,h\) and vary \(w\) in the ordered domain. Set
\[
\alpha=\frac{K(1+SH)}Z>0,\qquad
t=\frac w{1+w},\qquad
V(w)=\frac34+L(w,I),\qquad
B(t)=1-t+t^2.
\]
Direct differentiation of (19)--(20), using
\(f'(a)=(a-1)^2/(2a^2)\), gives
\[
n_w=0,\qquad m_w=\alpha,\qquad
r_w=\alpha\{B(t)-3/4\}.
\tag{27}
\]

We have \(V(w)\ge B(t)\) and \(V_w\ge0\). For completeness, rewrite
the floor as
\[
L(w,h)=\frac14\left(\frac{w-1}{w+1}\right)^2
 +\frac{w(w-1)}{2(w+1)^2}(h-1)
 +\frac w{w+1}\frac{hf(h)}{h-1}.
\tag{28}
\]
Each coefficient increases for \(w\ge1\), and the last factor
\(hf(h)/(h-1)\) increases for \(h\ge1\). The latter follows from
\(f(1)=0\), \(f'\ge0\), and \(f''\ge0\). Moreover
\[
I_w=\frac{2(1+w)(U-w)}{(w^2+U)^2}>0.
\]
Thus \(V_w\ge0\). Setting \(h=1\) in the continuous extension of (28)
gives \(3/4+L(w,1)=B(t)\), proving the other inequality.

Now (23)--(24), (27) give
\[
(\mathcal E_\Sigma)_w
 =\alpha\{B(t)-V(w)\}-(m-n)V_w\le0.
\tag{29}
\]
Similarly,
\[
(\mathcal E_v)_w=\alpha\{B(t)-49/64\}<0,
\tag{30}
\]
because \(1/2\le t\le4/7\) implies
\(B(t)\le37/49<49/64\).

Lowering \(w\) to \(z\) increases each residual. It also enlarges the
cost upper bound in (17), so it preserves admissibility of \(h\).
Accordingly, (26) need only be proved on the symmetric domain
\[
\boxed{
1\le z\le4/3,\qquad
1+6z/5\le U<3,\qquad
\frac{(1+z)^2}{z^2+U}\le h\le
\frac{(1+z)(5U-2-3z)}{3(z^2+U)},\qquad w=z.
}
\tag{31}
\]
The bound \(U\ge1+6z/5\) is exactly the condition that the interval for
\(h\) in (31) is nonempty.

**Completion of the scalar signs.** The sum sign in (26) follows from
[HAND_FORWARD_SYMMETRIC_SUM_REDUCTION](HAND_FORWARD_SYMMETRIC_SUM_REDUCTION.md)
and [HAND_FORWARD_SYMMETRIC_SUM_HIGH_D](HAND_FORWARD_SYMMETRIC_SUM_HIGH_D.md).
The second sign follows from
[HAND_FORWARD_LARGER_NORM_HAND_PROOF](HAND_FORWARD_LARGER_NORM_HAND_PROOF.md).
Their [independent hand audit](HAND_FORWARD_NORM_AUDIT.md) checks the full
scalar domain and strictness. Thus both bounds required in Section 2
hold for actual forward data. No interval cover, coefficient-count
oracle, or numerical premise is used.
