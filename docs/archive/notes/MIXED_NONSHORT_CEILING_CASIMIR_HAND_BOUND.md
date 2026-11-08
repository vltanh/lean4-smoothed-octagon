# A hand Casimir bound on a near-unit incident-ceiling face

Date: 2026-11-07 UTC. Conditional scalar hand theorem, accepted in
[the endpoint audit](HAND_ENDPOINT_REDUCTIONS_AUDIT.md), Section 12.
The additional shape and ratio restrictions in the theorem are explicit
hypotheses, not yet consequences asserted for every forward successor.

This note supplies one endpoint sign for the
[nonshort scale-Casimir comparison](MIXED_NONSHORT_FORWARD_SHAPE_CASIMIR.md).
At its upper shape endpoint, the solved incident norm is at its ceiling.
If the remaining parameters lie in the rectangle below, that endpoint
cannot satisfy the competitive Casimir cap. The proof does not use q,
an interval cover or a numerical minimum.

## 1. The conditional theorem

Write \(U(z)=1-z+z^2\). Suppose
\[
\frac13\le t\le\frac25,\qquad
1\le k\le\frac{51}{50},\qquad
\Phi(1-t)\le v\le U(t),
\tag{1}
\]
where
\[
\Phi(\eta)=1-\eta^2-\frac{4\eta}{3}
                  +\frac{2\eta}{3}\sqrt{12\eta-2}.
\]
At the incident ceiling put
\[
u=U(t/k),\qquad
H=\frac{k}{t}(v-1+t^2)+t(2-t).
\]
The central scalar determinant is
\[
\Gamma_U(t,k,v)
=\frac{4k^2uv-H^2}{16(k-t^2)^2}.
\tag{2}
\]

**Theorem.** Every point of (1) satisfies
\[
\boxed{\Gamma_U(t,k,v)>\frac{9193}{50000}.}
\tag{3}
\]

This is a sign for the explicit scalar function (2). A physical-period
application must separately establish (1) at its selected comparison
endpoint.

## 2. A polynomial floor for v and its correct comparison direction

For \(1/2\le\eta\le2/3\), the explicit floor satisfies
\[
\Phi(\eta)\ge\frac34+\frac{(2\eta-1)^2}{21}.
\tag{4}
\]
Indeed set \(h=\sqrt{12\eta-2}\), so \(2\le h\le\sqrt6\).
The already proved identity
\[
\Phi(\eta)-\frac34
 =\frac{h(4-h)(h-2)^2}{144}
\]
shows that (4) is equivalent, after removing the nonnegative square,
to
\[
21h(4-h)-4(h+2)^2=-25h^2+68h-16\ge0.
\]
This last polynomial decreases for \(h\ge2\). At \(\sqrt6\) it is
\(68\sqrt6-166>0\), since
\[
6>\left(\frac{83}{34}\right)^2
\quad\Longleftrightarrow\quad 6936>6889.
\]
At h=2 the removed square vanishes, giving equality in (4).
No approximation to the radical is needed.

For \(t\) in (1), (4) gives
\[
v\ge V(t):=\frac34+\frac{(1-2t)^2}{21}
          =\frac{67-16t+16t^2}{84}.
\tag{5}
\]
The determinant (2) increases strictly with v throughout
\(V(t)\le v\le U(t)\). To see the sign directly, put
\[
z=t/k,\qquad \rho=t^2/k=zt,\qquad E=H/k.
\]
Then
\[
\Gamma_U=\frac{4uv-E^2}{16(1-\rho)^2},\qquad
E=2z+t-\rho-\frac{1-v}{t}.
\]
Using \(v\le U(t)\), \(z\le t<1/2\), and \(u=U(z)>3/4\),
\[
E\le-1+2z+2t-zt<\frac32t.
\]
For the last inequality,
\[
-1+2z+\frac t2-zt
=-1+2z+t(1/2-z)
<-1+2z+\frac12(1/2-z)<0.
\]
Therefore
\[
\partial_v(4uv-E^2)=4u-\frac{2E}{t}>3-3=0.
\tag{6}
\]
It suffices to prove (3) with \(v=V(t)\).

## 3. One explicit polynomial identity

Let
\[
P(t)=67-16t+16t^2,\qquad A(t)=100t^2-16t-17,
\]
\[
N(t,k)=336t^2P(t)(k^2-kt+t^2)
          -\{kA(t)+84t^2(2-t)\}^2.
\]
Substitution of (5) into (2) gives
\[
\Gamma_U(t,k,V(t))=
\frac{N(t,k)}{112896\,t^2(k-t^2)^2}.
\]
Thus define
\[
Q(t,k)=50000N(t,k)-9193\cdot112896\,t^2(k-t^2)^2.
\tag{7}
\]
The denominator in the desired comparison is positive.

Put
\[
a=3t-1,\qquad b=51-50k.
\]
The rectangle (1) becomes
\[
0\le a\le1/5,\qquad 0\le b\le1.
\tag{8}
\]
Ordinary expansion of (7) gives the finite identity
\[
\frac{3^6 50^2}{48}\,
Q\left(\frac{1+a}{3},\frac{51-b}{50}\right)
=C_0(a)+C_1(a)b+C_2(a)b^2,
\tag{9}
\]
with the three complete coefficient polynomials
\[
\begin{aligned}
C_0={}&70814609+495487212768a-614982749016a^2\\
 &-38915200400a^3+478055912400a^4
       -81044040000a^5-58429840000a^6,\\
C_1={}&2194349082-26521349136a+15671180832a^2\\
 &+14313980400a^3-9473042400a^4-1785000000a^5,\\
C_2={}&-48361191+331996368a-30351816a^2\\
 &-234600000a^3-43350000a^4.
\end{aligned}
\tag{10}
\]
Equations (7) and (9)--(10) specify the entire algebraic calculation.
The following short bounds, rather than a coefficient sign test, prove
its strict sign.

## 4. Absorb every negative coefficient

From \(a\le1/5\), dropping the positive fourth-degree term of C0 gives
\[
\begin{aligned}
C_0(a)\ge{}&70814609+a\left[
495487212768-\frac{614982749016}{5}
-\frac{38915200400}{25}\right.\\
&\left.\hspace{23mm}
-\frac{81044040000}{625}-\frac{58429840000}{3125}\right]\\
={}&70814609+370785686936a\\
\ge{}&70814609+370000000000a.
\end{aligned}
\tag{11}
\]

For \(0\le b\le1\), discard only the nonnegative terms of C1:
\[
\begin{aligned}
C_1(a)b
&\ge-a\left[26521349136+
                  \frac{9473042400}{125}
                  +\frac{1785000000}{625}\right]\\
&=-\frac{132999947376}{5}a
\ge-27000000000a.
\end{aligned}
\tag{12}
\]
Similarly,
\[
\begin{aligned}
C_2(a)b^2
&\ge-48361191
 -a\left[\frac{30351816}{5}+\frac{234600000}{25}
                         +\frac{43350000}{125}\right]\\
&=-48361191-\frac{79005816}{5}a\\
&\ge-48361191-16000000a.
\end{aligned}
\tag{13}
\]
Combining (11)--(13),
\[
\boxed{
C_0+C_1b+C_2b^2
\ge22453418+342984000000a>0.
}
\tag{14}
\]
The multiplier in (9) is positive. Hence Q>0 on the whole rectangle.
Equations (5)--(7) then prove the theorem (3).

## 5. Exact role in the remaining forward problem

At \(k=k_{\rm top}\) in the scale-Casimir comparison, the boundary
incident norm equals \(U(t/k)\). The exact incoming secant still
satisfies \(v>\Phi(1-t)\), because t and that secant were held fixed
during the shape comparison. Thus this entire incident-ceiling face
is excluded whenever \(t\ge1/3\) and \(k_{\rm top}\le51/50\).

This does not prove those two additional bounds for all remaining
forward data. It also does not exclude the lower shape endpoints or
the stronger upper-w endpoint. Those restrictions and endpoint signs
remain separate hand tasks. The present theorem is a complete
conditional sign proof with an explicit positive rational margin.
