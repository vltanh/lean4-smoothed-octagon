# A retained central Casimir bound for the nonshort comparison

Date: 2026-11-07 UTC. Hand necessary conditions.

This bound is derived from the actual central PMP lift before the scalar
boundary comparison. Its arguments are unchanged by that comparison.
It does not impose the original Casimir cap on the solved boundary root.
The endpoint signs needed to finish the nonshort exclusion remain open.

## 1. Actual ratios and the incident norm floor

At the actual global minimum reverse centre put

\[
\rho=\frac{a^2}{a^2+4},\quad t=\frac a{a+c},\quad
z=\frac a{a+b},\quad k=\frac{a^2+4}{(a+c)^2}.
\]

The actual positive reverse factor and smaller-turn ordering give

\[
\rho=t^2/k,\qquad 0<\rho<zt<1/4,
\qquad 0<t,z<1/2,\qquad t/k<z\le t.
\tag{1}
\]

The actual incoming norm on the nonshort side is `v=Sec(a,c,d)`.
The [explicit turn floor](EXPLICIT_TURN_NORM_FLOOR.md) gives

\[
u,v>m(t):=\Phi(1-t),\qquad
\Phi(\eta)=1-\eta^2-\frac{4\eta}{3}
 +\frac{2\eta}{3}\sqrt{12\eta-2}.
\tag{2}
\]

Here the other turn has `b>=c`, so its corresponding eta is at least
`1-t`; the proved monotonicity of Phi gives the common floor (2).
One also has the incident ceilings `u<=U(z)`, `v<=U(t)`, where
`U(s)=1-s+s^2`. In particular,

\[
\frac34<m(t)<U(t)\le U(z).
\tag{3}
\]

For the strict upper comparison in (3), put `eta=1-t` and
`h=sqrt(12eta-2)`. Direct subtraction gives

\[
U(t)-\Phi(1-t)=\frac{\eta(h-2)^2}{6}>0.
\]

The same argument below also works with the simpler constant floor
`m=3/4`. That specialization is displayed separately in Section 4.

## 2. Lower only the opposite incident norm

The actual squared Casimir has the established form

\[
\gamma^2=\frac{4uv-E^2}{16(1-\rho)^2},\quad
E=1+z+t-\rho+\log\frac{\rho}{zt}
 -\frac{1-u}z-\frac{1-v}t.
\tag{4}
\]

For fixed actual `rho,z,t`, its numerator is strictly increasing in
`u` throughout the incident norm rectangle. Indeed substitution of the
upper norms and the monotonicity of `-rho+log(rho/(zt))` up to
`rho=zt<1` give

\[
E<-1+2z+2t-zt<\frac32z.
\]

The last inequality follows because
`-1+z/2+t(2-z)<-1+z/2+(2-z)/2=0`. Therefore

\[
\partial_u(4uv-E^2)=4v-2E/z>3-3=0.
\tag{5}
\]

Lowering only u to `m=m(t)` thus yields

\[
\gamma^2>
\frac{4mv-\mathcal E(z)^2}{16(1-\rho)^2},
\quad
\mathcal E(z)=1+z+t-\rho+\log\frac{\rho}{zt}
 -\frac{1-m}{z}-\frac{1-v}t.
\tag{6}
\]

This comparison retains the exact actual secant v.

For fixed t, m and v, the function in (6) is strictly increasing on
`0<z<=t`, since

\[
\mathcal E'(z)=1-1/z+(1-m)/z^2
 =\frac{U(z)-m}{z^2}>0
\tag{7}
\]

by (3). Its two endpoint values on the interval in (1) are

\[
E_0=1+t+\frac{t(1-t)}k+\frac{v-1-k(1-m)}t,
\]
\[
E_t=1+2t-\frac{t^2}k-\log k+\frac{m+v-2}t.
\tag{8}
\]

Every number between E0 and Et has square at most
`max(E0^2,Et^2)`, regardless of their signs. Define

\[
G_0=\frac{4mv-E_0^2}{16(1-t^2/k)^2},\qquad
G_t=\frac{4mv-E_t^2}{16(1-t^2/k)^2}.
\tag{9}
\]

Equations (6)--(8) prove

\[
\boxed{\gamma^2>\min\{G_0,G_t\}.}
\tag{10}
\]

Both quantities depend only on a,c,d, through t,k,v. These coordinates
are held fixed in the scalar comparison `b -> b*`. The actual
[competitive cap](HAND_PROOF_REFINEMENTS.md), Section 1, therefore gives
the retained necessary alternative

\[
\boxed{G_0<9193/50000\quad\hbox{or}\quad G_t<9193/50000.}
\tag{11}
\]

The actual Casimir first gave (11); the inequality is retained because
its arguments are unchanged. No statement about the artificial boundary
Casimir is used.

## 3. One endpoint suffices when a >= 3/4

At `z0=rho/t`, lower m and v to 3/4 in E0. As `z0*t=rho`,

\[
E_0>1-\rho+(z_0+t)\left(1-\frac1{4\rho}\right).
\]

The inequality `(1/2-z0)(1/2-t)>0` implies
`z0+t<1/2+2rho`. The displayed coefficient is negative, so

\[
E_0>1+\rho-\frac1{8\rho}.
\tag{12}
\]

This last expression increases with positive rho. If `a>=3/4`, then
`rho>=9/73` and

\[
E_0>\frac{82}{73}-\frac{73}{72}
 =\frac{575}{5256}>0.
\]

Thus `0<E0<=Et`, and (10)--(11) simplify to

\[
\boxed{\gamma^2>G_t,\qquad G_t<9193/50000.}
\tag{13}
\]

The weak endpoint equality in this formulation also covers the
zero-factor boundary limit k=1.

## 4. The simpler 3/4-floor version

Without using the explicit turn-floor improvement, lower u only to
3/4. The same proof gives (10)--(13) with

\[
\begin{aligned}
E_0^{(3/4)}&=1+t+t(1-t)/k+(v-1-k/4)/t,\\
E_t^{(3/4)}&=1+2t-t^2/k-\log k+(v-5/4)/t,
\end{aligned}
\]
\[
G_i^{(3/4)}=
\frac{3v-(E_i^{(3/4)})^2}{16(1-t^2/k)^2},\quad i=0,t.
\tag{14}
\]

These are weaker but shorter retained conditions. Both versions are
hand inequalities on the unchanged actual data, not endpoint execution
results or sampled lower bounds.
