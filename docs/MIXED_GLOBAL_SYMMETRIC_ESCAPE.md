# Symmetric reverse-four cores: cost obstruction or forced star exit

Date: 2026-11-07. Exact hand argument with a supplementary symbolic
certificate and an [independent internal hand audit](MIXED_GLOBAL_SYMMETRIC_AUDIT.md).
No Lean, Lake, typechecking, or CI. Internal review is not external peer review
or kernel validation.

## The theorem and its scope

Put `q=1/sqrt(3)`. Choose

\[
1<h<2,\qquad 0<v<3,\qquad
s=q(h-1),\qquad b=\frac{2q(h-1)}h,\qquad r=\frac{2-h}h.
\tag{1}
\]

On the interval `[-b,b]`, prescribe the reflection-symmetric four-piece
edge trajectory with word **2121**, switches `-s,0,s`, and

\[
w(x)=
\begin{cases}
\displaystyle \frac{vq^2}{(q+x)^2},&0\le x\le s,\\[5pt]
\displaystyle \frac{vq^2r^2}{(q-x)^2},&s\le x\le b,
\end{cases}
\qquad w(-x)=w(x),\qquad y=w^{-1/2}.
\tag{2}
\]

Every one of these four edge factors is `h`. Prepend an arbitrary positive
control-0 arc and append a control-0 arc whose factor is **at least h**.
Assume the resulting six-piece window stays in strict star.

**Theorem. Such a window cannot occur in any complete strict-star PMP
trajectory satisfying the actual twisted frame, state, and costate
endpoints and the complete-period budget `C<=A_oct`.** The first and last
arcs may be cuts inside longer vertex pieces. Thus, in particular, the
entire reflection-symmetric M1 family with all six factors equal to `h`
is excluded, for every admissible `h` and every state scale `v`.

The proof gives a dichotomy. Either the normal frame covector violates
the complete-period Casimir bound, or the outgoing last vertex is forced
to the strict-star boundary in finite positive time. It does not claim a
cheaper local replacement. It is consistent with the strong local minima
in [LOCAL_REVERSE_SIX_GLOBAL_MINIMUM](LOCAL_REVERSE_SIX_GLOBAL_MINIMUM.md).

This covers all symmetric equal-factor cores with sufficiently long
outgoing padding; it does **not** cover arbitrary unequal four-edge cores
or arbitrary shorter outgoing padding. In particular it does not close
universal M1, M2, M3, the other case-C targets, the octagon inequality, or
affine rigidity. No limiting case with a zero duration or a state on the
star boundary is silently included.

The structural continuation criterion in Section 1 applies without any
symmetry or equal-factor hypothesis. It is the reusable part of the
argument. The two-parameter family above supplies an exact uniform
application of it.

## 1. A vertex arc that passes its last critical point must escape

Use the minimizing Hamiltonian with scaled cost `A=(2/3)C`, and the
state-only clock `d tau=y dt`. Cyclically rotate the active vertex to 1.
The notation and exact equations are those of
[VERTEX_EVENT_ESCAPE](VERTEX_EVENT_ESCAPE.md), Sections 1--3:

\[
W=(q-a)^2w(a),\quad c=\frac W{q-a},\quad
u=\frac W{q-x},\quad S=u-c,\quad
R=\frac{1+W}{2qc}>1.
\tag{3}
\]

The third symbol here is the scalar `u`. Along the control-1 solution,
`x=q-W/u` increases strictly, and the first strict-star boundary occurs
at `u=cR`. The two inactive-minus-active Hamiltonians have the signs of
`-p_w` and `-B`, respectively. More explicitly,

\[
H_2-H_1=-\frac{4qwp_w}{q^2-x^2},\qquad
H_0-H_1=-\frac{2B}{1-w(q^2-x^2)}.
\tag{4}
\]

Put `mu=-1-m`, where `m` is the constant frame-covector component on this
arc. The exact numerators obey

\[
\frac{d}{du}(u^2p_w)=W(\mu-x(u)^2),
\tag{5}
\]
\[
B(S)=B_0+B_1S+\frac43S^2
 -2q(W+1)\bigl[(S+c)\log(1+S/c)-S\bigr].
\tag{6}
\]

**Continuation criterion.** Suppose a genuine PMP control-1 arc starts
at `a` and lasts through a point `z` before the star boundary. Suppose

\[
B_0<0,\qquad B_1\le0,\qquad R\ge16/5,
\qquad z>0,\qquad z^2>\mu.
\tag{7}
\]

Then the same vertex is forced after `z` until the star boundary. In
particular, this arc cannot be part of a closed twisted PMP lift.

To prove this, first apply the endpoint argument of
VERTEX_EVENT_ESCAPE. Since

\[
B_{SSS}=\frac{2q(W+1)}{(S+c)^2}>0,
\]

`B_S` is convex. Its nonpositive set is an interval containing zero,
so the maximum of `B` on `[0,c(R-1)]` is at an endpoint. Its final value is

\[
B(c(R-1))=B_0+B_1c(R-1)+\frac43c^2R^2\psi(R),
\quad
\psi(R)=2-3/R+1/R^2-\log R<0\quad(R\ge16/5).
\tag{8}
\]

The last logarithmic inequality has a rational proof in the cited note.
Both endpoint values are strictly negative, and hence `B<0` throughout.
As in that note, `R>=16/5` can be replaced by the sharper direct test
`B(c(R-1))<0`.

Let `u_z` denote the parameter at `z`. PMP gives `p_w<=0` on the actual
arc ending there. Equation (5) has strictly negative right side at `z`.
If `p_w(z)=0`, its numerator would be positive immediately to the left
of `u_z`, contradicting PMP. Therefore `p_w(z)<0`. Since `x>=z>0`
afterward, the right side of (5) stays strictly negative, so `p_w<0`
all the way to the boundary. Both inactive Hamiltonian gaps are strict.
The active vertex is the unique minimizer even among measurable simplex
controls, and the smooth state and adjoint equations give unique
continuation.

No transversality assumption at the *start* of this arc was used.
In particular `a` may be negative, and the starting tie may have zero
first derivative. The point `z` and the actual PMP condition before it
resolve that alternative. This is precisely the addition needed below;
the earlier criterion required a positive starting abscissa.

## 2. The unique stationary adjoint of the symmetric core

The four factors in (2) are `h` because on control 2 the quantity `q+x`
is multiplied by the factor, while on control 1 the quantity `q-x`
is divided by it. At the core center `w(0)=v`, and at its two endpoints
`w(-b)=w(b)=v`. Moreover

\[
w(x)(q^2-x^2)\le v/3<1.
\tag{9}
\]

For the inner positive arc this product is
`(v/3)(1-x/q)/(1+x/q)`. For the outer positive arc it is
`(v/3)r^2(1+x/q)/(1-x/q)` and its endpoint maximum is
`(v/3)r(2-r)<v/3`. Reflection proves (9) on the negative half.
Consequently `0<v<3` is exactly the strict-star restriction for this
core, rather than a numerical sampling box.

Use the upper triangular frame coordinate `A_frame=gK(x)`, where
`K(x)=[[1,x],[0,1]]`. Write its minimizing group covector as

\[
M=\begin{pmatrix}k/2&m\\n&-k/2\end{pmatrix}.
\]

Define the following dimensionless quantities, with `L=log h`:

\[
\begin{aligned}
\beta&=1-r=2(h-1)/h,&
\ell&=2(h-1)/h^2,\\
m_0&=h+1-\frac{2hL}{h-1},&
\mu&=m_0/3,\\
j&=\frac{4(h-1)(2-h)}{h^2}
       \left(L-\frac{h-1}{h}\right),&
S_b&=vq\ell.
\end{aligned}
\tag{10}
\]

The defining integral identities are

\[
\mu=\frac{\int_0^s x^2w(x)\,dx}{\int_0^s w(x)\,dx},\quad
S_b=\int_0^b w(x)\,dx,\quad
\frac1{w(b)}\int_0^b(x^2-\mu)w(x)\,dx=q^3j.
\tag{11}
\]

They follow by integrating the two rational pieces in (2). They give
`0<mu<s^2` and `j>0`; the latter also follows directly from
`log h>(h-1)/h`.

Set

\[
Q_b=1+\frac{\beta^2-m_0-j/r}{3}\,v-\frac{rj}{9}\,v^2,
\qquad
n_0=Q_b-(1+\mu)S_b^2.
\tag{12}
\]

For `S(x)=integral_0^x w`, the candidate adjoint on the core is

\[
m=-(1+\mu),\quad k=-2(1+\mu)S(x),\quad
n=n_0+(1+\mu)S(x)^2,
\tag{13}
\]
\[
p_w(x)=-\frac1{w(x)}\int_0^x(t^2-\mu)w(t)\,dt,
\qquad
p_x=-1-(x^2-\mu)w-b_i(x)wp_w,
\tag{14}
\]

where `b_2=-2/(q+x)` and `b_1=2/(q-x)` on the respective pieces.
Equations (13)--(14) solve the adjoint equation and the zero active
Hamiltonian. At the three inner edge switches `p_w=0`, so the costate
is continuous. At `b`, `p_w=-q^3j` and `n=Q_b`; hence the active 1 and
outgoing 0 Hamiltonians tie. By reflection the incoming 0 and active 2
Hamiltonians tie at `-b` as well. Extend this covector through the two
outer control-0 arcs. Each active Hamiltonian stays zero because the
vertex Hamiltonian is autonomous.

This constructs a stationary normalized adjoint, without asserting
Hamiltonian minimality for every value of the parameters. If the window
occurs in a PMP trajectory, its adjoint must be this one. Indeed,
[LOCAL_MIXED_SIX_RANK](LOCAL_MIXED_SIX_RANK.md) proves that all six-duration
endpoint maps for positive strict-star `021210` windows have rank five.
An abnormal first-variation identity would force the terminal covector
to vanish; a normal one uniquely determines it. Thus any PMP lift of
the present window is normal and has exactly (13)--(14). This use of
rank does not depend on a separate global normality assertion.

## 3. Exact data at the outgoing control-0 switch

Rotate by

\[
R_0=\begin{pmatrix}1/2&-\sqrt3/2\\ \sqrt3/2&1/2\end{pmatrix}.
\]

Old vertex 0 becomes new vertex 1, old vertex 1 becomes new vertex 2,
and old vertex 2 becomes new vertex 0. To distinguish the new arc's
constant from the core's, write it as `mu_+`. Put

\[
D=3-vr(2-r)>0,\qquad F=h^2(vr^2+3)>0.
\]

At the start of this outgoing arc one obtains

\[
\frac aq=\frac{vr(4-r)-3}{vr^2+3},\qquad
w_+=\frac{(vr^2+3)^2}{16v},\qquad
W=\frac{D^2}{12v},\qquad
R=\frac{3+v(2-r)^2}{D}.
\tag{15}
\]

The old 1--0 tie is the new 2--1 tie, so `p_w(a)=0`. The group
transformation, which also specifies every multiplier used here, is

\[
M_+=K(-a)R_0^T K(b)M(b)K(-b)R_0K(a),
\qquad \mu_+=-1-(M_+)_{12}.
\tag{16}
\]

In the four polynomials below the symbol `L` means `log h`:

\[
\begin{aligned}
A={}&(2-h)(-6Lh^3+12Lh^2-12Lh+8L
                 +h^4+2h^3+7h^2-26h+16),\\
B={}&-3h^2(2Lh^2-8Lh+4L+h^3-4h^2+7h-4),\\
C={}&(3h-2)(-2Lh^3-4Lh^2-4Lh+8L
                 +3h^4-14h^3+53h^2-74h+32),\\
E={}&-3h^2(2Lh^2-8Lh+4L+h^3+4h^2-9h+4).
\end{aligned}
\tag{17}
\]

Here `B` is a polynomial in `h,L`, not the switching function `B(S)`.
Direct substitution in (16) and (6) gives

\[
\mu_+-a^2=\frac{4hv(B-Av)}{3(h-1)F^2},
\tag{18}
\]
\[
B_0=-\frac{(h-1)(hL-h+1)F^2}{9h^6}<0,
\qquad
B_1=-\frac{\sqrt3 F(Cv+E)}{18h^5(h-1)D}.
\tag{19}
\]

For example the second identity can be checked without transporting a
state covector explicitly: at a two-way tie `p_w=0`, differentiation
of the exact gap gives

\[
B_1=-k_+-2a-\frac{(W-1)(\mu_+-a^2)}{q-a},
\quad k_+=2(M_+)_{11}.
\tag{20}
\]

Since the outgoing arc is a genuine PMP vertex-1 arc, `p_w<=0` just
to the right of `a`. Its derivative at the initial zero is
`mu_+-a^2`. Therefore

\[
B-Av\le0.
\tag{21}
\]

Equality is retained at this stage; no transverse-switch assumption
has been inserted.

The following exact signs and threshold inequalities are proved in
Section 5:

\[
A>0,\quad B>0,\quad C>0,\quad CB+EA>0
\qquad(1<h<2),
\tag{22}
\]
\[
B-3A>0\qquad(5/3\le h<2),
\tag{23}
\]
\[
\begin{aligned}
v_X&=\frac{3h^2}{(2-h)(h+2)(2h-1)},&
 B-Av_X&>0&& (1<h\le5/3),\\
v_R&=\frac{33h^2}{(22-h)(3h-2)},&
 B-Av_R&>0&& (5/4\le h\le5/3).
\end{aligned}
\tag{24}
\]

Equations (21)--(24), together with `v<3`, imply

\[
h<5/3,\qquad v\ge B/A>v_X,\qquad Cv+E>0,
\qquad B_1<0.
\tag{25}
\]

For `h>=5/4` they also imply `v>v_R`, equivalently `R>16/5`.
Section 4 supplies the same conclusion for competitive periods with
`h<=5/4`.

The point after factor `h` on the outgoing arc is

\[
z=q-\frac{q-a}{h}.
\tag{26}
\]

The identity `v=v_X` is exactly `a/q=-(h-1)/(h+1)`, or `z=-a`.
The expression for `a` in (15) is strictly increasing in `v`. Thus
`v>v_X` gives `z>-a`. Since also `z>a`, we have

\[
z>|a|\ge0,\qquad z^2>a^2\ge\mu_+.
\tag{27}
\]

The window contains this entire factor-`h` portion of its last arc.
Consequently it satisfies the continuation criterion of Section 1.
Its remaining time from that point to forced star exit is exactly

\[
\sqrt W\log(R/h)>0.
\tag{28}
\]

It is finite. Positivity also follows from `R>16/5` and `h<5/3`.
The actual twisted state and costate endpoints extend a closed lift
indefinitely in strict star, as explained in
[GLOBAL_PERIOD_BUDGET](GLOBAL_PERIOD_BUDGET.md), Section 1. They contradict
this forced exit. This proves the escape half of the theorem, including
the case of a zero derivative in (21).

## 4. The whole-period budget covers the remaining small-h region

At the core center the frame matrix in (13) is

\[
M(0)=\begin{pmatrix}0&-(1+\mu)\\n_0&0\end{pmatrix}.
\]

The original maximizing convention with physical cost `C` has frame
covector `Lambda_1=-(3/2)M` there. Hence

\[
\det\Lambda_1=\frac94\,\mathcal D(h,v,L),
\quad
\mathcal D=(1+m_0/3)
 \left[1+\frac{\beta^2-m_0-j/r}{3}v
       -\frac{rj}{9}v^2
       -(1+m_0/3)\frac{\ell^2}{3}v^2\right].
\tag{29}
\]

For fixed `h`, the expression `Dcal` is a strictly concave quadratic
in `v`: `j>0`, `r>0`, and `1+mu>0`. Its value at `v=0` is
`1+mu>1`. The exact certificate below proves

\[
\mathcal D(h,v_R,\log h)>99/100\qquad(1<h\le5/4).
\tag{30}
\]

By concavity the same strict lower bound holds for `0<v<=v_R`.
In this range `n_0>0`, so `Lambda_1` belongs to the **negative elliptic**
component; a positive determinant alone would not suffice to apply the
cost theorem. Moreover

\[
\det\Lambda_1>\frac{891}{400}>
\left(\frac{313}{210}\right)^2,
\qquad
\frac{891}{400}-\left(\frac{313}{210}\right)^2
=\frac{211}{35280}>0.
\tag{31}
\]

But [GLOBAL_COST_CASIMIR](GLOBAL_COST_CASIMIR.md) proves, for an actual
complete-period negative elliptic PMP lift,

\[
C\ge\frac{4\pi\kappa}{2\kappa+3},\qquad
\kappa=\sqrt{\det\Lambda_1}.
\]

The rational bounds `A_oct<313/100` and `pi>157/50` proved in
[GLOBAL_NUMERICAL_REDUCTION](GLOBAL_NUMERICAL_REDUCTION.md), Section 2,
give `kappa<313/210` whenever `C<=A_oct`. This contradicts (31).
Therefore every competitive occurrence in the small-h region must have
`v>v_R`, giving `R>16/5` as required above. Conservation of the Casimir
alone would not provide this exclusion; the complete-period cost theorem
is used explicitly.

### A finite rational certificate for (30)

For `h>1`, put

\[
L_- =\frac{2(h-1)}{h+1},\qquad
L_+ =\frac{(h-1)(h^2+10h+1)}{6h(h+1)}.
\tag{32}
\]

Then `L_-<log h<L_+`. The proof is differentiation from equality at
`h=1`:

\[
\frac1h-L_-'=\frac{(h-1)^2}{h(h+1)^2}>0,
\quad
L_+'-\frac1h=\frac{(h-1)^4}{6h^2(h+1)^2}>0.
\]

Let `L=L_-+theta(L_+-L_-)`, with `0<=theta<=1`, and define the polynomial

\[
P(h,\theta)=2700(h-22)^2(h+1)^2(3h-2)^2
       [\mathcal D(h,v_R,L)-99/100].
\tag{33}
\]

Clearing the rational factors in (29) gives degree eight in `h` and
degree two in `theta`. Its quadratic coefficient in `theta` is

\[
1100(h-1)^4(h^2-4h+2)(19h^2+24h-22)\le0
\quad(1\le h\le5/4).
\tag{34}
\]

It is enough to check `theta=0` and `theta=1`. Set `t=4(h-1)`.
For `epsilon=0,1`, the following table supplies the exact identity

\[
P(1+t/4,\epsilon)
=\sum_{k=0}^{8}\frac{N_{k,\epsilon}}{d_k}
   {8\choose k}t^k(1-t)^{8-k}.
\tag{35}
\]

| k | d_k | N_k,0 | N_k,1 |
|---:|---:|---:|---:|
| 0 | 1 | 47628 | 47628 |
| 1 | 8 | 463239 | 463239 |
| 2 | 448 | 25084107 | 25235307 |
| 3 | 896 | 41248845 | 42299145 |
| 4 | 8960 | 291978441 | 316279191 |
| 5 | 3584 | 73477692 | 92122967 |
| 6 | 114688 | 1701216315 | 2723688515 |
| 7 | 16384 | 338542731 | 570256931 |
| 8 | 16384 | 702595053 | 1049779728 |

All entries are strictly positive, and the Bernstein basis is a
partition of unity on `[0,1]`. Thus both endpoint polynomials are
strictly positive there. Concavity (34) proves positivity for all
`theta`, and the multiplier in (33) is positive. This proves (30).
The table is a finite rational identity verifiable by expansion; no
floating-point bound on `log h` or unrecorded computer search is a premise.

## 5. Hand sign certificate for the outgoing-arc inequalities

The expressions `A,B,C,F_1,F_2` and the three threshold differences
in (23)--(24) are affine in `L`, so it suffices to evaluate them at
the two rational bounds (32). The following
reductions give the signs in (22). In this table `Q_-` and `Q_+` are
positive multiples of the indicated expression evaluated at `L_-`
and `L_+`; the denominators shown are all positive for `1<h<2`.

| Expression | At L_- | At L_+ |
|---|---|---|
| A/[(2-h)(h-1)^2] | h(h^2-7h+30)/(h+1) | -2(6h^3-39h^2-5h+2)/(3h(h+1)) |
| B/[3h^2(h-1)^2] | (-h^2-3h+12)/(h+1) | -2(2h^3+2h^2-15h-1)/(3h(h+1)) |
| C/[(3h-2)(h-1)^2] | (3h^3-9h^2+14h+16)/(h+1) | 2(4h^4-14h^3+21h^2+27h-2)/(3h(h+1)) |
| F_1/(h-1) | (h^3-3h+6)/(h+1) | (3h^3-2h^2-5h+16)/(3(h+1)) |
| -F_2/(h-1)^3 | (8-h^2)/(h+1) | -2(2h^2-2h-11)/(3(h+1)) |

Here

\[
\begin{aligned}
F_1&=-4Lh+h^3-2h^2+7h-6,\\
F_2&=2Lh^3-8Lh^2+4Lh+h^4-8h^3+23h^2-24h+8.
\end{aligned}
\]

For explicit elementary checks of the ten positive numerators:
`h^2-7h+30>=20`; `6h^3-39h^2-5h+2<0` follows from
`6h^3<=12h^2`; and `-h^2-3h+12>=2`.
For the next cubic, `2h^3+2h^2-15h-1<=6h^2-15h-1<0`, the last
convex quadratic having negative values at both interval endpoints.
The derivative of `3h^3-9h^2+14h+16` is `9(h-1)^2+5>0`.
The next numerator is
`h^2(4h^2-14h+21)+27h-2>0`, since the quadratic has minimum `35/4`.
The two `F_1` numerators are increasing on `[1,2]`, with positive
initial values 4 and 12; their derivatives are `3(h^2-1)` and
`(h-1)(9h+5)`, respectively. Finally `8-h^2>=4` and
`-2(2h^2-2h-11)>=14`.

Thus `A,B,C,F_1,-F_2>0`. The exact factorization

\[
CB+EA=-24h^2(h-1)F_1F_2>0
\tag{36}
\]

completes (22).

For the threshold inequalities put

\[
\begin{aligned}
U_1&=h^3+6h^2-6h-12,& U_2&=2h^3+7h^2-10h-16,\\
V_1&=7h^4-79h^3+144h^2+144h-264,&
V_2&=3h^4-98h^3+234h^2+151h-362,\\
Q&=h^5+4h^4-33h^3+36h^2+6h-2.
\end{aligned}
\tag{37}
\]

Substitution of the two bounds gives

\[
\begin{array}{c|cc}
 &L_-&L_+\\\hline
B-Av_X&
\displaystyle\frac{-6h^2(h-1)^3U_1}{(h+1)(h+2)(2h-1)}&
\displaystyle\frac{-4h^2(h-1)^3U_2}{(h+1)(h+2)(2h-1)}\\[6pt]
B-Av_R&
\displaystyle\frac{-6h^2(h-1)^2V_1}{(h-22)(h+1)(3h-2)}&
\displaystyle\frac{-4h^2(h-1)^2V_2}{(h-22)(h+1)(3h-2)}\\[6pt]
B-3A&
\displaystyle\frac{-12h(h-3)(h-1)^2(3h-5)}{h+1}&
\displaystyle\frac{-4(h-1)^2Q}{h(h+1)}.
\end{array}
\tag{38}
\]

On `[1,5/3]`, `U_1` and `U_2` are increasing and their final values
are `-19/27` and `-107/27`. This proves the first line of (24).

On `[5/4,5/3]`, `V_1` and `V_2` are positive and increasing.
Their initial values are `971/256` and `2123/256`. Their second
derivatives are negative on this interval: respectively they are
bounded above by `84(5/3)^2-474(5/4)+288<0` and
`36(5/3)^2-588(5/4)+468<0`. Their first derivatives are therefore
bounded below by the positive final values `2573/27` and `1529/9`.
Since `h-22<0`, the second line of (38) proves the second line of (24).

Finally, on `[5/3,2]`, the third line's lower-bound expression is
nonnegative. Its upper-bound expression is strictly positive:
`Q(5/3)=-256/243<0`, and `Q'<0` throughout this interval. To see the
latter, `Q'''=6(10h^2+16h-33)>0`, so `Q'` is convex; its endpoint
values `-2944/81` and `-38` are both negative. Hence `Q` decreases
and stays negative. Because `log h` is strictly between `L_-` and
`L_+`, the affine interpolation is strictly positive even at `h=5/3`.
This proves (23) and finishes every uniform sign used above.

## Validation and retained alternatives

[The supplementary checker](../explorations/mixed_global_symmetric_certificate.py)
reconstructs the rational core integrals, state rotation, cotangent frame
rotation, both initial gap formulas, the factorizations, all threshold
substitutions, and the 18 rational Bernstein coefficients. It performs
symbolic identities and rational comparisons only. The displayed
identities, elementary derivative arguments, and finite Bernstein table
are the proof; the checker is reproducible supplementary verification.

The independent reviewer and root each ran
`python explorations/mixed_global_symmetric_certificate.py`; all 146 exact
algebra identities and rational sign checks passed with Python 3.12.14 and
SymPy 1.14.0. The checker uses no floating-point samples or random seeds.

The claim retains the following boundaries explicitly. The core is
reflection symmetric, its four factors are equal, and the last pad
must last at least that factor. An arbitrary asymmetric M1 input, a
shorter outgoing arc, or a degenerate limiting input is outside the
claim. Initial zero gap derivatives were retained and resolved by the
actual last arc and (27); they were not discarded by a numerical
transversality filter. The escape continuation has strict gaps, so it
contains no unresolved triple tie or branch choice. Only the actual
complete-period Casimir inequality supplies the budget obstruction.
