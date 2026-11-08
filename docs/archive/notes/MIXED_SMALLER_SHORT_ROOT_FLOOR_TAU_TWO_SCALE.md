# Scale monotonicity of the combined short test at tau=2

Date: 2026-11-08 UTC. Hand lemma, accepted in the
[independent short-lemma review](MIXED_SMALLER_SHORT_ORDER_AND_SCALE_AUDIT.md),
Section 12. This removes
the tau=2 scale face from the
[combined residual scale reduction](MIXED_SMALLER_SHORT_ROOT_FLOOR_SCALE.md).
It does not prove the signs on the remaining two scale faces.

## 1. Statement

Retain
\[
\frac{12}{5}\le x\le9,\qquad 1\le\alpha\le x\le\beta,
\qquad
\frac34\le u\le\frac{13}{16}.
\tag{1}
\]
Require in addition the incoming-floor hypothesis
\[
\boxed{u\ge\frac34+\frac{(x-1)^2}{28(x+1)^2}.}
\tag{1a}
\]
The theorem below is a scalar statement on (1)--(1a). In its actual
application, u=Sec(1,x,beta), and (1a) follows, strictly, from the
[uniform incoming floor](MIXED_SMALLER_SHORT_UNIFORM_INCOMING_FLOOR.md).
The interval 3/4<=u<=13/16 alone is insufficient for the lower bound
F used in the proof. In particular (1a) must be retained whenever
this theorem is used after a scalar comparison.

Use the coefficients A_1,A_2,A_3 of the envelope scale theorem and
put
\[
G_2(q)=R_2^*(q)+\frac12[w_*(q)-3/4].
\]
Then
\[
\boxed{G_2'(q)>0\qquad(0<q\le1/7).}
\tag{2}
\]
No inequality q<=r_A/2, no sign of D and no Casimir cap is assumed.

## 2. A domain consequence of the incoming secant

Write S=1+x and
\[
a=\alpha^{-2}\in(0,1],\quad \varepsilon=1-a,\quad
\delta=D/\alpha^2,\quad H=-E_0=S(1-u)-S^{-1}>0.
\]
The explicit hypothesis (1a) gives
\[
u\ge\frac34+\frac{(S-2)^2}{28S^2}.
\]
Therefore
\[
H\le\frac{3S}{14}+\frac17-\frac{8}{7S}
\le\frac{76}{35},
\tag{3}
\]
since the middle expression increases with S and S<=10.
There is also the useful implication
\[
H\ge2\quad\Longrightarrow\quad u\ge\frac{77}{100}.
\tag{4}
\]
Indeed H<=S/4-1/S, so H>=2 forces S>8. The same incoming floor
then gives
\[
u>\frac34+\frac{9}{448}
 =\frac{77}{100}+\frac1{11200}.
\]
All comparisons below may use the weak closed bounds (3)--(4).

## 3. Complete the diagonal square

Set
\[
A=\varepsilon^2+\varepsilon Sa+S^2a^2,
\qquad K=\varepsilon H+(2S-1)a,
\qquad b=2u-\frac52H,
\]
\[
C=6-H+a(H+S/2-4).
\]
As in the preceding scale reduction,
\[
A_1=2\varepsilon+Sa-\delta H,\quad
A_2=A-\delta K+u\delta^2,\quad
A_3=2u\delta-K.
\]
Differentiating the explicit tau=2 residual and its norm term gives
\[
qG_2'(q)
=1-q\left(\frac52A_1+1+A_3\right)+5q^2A_2
\]
\[
=1-Cq+5Aq^2+5u(\delta q)^2-(b+5Kq)\delta q
\ge F(q,a):=1-Cq+5Aq^2-\frac{(b+5Kq)^2}{20u}.
\tag{5}
\]
This completed square is valid for either sign of delta.

At fixed S,u,q, the expression F is concave in a. Its quadratic
coefficient is
\[
-\frac{5q^2S^2[u-U(1/S)]^2}{4u}\le0.
\tag{6}
\]
To check the identity, use
\(2S-1-H=S[u+U(1/S)]\) and
\(S^2-S+1=S^2U(1/S)\). Thus it suffices to prove
\[
F(q,0)>0,\qquad F(q,1)>0
\qquad(0\le q\le1/7).
\tag{7}
\]
The closed value q=0 is included only in these polynomial lower
bounds.

## 4. The common q=0 endpoint

Both values in (7) have
\[
F(0,a)=1-\frac{(2u-5H/2)^2}{20u}.
\tag{8}
\]
If 0<=H<=2, then -7/2<=2u-5H/2<=13/8. Consequently
\[
F(0,a)\ge1-\frac{(7/2)^2}{15}=\frac{11}{60}>0.
\tag{9}
\]
If H>=2, (3)--(4) give
\[
\left|2u-\frac52H\right|
=\frac52H-2u
\le\frac{1361}{350},\qquad20u\ge\frac{77}{5}.
\]
Hence
\[
F(0,a)\ge\frac{34179}{1886500}>0.
\tag{10}
\]

## 5. The a=0 endpoint

Here
\[
F(q,0)=1-(6-H)q+5q^2
 -\frac{[2u-(5/2-5q)H]^2}{20u}.
\tag{11}
\]
It is concave as a function of H at fixed q,u.

### 5.1. The range 0<=H<=2

Concavity reduces this range to H=0 and H=2, allowing u to remain
in [3/4,13/16] at both comparison endpoints.

At H=0, (11) becomes 1-6q+5q^2-u/5. It decreases on [0,1/7],
and thus is at least
\[
\frac{12}{49}-\frac{13}{80}=\frac{323}{3920}>0.
\tag{12}
\]
At H=2, the derivative of (11) at q=0 is
\[
\frac5u-6\ge\frac2{13}>0.
\]
If its quadratic coefficient in q is nonnegative, it increases on
q>=0. If that coefficient is negative, it is concave and its minimum
on [0,1/7] is at an endpoint. In either case it suffices to use
(9) at q=0 and its value at q=1/7. The latter is
\[
\frac{12}{49}-\frac u5+1-\frac{125}{196u}
\ge\frac{719}{2940}>0.
\tag{13}
\]
For the inequality, the expression increases with u throughout
[3/4,13/16], so substitute u=3/4.

### 5.2. The range 2<=H<=76/35

The derivative of (11) at zero is
\[
\frac{5H^2}{4u}-6\ge\frac2{13}>0.
\]
The same quadratic alternative reduces this entire range to q=0
and q=1/7. The first is positive by (10). The second equals
\[
\frac{12}{49}-\frac u5+\frac H2-\frac{125H^2}{784u}.
\tag{14}
\]
On 2<=H<=76/35 and 77/100<=u<=13/16 this decreases with H and
increases with u: these signs follow directly from its two partial
derivatives. Its minimum is therefore at H=76/35,u=77/100, giving
\[
\frac{18514271}{92438500}>0.
\tag{15}
\]
This completes F(q,0)>0.

## 6. The a=1 endpoint reduces to q endpoints

In this case
\[
F(q,1)=1-(2+S/2)q+5S^2q^2
 -\frac{[2u-5H/2+5(2S-1)q]^2}{20u}.
\tag{16}
\]
Its quadratic coefficient in q is
\[
5\left[S^2-\frac{(2S-1)^2}{4u}\right].
\tag{17}
\]
If (17) is nonpositive, concavity gives the two endpoint alternative.
If it is positive, put
\[
u_0=\frac{(2S-1)^2}{4S^2}<u.
\]
Using H=S(1-u)-1/S, direct expansion gives
\[
14u F_q(1/7,1)
=15S^2+\frac{5S}{2}-40+\frac{35}{2S}
 -u\left(15S^2+\frac{35S}{2}+14\right).
\tag{18}
\]
The right side strictly decreases with u. At u=u_0, the quadratic
coefficient (17) vanishes, and the derivative itself simplifies to
\[
F_q(1/7,1)\big|_{u=u_0}
=-\frac{23S-4}{4(2S-1)}<0.
\tag{19}
\]
Consequently F_q(1/7,1)<0 also for u>u_0. When (17)>0 the
derivative increases with q, so it is negative throughout [0,1/7].
Thus in this case the minimum is at q=1/7 as well. In every case,
only q=0 and q=1/7 need be checked. The first is already positive
by (9)--(10).

## 7. The last q=1/7 endpoint

Substitute H=S(1-u)-1/S in (16). The resulting value at q=1/7 is
concave in u: its nonaffine part has the form
\(-(c_1u+c_0)^2/(20u)\). It is therefore enough to check
u=3/4 and u=13/16. The two expressions are
\[
F(1/7,1)\big|_{u=3/4}
=\frac{2775S^4-7320S^3+19064S^2-12320S-19600}{47040S^2},
\tag{20}
\]
\[
F(1/7,1)\big|_{u=13/16}
=\frac{36975S^4-145960S^3+299984S^2-228480S-313600}{815360S^2}.
\tag{21}
\]
Each increases with S for S>=17/5. After division by S^2,
the derivatives of their respective numerators are
\[
5550S-7320+\frac{12320}{S^2}+\frac{39200}{S^3}>0,
\]
\[
73950S-145960+\frac{228480}{S^2}+\frac{627200}{S^3}>0.
\]
The positive signs already follow from the first two terms at
S=17/5. Their values at that endpoint are
\[
\frac{1210099}{2718912}>0,
\qquad\frac{39541839}{235639040}>0.
\tag{22}
\]
This proves F(q,1)>0. Sections 3--7 establish (7), and (5)--(6)
then prove the derivative sign (2).

## 8. Consequence for the scalar endpoint reduction

If the preceding fixed-p comparison reaches q=p/2, it has tau=2.
The present theorem then permits increasing q at fixed tau=2 until
\[
q=\min\left\{\frac{\alpha^2}{S^2+\alpha^2-1},\frac17\right\}.
\]
For the caller in
[the large-ratio exclusion, Section 3](MIXED_SMALLER_SHORT_LARGE_RATIO_HAND_EXCLUSION.md),
both the preceding fixed-p comparison and this tau=2 comparison
keep x,beta and the actual incoming value u=Sec(1,x,beta) fixed.
Thus (1a) holds at the start and throughout the comparison; the
caller still closes with exactly the same endpoint alternatives.

It remains valid if this comparison passes q=r_A/2, where the
formal value T=r_A/q becomes less than two. At such a comparison
point no actual outer reverse arc is asserted. Any subsequent
logarithm estimate must be valid at the resulting argument 2q/r_A,
which may exceed one.

Together with the preceding scale alternative, this leaves only the
q=0 scalar value and the central-duration and outer-scale faces for
the combined test. No physical completion cost, Casimir cap or
separate floor has been transported by either comparison.
