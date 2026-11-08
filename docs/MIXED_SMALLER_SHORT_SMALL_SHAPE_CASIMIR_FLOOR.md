# A corrected Casimir floor on a small short-shape domain

**Current dependency role:** the completed hand route uses the
[extended floor](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_FLOOR.md) and
[its six new derivative proofs](MIXED_SMALLER_SHORT_EXTENDED_CASIMIR_DERIVATIVES.md).
Only the analytic reductions in Sections 1--3 of this narrower note
are retained. Its older extracted coefficient groups are not premises
of the final hand argument.

Date: 2026-11-08 UTC. Hand lemma accepted in the
[independent Casimir review](MIXED_SMALLER_SHORT_SMALL_SHAPE_CASIMIR_AUDIT.md).
The two small-shape restrictions in the theorem are hypotheses, not
conclusions about every actual short bridge.

**Theorem.** Retain the actual smaller-short setup and its corrected
envelope comparison. Suppose additionally
\[
2\le x\le\frac{15}{7},\qquad
0\le\delta:=\frac{\beta}{x}-1\le\frac1{19}.
\tag{1}
\]
Then the squared Casimir of the original common covector satisfies
\[
\boxed{\Gamma_{\rm actual}>\frac{183}{1000}.}
\tag{2}
\]
No competitive upper cap is assigned to a scalar comparison point.
This lemma does not establish (1), compare the physical completion
cost, or close the smaller-short exclusion.

## 1. Shape bounds and notation

The strong lower order and the
[small-shape upper order](MIXED_SMALLER_SHORT_SMALL_SHAPE_UPPER_ORDER.md)
give
\[
1+\frac{13}{5}\delta\le\alpha\le1+3\delta.
\tag{3}
\]
For the lower bound, the coefficient
1+4x(x+1)/(7x+1) increases with x and equals 13/5 at x=2.
Write
\[
\alpha=1+\eta\delta,\qquad \frac{13}{5}\le\eta\le3,
\quad \beta=x(1+\delta).
\tag{4}
\]
When delta=0 the two order bounds give alpha=1, and any eta in this
interval represents the same shape.

Use
\[
S=1+x,\quad r=S^{-1},\quad r_A=\frac{\alpha}{\alpha+\beta},
\quad q=\rho_A,\quad
q_c=\frac{\alpha^2}{S^2+\alpha^2-1}.
\]
The incoming norm remains its original exact value u. The proved
incoming estimate gives
\[
\frac34\le u\le\bar u(x,\beta):=
\frac34+\frac{1}{\beta-1}
\left\{\frac{2(x-1)^3}{S(35x+13)}
               +\frac{(\beta-x)^3}{48x^2}\right\}<\frac{31}{40}.
\tag{5}
\]
For the last coarse bound, beta-1>=x-1, x<=15/7 and x-1>=1
bound the two positive terms respectively by 4/363 and 1/10000.
Their sum is less than 1/40.

The following elementary consequences of (1), (3) will be useful:
\[
0<D<S,\qquad q_c<\frac16,\qquad \frac{r_A}{q_c}>2,
\quad D=\alpha^2+2\alpha\beta+1+2x-2\beta x.
\tag{6}
\]
Indeed alpha<=22/19<6/5 and beta<=300/133<23/10. Thus
alpha^2+2alpha*beta<174/25<8<=x(x+2), proving the last inequality.
Also q_c<=121/843<1/6. Since D increases with alpha and decreases
with beta on alpha<=x,
\[
D\ge 6-\frac{4800}{931}>0.
\]
For the upper bound, substituting alpha<=1+3delta gives
\[
D-S\le1+3x-2x^2+\delta(6+8x-2x^2)
                         +\delta^2(9+6x).
\]
This decreases with x>=2 and increases with delta on the stated
rectangle. Its value at x=2,delta=1/19 is -74/361<0.

## 2. Increase the comparison scale up to q_c

At the original actual outer-root parameter put p=tau*q. The
[corrected envelope theorem](MIXED_SMALLER_SHORT_CORRECTED_ENVELOPE_CAP.md)
gives
\[
\Gamma_{\rm actual}\ge
 \Gamma_*(q)-\frac17R^*_{p/q}(q).
\tag{7}
\]
This is a lower bound on the original actual Casimir. The envelope
does not inherit that covector's competitive upper cap.

The fixed-p derivative proof in
[the corrected-cap scale theorem](MIXED_SMALLER_SHORT_CORRECTED_CAP_SCALE.md)
extends to q<=1/6 without alteration: its inequality (1) is independent
of q, and its derivative estimate becomes
\[
(\Gamma_*)_q<
 \frac{3L(p)}{32(1-q)^2}\le\frac{27}{200}L(p)<\frac17L(p).
\tag{8}
\]
Thus the right side of (7) decreases while q increases at fixed p.
Increase q to min(q_c,p/2). If the first endpoint is q_c, this part
is finished. Otherwise tau=2.

We next prove that the corrected expression also decreases at fixed
tau=2 for all 0<q<=1/6 on (1), (3), (5). Set
\[
a=\alpha^{-2},\quad \varepsilon=1-a,\quad
\Delta=D/\alpha^2,\quad E_0=S(u-1)+S^{-1},
\]
\[
H=S[U(1/S)-u]\ge0,\qquad
A_2=\varepsilon^2+\varepsilon Sa+S^2a^2
       +\Delta\varepsilon E_0-\Delta(2S-1)a+u\Delta^2.
\]
Here A_2>0. For a direct check use the discriminant identity (9) in
[the combined scale proof](MIXED_SMALLER_SHORT_ROOT_FLOOR_SCALE.md):
with z=(S-2)^2a<2 and 3<=S<=22/7<5, its numerator is at most
S^4-28S^2+4<=4-3S^2<0. Completing the diagonal square therefore
gives the strict sign exactly as in that proof.

Differentiating the tau-two residual gives
\[
(R_2^*)'=\frac1q-C_0+4qA_2,\qquad
C_0=2+\varepsilon(3+E_0)+2\Delta(E_0+u).
\]
On the present domain E_0<0 and E_0+u>0. The inequality D<S gives
\[
C_0\le2+3\varepsilon
             +2S(1-\varepsilon)(E_0+u)\le5.
\]
For the last step,
2S(E_0+u)=2[S(S+1)u-S^2+1]<=13/5<3: use u<=31/40
and note that the resulting quadratic decreases for S>=3.
Consequently (R_2^*)'>1 on q<=1/6.

The explicit envelope Casimir derivative satisfies
\[
(\Gamma_*)_q\le
 \frac{H(2S-1)}{8\alpha^2(1-q)^2}
\le\frac{1332}{13475}<\frac1{10}.
\]
Here H<=(S-2)^2/(4S)<=8/77 and 2S-1<=37/7.
It follows that
\[
\frac{d}{dq}\left(\Gamma_*-\frac17R_2^*\right)
<-\frac3{70}<0.
\tag{9}
\]
We may therefore continue from p/2 to q_c with tau fixed at two.
Equation (6) ensures that the final parameter still obeys
2<=tau<=T:=r_A/q_c. The possible passage beyond the original
outer cap q<1/7 is purely a scalar comparison, justified by (8)--(9).

## 3. Two scalar lower bounds at the central-duration endpoint

At q=q_c the physical scale is rho=r^2. Put
\[
X=x(x+2),\quad \Sigma=X+\alpha^2,\quad
U_1=1-S^{-1}+S^{-2},
\]
\[
E=S(u-1)+3S^{-1}-S^{-2},\qquad
w=\frac{S^4U_1+D^2u-DS^2E}{\Sigma^2},
\quad E_L=\frac{2Du-S^2E}{\Sigma},
\]
\[
\Gamma_*=\frac{S^4(4uU_1-E^2)}{16X^2},\qquad
q=\frac{\alpha^2}{\Sigma},\quad
T=\frac{\Sigma}{\alpha(\alpha+\beta)}.
\tag{10}
\]
Define
\[
R_2=2w-\frac12+\frac{u-1}{r_A}+r_A-q-E_L
                                  +\log(2/T),
\]
\[
\Phi=\Gamma_*-\frac{R_2}{7},\qquad
\Psi=\Gamma_*-\frac{R_2+(T-2)(w-3/4)}7.
\tag{11}
\]
For 2<=tau<=T the residual derivative is at most w-3/4. Hence
\[
R_\tau\le\max\{R_2,R_2+(T-2)(w-3/4)\},
\]
including either sign of w-3/4. The scale comparisons therefore give
\[
\Gamma_{\rm actual}\ge\min\{\Phi,\Psi\}.
\tag{12}
\]
No outgoing norm floor at q_c is assumed in this step.

Both functions in (11) strictly decrease as u increases on (5).
Here is a uniform elementary verification. Let z=D/Sigma and
C=S^3/Sigma. Then 0<z<1/3, C>=20/7 and 1/r_A>=30/11. Therefore
\[
(R_2)_u=\frac1{r_A}+C(1-2z)-2z(1-z)
\ge\frac{2242}{693}.
\]
Also w_u=D(D-S^3)/Sigma^2>=-1, and T<=S<=22/7. Thus the
u derivative of the second residual in (11) is at least 1450/693.
On u>=3/4, E>=0 on the rectangle, so
\[
(\Gamma_*)_u\le\frac{U_1}{4(1-S^{-2})^2}\le\frac{81}{320}
 <\frac{1450}{4851}.
\]
These estimates prove the two decreasing directions. The bound C>=20/7
uses Sigma<=21S^2/20, which follows from alpha^2-1<=123/361<9/20.
For E>=0, use its monotonicity in u and its decreasing dependence on S
at u=3/4, and evaluate at S=22/7. Consequently it suffices to use
the rational upper value u=bar u in both Phi and Psi.

## 4. Six polynomial signs on the complete small rectangle

In this section Phi and Psi mean (11) with u=bar u and the shape (4).
The following signs hold on the full closed rectangle (1), (4):
\[
-\Phi_\delta>0,\qquad
\frac{\Psi_\eta}{x\delta}>0,\qquad -\Psi_x>0,
\tag{13}
\]
\[
-\Phi_x\big|_{\delta=1/19}>0,\qquad
-\Phi_\eta\big|_{x=15/7,\delta=1/19}>0,\qquad
-\Psi_{\delta\delta}\big|_{x=15/7,\eta=13/5}>0.
\tag{14}
\]
The quotient in (13) is interpreted by its polynomial extension at
delta=0; in particular Psi_eta=0 there.

Here are complete finite coefficient bounds proving these six signs.
They are included to specify the arithmetic of the rational derivative
arguments. They require no interval cover or executable sign premise.

Denote the six expressions in (13)--(14), in that order, by W_1,...,W_6.
For brevity set B=beta-1, A=alpha+beta and Z=35x+13. Multiplication
by the following positive denominators gives polynomials P_i=D_i W_i:
\[
\begin{array}{c|l}
i&D_i\\ \hline
1&xS(x+2)^2Z^2\alpha^2B^3A^2\Sigma^3\\
2&SZ\alpha^2BA^2\Sigma^2\\
3&x^3S^2(x+2)^3Z^3\alpha B^3A^2\Sigma^2\\
4&x^3S^2(x+2)^3Z^3\alpha B^3A^2\Sigma^3\\
5&\alpha^2A^2\Sigma^3\\
6&\alpha^3B^4A^3\Sigma^3.
\end{array}
\tag{15}
\]
The specializations in (14) are made in the corresponding denominators
as well. For row two, the factor x*delta is canceled before forming
its polynomial. All logarithms disappear upon differentiation.

For rows 2 and 3 substitute
\[
x=2+h,\quad\delta=g,\quad\eta=3-a;
\]
for row 4 use x=2+h,eta=13/5+a; for row 5 use eta=3-a; and for
row 6 use delta=g. The ranges are
\[
0\le h\le1/7,\qquad 0\le g\le1/19,\qquad 0\le a\le2/5.
\tag{16}
\]
Divide each resulting polynomial by its positive constant term.
The signs of these constants can be checked directly from the
following respective values of W_i at those origins:
\[
\begin{array}{c|l}
2&4229/423549\\
3&171516573839/31870474223616\\
4&13795954844326628649722636697841/
  2813435823143289494140377799458816\\
5&63423229824441842100545543365/
  1474016540242549964438309079839984\\
6&2120647490225753/4761264653522531.
\end{array}
\tag{17}
\]
All are positive. If b_jkl is a coefficient in one of these
normalized polynomials, its complete negative coefficient norm is
bounded by
\[
\sum_{b_{jkl}<0}|b_{jkl}|h^j(1/19)^k(2/5)^l
\le \frac1{1000}\sum_{j=0}^{6} n_{ij}h^j,
\tag{18}
\]
where the complete integer rows are
\[
\begin{array}{c|rrrrrrr|c}
i&n_{i0}&n_{i1}&n_{i2}&n_{i3}&n_{i4}&n_{i5}&n_{i6}
 &\text{upper value on }h\le1/7\\ \hline
2&29&13&14&8&3&1442&2776&1/25\\
3&14&120&491&1318&59360&314907&5716647&1/7\\
4&2&3&4&9&87985&377707&5675199&1/8\\
5&2&0&0&0&0&0&0&1/500\\
6&359&0&0&0&0&0&0&9/25.
\end{array}
\tag{19}
\]
Every bound in the last column is less than one. It follows that
each normalized polynomial is positive: its retained constant one
strictly exceeds its complete negative part.

For precision, (18)--(19) use the following coefficient convention,
which also provides a direct finite way to verify every entry.
For a given h degree, sum all negative coefficients in absolute value
after multiplying their g and a degrees by (1/19)^k(2/5)^l.
Group all h degrees at least six into degree six, using h<=1.
Multiply each resulting coefficient by 1000 and round upward to
the integer printed in (19). Differentiating (10)--(11), clearing
exactly (15), and collecting the displayed shifted variables gives
these bounds; no sign of any discarded positive coefficient is needed.

Row one uses one additional positive-basis identity. In P_1 substitute
x=2+h and eta=13/5+a, and normalize by P_1(2,0,13/5)>0.
The corresponding value of W_1 is 35322804569/269987074560.
Let N=16 and write the resulting degree-sixteen polynomial in delta as
\[
P_1=\sum_{i=0}^{16}\binom{16}{i}
 E_i(h,a)(19\delta)^i(1-19\delta)^{16-i}.
\tag{20}
\]
If p_j(h,a) are its ordinary delta coefficients, this means exactly
\[
E_i=\sum_{j=0}^{i}\frac{\binom{i}{j}}{\binom{16}{j}}
                          \frac{p_j}{19^j}.
\tag{21}
\]
The only negative ordinary delta coefficients of P_1(0,delta,0)
have degrees 1,2,3,4. Their absolute contributions at delta=1/19
are bounded above, respectively, by
\[
\frac{28319}{10^6},\quad\frac{213159}{10^6},\quad
\frac{55189}{10^6},\quad\frac{2244}{10^6}.
\]
Their sum is 298911/10^6<3/10. Since every binomial ratio in (21)
lies in [0,1], this proves
\[
E_i(0,0)>\frac7{10}\qquad(0\le i\le16).
\tag{22}
\]
For every one of these seventeen polynomials, its entire negative
part, after weighting the a degrees by (2/5)^l, is bounded by
\[
\frac{105+691h+1720h^2+1226h^3+1643h^4
                     +1788h^5+2565h^6}{1000}<\frac14.
\tag{23}
\]
The coefficient convention is the same as (18), taking at each h
degree the largest of the seventeen negative coefficient sums before
grouping degrees at least six and rounding upward. This specifies
the full bound, not a selected subset of negative terms.
Equations (22)--(23) give E_i>7/10-1/4>0. The nonnegative basis
in (20) sums to one, proving row one on the whole closed interval.
This completes the six signs.

## 5. Reduction to three rational endpoint estimates

By (13)--(14), Phi first decreases in delta, then decreases in x
on the terminal delta face, and finally decreases in eta on that
terminal edge. Therefore
\[
\Phi\ge\Phi(15/7,1/19,3).
\tag{24}
\]
For Psi, first decrease eta to 13/5 using Psi_eta>=0, then increase x
to 15/7 using Psi_x<0. The remaining function is concave in delta.
Its minimum is consequently at delta=0 or delta=1/19:
\[
\Psi\ge\min\{\Psi(15/7,0,13/5),\Psi(15/7,1/19,13/5)\}.
\tag{25}
\]

Each of these three values has the form Z_0-log(y)/7 with rational
Z_0 and 0<y<1. The exact pairs are
\[
\begin{array}{c|c|c}
 &y&Z_0\\ \hline
\Phi&
139832/180751&
6109072818772517786763741171256271/
41727591241879596166863435095581248\\
\Psi,\ \delta=0&
7/11&
5555226774529/46828912649904\\
\Psi,\ \delta=1/19&
1137024/1499137&
744961501813421254393188682951/
5189733165315945593462888070144.
\end{array}
\tag{26}
\]
Put z=(y-1)/(y+1)<0. The odd logarithm series gives
\[
\log y<2(z+z^3/3+z^5/5).
\]
Substitution of the three rational rows in (26), followed by positive
denominator multiplication, gives the respective strict lower bounds
\[
Z_0-\frac27(z+z^3/3+z^5/5)-\frac{183}{1000}
>
\frac1{20000},\qquad\frac1{10000},\qquad\frac1{25000}.
\tag{27}
\]
Thus both scalar functions in (12) exceed 183/1000. This proves (2)
for the original common covector, conditional on the two shape
restrictions (1). The proof used the costate's original lower-bound
comparison (7), and did not move its physical upper cap or period
closure to any artificial endpoint.
