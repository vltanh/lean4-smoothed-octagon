# Central residual monotonicity along an exact short bridge

Research checkpoint, 2026-11-07. This is a uniform comparison on one
actual short bridge. It proves a central residual bound for either sign
of the bridge diagonal; it does not settle the outer root or close M2.

The general comparison is now completed in
[MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM](MIXED_GLOBAL_SHORT_BRIDGE_MINIMUM.md)
and its independent audit. The scope of this constituent lemma is retained.

## 1. Exact secant continuation

Normalize the selected global reverse-centre minimum to `a=1` in the
dimensionless ratios, keeping its physical scale fixed. Write an incoming
short bridge as `(alpha,beta,x,1)` and the opposite near turn as y. The
actual ordering is

`1<=alpha<x<=beta<=alpha*x`, `x<=y`.

Put `g(t)=1-t/(1+t)^2`, `U(r)=1-r+r^2`. The common turn norm u is

\[
u=\frac1{x-\alpha}\int_\alpha^x g(t/\beta)\,dt
 =\frac1{\beta-1}\int_1^\beta g(t/x)\,dt.             \tag{1}
\]

Hold x fixed and increase beta from x to its actual value along the
unique solution alpha(beta) of (1). At beta=x, alpha=1 and u=V(x).
The whole segment exists: the right average remains above g(beta/x)
up to its unique first return, while the left average decreases strictly
with alpha from its value at alpha=1 to g(x/beta) at alpha=x. The
equal-centre average comparison puts the former above the right average.
The actual beta is before that first return. This constructs the segment
without a choice of a second root or an endpoint-Jacobian inverse.

Set

\[
p=\alpha/\beta,\quad q=x/\beta,\quad
\eta=u-g(q)>0,\quad \xi=g(p)-u>0,
\quad M=\frac x\beta+\frac{x-\alpha}{\beta-1}.
\]

Differentiating the integral averages and their homogeneity gives

\[
u_\beta=-\frac\eta{\beta-1},\qquad
\alpha_\beta=\frac\alpha\beta+\frac\eta\xi M>0.      \tag{2}
\]

Thus the path remains between its equal-centre starting point and the
actual centre. The bridge order `beta<=alpha*x` holds throughout, by the
same two-average comparison used in the [positive-diagonal scale note](MIXED_GLOBAL_SHORT_BRIDGE_SCALE.md).

## 2. Two uniform bounds for the secant gaps

For `0<p<q<=1`, use the elementary logarithm upper bound

\[
\log z<\frac{(z-1)(z^2+10z+1)}{6z(z+1)}\quad(z>1).
\]

It follows by writing `z=(1+t)/(1-t)` and bounding every denominator
after the first term of the positive atanh series below by 3. Applying
it with `z=(1+q)/(1+p)` gives

\[
\eta>\eta_0: =
\frac{(q-p)(6+p-5pq-q^2-q)}
 {6(1+p)(1+q)^2(p+q+2)}>0.                            \tag{3}
\]

Moreover

\[
\boxed{\eta/\xi\ge2/7.}                            \tag{4}
\]

Here is a complete sign proof. Since
`g(p)-g(q)=(q-p)(1-pq)/[(1+p)^2(1+q)^2]`, it is enough to show
`eta0>=2[g(p)-g(q)]/9`. After clearing positive factors the numerator is

\[
R(p,q)=3(3-11q)p^2+3(q^2-10q+17)p
                         +3(1-q)(3q+10).
\]

If `q<=3/11`, all coefficients are nonnegative. If `q>=3/11`,
the polynomial is concave in p, so its minimum on `[0,q]` is at an
endpoint. Those endpoint values are
`3(1-q)(3q+10)` and `30(1-q)(1+q)^2`, both nonnegative.
This proves (4), including the limiting endpoint cases.

The established turn upper bound and the limit of V give

`u<=V(x)<3/2-log2<13/16`.

For the last rational inequality, the first two positive atanh terms
give `log2>56/81>11/16`. As `u>g(beta/x)`, and g increases above one,

\[
\boxed{1\le\beta/x<3.}                              \tag{5}
\]

## 3. The central residual derivative

Let `rho=a^2/(a^2+4)` denote the fixed physical scale, and set

\[
S=1+x,\quad
\mathcal D=(\alpha+\beta)^2+S^2-(\beta+x)^2,
\quad F_0=E-\rho\mathcal D u.
\]

Here E is the central stationarity expression in the [scale note](MIXED_GLOBAL_SHORT_BRIDGE_SCALE.md), with
the opposite actual norm v and y held fixed. Its beta derivative is
`E_beta=S u_beta`. Hence

\[
(F_0)_\beta=S u_\beta-\rho(\mathcal D u)_\beta.       \tag{6}
\]

The actual central factor and `x<=y` give `0<rho<1/S^2`. The expression
in (6) is affine in rho. At rho=0 it is strictly negative. At rho=1/S^2
its negative is W/S^2, where

\[
W=\frac{(S^3-\mathcal D)\eta}{\beta-1}
      +u\mathcal D_\beta,
\quad
\mathcal D_\beta=2C+2(\alpha+\beta)(\eta/\xi)M,
\quad C=\alpha^2/\beta+2\alpha-x.
\]

Notice `Dcal<=S^2<S^3`. Put
`B0=C+(2/7)(alpha+beta)M`. If `B0>=0`, equations (3)--(4) give W>0
directly. If `B0<0`, equations (3)--(5) give the strict lower bound

\[
W>
\mathscr R:=\frac{(S^3-\mathcal D)\eta_0}{\beta-1}
                 +\frac{13}{8}B_0.                  \tag{7}
\]

The following exact polynomial certificate proves `Rscript>0` on the
whole stated bridge domain. Consequently (6) is strictly negative at
both ends of the scale interval, and therefore throughout it:

\[
\boxed{(F_0)_\beta<0\quad(0\le\rho\le1/S^2).}       \tag{8}
\]

## 4. Complete polynomial certificate

In terms of alpha,beta,x, the lower bound in (3) is

\[
\eta_0=
\frac{(x-\alpha)\beta
 [6\beta^2+\alpha\beta-5\alpha x-x^2-\beta x]}
 {6(\alpha+\beta)(\beta+x)^2(\alpha+x+2\beta)}.
\]

Let

\[
\mathscr P=
168\beta(\alpha+\beta)(\beta-1)(\beta+x)^2
                         (\alpha+2\beta+x)\mathscr R.
\]

Every factor cleared here is positive. Substitute

\[
r=\beta/x-1\in[0,2],\quad z=\alpha-1-r\ge0,
\quad j=x-\alpha>0;
\quad \alpha=1+r+z,\ x=1+r+z+j,\ \beta=(1+r)x.
\]

The exact identity is

\[
\mathscr P=\mathscr P_+
 +j^6(112j^2-172j+2496)
 +r^5j^6(7069-1500r-702r^2)
\]
\[
\hspace{14mm}
 +r^5zj^6(2730-702r)
 +r^3j^7(3245+937r-477r^2-234r^3).                    \tag{9}
\]

The complete table below defines P-plus. Each row `(z power,j power)`
lists its coefficients in ascending powers of r; omitted rows and omitted
trailing coefficients are zero. All 362 nonzero coefficients are positive.

The four additional terms in (9) are nonnegative, with the first strictly
positive since j>0. The quadratic `112j^2-172j+2496` has discriminant
`-1088624<0` and positive leading coefficient. On `0<=r<=2`, the next
two brackets are at least 1261 and 1326. The last bracket is concave
because its second derivative is `-954-1404r<0`; its endpoint values
are 3245 and 1339, so it is positive throughout. This proves (7).

| z power | j power | Coefficients in ascending powers of r |
|---:|---:|---|
| 7 | 1 | 0, 336, 840, 672, 168 |
| 7 | 0 | 22464, 78624, 112320, 84240, 35100, 7722, 702 |
| 6 | 2 | 112, 2548, 5936, 4676, 1176 |
| 6 | 1 | 107952, 390528, 578688, 450600, 194235, 43725, 3978 |
| 6 | 0 | 134784, 651456, 1280448, 1347840, 828360, 299052, 58968, 4914 |
| 5 | 3 | 672, 8232, 17976, 13944, 3528 |
| 5 | 2 | 210248, 793460, 1230058, 1000543, 446889, 102318, 9126 |
| 5 | 1 | 567216, 2773248, 5563800, 6004824, 3789795, 1403472, 282690, 23868 |
| 5 | 0 | 336960, 2122848, 5458752, 7632144, 6423300, 3359070, 1071954, 191646, 14742 |
| 4 | 4 | 1680, 14700, 30240, 23100, 5880 |
| 4 | 3 | 209912, 840208, 1381602, 1183994, 548143, 125985, 10530 |
| 4 | 2 | 944528, 4689768, 9638240, 10697400, 6944201, 2635545, 539580, 45630 |
| 4 | 1 | 1216800, 7617600, 19734480, 28012560, 24037650, 12842010, 4187025, 763455, 59670 |
| 4 | 0 | 449280, 3594240, 11681280, 20835360, 22829040, 16089840, 7342920, 2102490, 343980, 24570 |
| 3 | 5 | 2240, 15680, 30520, 22960, 5880 |
| 3 | 4 | 110636, 486316, 869307, 794369, 379882, 84990, 5850 |
| 3 | 3 | 779712, 3955204, 8369868, 9588769, 6408462, 2483392, 510780, 42120 |
| 3 | 2 | 1677872, 10455304, 27318092, 39406170, 34497274, 18822434, 6258070, 1158660, 91260 |
| 3 | 1 | 1354080, 10536720, 34039320, 61043760, 67697550, 48484140, 22532250, 6574560, 1095540, 79560 |
| 3 | 0 | 336960, 3425760, 13815360, 30579120, 42084900, 38108070, 23176530, 9399780, 2442960, 368550, 24570 |
| 2 | 6 | 1680, 9996, 18480, 13692, 3528 |
| 2 | 5 | 27380, 145484, 297289, 294613, 143253, 28527, 702 |
| 2 | 4 | 323280, 1692648, 3718020, 4415973, 3033399, 1185846, 237240, 17550 |
| 2 | 3 | 1086384, 6747036, 17790516, 26083875, 23280495, 12941892, 4363938, 811710, 63180 |
| 2 | 2 | 1467248, 11123684, 35706184, 64342008, 72181406, 52491982, 24809746, 7359690, 1244040, 91260 |
| 2 | 1 | 814320, 7786176, 30686400, 67554312, 93368223, 85404405, 52661166, 21701280, 5736837, 880443, 59670 |
| 2 | 0 | 134784, 1819584, 9097920, 24598080, 41488200, 46681596, 36130536, 19364670, 7076160, 1684800, 235872, 14742 |
| 1 | 7 | 672, 3528, 6216, 4536, 1176 |
| 1 | 6 | 1724, 18352, 48663, 53300, 24697 |
| 1 | 5 | 58160, 321252, 743084, 918159, 639401, 240648, 40818, 1404 |
| 1 | 4 | 321372, 1988052, 5281131, 7848489, 7107363, 3989841, 1341996, 243030, 17550 |
| 1 | 3 | 669920, 4948132, 15748308, 28445359, 32197892, 23703951, 11346614, 3400552, 577380, 42120 |
| 1 | 2 | 628424, 5688516, 21896378, 47860319, 66319517, 61186664, 38192370, 15961895, 4280961, 665886, 45630 |
| 1 | 1 | 245232, 2907168, 13840008, 36702360, 61607175, 69564252, 54314436, 29466168, 10922595, 2641440, 375810, 23868 |
| 1 | 0 | 22464, 482976, 3077568, 10136880, 20645820, 28208466, 26912574, 18224622, 8743410, 2909790, 639522, 83538, 4914 |
| 0 | 8 | 0, 532, 896, 644, 168 |
| 0 | 7 | 0, 532, 2769 |
| 0 | 6 | 0, 15832, 40044, 50539, 31698 |
| 0 | 5 | 33020, 201568, 532979, 790368, 709792, 387443, 121057, 18171, 702 |
| 0 | 4 | 107048, 767020, 2403630, 4317853, 4889513, 3607857, 1726421, 512932, 84900, 5850 |
| 0 | 3 | 154008, 1324324, 4964034, 10726987, 14838280, 13749574, 8649385, 3647166, 985807, 153993, 10530 |
| 0 | 2 | 104656, 1121280, 5094168, 13222948, 22031865, 24906273, 19575662, 10727772, 4024989, 986009, 142068, 9126 |
| 0 | 1 | 27456, 423168, 2444400, 7734144, 15494580, 21081228, 20174583, 13768293, 6677964, 2251590, 502047, 66585, 3978 |
| 0 | 0 | 0, 44928, 404352, 1651104, 4043520, 6612840, 7606872, 6310278, 3803436, 1653210, 505440, 103194, 12636, 702 |

## 5. Consequence and remaining scope

Integrate (8) from beta=x, alpha=1 to the actual bridge. At the starting
point, the left norm is V(x); raising the fixed right norm to V(y) only
increases the central residual. The equal-centre proof therefore gives

\[
F_0\le F_{0,\rm equal}
 <-\frac{(1+y)[U(1/(1+y))-V(y)]}{2}<0.                \tag{10}
\]

This holds for both signs of Dcal, and is strict at the equal-centre
starting face as well. In particular F=lambda F0<0. For Dcal<=0,
the transported norm satisfies `w<=lambda^2v<=v`.

Equation (10) is a necessary-data scalar comparison, not a claim that
the auxiliary path preserves a closed trajectory or every Hamiltonian
gap. It establishes the central bound needed for the outer comparison.
The outer root residual and its boundary signs remain to be proved
before a general two-short-bridge minimum principle can be asserted.

## Independent audit and supplementary checks

The [joint independent internal hand audit](MIXED_GLOBAL_SHORT_BRIDGE_AUDIT.md)
reviews the same-lift, comparison-domain and coefficient-table interfaces.
The corresponding exact checker is
[`mixed_global_short_bridge_central_certificate.py`](../explorations/mixed_global_short_bridge_central_certificate.py).
These are hand and algebraic results, not Lean kernel validation.
