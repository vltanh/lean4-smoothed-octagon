# Independent source audit of the common compact state domain

Date: 2026-11-07. Hand proof with an exact algebra companion. No Lean, Lake, typechecking, or CI. Primary source: Hales–Vajjha, *Packings of Smoothed Polygons*, arXiv:2405.04331v1, [Chapter 5](https://arxiv.org/html/2405.04331v1#Ch5), with [Section 4.6](https://arxiv.org/html/2405.04331v1#Ch4.S6) and [Section 2.4](https://arxiv.org/html/2405.04331v1#Ch2.S4).

**Scope:** this note audits the common compact-state input and its all-control margin bound. The two nonshort M2 covers and final G4/G5 gates remain open.

## 1. Source scope and normalization

Theorem 5.0.2 explicitly quantifies over a balanced disk and **any point of its corresponding state trajectory**: leaving the single region of Definition 5.0.1 forces area above the octagon. Thus its contrapositive gives the same compact strict-star region for every competitive geometric minimizing realization. No finite-switch or normality hypothesis enters this claim. The source's Section 2.4 says every normalized worst disk is balanced; the repository's realization retains precisely such a balanced disk and its own boundary trajectory.

The physical-margin consequence is correct, for all three controls and at every time. Put q=1/sqrt(3), define

    rho0=(q+x)/y,
    rho1=(q-x)/y,
    rho2=sqrt(3)*(x^2+y^2-q^2)/(2*y).

In the repository label convention, p0=2rho2, p1=2rho1, p2=2rho0. In particular p1=sqrt(3) gamma1=2(q-x)/y. The region excludes y>15(q-x), giving p1>=2/15. It is cyclically invariant by construction (all three rotated boundary exclusions are removed), so the same lower bound holds for p0 and p2. This is a bound on inactive as well as active margins; no selected-global-active-minimum assumption is used.

## 2. Repair of the source sector reduction

The v1 HTML's displayed fundamental domain in Section 4.6 uses <=4/3, while the proof of Theorem 5.0.2 displays =4/3. Neither display supports the subsequent sentence about the larger region x>=0,y>=1. These are actual printed defects, not a reason to weaken the theorem's quantifier.

A correct sufficient sector is

    x>=0, (x-q)^2+y^2>=4/3.

To obtain it, choose a cyclic image of z with maximum imaginary part among z,Rz,R^2z, then reflect if necessary to make x>=0. Maximal height gives both

    (x-q)^2+y^2>=4/3, (x+q)^2+y^2>=4/3,

from Im(Az)=y/|cz+d|^2. Since 0<=x<q, the first gives y>=1. It also gives rho2>=rho0>=rho1. Consequently, if any cyclic boundary exclusion holds, rho1<1/15 already holds in this representative. The two finite-cusp horoballs have top height 8/27<1, so they do not meet this representative sector. If a horoball exclusion holds, it is y>9/2.

This proves the needed reduction without either erroneous printed fundamental-domain display. The source's statement that only one half-plane meets the whole larger set x>=0,y>=1 is also stronger than needed; for very large y both side margins can be small. The preceding ordering argument gives the needed implication directly.

## 3. Exact separation from the octagon

Use only the geometric area lower bound of Theorem 5.0.6. In density units, with a=rho0, b=rho1, c=rho2 and ab+bc+ca=1, it says

    delta >= 3/4 + sum_i max(0, area_i/sqrt(3)),
    area0/sqrt(3) = (ac-2b sqrt(ac))/4,
    area2/sqrt(3) = (bc-2a sqrt(bc))/4.

At any time of an actual balanced realization, apply the area bound to the image of the disk under the inverse contact frame. This determinant-one map sends that time's contact multi-point to the sixth roots of unity, preserving area, density and the critical-hexagon property. Thus the estimate applies to every point of the trajectory, not only its initial state. The subsequent cyclic rotation or reflection also preserves density.

The following derivation does not use the source's derivative or decimal checks in Lemma 5.0.7.

### Horoball: y>=9/2

Let s=a+b=2q/y and h=ab. Then 0<h<=s^2/4<=4/243. Dropping positive parts only weakens the lower bound, so

    delta >= 3/4 + [1-h-2 sqrt(h(1-h)(1+2sqrt(h)/s))]/4.

For fixed s and h<=s^2/4<1/2, h(1-h) and 1+2sqrt(h)/s increase with h; the displayed bracket therefore decreases. At h=s^2/4 it becomes 1-h-2sqrt(2h(1-h)), also decreasing for h<1/2. Hence

    delta >= (242-sqrt(478))/243 > 220/243 > 113/125.

The strict bound uses only 478<22^2 and exact rational comparison.

### Boundary neighborhood: 1<=y<=9/2, b<=1/15

For fixed s=2q/y, let

    P(b)=ac=(1-b(s-b))*(s-b)/s.

Its derivative is -s-1/s+4b-3b^2/s <= -2+4/15<0. The legitimate extension to b=1/15 has s>1/15, so P(b)>=P(1/15). With t=sqrt(3)y,

    P(1/15)=227/225 - 2/(15t) - 113t/3375.

This function is concave. On t in [sqrt(3),9sqrt(3)/2], the smaller endpoint value is

    227/225 - 3251sqrt(3)/20250 > 73/100,

using sqrt(3)<26/15. Thus ac>73/100>b^2. The function P-2b sqrt(P) increases with P in this range and decreases with b, so, using sqrt(73/100)<171/200,

    delta > 3/4 + [(73/100)-(2/15)*(171/200)]/4 = 113/125.

The positive-part condition causes no issue because the displayed area0 contribution is positive.

### Octagon separation

The known candidate density is

    delta_oct=(8-4sqrt(2)-log(2))/(2sqrt(2)-1).

Use sqrt(2)>140/99 and

    log(2)>2*(1/3+1/81+1/1215)=842/1215>693/1000.

Its numerator is positive. Substitution with the correct monotonic directions gives delta_oct<903/1000<113/125. Every excluded neighborhood is therefore separated strictly from the octagon by exact elementary inequalities.

## 4. One compact subset of the strict-star domain

The three boundary exclusions are exactly the three conditions `rho_i<1/15`, because cyclic rotation permutes the rho coordinates. Their complement has `rho_i>=1/15` for every i. The identity `rho0*rho1+rho1*rho2+rho2*rho0=1` then gives `rho_i<=15/2`. Consequently

    y=2q/(rho0+rho1)>=2q/15>0,
    q-x>=y/15, q+x>=y/15,
    x^2+y^2-q^2>=2y/(15sqrt(3)).

Together with `y<=9/2`, these inequalities keep the region bounded and a positive distance from each boundary component of the open star domain. All its defining exclusions have closed complements in this rectangle, so the full region is compact. This argument does not replace the sharper lower-height estimate used for the matrix norm in [GLOBAL_MINIMIZER_COMPACTNESS](GLOBAL_MINIMIZER_COMPACTNESS.md).

Combining the area separation with the same normalized disk at every time proves the contrapositive of the source theorem: every balanced realization with cost at most the octagon remains in this one compact region for its entire trajectory. The dictionary in Section 1 gives `gamma_i>=2/(15sqrt(3))` and `p_i>=2/15` for all three controls. In particular the inactive-margin constraints in [MIXED_NONSHORT_BLOWUP_REDUCTION](MIXED_NONSHORT_BLOWUP_REDUCTION.md) have the same scope as the active-margin bound.

## 5. Remaining external content and validation

The elementary repair above still uses the classical geometric balanced-disk/critical-hexagon facts and Theorem 5.0.6's geometric area bound. Its proof was read: it constructs points in the appropriate corner triangles from minimality of the circumscribed hexagon and takes their convex hull. It does not use later bang-bang, chattering, singular-avoidance, or numerical basin results.

Theorem 2.1.3 confirms greatest packing density equals greatest lattice-packing density for the centrally symmetric convex-disk class. Lemma 2.2.5 supplies existence and absence of corners; Lemmas 2.4.2–2.4.3 supply regular C1 parametrizations and Lipschitz tangents; Definition 2.4.7 and the immediately following discussion include every normalized minimizer in the balanced class. These are the correct source-level geometric premises for the repository's route.

Run the supplementary exact certificate from the repository root:

```sh
python explorations/compact_domain_source_certificate.py
```

All **24** named algebraic/rational checks passed in the reviewed run. They check the rho identity, physical-margin dictionary, sector-order identity, boundary-product formula and concavity, exact endpoint comparisons, and the octagon separation. The conceptual inequalities and maximum-height argument are written above; the script does not prove the geometric area theorem or replace those hand arguments. It uses Python exact rational arithmetic and SymPy, with no numerical sampling, interval cover, Lean compilation, Lake, typechecking or CI.

The geometric area lower bound in Theorem 5.0.6 remains an explicit external premise. The finite bang-bang theorem and numerical escape/basin results are not used. This source-input audit does not close either pending nonshort branch or the final global cost/equality gates.
