# The actual smaller-short ratio is greater than two

Date: 2026-11-08 UTC. **Result: S1.** The central and outer scalar
faces and their actual-period assembly have separate accepted
reviews. See the
[lower-ratio interface audit](MIXED_SMALLER_SHORT_LOWER_RATIO_HAND_AUDIT.md).

## Theorem

Every actual eligible competitive normal smaller-short mixed bridge
retained by the common-covector
[six-variable reduction](MIXED_SMALLER_SHORT_SIX_VARIABLE_REDUCTION.md)
satisfies

\[
\boxed{x>2.}
\]

The statement concerns the globally minimal active reverse centre
of an actual mixed minimizing period, with its chosen smaller
adjacent turn on a short forward run. It retains positive durations,
the genuine first switches, the original common normal covector,
the complete twisted endpoints and the whole-period competitive
budget. No bound on the number of pieces is used in the scalar
argument.

## 1. Original data and the original competitive cap

Suppose instead that \(1<x\le2\). The actual exact secants give

\[
1\le\alpha<x\le\beta\le\alpha x,
\qquad
\operatorname{Sec}(1,x,\beta)
 =\operatorname{Sec}(\alpha,\beta,x)=u.
\tag{1}
\]

The [strong lower order](MIXED_SMALLER_SHORT_STRONG_ORDER.md) and
[global upper order](MIXED_SMALLER_SHORT_GLOBAL_UPPER_ORDER.md) give

\[
x+\frac{8x(\alpha-1)}{9x+8}\le\beta
\le x+\frac{x(7x+1)(\alpha-1)}{4x^2+11x+1}.
\tag{2}
\]

The [positive-diagonal theorem](MIXED_SMALLER_SHORT_POSITIVE_DIAGONAL_PAIRING.md)
applies on this interval and gives \(D>0\), \(E_L>0\).
The actual outer first root has \(2<\tau<T\) and
\(R_\tau=0\). Its outer scale satisfies \(q<1/7\), by the
[reverse-centre scope theorem](HAND_REVERSE_CENTRE_SCALE_SCOPE_AUDIT.md).
The [whole-period refinement](HAND_PROOF_REFINEMENTS.md) gives

\[
\Gamma_{\rm actual}<g:=\frac{9193}{50000}.
\tag{3}
\]

Only this original common covector is subject to (3).

## 2. A lower bound on that same Casimir reaches two scalar faces

Put \(c=7/96\). The
[sharp corrected-cap theorem](MIXED_SMALLER_SHORT_SHARP_LOW_RATIO_CORRECTED_CAP.md)
first compares the actual outer root with the upper envelope at
unchanged shape and scale. Its exact derivative-ratio estimate gives

\[
\Gamma_{\rm actual}\ge\Gamma_*-cR_\tau^*.
\tag{4}
\]

Its fixed-normalized-duration and tau-two comparisons then decrease
the right side to one of exactly the two faces

\[
q=q_c\le\frac17,
\qquad
q=\frac17\le q_c,
\qquad
q_c=\frac{\alpha^2}{x(x+2)+\alpha^2}.
\tag{5}
\]

The shape and incoming norm \(u\) stay fixed throughout. The final
duration parameter satisfies \(2\le\widehat\tau\le T\).
Indeed \(r_A=\alpha/(\alpha+\beta)\ge1/(1+x)\ge1/3\),
and either final scale in (5) is at most \(1/7\); hence
\(T=r_A/q\ge7/3>2\). If the fixed-normalized-duration segment
first reaches \(\tau=2\), the separately proved tau-two comparison
continues it to (5). There is no omitted intermediate duration face.

This is a comparison of explicit scalar lower bounds in (4). It
does not move the uncorrected upper cap (3), an outgoing norm floor,
a physical completion cost, or a realized root to a changed scale.

## 3. Both faces contradict the cap

At a fixed terminal shape and scale write

\[
R_2=2w-\frac12+\frac{u-1}{r_A}+r_A-q-E_L+\log(2/T).
\]

Since \(\partial_\tau R_\tau=w-U(1/\tau)\le w-3/4\),

\[
R_{\widehat\tau}
\le\max\{R_2,\ R_2+(T-2)(w-3/4)\}.
\tag{6}
\]

This holds for either sign of the scalar \(w-3/4\). No outgoing
floor has to survive the comparisons. Both terminal theorems use
the valid rational upper bound

\[
\log y\le2z+\frac23z^3,
\qquad z=\frac{y-1}{y+1},\qquad0<y\le1,
\tag{7}
\]

at \(y=2/T<1\), and prove that the two corrected excesses
associated with (6) are strictly positive.

On the central face, \(q_c\le1/7\) is exactly
\(\alpha^2\le x(x+2)/6\). It implies
\(x\ge\sqrt7-1>23/14\). The exact square identity

\[
a_U(x)^2-\frac{x(x+2)}6
 =\frac{(337x-676)^2}{2340^2},
\qquad a_U(x)=\frac{1013x+676}{2340},
\tag{8}
\]

gives \(\alpha\le a_U(x)<6/5\). The
[central low-ratio sign theorem](MIXED_SMALLER_SHORT_LOW_RATIO_CENTRAL_HAND_SIGN.md)
therefore applies, with the original norm and order strip (2).
It proves both strict signs in (6).

On the outer face, \(1/7\le q_c\) is exactly
\(\alpha^2\ge x(x+2)/6\). The
[outer low-ratio sign theorem](MIXED_SMALLER_SHORT_LOW_RATIO_OUTER_HAND_SIGN.md)
exhausts this face by its three alternatives:
\(x\le3/2\); \(x\ge3/2,\alpha\ge6/5\); and
\(x\ge3/2,\alpha\le6/5\). Its two rational incoming norm
endpoints enclose the unchanged actual \(u\). Concavity in that
norm extends each endpoint sign to the original value. Thus both
strict signs in (6) hold on this face as well.

In either case, (6)--(7) and the terminal inequalities give

\[
\Gamma_*-cR_{\widehat\tau}^*>g.
\tag{9}
\]

Combining (4), its decreasing scale continuation and (9) yields
\(\Gamma_{\rm actual}>g\), contradicting (3).
The equality \(q_c=1/7\), the two duration endpoints, the shape
partition endpoints and \(x=2\) are all included with strict signs.
Consequently \(x\le2\) is impossible, proving the theorem.

## Scope

This lower-ratio theorem does not assume the sharp upper-ratio result,
the small displacement, a small-shape Casimir floor or the physical
cost exclusion. It uses only the broad actual short-shape facts and
the original competitive cap. Its conclusion therefore supplies the
lower endpoint needed by those later theorems without circularity.
