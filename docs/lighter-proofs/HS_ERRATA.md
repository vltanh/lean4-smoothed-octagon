# Three explicit corrections to the smaller-short notes

These corrections repair the three hypothesis/sign gaps identified in the
request for lighter polynomial proofs. They do not replace the large S1,
S2, S3, S4 or S6 polynomial signs, and they do not certify the generated
S1 coefficient tables as hand-proof premises.

## 1. The root-to-shear divisions have positive denominators

In [the root-to-shear note, equations (29)--(31)](../../archive/notes/MIXED_SMALLER_SHORT_SMALL_SHAPE_ROOT_SHEAR.md),
the actual shape satisfies

\[
2\le x\le13/6,\quad 0\le d\le1/19,\quad
\alpha=1+\eta d,\quad 13/5\le\eta\le3,\quad
\beta=x(1+d).
\]

Consequently

\[
1\le\alpha\le22/19,\qquad2\le\beta\le130/57,
\qquad \beta x-\alpha\ge54/19.
\]

Keep the quantities in their factored forms:

\[
\begin{aligned}
m={}&8\alpha x^2+8\alpha x-3\alpha
           +3\beta x^2-8\beta x-8\beta,\\
W={}&(\beta x-\alpha)m,\\
Q={}&2\beta x-\alpha\beta-x,\\
K_x={}&x^2+x+1,\qquad K_A=\alpha^2+\alpha\beta+\beta^2,\\
V={}&\alpha^2W+3K_xK_AQ(x-1).
\end{aligned}
\]

The following two three-term quadratics have obvious factorizations:

\[
8x^2+8x-48=8(x-2)(x+3)\ge0,
\qquad
3x^2-8x+4=(x-2)(3x-2)\ge0.
\]

They give

\[
m\ge45\alpha-12\beta
 \ge45-12(130/57)=335/19>0,
\qquad W>0.
\]

Also

\[
Q-x(2x-\alpha-1)
=2\beta x-\alpha\beta-2x^2+\alpha x
=(\beta-x)(2x-\alpha)\ge0,
\]

so \(Q\ge2(4-22/19-1)=70/19>0\). All factors in the second
term defining \(V\) are positive; hence \(V>0\).

The transport identity for \(F\) needs only the following collection,
after cancelling the common factor \(\beta x-\alpha\):

\[
\begin{aligned}
&3\{(x+2)\alpha+(2x+1)\beta\}(x-1)
 +13(\alpha x-\beta)(x+1)\\
&\quad=16\alpha x^2+16\alpha x-6\alpha
       +6\beta x^2-16\beta x-16\beta=2m.
\end{aligned}
\]

Thus, with \(S=x+1\), the original identities now have proved signs:

\[
F=\frac{2W}{3S^3K_A}>0,\qquad
G=\frac{2V}{3\alpha^2S^3K_A}>0.
\]

In particular the equivalence

\[
\frac{29\alpha^2}{30[x(x+2)+\alpha^2]}
  >\frac{\alpha^2W}{V}
\quad\Longleftrightarrow\quad
29V-30W[x(x+2)+\alpha^2]>0
\]

uses only multiplication by quantities already proved positive. This
correction supplies the missing signs; it leaves the original proof of
the last displayed inequality as a separate dependency.

## 2. The actual outer scale satisfies the angle barrier's hypothesis

The [cost-exclusion note, Section 2](../../archive/notes/MIXED_SMALLER_SHORT_SMALL_SHAPE_COST_EXCLUSION.md)
uses the angle barrier only for the initial derivative sign. Its needed
outer cap comes from the
[reverse-centre scope theorem](../../archive/notes/HAND_REVERSE_CENTRE_SCALE_SCOPE_AUDIT.md),
which proves \(\rho_A<1/7\) at **every** reverse-run centre of the same
competitive finite normal geometric period, including the outer centre
of this bridge. No global-minimum hypothesis at the outer centre is
needed.

For the strict cost conclusion, assume \(C_{\rm period}\le A_{\rm oct}\);
otherwise the conclusion already holds. This supplies competitiveness
for that scope theorem. If \(a_0\) is the central margin, the original
outer margin is \(\alpha a_0\), so

\[
\rho=\frac{a_0^2}{a_0^2+4},\qquad
q=\rho_A=\frac{\alpha^2\rho}{1+(\alpha^2-1)\rho}<\frac17.
\]

The scale map has the four-term polynomial form

\[
q+\alpha^2q\rho-q\rho-\alpha^2\rho=0.
\]

It implies

\[
\frac{\rho}{1-\rho}
=\frac{q}{\alpha^2(1-q)}<\frac1{6\alpha^2},
\]

since \(1-q-6q=1-7q>0\). Together with the original central-duration
cap and the original strong short order, this supplies the hypotheses
needed for the initial use of the angle barrier.

The continuation to central scale may pass \(q=1/7\). Its justification
remains the critical-angle argument already given in the cost note;
this correction does not assign the actual outer cap to a scalar
comparison point.

## 3. The tau-two theorem explicitly retains its incoming floor

The [tau-two scale note](../../archive/notes/MIXED_SMALLER_SHORT_ROOT_FLOOR_TAU_TWO_SCALE.md)
now states the additional scalar hypothesis

\[
u\ge\frac34+\frac{(x-1)^2}{28(x+1)^2}.
\]

Writing \(S=x+1\), its fully expanded polynomial form is

\[
28S^2u-22S^2+4S-4\ge0.
\]

This is stronger than the rectangular bound \(3/4\le u\le13/16\).
For example, \(S=9.91,\ u=0.7502\) violates it, because \(S>8\) makes
the displayed floor greater than \(77/100\). The completed-square
lower bound \(F\) in the old proof need not be positive on the larger
rectangle. The corrected statement makes no claim on that rectangle
without the floor.

Here is precisely where the hypothesis enters. For

\[
H=S(1-u)-S^{-1},
\]

the four-term identity

\[
3S^2+2S-16-14SH
=\frac12(28S^2u-22S^2+4S-4)
\]

gives

\[
H\le\frac{3S}{14}+\frac17-\frac8{7S}\le\frac{76}{35}
\quad(S\le10).
\]

The last function increases, since its derivative is

\[
\frac{3S^2+16}{14S^2}>0.
\]

If \(H\ge2\), the weaker estimate \(H\le S/4-1/S\) forces \(S>8\),
and the incoming floor then gives

\[
u>\frac34+\frac9{448}
=\frac{77}{100}+\frac1{11200}.
\]

These are exactly the bounds used in Sections 4--5 of the tau-two
proof. The rest of that proof retains its original conclusion

\[
G_2'(q)>0\qquad(0<q\le1/7).
\]

The caller in
[the large-ratio exclusion, Section 3](../../archive/notes/MIXED_SMALLER_SHORT_LARGE_RATIO_HAND_EXCLUSION.md)
keeps \(x,\beta\) and \(u=\operatorname{Sec}(1,x,\beta)\) fixed during
both scale comparisons. The
[uniform incoming-floor theorem](../../archive/notes/MIXED_SMALLER_SHORT_UNIFORM_INCOMING_FLOOR.md)
therefore supplies the new explicit hypothesis at every point used by
that caller. Its two endpoint alternatives and conclusion are unchanged.

## Algebra size of these corrections

The counts below are the nonzero monomials in the printed expanded
polynomial. Factored positive quantities \(W,V,K_x,K_A\) do not need to
be expanded to prove their signs. No new coefficient table, subdivision,
logarithm bound, arctangent bound or radical bound is used.

| Expanded polynomial | Monomials | Variables | Total degree | Largest absolute coefficient |
|---|---:|---:|---:|---:|
| \(8x^2+8x-48\) | 3 | 1 | 2 | 48 |
| \(3x^2-8x+4\) | 3 | 1 | 2 | 8 |
| \(2m\) | 6 | 3 | 3 | 16 |
| \(2\beta x-\alpha\beta-2x^2+\alpha x\) | 4 | 3 | 2 | 2 |
| \(q+\alpha^2q\rho-q\rho-\alpha^2\rho\) | 4 | 3 | 4 | 1 |
| \(28S^2u-22S^2+4S-4\) | 4 | 2 | 3 | 28 |
| \(3S^2+2S-16-14SH\) | 4 | 2 | 2 | 16 |
| \(3S^2+16\) | 2 | 1 | 2 | 16 |

The identities were checked by exact rational symbolic arithmetic as a
transcription check; the displayed factorizations and inequalities are
the proofs. No Lean compilation or CI was run.
