# Exact hand-proof gap in the smaller-short ratio contractions

Date: 2026-11-08 UTC. **Historical gap record: S2 is now closed; S1 remains open.**
The [accepted sharp upper-ratio theorem](MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_EXCLUSION.md)
and [review](MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_AUDIT.md) discharge both
S2 signs below with explicit hand proofs. The old coefficient-minimum
claims discussed here remain excluded as premises. This note
separates useful analytic reductions from the terminal coefficient
claims in the earlier unpushed leads. It does not alter the completed
computer-assisted theorem or relabel its certificates as hand proofs.

## 1. What has been reconstructed for S2

The [variable-floor reduction](MIXED_SMALLER_SHORT_VARIABLE_FLOOR_REDUCTION.md)
gives the following rigorous implication on the actual common-covector
shape with \(13/6\le x<12/5\): at least one of the two scale faces

\[
q=q_c:=\frac{\alpha^2}{x(x+2)+\alpha^2}\le1/7,
\qquad q=1/7\le q_c
\tag{1}
\]

has a strictly positive combined scalar. The original equal-secants
shape is held fixed. The scale continuation now has a small explicit
algebraic proof, documented in its [audit](MIXED_SMALLER_SHORT_VARIABLE_FLOOR_AUDIT.md).
No outgoing floor, upper Casimir cap or physical cost is assigned to
the comparison endpoint.

For a self-contained description of the remaining scalar, put

\[
S=1+x,\quad r_A=\frac\alpha{\alpha+\beta},\quad
D=\alpha^2+2\alpha\beta+1+2x-2\beta x,
\]
\[
a=\alpha^{-2},\quad\varepsilon=1-a,\quad\delta=D/\alpha^2,
\quad E_0=S(u-1)+S^{-1},
\]
\[
A_1=2\varepsilon+Sa+\delta E_0,
\]
\[
A_2=\varepsilon^2+\varepsilon Sa+S^2a^2
     +u\delta^2+\delta\varepsilon E_0-\delta(2S-1)a,
\qquad A_3=2u\delta+\varepsilon E_0-(2S-1)a.
\]

At either face in (1), take \(2q\le p\le r_A\), set
\(y=p/r_A\), \(z=(y-1)/(y+1)\), \(m=2-7y/4\), and define

\[
\begin{aligned}
\mathcal B(q,p;u)={}&E_0+\frac{u-1}{r_A}+r_A+1-pA_1
          +2z+\frac23z^3\\
 &+q(pA_2+p^{-1}-1-A_3)
   +m\left(\frac14-qA_1+q^2A_2\right).
\end{aligned}
\tag{2}
\]

The logarithm majorant is global for \(0<y\le1\), so (2) is an
upper bound for the necessary positive scalar. Its coefficient in
\(u\) is strictly positive by the variable-floor proof. Thus the
remaining task is a strict **negative** upper bound on (2) at both
faces using a proved incoming-norm ceiling. This is a concrete
finite analytic obligation, rather than a request for new geometric
reductions.

The actual shape lies in the proved order strip

\[
x+\frac{8x(\alpha-1)}{9x+8}\le\beta
\le x+\frac{x(7x+1)(\alpha-1)}{4x^2+11x+1}.
\tag{3}
\]

The following rational enlargements and ceilings are useful leads.

### Central face

On \(q=q_c\le1/7\),
\(\alpha^2\le x(x+2)/6\), hence
\(\alpha\le(5x+4)/12\), since the difference of the squared
bounds is \((x-4)^2/144\ge0\). A rational ceiling for the original
incoming norm on this enlarged strip is

\[
u_C=\frac34+
 \frac{680(x-1)^3+3S^2(\beta-x)}{9600S^2(\beta-1)}.
\tag{4}
\]

The derivation uses the
[Gauss incoming estimate](MIXED_SMALLER_SHORT_GAUSS_INCOMING_CEILING.md)
at \(\beta=x\), where

\[
V(x)-\frac34\le
\frac{(x-1)^2(71x^2+48x+1)}
 {96x(x+1)(13x^2+14x+3)}
<\frac{17(x-1)^2}{240S^2}.
\]

The latter sign, after clearing positive factors and putting
\(X=x-13/6\), is

\[
87X^3+\frac{893}{2}X^2+\frac{6799}{12}X+\frac{823}{72}>0.
\]

The upper endpoint in (3) and the alpha bound give
\((\beta-x)/x<3/25\): the cleared comparison is the concave
quadratic \(-731x^2+1671x+236>0\), with endpoint values
\(15295/36\) and \(896/25\). The positive incoming integral split
at \(x\) consequently satisfies

\[
u-\frac34\le
\frac{(x-1)[V(x)-3/4]+(\beta-x)^3/(48x^2)}{\beta-1}
\le u_C-\frac34,
\]

because the tail is at most
\(3(\beta-x)/10000\le(\beta-x)/3200\). This proves (4).

What remains is a readable proof of
\(\mathcal B(q_c,p;u_C)<0\) on this whole central domain.
The earlier draft specified a cleared polynomial, then a
power/Bernstein expansion with
\(48\cdot18\cdot10\cdot6=51840\) coefficients. It asserted
seven grouped lower bounds by an instruction to expand and check
all the coefficients. The coefficient-extraction identity specifies
the numbers, but supplies no short proof of their grouped signs.
That is the remaining gap in that proposed argument.

### Outer face

On \(q=1/7\le q_c\),
\(\alpha^2\ge x(x+2)/6\), hence
\(\alpha\ge(36x+25)/84\). The latter follows from

\[
84^2x(x+2)-6(36x+25)^2=-720x^2+3312x-3750>0,
\]

a concave quadratic with endpoint values \(46\), \(258/5\).
Use the proved rational incoming ceiling \(u_G\) from the
[Gauss theorem](MIXED_SMALLER_SHORT_GAUSS_INCOMING_CEILING.md).
The outstanding inequality is
\(\mathcal B(1/7,p;u_G)<0\) throughout this outer domain and
(3). The earlier draft specified a polynomial expansion with
\(53\cdot15\cdot13\cdot6=62010\) coefficients and asserted
eight grouped positive lower bounds. Here again an extraction rule
and a statement that the coefficients were all checked do not
provide the required readable sign argument.

The two inequalities above are not contradicted by the audit. They
remain plausible candidate statements requiring an analytic proof.
Their apparent truth and a computational verification are distinct
from supplying that proof.

## 2. The separate S1 gap

The proposed lower-ratio assembly would exclude \(1<x\le2\) by
comparing the original competitive cap
\(\Gamma_{\mathrm{actual}}<9193/50000\) with a corrected envelope
quantity

\[
\Gamma_*(q)-\frac7{96}R_\tau^*(q).
\tag{5}
\]

Its intended interface keeps the actual Casimir on the left while
moving only this combined scalar to the same two scale faces. This
scope distinction is appropriate. The unpushed proof of the sharper
\(7/96\) correction and its scale derivatives, however, still uses
coefficient-bound assertions, and the terminal signs for (5) use
sixteen multivariate coefficient-minimum cases. These have not been
replaced by analytic sign arguments.

Consequently no file headed “complete hand assembly” from those leads
should be promoted on the strength of its header or its former audit
label. S1 requires both the strengthened scalar comparison and the
uniform terminal corrected-cap signs with their original exact
hypotheses. The present variable-floor reduction is an S2 advance
and does not supply either S1 obligation.

## 3. Completion discipline

The completion plan's S1 box stays open until its stated
signs have short independently reviewable proofs. The eight quartics
in the new scale-continuation argument are fully displayed and have
individual elementary sign estimates; they do not justify replacing
the absent terminal proofs by tens of thousands of unexplained
coefficient signs. No numerical optimization, executable cover or
Lean/kernel check is a proof premise in the new reduction.
