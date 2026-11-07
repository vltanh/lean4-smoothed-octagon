# The stationary L1 example has a cheaper nonlocal six-piece replacement

Date: 2026-11-06. **This is a single explicit replacement, not a proof of
universal L1.** It complements [LOCAL_FORWARD_SIX.md](LOCAL_FORWARD_SIX.md):
that note proves a strict same-word local minimum. The present note proves
that the same input nevertheless has an actual cheaper `012021`
replacement with exactly the same initial and final frame and state.

The replacement is separated from the same-word local minimum. An exact
rational contraction argument turns the exploratory approximation into
an existence proof. No numerical optimizer residual is used as equality.
The input, initial state, endpoint chart, and cost normalization are those
of the preceding note.

## 1. Rational data for the replacement

Keep the original raw initial margins
\(P^{(0)}=(1,1,4761/3950)\), with normalization
\(p=\sigma P\), \(\sigma^2=1975/1684\), fixed.
Let \(E_*\) be the exact five-coordinate endpoint of the old word
`012012` with factors \((11/10,11/10,121/100,121/100,11/10,121/100)\).
For the new word `012021`, write

\[
E(y)=\bigl(F_{11},F_{12},F_{21},P^{(6)}_0,P^{(6)}_1\bigr),
\qquad F=\prod T_{i_k}(q_k),
\]

where \(y=(q_1,\ldots,q_5)\) and \(q_6=109/100\) is fixed.
Let \(f(y)=E(y)-E_*\). All entries of \(f\) are explicit rational
functions obtained by the two-by-two tangent products and the margin
recurrence in the preceding note.

Use the following rational center. Every terminating decimal below is
an **exact rational number**, not an interval or a claimed exact root:

\[
\begin{aligned}
c_1&=1.182504115604994555893003849647,\\
c_2&=1.121181801593551227623891266831,\\
c_3&=1.322925994119170300909296093597,\\
c_4&=1.129614983346815860414127778040,\\
c_5&=1.125598579575947873122187353667.
\end{aligned}                                                    \tag{1}
\]

Take the following exact rational matrix, again interpreting its decimals
literally:

\[
B=\begin{pmatrix}
20.238092&15.378147&-6.613901&1.537414&-4.365336\\
-4.754669&-3.229164&1.533209&-0.374696&1.063914\\
73.193410&51.482313&-28.689302&1.567271&-17.523544\\
-26.513687&-19.260435&9.169587&-1.205849&6.505239\\
-66.589556&-46.277963&26.327041&-0.695457&16.168477
\end{pmatrix}.                                                  \tag{2}
\]

The maximum-row-sum matrix norm and maximum-coordinate vector norm are
used throughout. Direct rational arithmetic gives

\[
\begin{array}{c|c}
\text{Quantity}&\text{Exact certified bound}\\\hline
\|B\|_\infty&<200\\
\|I-BDE(c)\|_\infty&<10^{-5}\\
\|f(c)\|_\infty&<10^{-28}\\
\|Bf(c)\|_\infty&<10^{-25}\\
\min_{k,j}P^{(k)}_j(c)&>7/10
\end{array}                                                     \tag{3}
\]

These are inequalities between explicitly specified rational numbers.
For checking derivatives in (3), the active-coordinate recurrence
\((A,B,C)\mapsto(A,(A+B)q-A,(A+C)/q-A)\) has derivative

\[
\dot B_{\rm end}=(\dot A+\dot B)q+(A+B)\dot q-\dot A,
\quad
\dot C_{\rm end}=(\dot A+\dot C)/q-(A+C)\dot q/q^2-\dot A.
                                                               \tag{4}
\]

Apply (4) to one coordinate direction at a time, and differentiate the
six tangent matrices by the ordinary product rule. This specifies the
finite calculation of every entry in (3).

## 2. Uniform analytic bounds on the contraction ball

Let \(\rho=10^{-15}\) and
\(\mathcal B=\{y:\|y-c\|_\infty\le\rho\}\). Every factor on this ball
lies in \([1,2]\), in fact strictly above one.

For clarity, the bounds used below are deliberately coarse and are
proved directly rather than inferred from a numerical interval sample.
On \([1,2]\), the linear margin-update matrix and its first and second
factor derivatives have row-sum norms at most \(3,2,4\), respectively.
The tangent matrices and their derivatives have row-sum norms at most
\(4,3,4\), respectively. Also \(\|P^{(0)}\|_\infty<2\).

Consequently, for any of the five varying factors, an end-state first
partial is bounded by \(2\cdot3^5\cdot2=972\); a second partial is bounded
by \(1944\) when the indices coincide, and by \(648\) otherwise.
Every tangent-product second partial is bounded by \(4096\): the bounds
are \(4^5\cdot4\) for repeated indices and \(4^4\cdot3^2\) for distinct
indices. These estimates also cover earlier switching states.
The mean-value theorem thus gives

\[
\|DE(y)-DE(c)\|_\infty\le 25\cdot4096\rho=102400\rho
\quad(y\in\mathcal B),                                    \tag{5}
\]

and

\[
\|P^{(k)}(y)-P^{(k)}(c)\|_\infty\le 5\cdot972\rho.
                                                               \tag{6}
\]

Define \(\Phi(y)=y-Bf(y)\). Equations (3) and (5) yield

\[
\|D\Phi(y)\|_\infty
<10^{-5}+200\cdot102400\cdot10^{-15}<\frac12.
\]

Also \(\|\Phi(c)-c\|_\infty<10^{-25}<\rho/2\). Hence \(\Phi\) maps
\(\mathcal B\) into itself and contracts distances by a factor less than
\(1/2\). Successive iteration from \(c\) is a Cauchy sequence in the
closed ball, and its limit \(y_*\) is a fixed point.

The inequality \(\|I-BDE(c)\|<1\) implies that \(BDE(c)\), and therefore
\(B\), is invertible, by the convergent geometric series for its inverse.
Thus \(\Phi(y_*)=y_*\) implies \(f(y_*)=0\). We have constructed an
**exact endpoint solution** within \(10^{-15}\) of (1).

By (3) and (6), all its switching margins remain positive. Monotonicity
of the two nonactive margins on each constant-control arc proves
strict star membership on the full arcs. All six factors exceed one.
The endpoint chart is legitimate because the fixed target has
\(F_{11}>0\), while the positive margin invariant determines the third
terminal margin from the first two. Therefore both actual frame and
state endpoints agree exactly with the original window.

## 3. The cost decrease has a rational logarithm certificate

For any rational \(q\in[1,4/3]\), put \(z=(q-1)/(q+1)\le1/7\). Then

\[
\ell(q)=2\sum_{n=0}^{11}\frac{z^{2n+1}}{2n+1},\qquad
\ell(q)\le\log q\le\ell(q)+
\frac{2(1/7)^{25}}{25(1-1/49)}.                            \tag{7}
\]

This follows by integrating the geometric expansion of
\(2/(1-z^2)\), with an explicit positive tail bound.
All factors in (1), together with \(109/100\) and the old factors,
lie in this interval.

Each exact arc cost is a rational nonlogarithmic term minus a positive
rational coefficient times \(\log q\). Applying (7) to the old and new
rational centers gives, by rational addition and multiplication,

\[
\frac{10263}{10^9}
 < J_{\rm old}-J_{012021}(c)
 <\frac{10264}{10^9}.                                    \tag{8}
\]

The complete formula being bounded is

\[
J(q)=\frac{\sigma^2}{8}\sum_k
 A_k\{(A_k+B_k)(q_k-1)+(A_k+C_k)(1-q_k^{-1})-A_k\log q_k\},
\]

where the raw switching margins come from (4)'s underlying recurrence.
Thus (8) is a finite rational certificate for a strict gap, not a
comparison of decimal evaluations of logarithms.

To transfer the gap from the center to the exact solution, on the
factor box \([1,2]^6\) every raw margin before an arc has absolute value
at most \(2\cdot3^5=486\). The sum of the absolute state partials of one
raw arc cost is at most \(5\cdot486/4\), and its explicit factor partial
is at most \(5\cdot486^2/8\), using \(0\le\log q\le1\).
Combining these with the state derivative bound \(972\), summing six
arcs, multiplying by \(\sigma^2<2\), and summing over the five varying
factors gives the convenient bound

\[
\|DJ_{012021}(y)\|_1<10^8\quad (y\in\mathcal B).
\]

Therefore
\[
|J_{012021}(y_*)-J_{012021}(c)|<10^8\rho=10^{-7}.
\]

Together with (8), this proves

\[
\boxed{J_{\rm old}-J_{012021}(y_*)>
\frac{10163}{10^9}>\frac1{100000}>0.}                     \tag{9}
\]

This is an actual six-piece strict-star, endpoint-preserving cheaper
replacement, with free elapsed time and unchanged initial state.

## 4. What this does and does not establish

The original `012012` point is a strict local minimum in its own word,
but the different word `012021` has a strictly cheaper exact solution.
Thus a positive same-word constrained Hessian does not refute the broad
L1 replacement statement. A successful L1 argument may need a nonlocal
comparison of different words, rather than only first and second
variations inside the original word.

This example does not prove that every eligible L1 window has such a
replacement. No universal gate, uniform word bound, global Reinhardt
inequality, or equality classification is claimed. The fixed-word search
that suggested the rational center was exploratory; equations (1)–(9)
are the independent finite-data existence and cost certificate.

No Lean compilation, typechecking, Lake command, or CI was performed.
