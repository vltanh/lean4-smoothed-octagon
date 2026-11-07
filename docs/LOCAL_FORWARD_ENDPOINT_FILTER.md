# An exact active-margin filter for complete L1 windows

Date: 2026-11-07. Hand derivation on the full positive strict-star
\(\mathtt{012012}\) domain.

## Result and scope

A selected window made of six **complete** pieces of an actual minimizer
starts and ends at genuine switches. The external Hamiltonian ties in
[MINIMIZER_WINDOW_PMP.md](MINIMIZER_WINDOW_PMP.md), together with the
uniform endpoint rank in
[LOCAL_FORWARD_RANK.md](LOCAL_FORWARD_RANK.md), therefore impose more
than the original cost, sector, and same-word stationarity conditions.

This note gives an explicit form of that additional filter. It requires
only the active margins, their nearest-neighbor action, the tangent
prefixes, and one three-by-three linear solve. No adjoint integration
is needed to evaluate it. The two boundary residuals must each be an
**endpoint of an explicitly given nonnegative interval**. The formulas
retain both possible neighboring labels and allow triple ties.

The filter is necessary, not sufficient for global minimality. Moreover,
even full local PMP with both external ties does not force equal factors
or a state-cyclic regular window. Section 6 proves that asymmetric
eligible PMP windows persist near the standard forward family. No
whole-period endpoint or global cost comparison is supplied by that
persistence argument. L1 and the uniform reduction remain open.

## 1. Active chain, action, and the frame covector

Use the physical determinant-one margins of LOCAL_FORWARD_RANK. Write

\[
a_{-1},a_0,\ldots,a_6>0,\qquad
s_i=a_i+a_{i+1},\qquad K_i=a_i^2+4,
\]
\[
b_i=\frac{4-a_{i-1}a_i}{s_{i-1}},\qquad
q_i=\frac{s_{i-1}s_i}{K_i}>1
\quad(0\le i\le5).                                         \tag{1}
\]

The adjacent products \(a_{i-1}a_i<4\) for \(0\le i\le6\),
together with (1), are the entire positive strict-star domain. The
initial and terminal states have margins

\[
(a,b,c):=(a_0,b_0,a_{-1}),\qquad
(A,B,C):=(a_6,b_6,a_5).                                    \tag{2}
\]

In both triples the coordinate order is labels \(0,1,2\). Put

\[
s_-=a+c,\quad S_-=a+b+c,\qquad
s_+=A+C,\quad S_+=A+B+C.
\]

Fixing both states fixes \(a_{-1},a_0,a_5,a_6\). The only remaining
active-margin variables are \(a_1,\ldots,a_4\).

Let \(J\) be cost divided by \(\sqrt{12}\), including the full boundary
terms in the action. Equivalently,

\[
8J=\sum_{i=0}^5
 \left[a_i(a_{i-1}+a_{i+1}-b_i-b_{i+1})
       -a_i^2\log q_i\right].                              \tag{3}
\]

Define, for **all** \(i=0,\ldots,5\),

\[
C_i=\frac14\left[
 a_{i-1}+a_i+a_{i+1}
 -a_i^2\left(\frac1{s_{i-1}}+\frac1{s_i}\right)
 +\frac{a_i^3}{K_i}-a_i\log q_i\right].                     \tag{4}
\]

For interior indices \(1\le i\le4\), this is exactly \(J_{a_i}\).
At the boundary indices it is a useful extended expression, rather
than the actual derivative with the outer state variables free.

For the tangent frame, set

\[
D_0=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad
D_1=\begin{pmatrix}1&-2\\0&-1\end{pmatrix},\quad
D_2=\begin{pmatrix}1&0\\2&-1\end{pmatrix},
\]
\[
E=-D_0,\qquad
\mathsf A(q)=\begin{pmatrix}q&-q\\q^{-1}&0\end{pmatrix},\qquad
P_i=\mathsf A(q_0)\cdots\mathsf A(q_{i-1}),\quad P_0=I.
\]

Then the arbitrary local tangent endpoint is \(F=P_6\). There is no
condition \(F=R\). Extend the explicit frame columns to the two boundary
indices by

\[
\widehat V_i=
P_i\,2\begin{pmatrix}
-a_i/K_i&q_i^2/s_i\\
-1/s_{i-1}&a_i/K_i
\end{pmatrix}P_i^{-1},
\qquad 0\le i\le5.                                        \tag{5}
\]

For \(1\le i\le4\), these are the actual right-trivialized frame
derivatives \(V_i=F_{a_i}F^{-1}\).

At a same-word stationary point, the rank theorem gives a unique linear
functional \(\mu\) on the three-dimensional space of trace-zero matrices
such that

\[
C_i=\mu(V_i),\qquad 1\le i\le4.                            \tag{6}
\]

This **three-dimensional frame covector** is distinct from the full
five-dimensional endpoint covector \(\lambda\) used in
MINIMIZER_WINDOW_PMP and LOCAL_FORWARD_NEEDLE_AUDIT.

The calculation can be made entirely explicit. The triple
\((V_1,V_2,V_3)\) is independent throughout the positive domain. With
trace-zero coordinates \((M_{11},M_{12},M_{21})\), set
\(\Delta=\det(V_1,V_2,V_3)\ne0\). Then

\[
\mu(W)=
\frac{
 C_1\det(W,V_2,V_3)
 +C_2\det(V_1,W,V_3)
 +C_3\det(V_1,V_2,W)}
 {\Delta}.                                                \tag{7}
\]

The remaining scalar test \(C_4=\mu(V_4)\) is precisely same-word
stationarity. Thus (7) and that test use every stationary point, without
discarding an interior rank locus. No lower bound on \(|\Delta|\) at
degenerating boundaries is asserted.

## 2. Boundary action and frame identities

Let \(V_j=F_{a_j}F^{-1}\) denote the actual derivatives of the full
tangent product when the indicated active-chain variable is free,
including \(j=-1,0,5,6\). Direct differentiation gives

\[
\begin{aligned}
J_{a_{-1}}&=\frac{aS_-}{8s_-},&
J_{a_0}&=C_0-\frac{cS_-}{8s_-},\\
J_{a_5}&=C_5-\frac{AS_+}{8s_+},&
J_{a_6}&=\frac{CS_+}{8s_+}.
\end{aligned}                                             \tag{8}
\]

Here is a short check of the first two identities. The part of \(8J\)
depending on \(c=a_{-1}\) or \(a=a_0\), up to terms independent of both,
is

\[
a(c-b)-a^2\log(a+c)+a^2\log(a^2+4)
+3aa_1-(a^2+a_1^2)\log(a+a_1),
\]
where \(b=(4-ac)/(a+c)\). Use

\[
b_c=-\frac{a^2+4}{(a+c)^2},\qquad
b_a=-\frac{c^2+4}{(a+c)^2}.
\]

The first derivative simplifies to \(aS_-/s_-\). The second is
\(8C_0-cS_-/s_-\), using
\(\log q_0=\log(a+c)+\log(a+a_1)-\log(a^2+4)\).
The terminal two identities follow from the corresponding symmetric
boundary expression in the action, with the active variable \(C=a_5\)
and outer variable \(A=a_6\). This is a symmetry of the displayed scalar
action, not a reversal of a control trajectory.

The corresponding frame identities are

\[
\begin{aligned}
V_{-1}&=-D_0/s_-,
&
\widehat V_0&=V_0-D_2/s_-,
\\
V_6&=-\operatorname{Ad}_F(D_2)/s_+,
&
\widehat V_5&=V_5-\operatorname{Ad}_F(D_0)/s_+.
\end{aligned}                                             \tag{9}
\]

For a check, write \(Z_i=P_iEP_i^{-1}\).
Differentiating \(\log q_i\) gives the actual boundary columns. In
particular \(V_{-1}=Z_0/s_-\) and \(V_6=Z_5/s_+\).
The identities

\[
\mathsf A(1)^{-1}E\mathsf A(1)=-D_2,\qquad
Z_6=-\operatorname{Ad}_F(D_0)
\]

supply the missing neighboring terms at \(i=0,5\) in the formula for
\(\widehat V_i\). Also
\(Z_5=-\operatorname{Ad}_F(D_2)\), because the last actual tangent factor
has label \(2\) and commutes with \(D_2\). This proves (9).

Define residual boundary derivatives

\[
\nu_{-1}=J_{a_{-1}}-\mu(V_{-1}),\quad
\nu_0=J_{a_0}-\mu(V_0),
\]
\[
\eta_5=J_{a_5}-\mu(V_5),\quad
\eta_6=J_{a_6}-\mu(V_6).                                  \tag{10}
\]

The terminal components \((\eta_5,\eta_6)\), together with \(\mu\),
are the full stationary endpoint covector in the coordinates
\((F,a_5,a_6)\). Equations (6) ensure that no interior residual remains.

## 3. The four inactive endpoint gaps

Use a log-time needle: prepend or append a vertex piece with factor
\(e^\varepsilon\). At any state with margins \(p\), the normalized
running cost at vertex \(j\) is

\[
\ell_j=\frac18p_j(p_0+p_1+p_2).                            \tag{11}
\]

Write \(D_{-,j}\) for its compensated first derivative at the initial
endpoint, and \(D_{+,j}\) for the derivative at the terminal endpoint.
They use the unique normal endpoint multiplier and preserve the fixed
initial and full final frame/state. This is the same gap convention as
LOCAL_FORWARD_NEEDLE_AUDIT: a negative gap is favorable for minimization.

At the initial state \((a,b,c)\), the changes in the two initial
active-chain coordinates \((a_{-1},a_0)\) are

\[
\begin{array}{c|ccc}
\text{needle label}&0&1&2\\ \hline
(\dot a_{-1},\dot a_0)&(-s_-,0)&(b+c,-a-b)&(0,s_-).
\end{array}
\]

Prepending changes the right-trivialized tangent endpoint by \(-D_j\).
After cancellation of the terminal residual derivatives, one obtains

\[
\begin{aligned}
D_{-,0}&=\ell_0+\mu(D_0)-s_-\nu_{-1}=0,\\
D_{-,1}&=\ell_1+\mu(D_1)+(b+c)\nu_{-1}-(a+b)\nu_0,\\
D_{-,2}&=\ell_2+\mu(D_2)+s_-\nu_0.
\end{aligned}                                             \tag{12}
\]

For clarity about the initial-state calculation, the needle changes
the state entering the old six arcs, but those old factors remain
fixed. Their old tangent product is therefore unchanged. In the
differential of their cost minus the endpoint pairing, the interior
terms vanish by (6); the terminal terms cancel against
\((\eta_5,\eta_6)\). Only \(\nu_{-1},\nu_0\) remain. The additional new
tangent factor contributes \(+\mu(D_j)\), giving (12).
The initial physical state itself has not been varied.

At the terminal state \((A,B,C)\), the changes of
\((a_5,a_6)=(p_2,p_0)\) are

\[
\begin{array}{c|ccc}
\text{needle label}&0&1&2\\ \hline
(\dot a_5,\dot a_6)&(-s_+,0)&(B+C,-A-B)&(0,s_+).
\end{array}
\]

Appending changes the right-trivialized tangent endpoint by
\(-\operatorname{Ad}_F(D_j)\). Thus

\[
\begin{aligned}
D_{+,0}&=\ell_0+\mu(\operatorname{Ad}_F D_0)+s_+\eta_5,\\
D_{+,1}&=\ell_1+\mu(\operatorname{Ad}_F D_1)
 -(B+C)\eta_5+(A+B)\eta_6,\\
D_{+,2}&=\ell_2+\mu(\operatorname{Ad}_F D_2)-s_+\eta_6=0.
\end{aligned}                                             \tag{13}
\]

The two active zero identities follow at once from (8)–(10), and
also express stationarity in the first and last arc durations.
The full endpoint rank permits the compensating changes of positive old
factors. At a junction, insert directly between intact arcs, so no
negative variation of a zero-duration split piece is used.

## 4. Two scalar interval-endpoint tests

Set

\[
e_0=C_0-\mu(\widehat V_0),\qquad
e_5=C_5-\mu(\widehat V_5).                                 \tag{14}
\]

Let

\[
X(a,b,c)=\frac12
\begin{pmatrix}-a&a+c\\-a-b&a\end{pmatrix},
\quad X_-=X(a,b,c),\quad X_+=X(A,B,C),
\]
\[
U_-=S_--4\mu(X_-),\qquad
U_+=S_+-4\mu(\operatorname{Ad}_F X_+).                     \tag{15}
\]

Then the four inactive gaps reduce exactly to

\[
\boxed{\begin{aligned}
D_{-,2}&=s_-e_0,&
D_{-,1}&=\frac{U_-}{s_-}-(a+b)e_0,\\
D_{+,0}&=s_+e_5,&
D_{+,1}&=\frac{U_+}{s_+}-(B+C)e_5.
\end{aligned}}                                           \tag{16}
\]

The first and third equalities follow immediately from (8)–(10).
For the other two, the useful matrix identity is

\[
(a+c)D_1+(b+c)D_0+(a+b)D_2=-4X(a,b,c).                   \tag{17}
\]

The same weighted combination of the three running costs equals \(S_-\):
indeed \(ab+bc+ca=4\), and therefore

\[
(a+c)\ell_1+(b+c)\ell_0+(a+b)\ell_2
=\frac{S_-}{8}\,2(ab+bc+ca)=S_-.
\]

Multiplying (12) by the indicated weights cancels both residual boundary
derivatives, giving

\[
s_-D_{-,1}+(a+b)D_{-,2}=U_-.
\]

At the terminal endpoint, apply (17) inside \(\operatorname{Ad}_F\)
and use (13); this gives

\[
s_+D_{+,1}+(B+C)D_{+,0}=U_+.
\]

These prove the remaining equalities in (16). All factors used for
division are strictly positive on the full domain.

For a complete-arc minimizer window, the necessary endpoint test is
therefore

\[
\boxed{\begin{gathered}
U_-\ge0,\quad
0\le e_0\le\frac{U_-}{s_-(a+b)},\quad
e_0\bigl(U_--s_-(a+b)e_0\bigr)=0,\\
U_+\ge0,\quad
0\le e_5\le\frac{U_+}{s_+(B+C)},\quad
e_5\bigl(U_+-s_+(B+C)e_5\bigr)=0.
\end{gathered}}                                           \tag{18}
\]

In words, each residual is one of the two endpoints of the indicated
closed interval. An interior point of either interval fails the
external-tie requirement. A negative gap fails Hamiltonian maximality.

The cases have a direct label interpretation:

| Boundary | Lower endpoint \(e=0\) | Upper endpoint |
|---|---|---|
| Start, active label \(0\) | predecessor \(2\) ties | predecessor \(1\) ties |
| End, active label \(2\) | successor \(0\) ties | successor \(1\) ties |

If \(U_-=0\) or \(U_+=0\), the corresponding interval degenerates to
zero and both inactive vertices tie. Thus (18) does not discard possible
triple ties or impose a simple-switch assumption.

All quantities in (18) are explicit rational/logarithmic functions of
the eight active margins, through (1), (4), (5), and (7). The filter
does not conceal a new unknown costate trajectory.

## 5. The forward-neighbor specialization

If the neighboring labels continue the forward sequence, so that the
predecessor is \(2\) and the successor is \(0\), (18) requires

\[
e_0=e_5=0.
\]

Together with interior stationarity, this says

\[
\boxed{C_i=\mu(\widehat V_i)\qquad(0\le i\le5).}             \tag{19}
\]

Thus the same action equation applies at all six active indices. This
is a useful uniform structural relation on complete forward-run windows.

One may eliminate \(\mu\) altogether: each augmented column
\((\widehat V_i,C_i)\) is a vector in a four-dimensional space, and the
three columns with indices \(1,2,3\) are independent. Equation (19) is
equivalent to the vanishing of the three four-by-four determinants
obtained by adjoining indices \(0,4,5\) to those three columns.
This is an explicit finite logarithmic system. It is not an equality
classification or a cost inequality.

For the other neighboring labels, the upper-endpoint alternatives in
(18) replace one or both of the equations in (19). Which external
labels actually occur is determined by the surrounding word and its
twisted seam, not by choosing whichever branch is easier.

## 6. Why endpoint ties cannot force the regular family

There is a rigorous local reason not to expect (18), or even all local
PMP conditions, to force equal factors.

Start with six consecutive complete arcs of one of the standard forward
polygons with \(N=3k+1\ge7\). The constructions and eligibility proof in
[LOCAL_FORWARD_PMP_LIMIT.md](LOCAL_FORWARD_PMP_LIMIT.md) give:

- a normal log-time extremal with zero active Hamiltonian;
- unique active maximization inside each arc and simple transverse
  switches, including the external switches \(2\to0\) and \(2\to0\);
- positive factors and strict-star margins on every closed arc;
- window cost strictly below the octagon's and strict sector inequalities
  at every positive time, including the terminal time.

We use this existing family only as a reference for a local persistence
argument, not as an exhaustive class of competitors.

Fix the initial frame \(g=I\). Its initial state has two free coordinates,
and a normal covector on the five-dimensional frame/state manifold has
five coordinates. At the initial switch impose

\[
h_0=h_2=0,\qquad h_j=\langle p,f_j\rangle-\ell_j.             \tag{20}
\]

These are two independent equations on the covector: \(f_0,f_2\) are
linearly independent, since their tangent-frame components are
\(-VD_0,-VD_2\) with \(V\) invertible and \(D_0,D_2\) independent.
A smooth local cotangent trivialization therefore makes (20) a smooth
codimension-two constraint. The space of initial state/covector data
satisfying it has dimension

\[
2+5-2=5.                                                   \tag{21}
\]

The third Hamiltonian is strictly smaller at the reference switch, and
the outgoing crossing is transverse. Both properties persist nearby.
For each of the next six switching events, the implicit function theorem
continues the first zero of the appropriate Hamiltonian difference
near the reference event. All six durations remain positive and depend
smoothly on the initial data. Conservation of the active Hamiltonian
on each autonomous arc, and equality at each switch, keep it zero.

The maximizing control remains the same six-arc sequence. To see this
on whole intervals, use the strict compact-interior gaps away from
switches and the simple crossing signs near switches. The inactive
third gap stays strict near every switch. Thus the continued trajectories
satisfy the full simplex PMP, start with predecessor \(2\) tied, and
end with successor \(0\) tied. They satisfy (19).
The same transverse signs allow the preceding label-\(2\) flow to be
continued backward for a short positive duration and the following
label-\(0\) flow forward for a short positive duration. These are genuine
positive neighboring arc portions, so the two ties are actual local
switches rather than only formal endpoint equalities.

Strict-star membership and the strict window budget persist by
continuity. Sector eligibility is also open here. Away from the initial
time the reference inequalities have positive compact minima. At the
initial endpoint the first determinant vanishes identically for every
left-normalized path, but its first derivative is strictly positive
for each contact by the strict-star condition; this gives uniform
positivity on a sufficiently short initial interval. The other sector
determinant starts at \(1\). These observations cover the whole interval,
including the structural initial zero.

Finally, this five-parameter family cannot collapse to the
three-parameter equal-factor locus. Map its initial state/covector data
to the two initial-state coordinates and six positive factors. The
uniform rank-five theorem reconstructs the unique normalized endpoint
covector smoothly from any stationary input near the reference:
choose a nonzero endpoint minor and use \(dJ=\lambda\,dE\).
Integrating the adjoint equation backward along the fixed finite word
then reconstructs the initial covector smoothly. This provides a smooth
left inverse to the continuation map, whose differential is therefore
injective.

Consequently its local image has dimension five. The equal-factor locus
has only three coordinates: the initial state and the single common
factor. A five-dimensional immersed image cannot lie in that
three-dimensional locus. Thus there are arbitrarily nearby **unequal-factor**
eligible windows satisfying same-word stationarity, every full local
PMP inequality, and both external ties.

This persistence result supplies no periodic extension for the perturbed
windows, no global-minimizer claim, and no local or global optimality
claim. It shows exactly why the external-tie filter, although necessary
and effective against endpoint-unique examples, cannot by itself reduce
L1 to the regular family.

## 7. Remaining mathematical boundary

The exact example in LOCAL_FORWARD_NEEDLE_AUDIT has strictly positive
inactive gaps at both external endpoints. By (16), its two residuals
lie strictly inside the corresponding intervals, so it fails (18).
The unique normalized adjoint prevents choosing a different lift to
repair that failure. This is consistent with its local optimality for
the fixed-endpoint problem.

What remains is a uniform comparison or a further genuine minimizer
restriction on the stationary inputs passing (18), with global
periodic/end-covector and budget information used where appropriate.
The explicit filter does not establish descent on that smaller set,
and the persistence argument prevents replacing it by an unproved
equal-factor assertion.

The derivation uses the hand identities in LOCAL_FORWARD_RANK and the
normality/external-tie lemma in MINIMIZER_WINDOW_PMP. Its four gap
formulas follow from the displayed boundary derivatives and the
two-by-two identity (17). A supplemental exact symbolic check of the
boundary derivative simplification and the initial column identity
returned zero residuals; those outputs are not premises of the hand
proof above. No numerical search, Lean, Lake, typecheck, or CI command
was used for this result.

An independent hand review derived all four boundary action derivatives,
the missing-column identities, both needle-residual formulas, and the
weighted reduction (16). It also checked the interval branches and the
five-dimensional persistence argument, including the structural initial
sector zero and the rank-based smooth left inverse. No material issue
was found.

