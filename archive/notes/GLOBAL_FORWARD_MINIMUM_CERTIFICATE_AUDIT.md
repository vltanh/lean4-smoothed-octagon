# Independent audit of the forward minimum certificate domain

Date: 2026-11-07. Internal hand review and exact algebra. No Lean, Lake, typechecking or CI. This does not close F.

## 1. Independent audit of the forward circular corner

The [forward corner calculation](GLOBAL_STRUCTURE_FORWARD_CIRCLE_CORNER.md)
has a valid estimate on its intended nondegenerate domain. Review of its
initial draft found an exact counterexample at the degenerate algebraic
base. The retained theorem now explicitly requires `t>0`; this covers
every actual positive three-arc window and preserves the degenerate fibre.

Use that calculation's variables
\(U=4/a^2\), \(z=b/a\), \(w=c/a\), \(S=1+z\),
\(T=1+w\), \(K=1+U\), and \(W_z=z^2+U\). Its central variables
have the normalization

\[
u=8d_{-1},\qquad v=8d_0,\qquad E=16e_0.
\]

The physical Casimir conversion is consequently exactly

\[
\kappa^2
=12(a^2+4)^2(d_{-1}d_0-e_0^2)
=\frac{3K^2}{4U^2}(4uv-E^2).
\]

This confirms the factor used in the corner proof. Its outer equations
also follow directly from the same Jacobi recurrence. Indeed

\[
y_{-2}=\frac{S^2}{W_z}y_{-1}-\frac K{W_z}y_0
\]

gives

\[
8d_{-2}=\frac{S^4u+K^2v-S^2KE}{W_z^2},\qquad
16e_{-1}=\frac{2S^2u-KE}{W_z}.
\]

The left outer factor satisfies
\(p/a=hW_z/S-z\). Substitution in the actual stationarity equation
at margin \(b\), followed by \(E=Su+Tv-A\), gives precisely
\(n_Lu+m_Lv=R_L\) with the proposed coefficients. Interchanging
left and right gives the other equation. The star condition
\(pb<4\) also gives

\[
h<\frac{1+z}{z}\le2,
\]

since \(z\ge1\). Thus the upper exterior-factor bound is a valid
necessary condition for the global-minimum window.

I independently reconstructed this substitution symbolically and
checked the positive row-coefficient factorization. I also reviewed the
interval arithmetic operations and reran the proposed corner checker:
it reproduces exactly the three rows
`[5,7,7,1,1]`, `[7,10,4,2,1]`, and `[7,4,10,1,2]` using rational
intervals. The reciprocal, power, product, logarithm enclosure and
second-order chain rules are inclusion-preserving on the stated positive
domain. No sampled or floating bound is used in that table.

On the stated closed box, put

\[
t=(3-U)+(z-1)+(w-1)+(h-1)+(k-1).
\]

The row-sum argument is valid for **\(t>0\)** and yields the advertised
strict bound
\(\kappa^2>16571/7500>276/125\). The mean-value path stays inside
the larger rational box; its bound \(\mathcal T\le10st\) and the
bounds \(L_1,L_2\ge t/4\) have compatible signs. The final estimate
uses \(E\ge0\), which is supplied for actual competitive forward
periods by the acute-pairing theorem.

At \(t=0\), however, take

\[
U=3,\quad z=w=h=k=1,\quad u=v=1.
\]

Then \(A=9/4\), \(n_L=n_R=m_L=m_R=R_L=R_R=0\), so both outer
stationarity equations hold. Moreover

\[
E=\frac74>0,\qquad
\kappa^2=\frac43\left(4-\frac{49}{16}\right)=\frac54
<\frac{276}{125}.
\]

It satisfies every displayed algebraic condition in the unqualified
closed-box statement. The degenerate central base point therefore has
a nontrivial fibre of covector variables; it is not an excluded single
\((u,v)\) value.

The correct theorem is: **every solution in the closed box with
\(t>0\) satisfies the strict Casimir separation**. Equivalently, state
it for an actual positive three-arc window, for which all three factors
are strictly greater than one. At \(t=0\), those factors all equal
one, so it cannot be an actual window. With this explicit restriction,
the corner lemma can be retained and used to remove the singular
central parameter box before a complementary-domain certificate.


## 2. The outer determinant has only the circular singularity

There is also an exact factorization useful for the complementary-domain
certificate. Put \(H=h-1\), \(I=k-1\), \(q=ST/K\), and retain the
corner proof's coefficients. Then

\[
\boxed{
\begin{aligned}
m_Lm_R-n_Ln_R
={}&\frac{K^4(q-1)}{STW_zW_w}
\bigl[(q-1)+H(qS-1)+I(qT-1)\\
&\hspace{28mm}+HI(q+1)\{q(S+T)-q^2-1\}\bigr].
\end{aligned}}
\tag{10}
\]

This follows by expanding the positive row-coefficient factorizations,
using \(ST=qK\); I checked the resulting rational identity independently.
On an actual global forward minimum, the star inequalities give
\(1<q<\min(S,T)\), and \(H,I>0\). Consequently

\[
q(S+T)-q^2-1>q^2-1>0,
\]

so every term in the square bracket is nonnegative, its first is
strictly positive, and the determinant in (10) is positive. In
particular, the outer two equations determine \(u,v\) uniquely at
every actual minimum window, regardless of unequal exterior factors.
Their original coefficient determinant is the negative of (10).

More quantitatively,

\[
m_Lm_R-n_Ln_R\ge
\frac{K^4}{STW_zW_w}(q-1)^2.
\]

On the minimum domain \(U\le3\), \(z,w\ge1\), one has
\(q-1\ge\{(3-U)+(z-1)+(w-1)\}/4\). Outside the central cube of
radius \(\eta\), this gives \(q-1\ge\eta/4\). Hence the corner
lemma really does remove the entire possible zero-denominator limit
for the complementary compact-domain calculation. No additional
interior determinant-zero surface has been left untreated.
