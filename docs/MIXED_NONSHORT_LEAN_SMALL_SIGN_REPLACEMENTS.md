# Lean-size replacement for two redundant forward shape-endpoint certificates

Date: 2026-11-08 UTC. **Mathematical sign reduction checked; Lean port and
performance measurement outstanding.** This note targets the `formalize`
branch, whose `FwdHand/CertLRb.lean` and `FwdHand/CertLGd.lean`
currently certify upper shape endpoints separately. No `formalize`
source or working certificate is changed here.

The key observation is already present in
[MIXED_NONSHORT_FORWARD_RATIO_REDUCTION](MIXED_NONSHORT_FORWARD_RATIO_REDUCTION.md)
§5 and [MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_EXCLUSION](MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_EXCLUSION.md)
§2. We restate their **exact** inequalities as small algebraic claims
designed to avoid a three-variable Bernstein expansion in Lean.

## 1. Unchanged domain, conclusions and callers

Use the original normalized notation
\[
c=1-t,\quad p=t+x,\quad W=1+x,\quad X=2+x,\quad
Y=x(x+2),\quad J=t+Y,\quad o=2t+x,\quad
e=q/W,\quad D=eJ-p.
\]
Set \(U(t)=1-t+t^2\), \(y=q-1\), and
\[
F_m(t,x,k,q;v,\ell)
=(m+1-Je^2)N(t,x,k,q,v,\ell)
 +C_*(3/4-\mathcal T_U(t,x,k,q,v)).
\tag{1}
\]
Here \(N,C_*,\mathcal T_U\) are precisely the already defined
quantities in the source notes and in `FwdHand/Basic.lean`.

**Low ratio.** On the *same enlarged domain* as
[MIXED_NONSHORT_FORWARD_RATIO_REDUCTION](MIXED_NONSHORT_FORWARD_RATIO_REDUCTION.md)
(2),
\[
\frac14\le t\le\frac13,\quad 1-2t\le x\le1,\quad
1\le k\le o,\quad 1\le q\le W/o,
\tag{2}
\]
the rational replacement
\(\widehat G(k)=F_6(k;\widehat v,L_+)\) is positive once the
**existing** unit-shape sign \(\widehat G(1)>0\) is imported.
The upper shape \(k=o\) does not require a separate certificate.
The caller remains `fh_lowRatio_core`, and the unchanged
actual-window conclusion is `fh_low_ratio : 1/3 < W.nt`.
The old extra sign is
`fhCLRb_pos_y` in `FwdHand/CertLRb.lean`; retain
`fhCLRa_pos_y` from `CertLRa.lean`.

**High ratio.** On the *same actual-domain comparison box* as
[MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_EXCLUSION](MIXED_NONSHORT_HIGH_RATIO_LARGE_GAP_EXCLUSION.md)
(3),
\[
\frac38\le t\le\frac25,\quad h=1-2t,\quad
\frac1{30}\le j=x-h\le\frac{5h}7,\quad
1\le q\le\frac{W}{1+2j},\quad
\frac{29t^2}4\le k\le o=1+j,
\tag{3}
\]
the rational residual
\[
G_4(k)=F_4(k;V,L_+)+F_\ell-V
\]
is positive once the **existing** lower-shape sign
\(G_4(29t^2/4)>0\) is imported. The terms \(F_\ell-V\)
are independent of \(k\). The caller remains
`fh_LGB_core` and then `fh_small_gap_j`, with its unchanged
conclusion \(2W.nt+W.nx-1<1/30\). The redundant sign is
`fhCLGd_pos_y` in `FwdHand/CertLGd.lean`; retain
`fhCLGc_pos_y` from `CertLGc.lean`.

Bounds in (2)--(3) include closed faces for the scalar signs, although
actual competitive points may have strict bounds. Neither reduction
moves a norm floor or a physical Casimir cap to a new trajectory.

## 2. The decisive *small* derivative identity

At fixed \(t,x,q,v,\ell\), \(F_m\) is quadratic in \(k\) with
negative leading coefficient
\[
-\frac{tW^2De^3}4<0.
\tag{4}
\]
Thus \(\partial_kF_m(k;U(t),y)\) is decreasing in \(k\), so
for \(k\le o\) it is at least its value at \(k=o\).

For **each fixed \(m=6\) or \(m=4\)**, the following exact
specialization holds:
\[
\boxed{\left.\partial_kF_m(t,x,k,1+y;U(t),y)\right|_{k=o}
  =\frac{t(1+y)}{2W^2}
    \bigl(d_0^{(m)}+d_1^{(m)}y+d_2y^2+d_3y^3\bigr).}
\tag{5}
\]

**All coefficients are displayed in full:**
\[
\begin{aligned}
d_0^{(m)}={}&x(1-t)\bigl[1-2t+
    (-2t^2+(2m+2)t-1)x+4mtx^2+2mtx^3\bigr],\\
d_1^{(m)}={}&t-2t^2
 +(2m+4-(2m+15)t+8t^2)x\\
 &+(8m+3-(8m+20)t+10t^2+4t^3)x^2\\
 &+(10m+3-(10m+20)t+16t^2)x^3\\
 &+(4m-(4m+4)t+4t^2)x^4,\\
d_2={}&-6t^2+(-16t-6t^2)x+(-5-27t+2t^3)x^2\\
 &+(-7-19t+8t^2)x^3+(-4-2t+2t^2)x^4,\\
d_3={}&x(1+x)\{t+x(x+2)\}.
\end{aligned}
\tag{6}
\]

The exact identity (5) was independently reconstructed by symbolic
differentiation from the **unexpanded** definitions of \(N\), the
transport numerator and \(F_m\), then coefficientwise comparison
after \(k=o,q=1+y,v=U(t),\ell=y\). This reconstruction is a
transcription check, **not** a proof premise for the proposed Lean port.

### Expansion budget

The coefficient identities in (6), **specializing \(m\) first**,
have the following independent exact monomial counts when written as
polynomials in \((t,x)\):

| Expression | Nonzero monomials | Total degree | Free variables |
|---|---:|---:|---:|
| \(d_0^{(6)}\) or \(d_0^{(4)}\) | 11 | 6 | 2 |
| \(d_1^{(6)}\) or \(d_1^{(4)}\) | 15 | 6 | 2 |
| \(d_2\) | 12 | 6 | 2 |
| \(d_3\) | 5 | 4 | 2 |
| \(2d_1^{(6)}+d_2\) | 15 | 6 | 2 |
| \(4d_1^{(4)}+d_2\) | 15 | 6 | 2 |

**Lean implementation requirement:** do not check (5) by one
`ring` over \((t,x,y)\). Instead first prove the quadratic
shape difference at abstract \(v,\ell,q\), specialize \(k=o\),
and extract the four \(y\)-coefficients into **four separate
two-variable identities**. Reconstruct the Horner sum with abstract
coefficient variables. All nontrivial coefficient normalizations
above are within the 150-monomial, degree-8, two-variable budget.
Whether the staged Lean implementation actually normalizes in this
way still requires a kernel check and timing.

## 3. Direct signs, with small rational coefficients

The common polynomial \(d_2\) is strictly negative on both
t-intervals: its five coefficients as a polynomial in \(x\)
are negative, using \(1/4\le t\le2/5\).
The common \(d_3>0\) whenever \(x,t>0\).
The braces in \(d_0^{(m)}\) are positive, since
\[
-2t^2+14t-1\ge19/8>0
\quad (m=6,\ 1/4\le t\le1/3),
\]
\[
-2t^2+10t-1\ge79/32>0
\quad (m=4,\ 3/8\le t\le2/5).
\tag{7}
\]

For \(m=6\), the exact polynomial \(2d_1^{(6)}+d_2\) is
\[
\begin{aligned}
&(2t-10t^2)+(32-70t+10t^2)x\\
&+(97-163t+20t^2+10t^3)x^2\\
&+(119-179t+40t^2)x^3
 +(44-58t+10t^2)x^4.
\end{aligned}
\tag{8}
\]
On (2), \(x\ge1/3\). Its constant coefficient is at least
\(-4/9\), its linear coefficient at least \(26/3\),
and the three remaining coefficients are at least
\(128/3,178/3,74/3\). Thus (8) is at least
\(-4/9+(26/3)(1/3)=22/9>0\).
Since \(0\le y\le1/2\) and \(d_2<0\),
\[
d_1^{(6)}+yd_2\ge d_1^{(6)}+d_2/2>0.
\]
Together with \(d_0^{(6)},d_3>0\), this proves the
parenthesis in (5) is positive on (2).

For \(m=4\), the exact polynomial \(4d_1^{(4)}+d_2\) is
\[
\begin{aligned}
&(4t-14t^2)+(48-108t+26t^2)x\\
&+(135-235t+40t^2+18t^3)x^2\\
&+(165-259t+72t^2)x^3+(60-82t+18t^2)x^4.
\end{aligned}
\tag{9}
\]
On (3), \(x\ge1/5\). Its constant coefficient is at least
\(-16/25\), its linear coefficient at least \(224/25\),
and the three remaining coefficients are at least
\(41,307/5,136/5\). Hence (9) is at least
\(-16/25+(224/25)(1/5)=144/125>0\).
Since \(0\le y\le1/4\),
\[
d_1^{(4)}+yd_2\ge d_1^{(4)}+d_2/4>0.
\]
Together with \(d_0^{(4)},d_3>0\), (5) is positive on (3).
No domain subdivision or coefficient table was used.

## 4. Transfer back to the existing rational residual

The original source notes already establish the following two
small-factor derivative identities, where \(m=6\) or \(4\)
and \(A_k=qx[1+tW+X(q-1)]>0\):
\[
\begin{aligned}
(F_m)_{kv}
  & =-(m+1-Je^2)A_k+W^2De(1-e^2Y),\\
(F_m)_{k\ell}
  & =-(m+1-Je^2)tpqW.
\end{aligned}
\tag{10}
\]
On (2), \(Je^2\le10/3\), \(WD/x\le9/4\);
therefore \((F_6)_{kv}<-(17/12)A_k<0\).
On (3), \(Je^2\le17/16\), \(WD/x\le41/24\);
therefore
\((F_4)_{kv}<-(107/48)A_k<0\).
Both \((F_m)_{k\ell}\) are strictly negative.

The low-ratio note proves **at the original comparison coordinates**
\[
\widehat v<U(t),\qquad L_+\le y;
\]
the high-ratio note proves
\[
V<U(t),\qquad L_+\le y,
\]
with the needed strictness also at \(q=1\) coming from the norm
comparison. The lower norm and logarithm comparisons, (10),
the concavity (4), and the endpoint signs of §3 consequently give
\[
\boxed{\partial_k\widehat G(k)>0\quad\text{on (2)},\qquad
       \partial_kG_4(k)>0\quad\text{on (3)}.}
\tag{11}
\]
For \(m=6\), this reuses the already proved
\(v_3-V=cx^6(31x^2+82x+46)/(60W^2X^5R)>0\)
and \(v_3+\rho(v_3-F_\ell)<U(t)\).
For \(m=4\), it reuses
\(U(t)-V=cx(1-tW-T_G(x))/W^2>0\).
Neither proof invokes a Casimir cap at a deformed shape.

Integrating (11) (or proving the corresponding quadratic
difference-factorization directly) gives both desired lower-endpoint
reductions. That **mathematically supersedes** the upper-shape
certificates \(\texttt{CertLRb}\) and \(\texttt{CertLGd}\), but
does not yet delete them from the Lean dependency graph.

## 5. Lean staging and remaining work

1. Preserve `fh_lowRatio_core`, `fh_low_ratio`,
   `fh_LGB_core` and `fh_small_gap_j` unchanged at their call sites.
2. Implement (10) using the existing affine-in-\(v,\ell\)
   decomposition in `FwdHand/Coef.lean`, not by a fully
   expanded rational `ring`.
3. Implement the quadratic-in-\(k\) difference as a factored
   identity, then (5) via four coefficientwise lemmas on \((t,x)\).
   Their counts are in §2.
4. Use the small sign inequalities in §3 and the existing
   norm bounds to obtain (11), then replace the upper-endpoint
   certificate call in each original caller.
5. Only after the replacement files kernel-check and their actual
   time/RSS improve should the old imports and generated
   certificate files be deleted or moved to legacy.

**Not removed by this reduction:** `CertLRa` (the low-ratio
unit-shape face), `CertLGc` (the high-ratio lower-shape face),
`CertLGa` and `CertLGb` (the low-t faces), and the envelope
Casimir signs `CertEn` and `CertPn`. They require separate,
genuinely lower-dimensional analytic proofs. This note gives two
independent, finite and checkable first targets without claiming
a speedup not yet benchmarked.
