# Uniform exclusion of the circular corner in the forward minimum system

This is a fixed-domain lemma for the remaining F comparison. It does not
close F. Its role is to remove the singular circular corner before a
finite exact interval comparison of the complementary domain. No Lean,
Lake, typechecking, or CI is used.

## 1. Necessary three-arc system

Use the actual five consecutive margins `(p,b,a,c,d)` at a whole-period
forward minimum. The small-minimum and minimum-budget theorems give
`4/3<a²<20/11`. Put

\[
 U=4/a^2,\quad z=b/a,\quad w=c/a,\quad
 S=1+z,\ T=1+w,\ K=1+U,\quad W_z=z^2+U,\ W_w=w^2+U.
\]

Thus `11/5<U<3`, `z,w≥1`. Write `h,k` for the two genuine exterior
forward factors. The star inequalities give `1<h,k<2`. The same
normal covector gives variables `u,v,E`, with `u,v≥3/4`, and

\[
 q=ST/K,\qquad E=Su+Tv-A,\qquad
 \kappa^2=\frac{3K^2}{4U^2}(4uv-E^2),                 \tag{1}
\]

where

\[
\begin{split}
 A&=1+z+w-S^{-1}-T^{-1}+K^{-1}-\log q,\\
 B&=W_zh/S+1-z^2S/(W_zh)-z^2/S+z^3/W_z-z\log h,\\
 C&=W_wk/T+1-w^2T/(W_wk)-w^2/T+w^3/W_w-w\log k.
\end{split}                                                     \tag{2}
\]

Set

\[
\begin{array}{ll}
 \alpha_L=K(hS-z)/W_z,&\alpha_R=K(kT-w)/W_w,\\
 n_L=S^2(U-z)(h-1)/W_z,&n_R=T^2(U-w)(k-1)/W_w,\\
 m_L=\alpha_LT-K^2h/(SW_z),&m_R=\alpha_RS-K^2k/(TW_w),\\
 R_L=\alpha_LA-B,&R_R=\alpha_RA-C.
\end{array}
\]

The two outer stationarity equations are

\[
 n_Lu+m_Lv=R_L,\qquad m_Ru+n_Rv=R_R.                \tag{3}
\]

These are the actual same-lift equations; no division by the determinant
of their coefficient matrix will be made. In particular, the argument
retains its degenerate boundary. The competitive whole-period Casimir
cap from the existing minimum-threshold note is `κ²<276/125`.

## 2. Statement

**Lemma.** The necessary system (1)–(3), with `u,v≥3/4` and `E≥0`,
has no competitive solution with
`t=(3-U)+(z-1)+(w-1)+(h-1)+(k-1)>0` in

\[
 0\le 3-U\le\eta,\qquad 0\le z-1\le\eta,
 \qquad 0\le w-1\le\eta,
 \qquad 1\le h,k\le2,\qquad \eta=1/12500.            \tag{4}
\]

In fact every such nondegenerate solution obeys

\[
 \kappa^2>\frac{16571}{7500}>\frac{276}{125}.
                                                               \tag{5}
\]

The already proved acute theorem supplies `E>0` on an actual competitive
forward period. The corner proof requires neither an endpoint rank nor
any assertion that the intermediate comparison arrays close.

## 3. A residual with a regular limit

Define

\[
 L_1=n_L+m_R,\quad L_2=m_L+n_R,\qquad
 \mathcal T=R_L+R_R-\tfrac34(L_1+L_2).
\]

Equation (3) gives

\[
 L_1(u-\tfrac34)+L_2(v-\tfrac34)=\mathcal T.         \tag{6}
\]

At `U=3,z=w=1`, direct substitution gives

\[
 \mathcal T=-f(h)-f(k),\qquad
 f(r)=\frac{r^2-1}{2r}-\log r\ge0,                  \tag{7}
\]

because `f(1)=0` and `f'(r)=(r−1)²/(2r²)≥0`. Also the first
derivatives of `𝒯` in `U,z,w` all vanish at `(3,1,1,1,1)`.

The following rational interval bounds hold throughout the larger box

\[
 299/100\le U\le3,\quad 1\le z,w\le101/100,
 \quad 1\le h,k\le2.                                \tag{8}
\]

Each entry bounds the absolute mixed second derivative indicated by
its row and column.

| First derivative | `U` | `z` | `w` | `h` | `k` |
|---|---:|---:|---:|---:|---:|
| `U` | 5 | 7 | 7 | 1 | 1 |
| `z` | 7 | 10 | 4 | 2 | 1 |
| `w` | 7 | 4 | 10 | 1 | 2 |

This small table has an exact reconstruction: differentiate the formulas
(2) and (3) twice with the sum and product rules; for a positive interval
`[l,r]` use reciprocal interval `[1/r,1/l]`, the four endpoint products,
and

\[
 (l-1)/l\le\log x\le r-1,\qquad
 (\log x)'=1/x,\quad(\log x)''=-1/x^2.              \tag{9}
\]

All endpoints in (8) are rational. The companion checker implements
these exact rational operations and prints the displayed integer ceilings;
it also reconstructs (7) and the three vanishing derivatives. Thus the
table is a finite rational inequality certificate, with no floating
arithmetic or sampled signs. The broad interval bounds (9), rather than
a numerical logarithm routine, suffice.

Write

\[
 d=3-U,\quad x=z-1,\quad y=w-1,\quad
 s=d+x+y,\quad t=s+h+k-2.
\]

The vanishing first derivatives, the mean value theorem, and the uniform
bound `10` in the table give

\[
 \mathcal T(U,z,w,h,k)
 \le\mathcal T(3,1,1,h,k)+10s\,t\le10s\,t.          \tag{10}
\]

Indeed first move from `(3,1,1,1,1)` to `(3,1,1,h,k)` to bound each
central first derivative by `10(h+k−2)`, then integrate those derivatives
along the segment in the three central coordinates. The sharper bound
`5s²+10s(h+k−2)` is available but is not needed.

## 4. Positive row sums replace matrix inversion

Throughout (8), the displayed rational coefficients give

\[
 n_L\ge h-1,\quad n_R\ge k-1,
 \quad m_L\ge(q-1)+(h-1),\quad m_R\ge(q-1)+(k-1).
                                                               \tag{11}
\]

For example

\[
 m_R=\frac{K^2}{TW_w}\{(q-1)+(k-1)(qT-1)\},
\]

where `qT−1≥1`, and

\[
 \frac{K^2}{TW_w}\ge
 \frac{(399/100)^2}{(201/100)(40301/10000)}>1.
\]

Similarly

\[
 \frac{S^2(U-z)}{W_z}\ge
 \frac{4(198/100)}{40301/10000}>1.
\]

Also

\[
 q-1=\frac{d+2x+2y+xy}{4-d}\ge s/4.
\]

Consequently `L1,L2≥t/4`. If `t>0`, (6), (10), and `u,v≥3/4`
give

\[
 u+v\le\tfrac32+40s.                              \tag{12}
\]

When `t=0`, all factors equal one, so the point is not an actual positive
forward three-arc window. No stationarity determinant or factor gap has
been divided out.

## 5. Casimir separation

On (4), `s≤3η`, `S,T≤2+η`, and

\[
 A\ge\tfrac94-\log q\ge\tfrac94-2\eta.
\]

The last inequality follows from `log q≤q−1` and
`q−1≤(5η+η²)/(4−η)≤2η`. Therefore (1) and (12) give

\[
 0\le E\le\tfrac34+(240+\tfrac72)\eta+120\eta^2
 =\frac{12023137}{15625000}<\frac{77}{100}.
\]

Finally `K/U≥4/3` and `4uv≥9/4`, so

\[
 \kappa^2\ge\frac43(\tfrac94-E^2)
 >\frac43\left(\tfrac94-\frac{77^2}{100^2}\right)
 =\frac{16571}{7500}
 =\frac{276}{125}+\frac{11}{7500}.
\]

This proves the lemma uniformly in both outer factors. It removes only
the explicitly stated circular corner; the complementary F domain and
the whole M2 case remain open.

## Independent audit and exact scope

[GLOBAL_FORWARD_MINIMUM_CERTIFICATE_AUDIT](GLOBAL_FORWARD_MINIMUM_CERTIFICATE_AUDIT.md) independently reconstructs the actual stationarity interface, the rational derivative table, and the final strict separation. Its review corrected the initial algebraic statement to require `t>0`. At `U=3,z=w=h=k=1`, the outer equations vanish for a fibre of covectors; for example `u=v=1` gives `kappa^2=5/4`, so that degenerate fibre must not be declared excluded. Every actual positive three-arc window has `t>0`.

[GLOBAL_FORWARD_MINIMUM_NONSINGULAR](GLOBAL_FORWARD_MINIMUM_NONSINGULAR.md) proves that the complementary actual minimum domain has no interior denominator zero. The remaining compact-domain cost–Casimir inequality is still open.
