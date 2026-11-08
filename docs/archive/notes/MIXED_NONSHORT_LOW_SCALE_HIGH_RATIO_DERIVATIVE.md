# A hand derivative lemma for the high-ratio low-scale rectangle

Date: 2026-11-07 UTC. Complete hand lemma, accepted in the
[independent low-scale audit](MIXED_NONSHORT_LOW_SCALE_HAND_AUDIT.md), Section 5.

This note supplies the six derivative signs used in the common
nonshort low-\(a\) reduction. It proves a symbolic polynomial identity
and its sign on a fixed rectangle. It does not assert the separate
base endpoint signs or the complete low-\(a\) exclusion.

## 1. Definitions and statement

Use the general normalized residual \(N_k=tB_kqW R_k\) from
[MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md](MIXED_NONSHORT_REVERSE_HAND_EXCLUSION.md),
equation (1), with
\[
W=1+x,\quad X=x+2,\quad p=t+x,\quad Y=x(x+2),
\quad k_h(t)=2t+\tfrac12,\quad y=q-1.
\]
In that residual replace the exact incoming secant and logarithm by
\[
\bar v=
1+\frac{(1-t)^2}{W}
-\frac{2(1-t)}{X}\left(1+\frac{x^2}{3X^2}\right),
\qquad
L_+=\frac{(q-1)(q^2+10q+1)}{6q(q+1)}.
\]
Call the resulting rational residual \(\bar N_k\), and set
\[
F_\ell=1+\frac{p^2q}{W^2}
-\frac pW\frac{q^2+10q+1}{6(q+1)},
\]
\[
I_0=k+tx+tW(k-2t),\qquad
I_1=k(x+2)+tx(x+2)^2,\qquad
A=xq(I_0+I_1y).
\]
The exact coefficient identity \(N_v=-A\) checks the normalization
of this multiplier.

Define, at \(k=k_h(t)\),
\[
Q=6(q+1)W^2\{\bar N_k-A(\bar v-F_\ell)\}
  =\sum_{j=0}^4 P_j(t,x)y^j.
\tag{1}
\]
The coefficients are rational functions whose common denominator
divides \(X^3\). Finally put
\[
\begin{aligned}
J_0&=P_0,&
J_1&=P_1+2P_0,&
J_2&=P_2+48P_0,\\
J_3&=P_3+4P_2,&
J_4&=P_3-P_0,&
J_5&=P_4-P_0.
\end{aligned}
\tag{2}
\]

**Lemma.** For every
\[
\frac14\le t\le\frac7{20},\qquad
\frac12\le x\le1,
\tag{3}
\]
all six total derivatives along \(k=k_h(t)\) are positive:
\[
\frac{d}{dt}J_i(t,x)>0,\qquad i=0,\ldots,5.
\tag{4}
\]
The variable \(x\) is held fixed. Thus each of these six expressions
is bounded below by its value at \(t=1/4\).

## 2. An explicit positive decomposition

Set
\[
u=4t-1\in[0,2/5],\qquad z=2x-1\in[0,1].
\]
For a coefficient vector, use the unambiguous convention
\[
\operatorname{poly}(a_0,\ldots,a_n)
  :=\sum_{j=0}^n a_j z^j.
\]
The following single identity applies to each of the six derivatives:
\[
1024X^3\frac{dJ_i}{dt}
=g_i(1+z)^{m_i}
 \{A_i(z)+u(1-u)B_i(z)+u^2D_i(z)\}.
\tag{5}
\]
Here
\[
(g_0,\ldots,g_5)=(2,1,1,1,1,1),\qquad
(m_0,\ldots,m_5)=(2,1,0,0,0,1),
\]
and all eighteen polynomials in (5) are displayed below.

Every coefficient of each \(B_i,D_i\) is nonnegative, and their
constant coefficients are positive. Four of the \(A_i\) have
positive coefficients. The only exceptions are \(A_0,A_2\), for which
\(0\le z\le1\) gives the immediate bounds
\[
A_0(z)\ge7992-30-9=7953>0,
\]
\[
A_2(z)\ge1060164-7765-1104-3=1051292>0.
\]
Also \(u(1-u)\ge0\) and \(u^2\ge0\). Therefore the right side of
(5) is strictly positive, proving (4).

Identity (5) can be checked by substituting
\(t=(1+u)/4\), \(x=(1+z)/2\) in the derivative of (1)--(2).
After clearing \(X^3\), each derivative is quadratic in \(u\).
Writing it as \(A+uB+u^2C\) and using
\(A+uB+u^2C=A+u(1-u)B+u^2(B+C)\) gives (5).
Thus the table records a complete polynomial decomposition, not a
list of test values or a coefficient-count claim.

## 3. The complete coefficient identities

### Derivative 0

\[
\begin{aligned}
A_0&=\operatorname{poly}(7992,6669,2502,348,-30,-9),\\
B_0&=\operatorname{poly}(30456,31626,14236,3544,492,30),\\
D_0&=\operatorname{poly}(12456,12951,6226,1780,294,21).
\end{aligned}
\]

### Derivative 1

\[
\begin{aligned}
A_1&=\operatorname{poly}(190404,340569,211377,67944,12766,1585,173,14),\\
B_1&=\operatorname{poly}(545472,1142370,927402,404560,103588,15282,1138,28),\\
D_1&=\operatorname{poly}(387972,715995,549627,235000,59938,8739,607,10).
\end{aligned}
\]

### Derivative 2

\[
\begin{aligned}
A_2&=\operatorname{poly}(1060164,2865894,2868877,1331764,299847,12278,-7765,-1104,-3),\\
B_2&=\operatorname{poly}(3820152,11465800,13434314,8096796,2870438,625296,80214,5004,66),\\
D_2&=\operatorname{poly}(2173152,6191350,7032299,4252320,1570433,367950,51405,3420,39).
\end{aligned}
\]

### Derivative 3

\[
\begin{aligned}
A_3&=\operatorname{poly}(2009583,5243400,5422806,2885794,957998,236816,47550,6962,591,20),\\
B_3&=\operatorname{poly}(4745394,13455396,15797392,10123400,3927120,946228,137240,10784,342,0),\\
D_3&=\operatorname{poly}(5333769,13865796,14862922,8838542,3232314,742432,103058,7694,225,0).
\end{aligned}
\]

### Derivative 4

\[
\begin{aligned}
A_4&=\operatorname{poly}(821871,2433270,3051122,2150760,968786,294282,60274,7940,603,20),\\
B_4&=\operatorname{poly}(1098978,2941712,3294744,2047460,779080,186200,27248,2228,78,0),\\
D_4&=\operatorname{poly}(1399353,3564062,3764814,2213168,801142,183230,25790,2036,69,0).
\end{aligned}
\]

### Derivative 5

\[
\begin{aligned}
A_5&=\operatorname{poly}(327141,732678,698383,379030,129413,28378,3869,298,10),\\
B_5&=\operatorname{poly}(261588,447586,341676,147810,38684,6118,548,22,0),\\
D_5&=\operatorname{poly}(370713,613186,445221,182298,45155,6766,575,22,0).
\end{aligned}
\]
