# A uniform size bound for competitive pure-forward periods

Date: 2026-11-07 UTC. Hand proof. No Lean, Lake, typechecking, or CI.

## Statement and scope

Every geometrically eligible, competitive entirely forward normal period
has

\[
\boxed{N\le61.}
\tag{1}
\]

This is a uniform consequence of the actual whole-period winding,
the small-forward-minimum theorem, and the complete-period Casimir cap.
It does not close case F, supply a constrained descent direction, or
authorize a catalogue of the remaining lengths.

The inputs are
[MIXED_GLOBAL_SMALL_FORWARD_MINIMUM](MIXED_GLOBAL_SMALL_FORWARD_MINIMUM.md),
[GLOBAL_STRUCTURE_FORWARD_ACUTE](GLOBAL_STRUCTURE_FORWARD_ACUTE.md),
[MIXED_GLOBAL_PROJECTIVE_WINDING](MIXED_GLOBAL_PROJECTIVE_WINDING.md),
and the rational Casimir bound in
[GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD, Section 2](GLOBAL_STRUCTURE_FORWARD_MINIMUM_THRESHOLD.md).

## 1. A strict gap in every forward angle

Use the common forward notation

\[
K_i=a_i^2+4,\qquad
d_{i-1}=y_{i-1}^{T}S y_{i-1},\quad
d_i=y_i^{T}S y_i,\quad S>0,
\]

and put \(\gamma=\sqrt{\det U}=\kappa/\sqrt{12}\).
Let \(\theta_i\) be the positive angle from
\(S^{1/2}y_{i-1}\) to \(S^{1/2}y_i\). The acute theorem gives
\(0<\theta_i<\pi/2\). The Wronskian identity gives

\[
\sin\theta_i
=\frac{\gamma}{K_i\sqrt{d_{i-1}d_i}}.
\tag{2}
\]

A global minimum in the cyclic active-margin sequence is a five-active
forward minimum. The small-forward-minimum theorem therefore gives
\(a_i^2>4/3\) at every site, hence \(K_i>16/3\).
The forward switching inequalities imply

\[
d_i\ge\frac{1-r_i+r_i^2}{8}\ge\frac3{32}.
\]

Consequently

\[
\sin\theta_i<2\gamma=\frac\kappa{\sqrt3},
\qquad \kappa<\frac{205}{138}.
\tag{3}
\]

Set \(\varepsilon=\pi/192\). We claim

\[
\frac{205}{138}<\sqrt3\sin(\pi/3-\varepsilon).
\tag{4}
\]

Indeed \(\pi<22/7\) gives
\(0<\varepsilon<11/672\), and \(\sqrt3<26/15\).
Using \(\cos\varepsilon\ge1-\varepsilon^2/2\) and
\(\sin\varepsilon\le\varepsilon\),

\[
\begin{aligned}
\sqrt3\sin(\pi/3-\varepsilon)
&=\frac32\cos\varepsilon-\frac{\sqrt3}{2}\sin\varepsilon\\
&\ge\frac32-\frac34\varepsilon^2-\frac{13}{15}\varepsilon\\
&>\frac{13417577}{9031680}
=\frac{205}{138}+\frac{21871}{207728640}.
\end{aligned}
\]

Thus (4) holds. Both angles in the comparison are acute, so (3)--(4)
and strict monotonicity of sine give

\[
\boxed{\theta_i<\frac\pi3-\frac\pi{192}.}
\tag{5}
\]

## 2. Use the actual winding once

The geometric winding theorem gives

\[
N=3k+1,\qquad \sum_{i=1}^{N}\theta_i=k\pi.
\]

It follows that

\[
\frac\pi3
=\sum_{i=1}^{N}\left(\frac\pi3-\theta_i\right)
>\frac{N\pi}{192}.
\]

Hence \(N<64\). Since \(N\equiv1\pmod3\), this is exactly
\(N\le61\), proving (1).

The winding statement uses the actual geometric sector and the full
twisted frame endpoint. Matrix centrality by itself would determine
only the parity and would not justify this count. No trajectory
variation or endpoint-rank assertion enters the argument.

## Verification boundary

The short supplementary checker
[`global_structure_forward_angle_count_certificate.py`](../explorations/global_structure_forward_angle_count_certificate.py)
checks the displayed rational arithmetic and the scalar determinant
normalization. The sine comparison and whole-period implications are
the hand argument above. The remaining F cost or index comparison is
still open; this note supplies a size restriction, not a new exclusion
of all non-octagonal forward periods.
