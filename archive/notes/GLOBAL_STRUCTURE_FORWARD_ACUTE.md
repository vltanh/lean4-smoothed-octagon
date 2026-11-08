# Competitive forward periods have positive adjacent Jacobi pairings

Date: 2026-11-07 UTC. Hand lemma with supplementary exact algebra and an
[independent internal audit](GLOBAL_NORMAL_PERIOD_STRUCTURE_AUDIT.md).
No Lean, Lake, typechecking, or CI.

## Statement and scope

Use the notation and hypotheses of
[GLOBAL_STRUCTURE_FORWARD_ELLIPTIC](GLOBAL_STRUCTURE_FORWARD_ELLIPTIC.md).
For an entirely forward normal closed period, assume additionally

\[
\kappa:=\sqrt{\det\Lambda_1}<3/2.
\]

The competitive complete-period cost--Casimir bound implies this strict
inequality. Then every adjacent Gram pairing is strictly positive:

\[
\boxed{e_i=y_{i-1}^{T}S y_i>0.}
\tag{1}
\]

Since that earlier theorem gives `S>0`, consecutive vectors `S^(1/2)y_i`
have angles strictly between zero and `pi/2`. Their orientation is the
positive Wronskian orientation. This lemma treats arbitrary unequal
positive factors and uses only the weak forward switching inequality;
no strict switching derivative is assumed.

This is a restriction on all competitive periods in case F. It is not
a constrained index theorem or a complete cost comparison for case F.

## 1. A determinant minimization on a triangle

Fix an index and abbreviate

\[
a=a_i,\quad x=a_{i-1},\quad y=a_{i+1},\quad
p=x+a,\quad s=a+y,\quad K=a^2+4,\quad q=ps/K>1.
\]

The exact stationarity and Gram identities are

\[
e=\frac{p d_-+s d_+-C/2}{2a},\qquad
\Delta:=\det U=K^2(d_-d_+-e^2),
\tag{2}
\]

and forward switching gives

\[
d_-\ge t_-:=\frac{x^2+xa+a^2}{8p^2},\qquad
d_+\ge t_+:=\frac{a^2+ay+y^2}{8s^2}.
\tag{3}
\]

Suppose, for contradiction, that `e<=0`. Set

\[
u=pd_-,\quad v=sd_+,\quad c=C/2,\quad
u_0=pt_-,\quad v_0=st_+.
\]

Then `(u,v)` belongs to the nonempty triangle

\[
u\ge u_0,\quad v\ge v_0,\quad u+v\le c.
\tag{4}
\]

On this triangle,

\[
\Delta/K^2=F(u,v):=\frac{uv}{ps}
                 -\frac{(c-u-v)^2}{4a^2}.
\tag{5}
\]

The Hessian of `F` has eigenvalues `-1/(ps)` and
`1/(ps)-1/a^2`, both negative because `ps>a^2`. Thus `F` is
concave, and its minimum on (4) occurs at a vertex. Put
`h=c-u_0-v_0>=0`. Its three vertex values satisfy

\[
F(u_0+h,v_0)-F(u_0,v_0)
 =\frac{hv_0}{ps}+\frac{h^2}{4a^2}\ge0,
\]
\[
F(u_0,v_0+h)-F(u_0,v_0)
 =\frac{hu_0}{ps}+\frac{h^2}{4a^2}\ge0.
\]

Consequently the minimum is attained at `(u_0,v_0)`:

\[
\Delta\ge K^2\left(t_-t_+-\frac{E^2}{256}\right),\qquad
E=1-2a(1/p+1/s)+a^2/K-\log q.
\tag{6}
\]

Here the exact scalar derivative formula for `C` gives
`h=aE/8`. In particular, the assumed nonempty triangle implies `E>=0`.

## 2. The lower bound exceeds the singular determinant

Introduce the dimensionless variables

\[
r=a/p,\quad t=a/s,\quad d=a^2/K,\quad
B=rt,\quad L=\log(d/B)=\log q>0.
\]

The strict-star and positive-duration inequalities give

\[
0<d<r,t<1,\qquad B<d<1.
\tag{7}
\]

Write `f(z)=1-z+z^2`. Then

\[
t_-=f(r)/8,\quad t_+=f(t)/8,\quad
K=4/(1-d),\quad E=1-2(r+t)+d-L\ge0.
\]

The following elementary identity is the sign certificate:

\[
\boxed{
\begin{aligned}
4f(r)f(t)-E^2-3(1-d)^2
={}&4(d-rt)(1+r+t-d-rt)\\
 &+2LE+L^2.
\end{aligned}}
\tag{8}
\]

Every term on the right is nonnegative, and the first and last are
strictly positive. In particular, `1+r+t-d-rt>0`, since
`1-d>0` and `r+t-rt>0`. Thus (6) gives

\[
\Delta\ge\frac{4f(r)f(t)-E^2}{16(1-d)^2}
>\frac3{16}.
\tag{9}
\]

The multiplier normalization of the preceding note is
`det U=det Lambda_1/12=kappa^2/12`. Hence (9) says
`kappa>3/2`, contradicting the hypothesis. This proves (1).

## Exact checker and remaining implication

Run

```
python explorations/global_structure_forward_acute_certificate.py
```

The checker verifies the displayed scalar identities. Concavity,
triangle minimization, the strict inequalities, and the PMP interface
are the hand arguments above. No lengths, stationary families,
numerical optimizers, or sampled signs enter the certificate.

For the outstanding index problem, (1) makes the phase-variation block
of the augmented Hessian a negative weighted Laplacian with coefficients
`K_i e_i>0`. Its phase kernel is precisely the common rotation. The
remaining radial/margin block and its interaction with full frame
closure still need an index or cost argument; this lemma does not
discard the endpoint-curvature term from the constrained Hessian.
