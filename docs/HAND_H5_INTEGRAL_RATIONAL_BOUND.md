# A hand proof of the final H5 integral bound

Date: 2026-11-07. Every polynomial identity and every sign argument
used below is displayed. Symbolic manipulation was used for discovery;
the proof consists of the identities and elementary inequalities here,
with no coefficient table, interval cover, or numerical premise.

## 1. Statement and normalization

Suppose

\[
0\le\lambda\le1,\qquad
z\ge\frac{3-\lambda}{1+\lambda},\qquad
0\le s\le\lambda.
\tag{1}
\]

Put

\[
S=z+1,\quad U=z+\lambda S,\quad L=1+U,
\quad Z=z^2+U,
\]
\[
q=S^2/L,\quad H=S^2/Z,\quad d=H-1,
\quad x=z/S,\quad h=S/(z+s),\quad e=h-1,
\]
\[
\Delta_0=x(x-1/2)d+\frac{xd^2}{3(d+2)}.
\tag{2}
\]

Define the rational expression

\[
\begin{aligned}
\mathcal B={}&
\frac{eSL}{Z}\frac{x(q-1)(q/S-x)}q\\
&-\frac{L^2}{SZ}\{q-1+e(Sq-1)\}\Delta_0
 +\frac{z^2de^2}{2h}-\frac{ze^3}{3h(h+1)}.
\end{aligned}
\tag{3}
\]

**Theorem.** On (1), `B<=0`. In fact `B<0` whenever `h>1`.
Thus the integral upper bound (3) is strictly negative at every
actual positive exterior factor.

This theorem proves the final rational comparison. The preceding
H5 identities expressing the residual in terms of (3), and the
logarithmic bounds used to obtain (3), are separate inputs to its
application.

Let

\[
m=1-\lambda,\qquad v=1-s.
\]

The domain becomes

\[
0\le m\le1,\qquad m\le v\le1,
\qquad z\ge\frac{2+m}{2-m}.
\tag{4}
\]

In particular `z>=1`. Useful exact simplifications are

\[
L=S(1+\lambda),\quad Z=S(z+\lambda),\quad
q=\frac S{1+\lambda},\quad d=\frac m{z+\lambda},
\]
\[
e=\frac v{S-v},\qquad \frac e h=\frac vS.
\tag{5}
\]

If `v=0`, then `m=0`, `d=e=Delta_0=0`, and (3) is zero.
It remains to consider `v>0`.

## 2. Two weakenings reduce the comparison to a cubic

First, the floor in (2) has the exact form

\[
\Delta_0=
\frac{zm}{S^2(z+\lambda)}
\left\{\frac{z-1}{2}+\frac{Sm}{3(2S-m)}\right\}.
\]

Since `2S-m<=2S`, it follows that

\[
\Delta_0\ge
\overline\Delta:=
\frac{zm\{3(z-1)+m\}}{6S^2(z+\lambda)}.
\tag{6}
\]

Second, put `t=e/h=v/S`. Then

\[
\frac{e^2}{3h(h+1)}=
\frac{t^2}{3(2-t)}\ge\frac{t^2}{6}.
\tag{7}
\]

Divide (3) by `e>0`. The coefficient multiplying the negative floor
can be rewritten as

\[
\frac{q-1+e(Sq-1)}e
=\frac{q-1}{t}+qz>0.
\tag{8}
\]

Consequently replacing `Delta_0` by (6), and using (7), both increase
the upper bound. Substitution of (5) gives

\[
\boxed{
\mathcal B\le
-\frac{zP}{6S^2(z+\lambda)^2(S-v)},}
\tag{9}
\]

where

\[
\begin{aligned}
P={}&(z+\lambda)^2v^3
 -3zmS(z+\lambda)v^2\\
&+\left[(1+\lambda)mSz\{3(z-1)+m\}
       -6(z+\lambda)(z-\lambda)(1-z\lambda)\right]v\\
&+(1+\lambda)mS\{3(z-1)+m\}(z-\lambda).
\end{aligned}
\tag{10}
\]

All denominators in (9) are positive. It suffices to prove `P>0`
on (4) when `v>0`.

## 3. Increase the scale from its boundary value

Set

\[
p=(2-m)z-(2+m)=U-3\ge0.
\]

Direct polynomial multiplication gives

\[
(2-m)^3P=R_0+R_1p+R_2p^2+R_3p^3,
\tag{11}
\]

with the following four explicit polynomials:

\[
\begin{aligned}
R_3={}&3\{(2-m^2)v+m(2-m-v^2)\},\\[1mm]
R_2={}&(2-m)v^3-3m(m^2-m+10)v^2\\
 &+(m^4-13m^3-14m^2+24m+24)v+E,\\
E={}&4m^4+28m^2(1-m)+24m,\\[1mm]
R_1={}&2(2-m)(m^2-2m+4)v^3\\
 &-3m(m^3+4m^2-4m+32)v^2\\
 &+m(7m^4-46m^3+40m^2-96m+144)v+C,\\
C={}&m^2(-m^4+14m^3-40m^2-48m+160),\\[1mm]
R_0={}&(2-m)(m^2-2m+4)^2v^3-12m(m^3+8)v^2\\
 &+2m^2(3m^4-16m^3+20m^2-56m+64)v\\
 &+4m^3(2-m)(4-m)(8-m).
\end{aligned}
\tag{12}
\]

The first three are nonnegative by short bounds using `0<=m,v<=1`.
For `R_3`, use `2-m-v^2>=1-m>=0`.

For `R_2`, its quadratic coefficient in `v` is nonpositive. Thus
`v^2<=v` and discarding its nonnegative cubic term give

\[
R_2\ge E+D_2v,
\qquad D_2=m^4-16m^3-11m^2-6m+24.
\]

Here `E>=0`, while

\[
\begin{aligned}
E+D_2
&=5m^4-44m^3+17m^2+18m+24\\
&\ge-27m^2+18m+24\\
&=15+9(1-m)+27m(1-m)\ge15.
\end{aligned}
\]

It follows that

\[
R_2\ge(1-v)E+v(E+D_2)\ge0.
\tag{13}
\]

For `R_1`, its cubic coefficient is positive and its quadratic
coefficient is nonpositive. The same argument gives

\[
R_1\ge C+D_1v,
\qquad D_1=m(7m^4-49m^3+28m^2-84m+48).
\]

The elementary bounds

\[
C\ge71m^2,
\]
\[
\begin{aligned}
C+D_1
&=m(-m^5+21m^4-89m^3-20m^2+76m+48)\\
&\ge m(48-34m)\ge14m
\end{aligned}
\]

give

\[
R_1\ge71m^2(1-v)+14mv\ge0.
\tag{14}
\]

In the first bound, discard `14m^3` inside `C/m^2` and use
`m^4,m^2,m<=1`. In the second, discard `21m^4` and use
`m^5,m^3,m^2<=m`. Thus none of these sign arguments requires
checking a collection of undisplayed coefficients.

## 4. The boundary polynomial is positive

It remains to show `R_0>0` when `v>0` and `m<=v<=1`.
There are two cases.

### 4.1 Small m

If `0<=m<=1/5`, the three coefficients of the first three terms
of `R_0` satisfy

\[
(2-m)(m^2-2m+4)^2\ge\frac95\left(\frac{18}{5}\right)^2>23,
\]
\[
12(m^3+8)\le\frac{12012}{125}<97,
\]
\[
2(3m^4-16m^3+20m^2-56m+64)
\ge\frac{13168}{125}>105.
\]

Its constant term is nonnegative. Hence

\[
\begin{aligned}
R_0&\ge v(23v^2-97mv+105m^2)\\
&=v\left\{23\left(v-\frac{97m}{46}\right)^2
          +\frac{251m^2}{92}\right\}>0.
\end{aligned}
\tag{15}
\]

For `m=0`, the last strict inequality follows directly from `v>0`.

### 4.2 The remaining compact interval

Suppose `1/5<=m<1`. Write

\[
v=m+(1-m)t,\qquad0\le t\le1.
\]

The cubic in (12) has the exact four-term identity

\[
R_0=m^3A_0(1-t)^3
    +m^2A_1t(1-t)^2
    +m^2A_2t^2(1-t)+Q t^3,
\tag{16}
\]

where

\[
\begin{aligned}
A_0={}&320-384m+136m^2-68m^3+12m^4-m^5,\\
A_1={}&9m^5-64m^4+132m^3-736m^2+672m+32,\\
A_2={}&6m^5-35m^4+138m^3-776m^2+792m-80,\\
Q={}&2m^6+23m^5-190m^4+124m^3+168m^2-144m+32.
\end{aligned}
\tag{17}
\]

Here are direct proofs that all four coefficients are strictly
positive on the specified interval.

For `A_0`, set `n=1-m` and expand:

\[
A_0=n^5+7n^4+30n^3-6n^2+273n+15
\ge267n+15>0.
\]

The next two polynomials are strictly concave on `[0,1]`, since

\[
A_1''=4(45m^3-192m^2+198m-368)<0,
\]
\[
A_2''=4(30m^3-105m^2+207m-388)<0.
\]

For example their bracketed expressions are at most respectively
`45+198-368=-125` and `30+207-388=-151`. Consequently their
minima on any closed subinterval are at an endpoint. The explicit
endpoint values

\[
A_1(0)=32,\quad A_1(1)=45,
\qquad A_2(1/5)=\frac{151281}{3125},\quad A_2(1)=45
\]

prove the required positive signs.

For `Q`, if `m<=1/2`, then `-190m^4>=-95m^3`, so

\[
Q\ge29m^3+168m^2-144m+32
 =29m^3+168(m-3/7)^2+8/7>0.
\tag{18}
\]

If `m>=1/2`, let `n=1-m`, so `0<=n<=1/2`. Direct substitution
and `n^5<=n^3/4`, `n^4<=n^3/2` give

\[
\begin{aligned}
Q&=2n^6-35n^5-45n^4+366n^3-340n^2+69n+15\\
&\ge\frac{1339}{4}n^3-340n^2+69n+15.
\end{aligned}
\]

Set `r=2n`, so `0<=r<=1`. The last expression is exactly

\[
15(1-r)^3+\frac{159}{2}r(1-r)^2
 +29r^2(1-r)+\frac{203}{32}r^3>0.
\tag{19}
\]

This finishes the four positive signs in (16), proving `R_0>0`.
At the remaining endpoint `m=1`, condition (4) forces `v=1`, and
(12) gives `R_0=15>0` directly.

## 5. Conclusion

Equations (11)--(19) show `P>0` whenever `v>0`. Substitution in
(9) therefore proves `B<0` whenever `h>1`; the zero-factor
boundary was handled directly after (5). This completes the
rational comparison on the entire domain (1).
