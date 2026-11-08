# A rational quadratic improvement of the short secant order

Date: 2026-11-08 UTC. Explicit hand lemma. The complete polynomial identity below replaces
the former aggregate bounds on 72 Bernstein coefficients.

Suppose the exact short secants satisfy
\[
2\le x\le\frac{13}{6},\qquad
1\le\alpha<x\le\beta\le\alpha x,\qquad
\operatorname{Sec}(1,x,\beta)
 =\operatorname{Sec}(\alpha,\beta,x).
\]
Put
\[
d=\frac\beta x-1,\qquad
c(x)=1+\frac{4x(x+1)}{7x+1}
    =\frac{4x^2+11x+1}{7x+1}.
\]
Then
\[
\boxed{\alpha\ge1+c(x)d+\frac{d^2}{1+4d}.}
\tag{1}
\]
The inequality is strict if d>0. In particular, on the region
d>=1/19,
\[
\boxed{\alpha>1+\left(c(x)+\frac1{23}\right)d.}
\tag{2}
\]
This is solely a restriction on the unchanged exact short shape.
It supplies neither a root sign nor the desired exclusion d>=1/19.

## 1. The comparison interval and derivative criterion

The accepted
[strong lower order](MIXED_SMALLER_SHORT_STRONG_ORDER.md)
gives alpha>=1+c(x)d. Since c(x) increases for x>=2 and c(2)=13/5,
\[
0\le d<\frac{x-1}{c(x)}
\le\frac{35}{78}<\frac9{20}.
\tag{3}
\]
The entire equal-secant continuation from beta=x to the actual beta
therefore lies in this interval.

Use its exact derivative formula, with
\[
p=\alpha/\beta,\quad q=x/\beta,\quad
N=(1+p)(6+p-5pq-q^2-q),\quad
W=6(p+q+2)(1-pq).
\]
At every nondegenerate point p<q,
\[
\alpha_\beta>
p+\frac{N}{W-N}\frac{(2q-p)x-q^2}{x-q},
\qquad W-N>0.
\tag{4}
\]
These are exactly the derivative and explicit secant-gap estimate
already proved in the cited strong-order theorem.

Consider the barrier
\[
B(d)=1+c(x)d+\frac{d^2}{1+4d},\qquad
B'(d)=c(x)+\frac{d(2+4d)}{(1+4d)^2}.
\]
At a contact with this barrier,
\[
q=\frac1{1+d},\qquad p=\frac{B(d)}{x(1+d)}.
\tag{5}
\]
It is enough to prove
\[
F:=N\{(2q-p)x-q^2\}
 -(x-q)(W-N)\left(\frac{B'(d)}x-p\right)\ge0.
\tag{6}
\]
Indeed (4), together with positive x-q and W-N, then makes the
actual branch derivative strictly larger than B'(d)/x.
Only contacts with B(d)<x are relevant, so these positive denominators
are exactly the ones present on the actual continuation.

## 2. A complete polynomial identity and its elementary sign

After (5), direct multiplication gives
\[
F=\frac{d\,Q(d,x)}
 {x^3(1+d)^5(1+4d)^4(7x+1)^3},
\qquad Q(d,2+X)=\sum_{k=0}^7 X^k Q_k(d).
\tag{7}
\]
The following table prints every coefficient of every \(Q_k\), in
ascending powers \(d^0,\ldots,d^8\). Equations (5)--(6) and this
table specify the entire rational identity; there is no coefficient
extraction or minimum assertion left to execute.

| \(k\) | Coefficients of \(Q_k(d)\), in ascending powers of \(d\) |
|---|---|
| 0 | `36720, 1629288, 17492895, 74741292, 105796719, -166842396, -727738209, -852289776, -354696408` |
| 1 | `238626, 8238690, 83306538, 360237447, 635229657, -86528583, -1858423950, -2400943680, -1020299220` |
| 2 | `593592, 17166666, 163840779, 705290757, 1373526066, 605939586, -1840319490, -2832837468, -1244301468` |
| 3 | `756714, 19160832, 173117946, 734815226, 1501754180, 1093860788, -819809180, -1801734292, -832609260` |
| 4 | `543312, 12411244, 106539549, 443438138, 926686305, 822274086, -92531309, -659469924, -329457820` |
| 5 | `222422, 4681266, 38321998, 155892919, 328222643, 321672435, 55204082, -136079836, -76886224` |
| 6 | `48520, 955170, 7482521, 29687685, 62391462, 64565076, 20939672, -14040576, -9764480` |
| 7 | `4382, 81580, 613358, 2369976, 4939992, 5266560, 2182912, -495616, -518144` |

Each row has positive coefficients up to one degree, followed only
by negative coefficients. This gives a particularly short sign
argument. If
\[
P(t)=\sum_{j=0}^n p_jt^j,\qquad
p_0,\ldots,p_m>0,\quad p_{m+1},\ldots,p_n<0,
\]
then for \(0<t\le b\), termwise comparison gives
\[
P(t)\ge(t/b)^m P(b).
\tag{8}
\]
Indeed, a positive term of degree at most \(m\) is at least its
value at \(b\) times \((t/b)^m\); the same inequality holds for
a negative term of higher degree. At \(t=0\), use \(p_0>0\).

For the first row take \(b=9/20\). Direct substitution gives
\[
Q_0(9/20)=\frac{8187154568095419}{3200000000}>0.
\tag{9}
\]
For all other rows it is even enough to take \(b=1/2\). Their
seven exact values, in row order \(k=1,\ldots,7\), are
\[
\left(
\frac{3547605195}{64},\ 
\frac{11989271565}{64},\ 
\frac{15575894919}{64},\ 
\frac{5265366165}{32},\ 
\frac{1974254445}{32},\ 
\frac{48816675}{4},\ 996300
\right).
\tag{10}
\]
All are positive. Since \(0\le d\le9/20<1/2\), (8)--(10)
prove every \(Q_k(d)>0\). Also \(X=x-2\ge0\). Thus
\(Q(d,x)>0\) on the full required domain, and (7) proves
\(F\ge0\), including the removable initial face \(d=0\).

## 3. Complete the barrier argument

At beta=x the exact branch and B both have value one. The strict
secant-gap inequality in (4), together with F>=0, gives strict
derivative separation even at this initial contact. Thus the exact
branch starts above the barrier. A first later contact from above
would require its derivative to be no larger than the barrier
derivative, contradicting (4)--(7). If B were to reach x first,
such a contact would be forced because the actual branch remains
below x. Therefore the barrier comparison holds throughout the
actual continuation and proves (1).

Finally, d/(1+4d) increases for d>=0 and has value 1/23 at d=1/19.
Combining this with the strict form of (1) proves (2).
