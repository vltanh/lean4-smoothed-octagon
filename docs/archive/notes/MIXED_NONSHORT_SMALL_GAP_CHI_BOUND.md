# The forward ratio chi on the small-gap domain

Date: 2026-11-08 UTC. Hand lemma conditional on the two displayed
small-gap bounds. This note does not prove those bounds.

Use the original normalized common nonshort geometry and the incident
upper residual numerator N from
[MIXED_NONSHORT_FORWARD_RATIO_REDUCTION](MIXED_NONSHORT_FORWARD_RATIO_REDUCTION.md).
Thus
\[
c=1-t,\quad p=t+x,\quad W=1+x,\quad j=p-c=2t+x-1,
\quad B=k-t^2+p^2,\quad e=q/W,\quad \chi=pe,
\]
and the incoming norm is the original value
\[
v=1+\frac{c^2}{W}-\frac{c\log W}{x}>3/4.
\]
The established common scale and ordering bounds include
\[
k>\frac{29}{4}t^2,\qquad 1\le k<1+j,
\]
and actual forward data have \(q>1\) and \(N<0\).

**Theorem.** If in addition
\[
\boxed{\frac13\le t,\qquad 0\le j\le\frac1{30},}
\tag{1}
\]
then
\[
\boxed{\chi>\frac47.}
\tag{2}
\]
No transported next-norm inequality or newly assigned Casimir bound is
needed in this implication.

## 1. Reduce the shape and bound the turn interval

The common scale and ordering inequalities give
\[
t^2<\frac{4}{29}\frac{31}{30}=\frac{62}{435}
<\left(\frac{19}{50}\right)^2.
\]
Put \(h=1-2t\). Under (1), we therefore have the enlarged domain
\[
\frac6{25}\le h\le\frac13,\qquad
0\le j\le\frac1{30},\qquad
x=h+j,\quad c=\frac{1+h}{2},\quad p=c+j.
\tag{3}
\]
The proved shape monotonicity of N allows us to lower k to one,
keeping t,x,q and the exact incoming norm fixed. Write the resulting
scalar numerator as \(N_1(q)\). Actual \(N<0\) would imply
\(N_1(q)<0\).

Suppose for contradiction that \(\chi\le4/7\). Then
\[
1<q\le q_\chi:=\frac{4W}{7p}\le\frac87,
\tag{4}
\]
since \(W=p+c\le2p\). We will show that \(N_1\) is strictly concave
on this interval and positive at both endpoints.

For clarity, the numerator used below can be defined without any
implicit differentiation of a boundary point. At k=1 put
\[
H_t=v-1+t^2+t^2(2-t),
\qquad Q_t=t(1-t+t^2)+H_tY+tvY^2,
\qquad Y=x(x+2),
\]
where \(H_t=tH_U\) and \(Q_t=tB^2w_U\). Then
\[
\begin{aligned}
N_1(q)={}&tBqWc+tq^2B^2-tBqp^2-tp^2W^2+tqWp^3\\
&-tBqWp\log q-tBqW^2v-q^2Q_t
 +qWp(H_t+2tvY).
\end{aligned}
\tag{5}
\]
This is the same scalar comparison numerator as the common hand
reduction, with the actual incoming norm unchanged.

## 2. Concavity in q

Writing
\[
N_1(q)=A_2q^2+A_1q-tp^2W^2-Cq\log q,
\qquad C=tpBW>0,
\]
we have \(A_2=tB^2-Q_t\) and
\[
N_1''(q)=2A_2-C/q.
\]
The coefficient of v in \(A_2\) is \(-Y-tY^2<0\).
Thus (4) and \(v>3/4\) give
\[
N_1''(q)<-\frac18\,
 \left.(7C-16A_2)\right|_{v=3/4}.
\tag{6}
\]
The remaining polynomial is
\[
\left.(7C-16A_2)\right|_{v=3/4}
 =\sum_{i=0}^4 b_i(h)j^i,
\]
where
\[
\begin{aligned}
b_0&=-\frac{h+1}{4}(16h^4+23h^3-9h^2-7h+1),\\
b_1&=-\frac{h+1}{4}(87h^3+12h^2-55h-12),\\
b_2&=-\frac12(66h^3+33h^2-58h-33),\\
b_3&=\frac{67}{4}(1-h^2),\qquad
b_4=\frac32(1-h).
\end{aligned}
\tag{7}
\]
Each is positive on (3). For the first inner polynomial, for example,
\[
16h^4+23h^3-9h^2-7h+1
\le\frac{16}{81}+\frac{23}{27}+1
 -9\left(\frac6{25}\right)^2-7\frac6{25}<0.
\]
For the next two, use respectively
\[
\frac{87}{27}+\frac{12}{9}-55\frac6{25}-12<0,
\quad
\frac{66}{27}+\frac{33}{9}-58\frac6{25}-33<0.
\]
The last two signs are immediate. This proves strict concavity.

## 3. The q=1 endpoint

The following simple secant upper bound suffices throughout this proof:
\[
v<V_2:=1-\frac{cp}{W^2}
 +\frac{cx}{W^2}\left(\frac12-\frac x3+\frac{x^2}{12}-t\right).
\tag{8}
\]
One direct proof is to put
\(I(x)=\int_0^1(1-u)^2/(1+xu)\,du\). Polynomial division gives
\[
I(x)=\frac13-\frac{x}{12}
 +x^2\int_0^1\frac{u^2(1-u)^2}{1+xu}\,du
 >\frac13-\frac{x}{12}.
\]
The exact identities
\[
T_0(x)=\frac12-xI(x),\qquad
v-\left(1-\frac{cp}{W^2}\right)
 =\frac{cx}{W^2}(T_0(x)-t)
\]
prove (8).

The numerator N is decreasing in its scalar incoming-norm argument.
At q=1, substitution of (8) in (5) gives
\[
\begin{aligned}
N_1(1)>
\frac{(h+1)^2(h+j)^2}{48(h+j+1)^2}
\{&h^4+3h^3j+2h^3+3h^2j^2+3h^2j+4h^2\\
 &+hj^3+2h-j^3-4j^2-4j\}.
\end{aligned}
\tag{9}
\]
The expression in braces is greater than
\[
2h-j^3-4j^2-4j
\ge\frac{12}{25}-\frac1{30^3}-\frac4{30^2}-\frac4{30}>0.
\]
Thus \(N_1(1)>0\).

## 4. The chi=4/7 endpoint

Retain the elementary logarithm upper bound
\[
\log q<L_+(q)=\frac{(q-1)(q^2+10q+1)}{6q(q+1)}
\qquad(q>1).
\]
Both scalar coefficients \(N_v\) and \(N_{\log q}\) are negative.
Consequently, at \(q=q_\chi\), (8) and this bound give
\[
N_1(q_\chi)>
\frac{P(h,j)}{294(15c+11j)p^2},
\qquad P(h,j)=\sum_{i=0}^8 P_i(h)j^i,
\tag{10}
\]
with the following explicit coefficient identities:
\[
\begin{aligned}
32P_0/(h+1)^3={}&60h^7+660h^6+1365h^5+2368h^4+1076h^3-90h^2-41h+2,\\
32P_1/(h+1)^2={}&88h^7+3188h^6+7445h^5+10940h^4+5540h^3-938h^2-705h-118,\\
32P_2/(h+1)^2={}&-1260h^6+6016h^5+6063h^4+4086h^3-1024h^2-1030h-3,\\
32P_3/(h+1)={}&-6048h^6+3448h^5-253h^4-15330h^3-4104h^2+3770h+1237,\\
8P_4/(h+1)={}&-3115h^5+1245h^4-851h^3-2317h^2+1158h+112,\\
8P_5/(h+1)={}&-3570h^4+2395h^3+2733h^2+289h-1927,\\
8P_6/(h+1)={}&-2373h^3+2239h^2+3813h-3415,\\
2P_7/(1-h)={}&215h^2+199h-367,\\
P_8={}&\frac{33}{2}(1-h^2).
\end{aligned}
\tag{11}
\]
The displayed identities come simply from substituting \(q_\chi\),
\(V_2\), and \(L_+\) into (5) and collecting powers of j. Their
signs require only the following short estimates:
\[
P_0>\frac35,\quad P_1>-13,\quad P_2>-26,\quad
P_3>0,\quad P_4>0,\quad
P_5>-330,\quad P_6>-585,\quad P_7>-140,\quad P_8>0.
\tag{12}
\]
Here are explicit checks, to make (12) a hand inequality rather than
an unexplained coefficient sign assertion.

Let \(R_0=32P_0/(h+1)^3\). Its derivative is positive: its only
negative derivative terms are \(-180h-41\), while
\[
3228h^2-180h-41\ge
3228(6/25)^2-60-41>0.
\]
At \(h=6/25\), the four positive terms
\(2368h^4,1076h^3,1365h^5,660h^6\) exceed respectively
\(39/5,74/5,1,1/10\), whereas
\(90h^2+41h-2<131/10\). Thus \(R_0>53/5\), and
\[
P_0>\frac{31^3}{32\cdot25^3}\frac{53}{5}>\frac35.
\]

Let \(R_1=32P_1/(h+1)^2\). Its derivative is positive as well.
Indeed
\[
43760h^3+16620h^2-1876h-705
\]
is increasing on (3), because its derivative is greater than
\(33240(6/25)-1876>0\), and its value at \(6/25\) is positive.
The other terms in \(R_1'\) are positive. At \(6/25\), the three
positive terms \(5540h^3,10940h^4,7445h^5\) exceed
\(76,36,5\), while \(938h^2+705h+118<342\).
Therefore \(R_1>-225\). Since \((h+1)^2/32\le1/18\),
this implies \(P_1>-225/18>-13\).

For \(P_2\), discard its positive terms and use
\[
-P_2\le\frac1{18}
 \left(\frac{1260}{729}+\frac{1024}{9}+\frac{1030}{3}+3\right)<26.
\]
For \(P_3\) and \(P_4\), the required signs follow from
\[
\frac{6048}{729}+\frac{253}{81}+\frac{15330}{27}+\frac{4104}{9}
-3770\frac6{25}-1237<0,
\]
\[
\frac{3115}{243}+\frac{851}{27}+\frac{2317}{9}
-1158\frac6{25}-112<0.
\]
Finally, discarding positive terms and using \((h+1)/8\le1/6\)
gives
\[
-P_5\le\frac16(3570/81+1927)<330,
\quad
-P_6\le\frac16(2373/27+3415)<585,
\]
while \(-P_7\le367(1-6/25)/2<140\). The sign of \(P_8\)
is immediate.

Using (12) and \(0\le j\le1/30\), we conclude
\[
\begin{aligned}
P(h,j)
&>\frac35-13j-26j^2-330j^5-585j^6-140j^7\\
&\ge\frac35-\frac{13}{30}-\frac{26}{900}
       -\frac{1055}{30^5}
>\frac{2}{15}>0.
\end{aligned}
\tag{13}
\]
This proves \(N_1(q_\chi)>0\).

## 5. Contradiction

A concave function on a closed interval is at least the minimum of its
endpoint values. Equations (6)--(13) therefore give
\(N_1(q)>0\) for every q in (4), contradicting the required
\(N_1(q)<0\). This proves (2).

The implication in this note is conditional on (1). Establishing
\(t\ge1/3\) and \(j\le1/30\) for every actual remaining window
is still separate work. Once those two assertions are supplied, this
lemma supplies the chi hypothesis of
[MIXED_NONSHORT_FORWARD_CASIMIR_MONOTONICITY](MIXED_NONSHORT_FORWARD_CASIMIR_MONOTONICITY.md)
on the same actual fixed geometry and covector.
