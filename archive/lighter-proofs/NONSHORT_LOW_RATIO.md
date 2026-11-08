# A small square proof for the low-ratio base quadratic

Date: 2026-11-08.

**Scope.** This replaces Section 4 of
[MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION](../../archive/notes/MIXED_NONSHORT_LOW_RATIO_HAND_EXCLUSION.md),
including its degree-14 discriminant and large coefficient table. It is a completed
subordinate replacement. The separate
[monotonicity proof](NONSHORT_LOW_RATIO_MONOTONICITY.md) and
[factored remainder proof](NONSHORT_LOW_RATIO_REMAINDER.md) supply the other
sign premises, and the [fourth-derivative bridge](NONSHORT_LOW_RATIO_LINK.md)
combines them into a replacement for the full unit-shape sign (10).

The caller is equation (15) of that note. It uses
\(\beta=j/[h(h+1)]\ge0\), and needs precisely
\[
 a_0(z)+\beta a_1(z)+\frac43\beta^2a_2(z)>0,
 \qquad 0\le z\le1.
\]
We prove the stronger margin
\[
\boxed{a_0+\beta a_1+\frac43\beta^2a_2>4
       \quad(0\le z\le1,\ \beta\ge0).}
\tag{1}
\]
We also prove \(a_0>0\) and \(a_2>0\). The original discriminant conclusion
for arbitrary real \(\beta\) is not retained: this caller needs only
\(\beta\ge0\). Its passage from the first line to the last line of (15)
therefore still closes, subject to its separate monotonicity premises.

The proof has three fixed rational intervals, at \(z=1/2\) and \(z=3/4\).
All identities below have at most 21 monomials, total degree at most eight,
and at most two variables. No transcendental estimate is needed here.

## 1. The original polynomials and integer lower bounds

These are the original three polynomials, printed in full:
\[
\begin{aligned}
a_0(z)={}&168+\frac29+\frac{19741}{9}z-\frac{864913}{243}z^2
 -\frac{632434}{2187}z^3+\frac{7868156}{6561}z^4\\
 &+\frac{9424115}{19683}z^5+\frac{437189}{6561}z^6
 -\frac{45152}{59049}z^7,\\
a_1(z)={}&\frac{17812}{27}+\frac{689290}{243}z
 -\frac{37970326}{2187}z^2+\frac{7854788}{2187}z^3
 +\frac{166227560}{19683}z^4\\
 &+\frac{51599650}{19683}z^5+\frac{50122106}{177147}z^6
 -\frac{51824}{19683}z^7,\\
a_2(z)={}&\frac{14324}{9}+\frac{115918}{81}z
 -\frac{30095420}{2187}z^2+\frac{3564514}{243}z^3
 +\frac{286749662}{19683}z^4\\
 &+\frac{24894044}{6561}z^5+\frac{20583334}{59049}z^6
 -\frac{429568}{177147}z^7.
\end{aligned}
\tag{2}
\]
Each has eight monomials and degree seven in one variable. Define the following
three degree-six polynomials, each with seven monomials:
\[
\begin{aligned}
A(z)={}&168+2193z-3560z^2-290z^3+1199z^4+478z^5+65z^6,\\
B(z)={}&659+2836z-17362z^2+3591z^3+8445z^4+2621z^5+280z^6,\\
C(z)={}&2122+1908z-18349z^2+19558z^3+19424z^4+5058z^5+461z^6.
\end{aligned}
\tag{3}
\]
The three exact error identities are
\[
\begin{aligned}
59049(a_0-A)={}&13122+26244z+40581z^2+48492z^3\\
 &+13653z^4+46923z^5+51364z^6+45152z^6(1-z),\\
177147(a_1-B)={}&124659+103518z+29808z^2+102951z^3\\
 &+41625z^4+94563z^5+54530z^6+466416z^6(1-z),\\
531441\left(\frac43a_2-C\right)={}&39366+61236z+494829z^2+199746z^3\\
 &+277848z^4+528174z^5+287435z^6+1718272z^6(1-z).
\end{aligned}
\tag{4}
\]
Every summand on the right is nonnegative on \([0,1]\), and each
constant is positive. Hence \(a_0>A\), \(a_1>B\), and \(4a_2/3>C\).
Each identity in (4), after its displayed denominator is cleared and its
last product is expanded, has eight monomials and degree seven.

Put
\[
 Q(z,\beta)=A(z)+\beta B(z)+\beta^2C(z).
\tag{5}
\]
This is a polynomial of 21 monomials and total degree eight in the two
variables \((z,\beta)\). The formula (3) prints all of its coefficients.
For \(\beta\ge0\), (4) gives
\[
 a_0+\beta a_1+\frac43\beta^2a_2>Q(z,\beta).
\tag{6}
\]
It remains to prove \(Q>4\).

## 2. First interval: \(0\le z\le1/2\)

Write \(z=r/2\), so \(0\le r\le1\). The following is an exact identity:
\[
\begin{aligned}
64\{Q(r/2,\beta)-4\}={}&(1-r)^{6}\bigl(10496+42176\beta+135808\beta^2\bigr)\\
&+r^1(1-r)^{5}\bigl(133152+343808\beta+875904\beta^2\bigr)\\
&+r^2(1-r)^{4}\bigl(451360+808608\beta+2048816\beta^2\bigr)\\
&+r^3(1-r)^{3}\bigl(681520+668600\beta+2308848\beta^2\bigr)\\
&+r^4(1-r)^{2}\bigl(515276(1-\beta)^2+1023924\beta+917988\beta^2\bigr)\\
&+r^5(1-r)^{1}\bigl(189604(1-\beta)^2+133842\beta+391088\beta^2\bigr)\\
&+r^6\bigl(27209(1-2\beta)^2+32002\beta+39181\beta^2\bigr)
\end{aligned}
\tag{7}
\]
This identity has 21 monomials and total degree 8 in \((r,\beta)\). The largest absolute coefficient of either fully expanded side is 293584.

## 3. Second interval: \(1/2\le z\le3/4\)

Write \(z=1/2+r/4\), so \(0\le r\le1\). Again there is the exact identity:
\[
\begin{aligned}
16384\{Q(1/2+r/4,\beta)-4\}={}&(1-r)^{6}\bigl(6965504(1-2\beta)^2+8192512\beta+10030336\beta^2\bigr)\\
&+r^1(1-r)^{5}\bigl(38420224(1-2\beta)^2+8062208\beta+113021696\beta^2\bigr)\\
&+r^2(1-r)^{4}\bigl(86043584(1-3\beta)^2+87542912\beta+38739200\beta^2\bigr)\\
&+r^3(1-r)^{3}\bigl(25042336(2-7\beta)^2+56207616\beta+134756576\beta^2\bigr)\\
&+r^4(1-r)^{2}\bigl(16033756(2-9\beta)^2+54476112\beta+8773844\beta^2\bigr)\\
&+r^5(1-r)^{1}\bigl(21639024(1-5\beta)^2+1102832\beta+135017472\beta^2\bigr)\\
&+r^6\bigl(3084740(1-6\beta)^2+2261312\beta+34946020\beta^2\bigr)
\end{aligned}
\tag{8}
\]
This identity has 21 monomials and total degree 8 in \((r,\beta)\). The largest absolute coefficient of either fully expanded side is 48003776.

## 4. Third interval: \(3/4\le z\le1\)

Write \(z=3/4+r/4\), so \(0\le r\le1\). Again there is the exact identity:
\[
\begin{aligned}
4096\{Q(3/4+r/4,\beta)-4\}={}&(1-r)^{6}\bigl(771185(1-6\beta)^2+565328\beta+8736505\beta^2\bigr)\\
&+r^1(1-r)^{5}\bigl(3844464(1-7\beta)^2+3377644\beta+80612976\beta^2\bigr)\\
&+r^2(1-r)^{4}\bigl(8207296(1-7\beta)^2+1102368\beta+424686736\beta^2\bigr)\\
&+r^3(1-r)^{3}\bigl(10227072(1-6\beta)^2+1142464\beta+986319488\beta^2\bigr)\\
&+r^4(1-r)^{2}\bigl(8370944(1-4\beta)^2+11234048\beta+1111587840\beta^2\bigr)\\
&+r^5(1-r)^{1}\bigl(4297728(1-\beta)^2+6782976\beta+604707840\beta^2\bigr)\\
&+r^6\bigl(1019904+4382720\beta+123625472\beta^2\bigr)
\end{aligned}
\tag{9}
\]
This identity has 21 monomials and total degree 8 in \((r,\beta)\). The largest absolute coefficient of either fully expanded side is 49996722.

## 5. Signs, strictness, and the caller

In (7)–(9), every factor \(r^i(1-r)^{6-i}\) is nonnegative.
Every parenthesis has a positive constant or a positive multiple of a square,
a positive coefficient of \(\beta\), and a positive coefficient of \(\beta^2\).
When \(\beta=0\), its constant or its square is strictly positive.
When \(\beta>0\), its linear term is strictly positive. Thus each parenthesis
is strictly positive for all \(\beta\ge0\).

For \(0<r<1\), all seven outer factors are positive. At \(r=0\), the first
factor is one; at \(r=1\), the last factor is one. Hence each right side
is strictly positive on the whole closed interval, including endpoints.
The three intervals cover \([0,1]\), so \(Q>4\). Equation (6) proves (1).

Setting \(\beta=0\) also gives \(A(z)>4\), so \(a_0(z)>0\).
The coefficient of \(\beta^2\) on each right side is a sum of the same
nonnegative outer factors times strictly positive constants: the displayed
quadratic term is positive, and a square adds a nonnegative quadratic
coefficient. Therefore \(C(z)>0\), whence \(a_2(z)>0\).

In the caller's notation, its independently established
\(A_i(h,z)\ge a_i(z)\), \(h+1\ge4/3\), and \(\beta\ge0\) now give
\[
\begin{aligned}
 A_0(h,z)+\beta A_1(h,z)+(h+1)\beta^2A_2(h,z)
 &\ge a_0(z)+\beta a_1(z)+\frac43\beta^2a_2(z)\\
 &>4.
\end{aligned}
\tag{10}
\]
The positivity of \(a_2\) justifies the first inequality's use of
\(h+1\ge4/3\). This replaces the original use of a degree-14 discriminant
by comparisons and three bivariate degree-eight identities.

## 6. Expansion budget and connection to the full sign

| Item | Variables | Monomials after clearing denominators | Total degree |
| --- | --- | ---: | ---: |
| Each original polynomial in (2) | \(z\) | 8 | 7 |
| Each lower polynomial in (3) | \(z\) | 7 | 6 |
| Each error identity in (4) | \(z\) | 8 | 7 |
| \(Q\) in (5) | \(z,\beta\) | 21 | 8 |
| Each of (7), (8), (9) | \(r,\beta\) | 21 | 8 |

All displayed coefficients have at most ten digits. The largest coefficient
after expanding and clearing denominators in the three original polynomials
is 3,075,596,406. The signs of the three error identities are visible term
by term; the three final signs are visible products and square completions.
No coefficient file, coefficient minimum, root isolation, or program execution
is a premise. The identities can be checked directly by multiplying the
printed factors, within the stated budget.

These are **replacement identities for the base quadratic only**. They do
not prove the \(h\)-derivative signs or the three-variable remainder in the
original low-ratio note. Those separate results and their connection to
the original rational residual are proved in the companion notes linked
above. The bridge uses four boundary calculations and a fourth derivative
before expanding; a global expansion of the original polynomial is outside
the proposed verification interface. No Lean check or performance claim is made.

An independent review parsed the printed square identities from this
document and verified all three identities, their stated expansion sizes,
the three error identities, positivity at every closed interval endpoint,
and the exact use of the nonnegative caller parameter. The review does
not by itself establish the separate derivative or remainder premises.
