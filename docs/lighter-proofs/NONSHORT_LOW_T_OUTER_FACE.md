# The outer-gap unit face for the new low-t residual

## Exact face and reduction

This proves another boundary face of the new residual in
[NONSHORT_LOW_T_SHAPE](NONSHORT_LOW_T_SHAPE.md):
\[
\boxed{G_n(t,x,1+y,1)>0}
\]
when
\[
j=5h/7,\quad h=1-2t\in[1/4,1/3],\quad x=h+j=12h/7,
\quad0\le y\le\frac{h-j}{1+2j}.
\tag{1}
\]
It suffices to prove the sign on the enlarged domain
\[
\frac37\le x\le\frac47,\qquad
 t=\frac{12-7x}{24},\qquad j=5x/12,\qquad0\le y\le2/31.
\tag{2}
\]
The upper bound for y enlarges the actual face and is sufficient here.

Put W=1+x, D=17x+76, q=1+y and define the positive normalization
\[
S=96q(q+1)W^3D\,G_n=\sum_{i=0}^6 C_i(x)y^i.
\tag{3}
\]
We prove \(S(x,0)>10\) and \(S_y>500\) on (2). Thus S>0.
This does not supply the still-required three-dimensional reduction in h.

The point of the verification order below is that the C_i may contain
factored powers of degree ten, while their **second derivatives** have degree
at most eight. Differentiate before expanding, and check two scalar boundary
values. No degree-ten polynomial identity is expanded.

## 1. Source cancellation and small second-derivative interface

Use exactly N and the transported polynomial in Section 2 of the shape note,
with the substitutions for t and j in (2). Before replacing the scalar norm v
and logarithm ell, their affine dependence is
\[
G(v,\ell)=\frac{\mathscr C}{3981312qW^2}
 +\frac{\mathscr A}{6912qW}v
 +\frac{\mathscr B}{165888(q-1)W}\ell.
\tag{4}
\]
Here \(\mathscr A=\sum_{i=0}^4 a_iq^i\),
\(\mathscr B=\sum_{i=0}^4 b_iq^i\),
\(\mathscr C=\sum_{i=0}^5 c_iq^i\).
Every coefficient is printed below. Check (4) one q-coefficient at a time,
after separating the scalar coefficients of v and ell. The factor W in the
norm coefficient cancels before its denominator is cleared; the coefficient
identities have degree at most eight in x, with at most nine monomials.

\[
a_{0}=- 1428 x^{6} - 4272 x^{5} - 1080 x^{4} + 9840 x^{3} + 14700 x^{2} + 8352 x + 1728.
\]

(7 monomials, degree 6.)

\[
a_{1}=2016 x^{6} + 6036 x^{5} + 1116 x^{4} - 14436 x^{3} - 42924 x^{2} + 23328 x + 54720.
\]

(7 monomials, degree 6.)

\[
a_{2}=- 26376 x^{6} - 70452 x^{5} + 50112 x^{4} + 294492 x^{3} + 285264 x^{2} + 26208 x - 58752.
\]

(7 monomials, degree 6.)

\[
a_{3}=45360 x^{6} + 138456 x^{5} - 49944 x^{4} - 566400 x^{3} - 674208 x^{2} - 247392 x + 3456.
\]

(7 monomials, degree 6.)

\[
a_{4}=- 19572 x^{6} - 65652 x^{5} + 8371 x^{4} + 262056 x^{3} + 349776 x^{2} + 141696 x.
\]

(6 monomials, degree 6.)

\[
b_{0}=0.
\]

(The zero polynomial.)

\[
b_{1}=- 207060 x^{6} - 702264 x^{5} - 528612 x^{4} + 1323792 x^{3} + 2669328 x^{2} + 2988288 x + 1278720.
\]

(7 monomials, degree 6.)

\[
b_{2}=349860 x^{6} + 1186584 x^{5} + 893172 x^{4} - 2236752 x^{3} - 5172048 x^{2} - 4834944 x - 1679616.
\]

(7 monomials, degree 6.)

\[
b_{3}=- 128520 x^{6} - 440053 x^{5} - 341040 x^{4} + 816852 x^{3} + 1930896 x^{2} + 1480896 x + 393984.
\]

(7 monomials, degree 6.)

\[
b_{4}=- 14280 x^{6} - 44267 x^{5} - 23520 x^{4} + 96108 x^{3} + 180144 x^{2} + 108864 x + 20736.
\]

(7 monomials, degree 6.)

\[
c_{0}=616896 x^{7} + 2462400 x^{6} + 2312064 x^{5} - 3784320 x^{4} - 10601280 x^{3} - 9958464 x^{2} - 4354560 x - 746496.
\]

(8 monomials, degree 7.)

\[
c_{1}=5829264 x^{7} + 21295296 x^{6} + 16126560 x^{5} - 36838080 x^{4} - 73465200 x^{3} - 80901504 x^{2} - 82425600 x - 37490688.
\]

(8 monomials, degree 7.)

\[
c_{2}=- 5172132 x^{7} - 14574864 x^{6} - 21421140 x^{5} - 45494664 x^{4} - 66648096 x^{3} - 27044352 x^{2} + 33827328 x + 25712640.
\]

(8 monomials, degree 7.)

\[
c_{3}=- 5630520 x^{7} - 35671308 x^{6} - 25693248 x^{5} + 186964740 x^{4} + 461410992 x^{3} + 430159680 x^{2} + 168397056 x + 18413568.
\]

(8 monomials, degree 7.)

\[
c_{4}=4450152 x^{7} + 25114613 x^{6} + 23810340 x^{5} - 97608108 x^{4} - 264043296 x^{3} - 245083968 x^{2} - 88252416 x - 6469632.
\]

(8 monomials, degree 7.)

\[
c_{5}=50400 x^{7} + 241620 x^{6} + 408384 x^{5} - 53280 x^{4} - 1213056 x^{3} - 1867968 x^{2} - 1202688 x - 248832.
\]

(8 monomials, degree 7.)

The incoming bound is
\[
V_L=\frac{V_n}{576W^2D},\qquad
V_n=833x^4+8686x^3+48544x^2+73008x+32832.
\]
Insert the unchanged logarithm bound
\(L=(q-1)(q^2+10q+1)/(6q(q+1))\). Cancel q-1 before taking q=1.
The exact factored normalization is
\[
41472S=WD(q+1)\mathscr C+(q+1)V_n\mathscr A
       +4W^2D\mathscr B(q^2+10q+1).
\tag{5}
\]
This is field arithmetic applied to (4), not a large ring identity.
Each q-coefficient of the right side has degree at most ten in x.

Here are the complete coefficient expressions of S. Their high powers are
kept as powers; the next paragraph specifies their verification by second
derivatives and boundary values.

\[
C_{0}=\frac{x^{2} \left(7 x + 12\right) \left(839664 x^{6} + 3852576 x^{5} + 6557677 x^{4} + 1436064 x^{3} - 1763136 x^{2} + 212544 x - 84096\right)}{20736}.
\]

\[
C_{1}=\frac{x \left(3918432 x^{9} + 28337288 x^{8} + 113610616 x^{7} + 240616649 x^{6} + 172982660 x^{5} - 150470920 x^{4} - 189406560 x^{3} + 65953536 x^{2} + 80563200 x - 3502080\right)}{13824}.
\]

\[
C_{2}=- \frac{1749300 x^{10} + 20040951 x^{9} + 67011273 x^{8} + 113883629 x^{7} + 193086372 x^{6} + 409156629 x^{5} + 458561604 x^{4} + 67481712 x^{3} - 162272448 x^{2} - 49347072 x + 2101248}{10368}.
\]

\[
C_{3}=- \frac{30647736 x^{10} + 307805736 x^{9} + 1491719918 x^{8} + 3407982385 x^{7} + 2704960954 x^{6} - 2524770746 x^{5} - 6821823384 x^{4} - 5995244640 x^{3} - 2972059776 x^{2} - 895094784 x - 134479872}{20736}.
\]

\[
C_{4}=- \frac{10005996 x^{10} + 105811356 x^{9} + 550403496 x^{8} + 1271989063 x^{7} + 823237564 x^{6} - 1562499066 x^{5} - 3187955864 x^{4} - 2106999840 x^{3} - 450134400 x^{2} + 56411136 x + 18911232}{6912}.
\]

\[
C_{5}=- \frac{16303476 x^{10} + 167316324 x^{9} + 846173760 x^{8} + 1808944133 x^{7} + 650294256 x^{6} - 3143900820 x^{5} - 4146887520 x^{4} - 90720000 x^{3} + 2960266752 x^{2} + 1988195328 x + 403439616}{41472}.
\]

\[
C_{6}=- \frac{\left(x + 1\right) \left(3 x + 4\right) \left(7 x - 12\right) \left(8 x + 3\right) \left(17 x + 76\right) \left(2 x^{2} - 7 x - 24\right) \left(5 x^{2} + 12 x + 12\right)}{10368}.
\]

For each i, differentiate the products in (5) twice with respect to x before
collecting q-powers. Change q to 1+y by the degree-six binomial identity.
Compare the coefficient of y^i with the second derivative of the corresponding
printed C_i. These are seven univariate identities of degree at most eight,
with at most nine monomials. At x=1/2 the value and first derivative agree;
the fourteen scalar values are printed here:

\[
C_{0}(1/2)=\frac{150916711}{2654208},\qquad C_{0}'(1/2)=\frac{1369243441}{1327104}.
\]

\[
C_{1}(1/2)=\frac{647657033}{589824},\qquad C_{1}'(1/2)=\frac{3310460953}{884736}.
\]

\[
C_{2}(1/2)=\frac{4633414201}{5308416},\qquad C_{2}'(1/2)=- \frac{63928490111}{2654208}.
\]

\[
C_{3}(1/2)=\frac{320558440267}{2654208},\qquad C_{3}'(1/2)=\frac{741050237377}{1327104}.
\]

\[
C_{4}(1/2)=\frac{141235242977}{1769472},\qquad C_{4}'(1/2)=\frac{79454626315}{147456}.
\]

\[
C_{5}(1/2)=- \frac{459975142009}{10616832},\qquad C_{5}'(1/2)=- \frac{141016272197}{2654208}.
\]

\[
C_{6}(1/2)=- \frac{17034017}{8192},\qquad C_{6}'(1/2)=- \frac{1288201453}{221184}.
\]

For the remaining zeroth row, the full second derivative is
\[
3456C_0''=70531776x^7+345744000x^6+644942557x^5
+443722860x^4+16302720x^3-39339648x^2+1961856x-336384.
\]
It has eight monomials and degree seven. The other six second derivatives
are printed in Section 2.

The scalar checks use the printed factors of (5), coefficientwise in q,
so their coefficients are precisely the small rational numbers displayed
above. Equal second derivatives and these two boundary values imply the
coefficient identities by two integrations. This supplies the normalization
link without expanding a degree-ten row.

## 2. Curvature bounds for four coefficients

Put w=2x-1, so \(-1/7\le w\le1/7\). The following are the full second
derivative polynomials needed for C_1,C_2,C_5,C_6.
For each, an odd power lies between -7^{-i} and 7^{-i}, and an even
positive power lies between 0 and 7^{-i}. Termwise use of these bounds,
rounded down to integers, gives the explicitly stated lower sums.

\[
221184C_{1}''=22041180 w^{8} + 431365032 w^{7} + 3992950808 w^{6} + 21186294885 w^{5} + 64781585625 w^{4} + 107240102970 w^{3} + 84349479642 w^{2} + 24453767241 w + 2743495273.
\]

\[
C_{1}''\ge 12403-15795+0-1414+0-6+0-1+0=-4813.
\]

\[
110592C_{2}''=- 6559875 w^{8} - 172724706 w^{7} - 1650834990 w^{6} - 8239514920 w^{5} - 25882950650 w^{4} - 59386184930 w^{3} - 98610988894 w^{2} - 92305481780 w - 30490759703.
\]

\[
C_{2}''\ge -275705-119236-18198-1566-98-5-1-1-1=-414811.
\]

\[
442368C_{5}''=- 61138035 w^{8} - 1493002224 w^{7} - 16636772348 w^{6} - 97216535206 w^{5} - 297512391320 w^{4} - 417950957100 w^{3} - 88333071304 w^{2} + 286264156642 w + 108994677743.
\]

\[
C_{5}''\ge 246389-92446-4076-2755-281-14-1-1-1=146814.
\]

\[
165888C_{6}''=- 257040 w^{7} - 3544436 w^{6} - 2673069 w^{5} + 160989825 w^{4} + 915205830 w^{3} + 1751109702 w^{2} + 361804119 w - 1599003379.
\]

\[
C_{6}''\ge -9640-312+0-17+0-1-1-1=-9972.
\]

The first three identities have nine monomials and degree eight; the fourth
has eight monomials and degree seven. Their cleared coefficients have at
most twelve digits. In particular,
\[
C_1''>-5000,\quad C_2''>-415000,\quad C_5''>0,
\quad C_6''>-10000.
\tag{6}
\]

For C_3,C_4 it is shorter to retain positive factors. Their second derivatives
are the following nine-term, degree-eight polynomials:

\[
10368C_{3}''=- 1379148120 x^{8} - 11081006496 x^{7} - 41768157704 x^{6} - 71567630085 x^{5} - 40574414310 x^{4} + 25247707460 x^{3} + 40930940304 x^{2} + 17985733920 x + 2972059776.
\]

(9 monomials, degree 8.)

\[
1152C_{4}''=- 150089940 x^{8} - 1269736272 x^{7} - 5137099296 x^{6} - 8903923441 x^{5} - 4116187820 x^{4} + 5208330220 x^{3} + 6375911728 x^{2} + 2106999840 x + 150044800.
\]

(9 monomials, degree 8.)

For C_3 the negative high-degree part is x^4 times
\[
A_3(x)=1379148120x^4+11081006496x^3+41768157704x^2
       +71567630085x+40574414310.
\]
Its coefficients are positive. Since x<=4/7<3/5, direct Horner evaluation
at 3/5 gives A_3(x)<101500000000. Therefore
\[
x^4A_3(x)<\frac9{25}\,101500000000x^2
          <40930940304x^2.
\]
The latter term is one of the positive terms already printed in
10368C_3''. Every other term of degree at most three is positive.
Hence C_3''>0.

For a scalar check that keeps every integer small, upward-rounded Horner
bounds for A_3(3/5) are
\[
1379148120\ \longrightarrow\ 11908495368\ \longrightarrow\ 48913254925
\ \longrightarrow\ 100915583040\ \longrightarrow\ 101123764134.
\]
At each step multiply the previous bound by 3/5, add the next printed
coefficient, and round upward. The last number is below 101500000000;
every multiplication uses integers of at most twelve digits.

For C_4 the analogous polynomial is
\[
A_4(x)=150089940x^4+1269736272x^3+5137099296x^2
       +8903923441x+4116187820.
\]
Again its coefficients are positive; A_4(3/5)<12000000000, and
\[
x^4A_4(x)<\frac9{25}\,12000000000x^2
          <6375911728x^2.
\]
The remaining low-degree terms of 1152C_4'' are positive, so C_4''>0.
These two comparisons use five-term quartics and scalar multiplication;
they do not expand an additional high-degree identity.

The corresponding upward-rounded Horner bounds for A_4(3/5) are
\[
150089940\ \longrightarrow\ 1359790236\ \longrightarrow\ 5952973438
\ \longrightarrow\ 12475707504\ \longrightarrow\ 11601612323
<12000000000.
\]

## 3. Uniform coefficient bounds from curvature

Let delta=x-1/2, so |delta|<=1/14. The scalar values in Section 1 give
\[
\begin{gathered}
C_1(1/2)>1098,\quad |C_1'(1/2)|<3742,\\
C_2(1/2)>872,\quad |C_2'(1/2)|<24086,\\
C_3(1/2)>120000,\quad |C_3'(1/2)|<559000,\\
C_4(1/2)>79000,\quad |C_4'(1/2)|<539000,\\
C_5(1/2)>-43326,\quad |C_5'(1/2)|<53130,\\
C_6(1/2)>-2080,\quad |C_6'(1/2)|<5825.
\end{gathered}
\tag{7}
\]
If f''>=-M, Taylor's inequality gives
\(f(x)\ge f(1/2)+f'(1/2)\,delta-M\,delta^2/2\).
Use (6)--(7) and the two positive curvature bounds to obtain
\[
\begin{aligned}
C_1&>1098-3742/14-5000/392>800,\\
C_2&>872-24086/14-415000/392>-2000,\\
C_3&>120000-559000/14>0,\\
C_4&>79000-539000/14>0,\\
C_5&>-43326-53130/14>-50000,\\
C_6&>-2080-5825/14-10000/392>-3000.
\end{aligned}
\tag{8}
\]
These leave wide margins. Differentiating S in y and using 0<=y<=2/31,
\[
\begin{aligned}
S_y&=C_1+2C_2y+3C_3y^2+4C_4y^3+5C_5y^4+6C_6y^5\\
&>800-4000y-250000y^4-18000y^5\\
&\ge800-4000(2/31)-250000(2/31)^4-18000(2/31)^5>500.
\end{aligned}
\tag{9}
\]
The last polynomial has four monomials and degree five. Thus only the
lower event endpoint y=0 needs checking.

## 4. The y=0 sign

The printed C_0 is x^2(7x+12) times the sextic
\[
R(x)=839664x^6+3852576x^5+6557677x^4+1436064x^3
        -1763136x^2+212544x-84096,
\]
divided by 20736. Its derivative is
\[
R'(x)=5037984x^5+19262880x^4+26230708x^3
       +4308192x^2-3526272x+212544.
\]
Since x>=3/7,
\[
26230708x^3-3526272x
\ge x\{26230708(9/49)-3526272\}>0.
\]
Every other term of R' is positive. Thus R'>0, and
\[
R(3/7)=26867115/343>0.
\]
The two positive factors x^2 and 7x+12 increase too. The exact endpoint
value satisfies C_0(3/7)>10. Hence S(x,0)>10. Together with (9) this
proves the face sign (1).

## Budget and proof boundary

The source affine coefficient identities have degree at most eight.
The seven second-derivative identities are univariate of degree at most
eight, with at most nine monomials. The fourteen initial scalar values
have numerators of at most twelve digits. The displayed derivative sign
identities have coefficients of at most twelve digits, and the final event
comparison has four monomials of degree five. The high powers in the source
coefficient expressions remain factored until differentiation.

All displayed identities and rational bounds were checked exactly as
transcription checks. They are not sampling premises or coefficient tables.
No Lean compilation, typechecking, Lake or CI was run.

The full unit sign follows from the other two face signs and the proved
monotonicity in h. The [complete caller argument](NONSHORT_LOW_T_CALLER.md)
gives that combination, its unchanged actual domain, and the replacement
of the old multiplier call.
