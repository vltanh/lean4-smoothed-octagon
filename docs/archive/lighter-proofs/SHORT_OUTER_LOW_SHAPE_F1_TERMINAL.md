# Outer B F1: the lower-shape terminal curves

## Statement

Use the unchanged \(F_1\) and fixed logarithm majorant of
[the beta note](SHORT_OUTER_BETA.md). For each
\[
 (C,u)\in\{1/2,10/13\}\times\{3/4,19/25\},
\]
put \(\beta=x+C(a-1)\), and use the lower shape from
[the reciprocal-shape reduction](SHORT_OUTER_RECIPROCAL_LOW_SHAPE.md):
\[
 a_*(x)=1\quad(3/2\le x\le5/3),\qquad
 a_*(x)=(6x+3)/13\quad(5/3\le x\le2).
\]
This note proves
\[
 \boxed{F_1(x,a_*(x),\beta,u)\ge1597/144000000>0.}
 \tag{1}
\]
The exact derivative source on the second piece, including every source
polynomial and its small verification interface, is printed in
[the companion source note](SHORT_OUTER_LOW_SHAPE_F1_SOURCE.md).
The \(a=6/5\) comparison is a separate terminal. Together these two
terminals and the reciprocal-shape reduction prove the actual B \(F_1\) sign.

## 1. The same logarithm bound, differentiated

Write
\[
 \ell(y)=2s+\frac23s^3,\qquad s=\frac{y-1}{y+1}.
\]
This is the single majorant already used in \(F_1\).
Its exact derivative identity is
\[
 y\ell'(y)=1-s^4.
 \tag{2}
\]
After clearing \((y+1)^4\), this is a five-monomial, degree-four identity.
It implies
\[
 \ell'(y)\ge\frac{399}{400y}
 \tag{3}
\]
on either range used below: \(5/7\le y\le1\), where \(|s|\le1/6\),
and hence \(s^4\le1/1296<1/400\).
No new approximation to the logarithm is introduced.

## 2. The first piece a=1

Here \(\beta=x\), independently of \(C\), and \(y=2(x+1)/7\).
Let \(Q=F_1+(7/96)\ell(y)\), \(v=x-3/2\), and \(S=x+1\).
The two complete derivative identities are
\[
\begin{aligned}
 -Q'+\frac{7\cdot399}{96\cdot400S}
 =\frac1{115200S^3}\bigl[&
 10800v^5+84625v^4+227550v^3\\
 &+\tfrac{458133}{2}v^2+\tfrac{174715}{2}v+\tfrac{70725}{16}\bigr]
 \qquad(u=3/4),
\end{aligned}
\]
\[
\begin{aligned}
 -Q'+\frac{7\cdot399}{96\cdot400S}
 =\frac1{2880000S^3}\bigl[&
 273600v^5+2152224v^4+5837040v^3\\
 &+6028875v^2+2494075v+\tfrac{943875}{4}\bigr]
 \qquad(u=19/25).
\end{aligned}
\]
Each polynomial has six monomials and degree five. All its coefficients
are positive, so (3) proves \(F_1'<0\) on \([3/2,5/3]\).
It remains to check \(x=5/3\).

At this point the exact source inputs are
\[
 \lambda=1,\quad \delta=4/9,\quad v=337/441,\quad B/a=8/3,
\]
\[
 E=55/168\ (u=3/4),\qquad E=1487/4200\ (u=19/25),
 \qquad \ell(16/21)=-41320/151959.
\]
Use the grid \(M=100000\), rounding after every multiplication.
The common input bounds are
\[
 76417\le Mv\le76418,\quad
 44444\le M\delta\le44445,\quad
 M\ell\le-27191,\quad M\delta^2\le19754.
\]
For \(u=3/4\), \(32738\le ME\le32739\); for \(u=19/25\),
\(35404\le ME\le35405\).
Using
\[
 \Gamma=\frac{49}{144}\lambda^2(uv-E^2/4),\quad
 w=\lambda^2v+\delta^2u-\delta\lambda E,\quad
 E_L=2\delta u-\lambda E,
 \tag{4}
\]
the complete directed product bounds are
\[
\begin{aligned}
 Muv&\ge57312,& ME^2&\le10719,& M(uv-E^2/4)&\ge54632,\\
 M\delta^2u&\le14816,&M\delta E&\ge14550,&
 Mw&\le76684,\quad ME_L\ge33927
 \qquad(u=3/4),
\end{aligned}
\]
\[
\begin{aligned}
 Muv&\ge58076,& ME^2&\le12536,& M(uv-E^2/4)&\ge54942,\\
 M\delta^2u&\le15014,&M\delta E&\ge15734,&
 Mw&\le75698,\quad ME_L\ge32149
 \qquad(u=19/25).
\end{aligned}
\]
All integer products here have at most ten digits.

Use the exact form
\[
 R_1=\frac{7w-17/4}{B/a}-E_L+(u-1)B/a+6/7+\ell,
 \qquad F_1=\Gamma-\frac7{96}R_1-\frac{9193}{50000}.
 \tag{5}
\]
The two upper bounds for \(MR_1\) are explicitly
\[
 41921-33927-66666+85715-27191=-148,
\]
\[
 39333-32149-64000+85715-27191=1708.
\]
Together with (4), these give respectively
\[
 F_1\ge15469/7200000,\qquad F_1\ge37/20000.
 \tag{6}
\]
Both exceed the bound in (1).

## 3. Pair the B pole with the logarithm on the second piece

Now \(a=(6x+3)/13\), \(T=2x+1\), \(S=x+1\), and \(B=a+\beta\).
The source note gives
\[
 Q'=R_{ij}'+V\,B'/B^2,
\]
with \(V<507/10000\) for \(C=1/2\), and
\(V<157/5000\) for \(C=10/13\). Also
\[
 k_C=aB'-Ba'=(3+6C)/13>0,\qquad
 \frac{d}{dx}\log\!\left(\frac{2B}{7a}\right)=\frac{k_C}{aB}.
\]
The logarithm argument increases from \(16/21\); its largest value is
\(158/195<1\), so (3) applies.

For \(C=1/2\), put \(V_+=507/10000\), \(\epsilon=0\). The exact identity is
\[
 \frac7{96}\frac{399}{400}k_CB
       -V_+B'a-\epsilon aB^2
 =\frac3{13520000}(77561x-112507)>0.
 \tag{7}
\]
The two-monomial linear polynomial has value \(50284/3>0\) at \(5/3\)
and increases.

For \(C=10/13\), put \(V_+=157/5000\), \(\epsilon=1/200\). Then
\[
 \frac7{96}\frac{399}{400}k_CB
       -V_+B'a-\epsilon aB^2
 =\frac3{118813760000}P_C(x),
 \tag{8}
\]
\[
 P_C=-301596800x^3-30945600x^2+2070765757x-1136357459.
 \tag{9}
\]
This four-monomial cubic is concave, because
\[
 P_C''=-2947200(614x+21)<0.
 \tag{10}
\]
Its endpoint values are \(22482287672/27\) and \(468617255\), both
positive. Equations (7)--(10) therefore prove, for the appropriate
\(\epsilon\),
\[
 V\frac{B'}{B^2}
 -\frac7{96}\frac{d}{dx}\ell\!\left(\frac{2B}{7a}\right)<-\epsilon.
 \tag{11}
\]
Every expanded identity in this step is univariate of degree at most three.

## 4. Four degree-eight derivative signs

The affine derivative of the polynomial part of each \(R_{ij}\) decreases
in \(x\). Its value at \(x=5/3\) is, respectively,
\[
 3/176,\quad118/6875,\quad177/9824,\quad13889/767500.
\]
Round these up, and round each proper-fraction coefficient in the direction
needed for an upper derivative bound. Together with (11), this gives
\(F_1'<U_{ij}\), where the complete rational bounds are
\[
\begin{aligned}
 10^6U_{00}={}&17046-\frac{2\cdot14856859}{T^2}
 +\frac{4\cdot10756574}{T^3}-\frac{6\cdot5443232}{T^4}
 +\frac{8\cdot774767}{T^5}\\
 &+\frac{7183835}{S^2}+\frac{2\cdot1065866}{S^3},
\end{aligned}
\]
\[
\begin{aligned}
 10^6U_{01}={}&17164-\frac{2\cdot14874067}{T^2}
 +\frac{4\cdot10786967}{T^3}-\frac{6\cdot5451325}{T^4}
 +\frac{8\cdot767896}{T^5}\\
 &+\frac{7183835}{S^2}+\frac{2\cdot1065866}{S^3},
\end{aligned}
\]
\[
\begin{aligned}
 10^6U_{10}={}&13018-\frac{2\cdot14828351}{T^2}
 +\frac{4\cdot10979542}{T^3}-\frac{6\cdot5479537}{T^4}
 +\frac{8\cdot774767}{T^5}\\
 &+\frac{7129285}{S^2}+\frac{2\cdot1065866}{S^3},
\end{aligned}
\]
\[
\begin{aligned}
 10^6U_{11}={}&13097-\frac{2\cdot14849157}{T^2}
 +\frac{4\cdot11013281}{T^3}-\frac{6\cdot5489911}{T^4}
 +\frac{8\cdot767896}{T^5}\\
 &+\frac{7129285}{S^2}+\frac{2\cdot1065866}{S^3}.
\end{aligned}
\]
The constants in the last two lines already include the loss of \(1/200\).
Every scalar rounding is directly from a fraction printed in the source
note. It may be checked by six digits of ordinary long division: divide
off the integer part first, then multiply the remainder by ten at each
step. The largest denominator is \(12937320000\), so this requires no
integer product exceeding twelve digits; multiplying the original
numerator by \(10^6\) at once is unnecessary.

Let \(H_{ij}=-10^6T^5S^3U_{ij}\). Its four complete polynomial identities are
\[
\begin{aligned}
 H_{00}={}&-545472x^8-3000096x^7+735888x^6+15374328x^5\\
           &+10380576x^4-17811944x^3-7312198x^2+10380839x+3816065,
\end{aligned}
\]
\[
\begin{aligned}
 H_{01}={}&-549248x^8-3020864x^7+962128x^6+16061880x^5\\
           &+10750896x^4-18315420x^3-7893026x^2+10245739x+3832317,
\end{aligned}
\]
\[
\begin{aligned}
 H_{10}={}&-416576x^8-2291168x^7+3701008x^6+18087320x^5\\
           &+3323828x^4-34699474x^3-21157280x^2+5366155x+3143585,
\end{aligned}
\]
\[
\begin{aligned}
 H_{11}={}&-419104x^8-2305072x^7+4001040x^6+19001920x^5\\
           &+3999862x^4-34979391x^3-21628915x^2+5271068x+3167374.
\end{aligned}
\]
Each has nine monomials and degree eight. No factor involving \(B\)
remains in this expansion.

Put \(v=2-x\in[0,1/3]\), and \(J_{ij}(v)=H_{ij}(2-v)\).
The complete shifts are
\[
\begin{aligned}
 J_{00}={}&-545472v^8+11727648v^7-102358320v^6+472174536v^5\\
           &-1242678384v^4+1859591720v^3-1452041014v^2
                          +431802449v+34344823,
\end{aligned}
\]
\[
\begin{aligned}
 J_{01}={}&-549248v^8+11808832v^7-102845744v^6+472208264v^5\\
           &-1231902304v^4+1811828828v^3-1358175946v^2
                          +343180781v+66520939,
\end{aligned}
\]
\[
\begin{aligned}
 J_{10}={}&-416576v^8+8956384v^7-75031856v^6+316584744v^5\\
           &-701834652v^4+722013042v^3-100523820v^2
                          -315267891v+120578023,
\end{aligned}
\]
\[
\begin{aligned}
 J_{11}={}&-419104v^8+9010736v^7-75209616v^6+314370240v^5\\
           &-680735178v^4+644611983v^3+44851875v^2
                          -453516828v+173144674.
\end{aligned}
\]
Each shift identity has nine monomials and degree eight.

### The two C=1/2 signs by concavity

The complete second derivatives are
\[
\begin{aligned}
 J_{00}''={}&-30546432v^6+492561216v^5-3070749600v^4
                  +9443490720v^3\\
             &-14912140608v^2+11157550320v-2904082028,
\end{aligned}
\]
\[
\begin{aligned}
 J_{01}''={}&-30757888v^6+495970944v^5-3085372320v^4
                  +9444165280v^3\\
             &-14782827648v^2+10870972968v-2716351892.
\end{aligned}
\]
These have seven monomials and degree six.
In each expression, the quadratic consisting of its constant, linear
and quadratic terms increases on \([0,1/3]\): its derivative at the
right endpoint is respectively \(1216123248\) and \(1015754536\),
and its derivative is decreasing. Bound this quadratic and the two
remaining positive terms at \(v=1/3\), discarding the negative fourth
and sixth powers. The resulting upper bounds are
\[
 J_{00}''\le-4410154652/9<0,\qquad
 J_{01}''\le-31055862460/81<0.
 \tag{12}
\]
Thus both \(H_{00},H_{01}\) are concave. Their values at \(x=2\) are
\(34344823\) and \(66520939\), and their left endpoint bounds are
printed below. Positivity at both endpoints proves positivity throughout.

### The two C=10/13 signs by monotonicity

The complete first derivatives of the shifted polynomials are
\[
\begin{aligned}
 J_{10}'={}&-3332608v^7+62694688v^6-450191136v^5+1582923720v^4\\
            &-2807338608v^3+2166039126v^2-201047640v-315267891,
\end{aligned}
\]
\[
\begin{aligned}
 J_{11}'={}&-3352832v^7+63075152v^6-451257696v^5+1571851200v^4\\
            &-2722940712v^3+1933835949v^2+89703750v-453516828.
\end{aligned}
\]
These have eight monomials and degree seven.
Discard all negative nonconstant terms and bound the positive terms
at \(v=1/3\). This gives
\[
 J_{10}'\le-40072115165/729<0,\qquad
 J_{11}'\le-137965308541/729<0.
 \tag{13}
\]
Their minimum is therefore at \(v=1/3\), or \(x=5/3\).

### All four left endpoints

The following downward Horner chains evaluate the printed \(H\) polynomials
at \(x=5/3\). Each next integer is the floor of \(5/3\) times the
previous one plus the next printed coefficient:
\[
\begin{aligned}
 H_{00}:{}&
 -545472,-3909216,-5779472,5741874,19950366,15438666,
 18418912,41079025,72281106;\\
 H_{01}:{}&
 -549248,-3936278,-5598336,6731320,21969762,18300850,
 22608390,47926389,83709632;\\
 H_{10}:{}&
 -416576,-2985462,-1274762,15962716,29928354,15181116,
 4144580,12273788,23599898;\\
 H_{11}:{}&
 -419104,-3003579,-1004925,17327045,32878270,19817725,
 11400626,24272111,43620892.
\end{aligned}
\]
All four final integers are positive. The preceding derivative arguments
prove \(H_{ij}>0\), hence \(U_{ij}<0\) and
\[
 \boxed{\frac{d}{dx}F_1(x,(6x+3)/13,\beta,u)<0.}
 \tag{14}
\]

## 5. The four endpoint values at x=2

At \(x=2,a=15/13\), the exact common inputs are
\[
 \lambda=1519/1575,\quad v=1794277/2307361,
\]
\[
 E=2545/18228\ (u=3/4),\qquad E=19324/113925\ (u=19/25).
\]
For \(C=1/2\) the other inputs are
\[
 \delta=476/1575,\quad B/a=14/5,\quad \ell(4/5)=-488/2187.
\]
For \(C=10/13\) they are
\[
 \delta=6034/20475,\quad B/a=553/195,\quad
 \ell(158/195)=-27764504/131960931.
\]
These fractions are obtained directly from the original source, not from
the partial-fraction derivative decomposition.

Use the grid \(M=10^6\), rounding after each product.
The common input and square bounds are
\[
 964444\le M\lambda\le964445,\quad
 777631\le Mv\le777632,\quad
 930152\le M\lambda^2\le930155,
\]
\[
 139620\le ME\le139621\ (u=3/4),\qquad
 169620\le ME\le169621\ (u=19/25).
\]
For \(C=1/2\),
\[
 302222\le M\delta\le302223,\quad
 M\delta^2\le91339,\quad M\delta\lambda\ge291476,\quad
 M\ell\le-223136.
\]
For \(C=10/13\),
\[
 294700\le M\delta\le294701,\quad
 M\delta^2\le86849,\quad M\delta\lambda\ge284221,\quad
 M\ell\le-210399.
\]
Every scalar division can be checked by successive decimal remainders.
All products used below are at most twelve digits.

The two gamma lower bounds from (4) are obtained by the complete chains
\[
 Muv\ge583223,\quad ME^2\le19495,\quad
 M(uv-E^2/4)\ge578349,\quad
 M\lambda^2(uv-E^2/4)\ge537952
 \quad(u=3/4),
\]
\[
 Muv\ge590999,\quad ME^2\le28772,\quad
 M(uv-E^2/4)\ge583806,\quad
 M\lambda^2(uv-E^2/4)\ge543028
 \quad(u=19/25).
\]
Thus \(\Gamma\ge49g/(144M)\), with \(g=537952\) or \(543028\).

For the w and \(E_L\) bounds, the common upper product is
\(M\lambda^2v\le723319\).
The remaining complete product calculations are
\[
\begin{aligned}
 Mw&\le723319+68505-40695=751129,& ME_L&\ge318676
 &&(C=1/2,u=3/4),\\
 Mw&\le723319+69418-49440=743297,& ME_L&\ge295786
 &&(C=1/2,u=19/25),\\
 Mw&\le723319+65137-39682=748774,& ME_L&\ge307393
 &&(C=10/13,u=3/4),\\
 Mw&\le723319+66006-48209=741116,& ME_L&\ge284353
 &&(C=10/13,u=19/25).
\end{aligned}
\]
The second and third terms in each w line are respectively the upward
bound for \(M\delta^2u\) and the downward bound for \(M\delta\lambda E\).
For \(E_L\), use
\(\lfloor2(M\delta)_{\rm lo}(Mu)/M\rfloor
 -\lceil(M\lambda)_{\rm hi}(ME)_{\rm hi}/M\rceil\).

Substitution in (5), with upward rounding of each remaining term, gives
the four complete \(MR_1\) upper bounds
\[
\begin{aligned}
 &359966-318676-700000+857143-223136=-24703,\\
 &340386-295786-672000+857143-223136=6607,\\
 &349596-307393-708974+857143-210399=-20027,\\
 &330694-284353-680615+857143-210399=12470.
\end{aligned}
\]
For instance the last first term is
\(\lceil(7\cdot741116-17M/4)/(553/195)\rceil=330694\).
Use the same formula for each of the other pole terms.

Putting these bounds over \(288M\), the four lower numerators for \(F_1\)
are respectively
\[
 286379,\quad126317,\quad188183,\quad3194.
 \tag{15}
\]
They are computed by the small integer expression
\(98g-21(MR_1)_{\rm up}-9193\cdot5760\).
Their minimum is \(3194\), proving
\[
 F_1(2,15/13,\beta,u)\ge1597/144000000>0.
 \tag{16}
\]
Together with monotonicity (14) and the first-piece bounds (6), this proves (1).

## Size and margin

All required expanded identities are univariate of degree at most eight,
with at most nine monomials. The largest derivative-polynomial coefficient
is \(14912140608\); the derivative-source scalar checks in the companion
have largest numerator \(192108297503\). The largest grid product in
Section 5 is \(964445^2=930154158025\), twelve digits. No full degree-nine
or degree-eleven numerator is an identity premise.

The simpler 13-denominator chord reduces endpoint slack relative to the
97-denominator chord. The explicit certified margin here is
\(1597/144000000\), about \(1.11\cdot10^{-5}\). The proof retains the same
low-degree logarithm majorant; it does not claim an increased margin or
require an additional logarithm series.
