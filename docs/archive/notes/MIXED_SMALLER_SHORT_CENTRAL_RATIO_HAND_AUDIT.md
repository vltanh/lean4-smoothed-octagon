# Audit of the central terminal sign for the short upper-ratio bound

Date: 2026-11-08 UTC. **Result:** the
[CENTRAL_RATIO_HAND_SIGN](MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_SIGN.md)
proves the whole central scalar face for \(13/6\le x\le12/5\),
including every duration and boundary. The reconstruction and the
independent mathematical reading below are accepted. The
outer scale face, and hence S2 as a whole, remain separate obligations.

## 1. Exact statement and actual-period interface

The scalar theorem starts with the original order strip and the central
cap \(a^2\le x(x+2)/6\). Its variables \(a,b\) are exactly
\(\alpha,\beta\), and its scale is \(q=q_c=a^2/[x(x+2)+a^2]\).
The actual-to-scalar implication is the accepted
[variable-floor reduction](MIXED_SMALLER_SHORT_VARIABLE_FLOOR_REDUCTION.md).
That implication uses the original common PMP covector, positive arc
durations, genuine first outer root and strict outgoing norm floor
before making its scalar envelope comparison.

The new theorem inserts only the proved incoming ceiling \(u_C\).
The positive coefficient in u was established in the variable-floor
proof. The ceiling itself follows from the Gauss incoming identity,
the central shape inequality and the positive integral tail estimate,
with the details already printed in
[RATIO_SIGN_HAND_GAP](MIXED_SMALLER_SHORT_RATIO_SIGN_HAND_GAP.md).
All transport formulas in the new note agree with the original central
formulas after this one scalar substitution.

The theorem does not assign a common covector, outgoing norm floor,
competitive upper Casimir cap, physical cost or genuine switch to any
later scalar endpoint. This is essential when beta and x subsequently
move. The scalar theorem was proved on an explicit enlarged domain
that contains those comparisons.

## 2. Duration is bounded without guessing its maximizer

At fixed shape the exact derivative is

\[
G_\tau'=\left(1-\frac7{4T}\right)(w-3/4)
          -\frac{(\tau-2)^2}{4\tau^2}.
\]

Integrating with \(\tau\le T\) gives a cubic loss. Its unrestricted
maximum on \(\tau-2\ge0\) is an upper bound for the restricted duration
interval; no stationary root needs to be selected or transported.
The elementary inequality \(\sqrt A\le6A+1/24\) gives the rational
correction \(8TA^2+TA/18\) only when \(A\ge0\). If \(A\le0\),
\(G_2\) alone is an upper bound.

The proof explicitly retains these two alternatives. In particular,
it does not infer that the actual or artificial maximizing duration is
an endpoint. The weaker tangent estimate can be positive on part of
the central domain, which is why the cubic loss is retained.

## 3. Beta comparison and all enlarged-domain bounds

The original beta strip is inside

\[
x+\frac58(a-1)\le b\le
x+\frac{24x+51}{128}(a-1).
\]

The lower comparison is \(19x\ge40\). The upper comparison is the
single cubic

\[
96x^3-428x^2+457x+51
=6-11v+(220+96v)v^2>0,
\qquad v=x-9/4\ge-1/12.
\]

The central cap implies \(1\le a<4/3\). The enlarged set used by
the derivatives is therefore

\[
13/6\le x\le12/5,\quad 1\le a\le4/3,
\quad b=x+c(a-1),\quad5/8\le c\le7/8.
\]

All its denominators are positive. The displayed estimate
\(K-2a(a+b)\ge25/36\) verifies \(T>2\) on this entire enlarged
set. Thus the logarithm arguments are positive and below one at the
terminal duration two, including all endpoints used in the proof.

Appendix A proves \(G_{2,b}>1/16\) and \(w_b<0\) throughout this
set. When the duration correction is needed, its h is nonnegative.
It increases in h and decreases in k on \(0<k<1/2\). Consequently
moving beta down increases that correction, while moving beta up
increases \(G_2\). This justifies the two different beta endpoints
in \(F_0,F_1\). If the correction's h at the lower endpoint is
negative, that correction is not invoked; the \(F_0\) alternative
already applies. There is no unstated sign assumption in this case.

## 4. Exact-log x comparison and terminal signs

Appendix B proves both \(F_{j,x}<0\) while holding a fixed. The
logarithm is differentiated exactly at this step. No derivative of a
logarithm majorant is substituted for the derivative of the original
function. The positive clearing denominators are printed in factored
form, and the two global lower polynomials have all coefficients
printed. The first has only positive coefficients. The second has
positive coefficients through degree sixteen; its twelve negative
higher coefficients have the displayed elementary uniform tail bound
on \(0\le x-13/6<1/4\).

This permits x to decrease to 13/6 with a unchanged, even if the
resulting scalar point is outside the original central cap. The
comparison was proved on the larger rectangle for exactly that reason.

Only after reaching that edge is \(\log y\) replaced by
\(2z+2z^3/3\), with \(z=(y-1)/(y+1)<0\). The two terminal
polynomials have degrees 15 and 22, positive clearing denominators,
and complete printed coefficient vectors. Their signs follow from:

- One completed quadratic and an explicit remainder norm for \(P_0\).
- A centered norm on \(1\le a\le11/10\) for \(P_1\).
- A completed quadratic with only the negative higher terms retained
  on \(11/10\le a\le4/3\) for \(P_1\).

The shared endpoint \(a=11/10\), both endpoints in x, \(a=1,4/3\),
and \(\tau=2,T\) are included. Strict signs persist at every one.

## 5. Arithmetic transparency and independent reconstruction

This proof has a moderate amount of explicit exact arithmetic. It
replaces the former assertion of bounds on 51,840 transformed
coefficients by six finite polynomial specifications and directly
explained norm estimates. The complete lower-polynomial arrays have
13, 6, 16 and 29 coefficients. The two terminal coefficient vectors
have 16 and 23 entries. Every negative contribution is accounted for
by a printed norm rule and a displayed inequality. There is no hidden
coefficient minimum, interval subdivision or parameter search.

For transcription verification, a fresh exact reconstruction started
with the original formulas (3)--(4), independently of the earlier
construction expressions. It checked:

1. Both beta derivative identities and every coefficient of the two
   printed beta lower polynomials.
2. Both x derivative identities with their positive denominators and
   every coefficient of the two printed x lower polynomials.
3. Both terminal polynomial identities after the stated logarithm
   replacement, including their complete coefficient vectors.
4. All 55 displayed rational contribution bounds in the final norm
   table and the three stated column sums.

All identities agreed exactly. These computations are transcription
checks, not mathematical premises: the hand proof consists of the
finite product identities, the complete coefficients and the printed
norm/sign arguments. No Lean, Lake, typechecking or CI was run.

## 6. Consequence and remaining work

A separate second reading checked the enlarged beta interval, the
strict T>2 bound on its full rectangle, both alternatives in the
cubic duration estimate, and the directions of the two different
beta comparisons. It checked that the x derivatives are taken before
the logarithm replacement and on the entire rectangle needed by the
subsequent endpoint move. The finite norm rules, their sign arguments,
the three terminal estimates and all boundary inclusions are sound.
This accepts the scalar theorem and its actual-to-scalar interface.

The positive central endpoint supplied
by the variable-floor reduction is excluded. The remaining S2
terminal obligation is the outer face \(q=1/7\le q_c\), with the
same original shape, root and actual-to-scalar scope. This audit does
not mark S2, H-S or H-A complete.
