# Actual-period audit of the sharper short upper-ratio exclusion

Date: 2026-11-08 UTC. **Accepted conclusion:** S2,
\(x<13/6\), follows from the existing actual-period interface,
the accepted variable-floor reduction, and the two new complete hand
terminal signs. This audit records the interface and the separate
mathematical acceptance below. It does not close H-S or H-A.

## 1. The exact object excluded

The [upper-ratio assembly](MIXED_SMALLER_SHORT_SHARP_RATIO_HAND_EXCLUSION.md)
starts with the actual eligible competitive finite normal mixed period
with at least six positive pieces, at a globally minimal active reverse
centre, whose chosen smaller adjacent turn lies on a short forward run.
All these conditions are inherited through the six-variable reduction.
The actual twisted state/frame and costate seam, original common PMP
covector, free initial state, genuine first/last switches, positive
arc durations and whole-period competitive budget are not altered.

The new algebra neither chooses a different covector nor constructs a
new physical period. Reflection, reversal and an equal-turn tie are
handled by the original choice of smaller adjacent turn; the scalar
proofs retain every weak order boundary they reach. No word-length
catalogue or local-window substitute is introduced.

## 2. Dependency chain, with no S1 or small-gap assumption

| Step | Exact input and conclusion |
| --- | --- |
| S0 | The actual object has \(x<12/5\). The positive-diagonal theorem gives \(D>0,E_L>0\) on the remaining actual domain. |
| Contradiction assumption | \(x\ge13/6\), so the whole argument lies in the closed scalar interval \([13/6,12/5]\). |
| Actual root | \(R_\tau=0\), \(w>3/4\), \(2<\tau<T\) for the original first outer root and original covector. |
| Variable-floor scalar | The positive weight \(2-7\tau/(4T)\) gives strict actual positivity before the envelope comparison. |
| Envelope/scale reduction | The accepted reduction produces a positive scalar at \(q=q_c\le1/7\) or \(q=1/7\le q_c\), with the original shape and norm fixed and \(2\le\widehat\tau\le T\). |
| Central terminal sign | The first face implies \(\alpha^2\le x(x+2)/6\), exactly the central theorem's hypothesis. Its incoming upper bound and strict scalar sign contradict the positive endpoint. |
| Outer terminal sign | The second face implies \(\alpha^2\ge x(x+2)/6\), exactly the outer theorem's hypothesis. The split at \(\alpha=3/2\) is exhaustive, and both terminal tests are strictly negative. |

The strong lower short order and the 9/8 upper short order have already
been established on the larger remaining domain. Neither S1
\((x>2)\) nor a displacement bound is used: the contradiction
assumption \(x\ge13/6\) itself supplies every lower ratio needed
by the new arguments. No upper or lower Casimir value is needed in
the terminal sign proofs.

## 3. Scale and norm comparisons retain their correct direction

The variable-floor reduction raises the actual combined root/floor
expression to its envelope. Its outgoing norm floor is incorporated
before that comparison, so the proof does not need to preserve that
floor separately at the envelope. At fixed normalized duration the
scale comparison is convex, and its zero-scale value is explicitly
negative. The independently reviewed \(\tau=2\) continuation is
strictly increasing and reaches one of the two positive scale caps.

At these endpoints the coefficient of the incoming norm in the
combined scalar is strictly positive. It is therefore correct to
insert the central ceiling \(u_C\), or the outer ceiling \(u_s\)
or \(u_v\), before applying the corresponding terminal theorem.
The actual incident norm ceiling need not hold after this replacement,
and none of the terminal proofs asserts it.

The beta, alpha and x motions made inside the terminal proofs are
comparisons of explicit scalar functions on their proved enlarged
domains. The original competitive upper cap, conserved covector,
physical cost and positive-period closure are never transferred to
those scalar shapes. Their only purpose is to upper-bound a scalar
whose actual antecedent was already proved positive.

## 4. Exhaustiveness and endpoint signs

The two scale faces are exhaustive by the accepted reduction. When
\(q_c=1/7\), both squared alpha inequalities hold, and both scalar
theorems include that equality. Both also include \(x=13/6\),
\(x=12/5\), \(\tau=2\), and \(\tau=T\) with strict negative
signs. The central enlarged alpha endpoints and the outer split
\(\alpha=3/2\) are included explicitly. Thus no equality boundary
or event ordering is left open by the assembly.

The central and outer arithmetic audits are
[CENTRAL_RATIO_HAND_AUDIT](MIXED_SMALLER_SHORT_CENTRAL_RATIO_HAND_AUDIT.md)
and [OUTER_RATIO_HAND_AUDIT](MIXED_SMALLER_SHORT_OUTER_RATIO_HAND_AUDIT.md).
They reconstruct every displayed finite polynomial and coefficient
bound from the original transport formulas. Those checks confirm
transcription; the published deductions use the explicit factor
specifications, complete lower-polynomial arrays, finite coefficient
norms and elementary sign arguments. The old large Bernstein minimum
claims and executable covers are not premises.

## 5. Acceptance and downstream scope

A separate second reading accepts both scalar signs and this
actual-period interface. It checked that the contradiction hypothesis
supplies the ratio interval independently of S1, that the two scale
faces exhaust the accepted comparison, and that every norm and shape
motion retains only its proved scalar inequality. The original common
covector, first-root data, positive durations and whole-period scope
are unchanged. All equality boundaries are covered. The completion
plan may therefore mark **S2 closed**
with the exact strict conclusion \(x<13/6\). The result does not
supply S1, a small displacement bound, a stronger Casimir floor,
root-to-shear monotonicity, or the physical completion-cost
contradiction. H-S and H-A retain their own completion conditions.
No Lean, Lake, typechecking or CI was run, and no kernel verification
is asserted.
