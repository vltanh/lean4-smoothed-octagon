# The sharpened scale bound applies at every reverse centre

Date: 2026-11-08 UTC. Independent scope review of Section 2 of
[HAND_PROOF_REFINEMENTS](HAND_PROOF_REFINEMENTS.md).

**Accepted scope.** Every reverse-run centre of a competitive finite
normal geometric period satisfies
\[
\rho=\frac{a^2}{a^2+4}<\frac17,
\qquad a^2<\frac23.
\]
The chosen centre need not realize the global active-margin minimum.
In particular the same bound applies to an outer reverse centre A
in a smaller-short window, with \(\rho_A=A^2/(A^2+4)\).

## Exact local and global inputs

The proof of the sharpened bound uses the following information at
the selected actual reverse centre:

1. The two neighboring margins exceed its margin, giving
   \(0<r,t<1/2\).
2. Its reverse arc has positive duration, giving
   \(0<\rho<rt<1/4\).
3. Its two incident norms satisfy
   \(3/4<u\le1-r+r^2\) and \(3/4<v\le1-t+t^2\).
4. The same normal covector gives the exact centre stationarity and
   determinant identities
   \[
   E=1+r+t-\rho+\log\frac{\rho}{rt}
      -\frac{1-u}{r}-\frac{1-v}{t},
   \quad
   \gamma^2=\frac{4uv-E^2}{16(1-\rho)^2}.
   \]
5. The actual complete period is competitive, so its conserved
   normalized Casimir satisfies \(\gamma^2<9193/50000\).

Items 1--4 are stated at every reverse-run centre in
[MIXED_REVERSE_CENTRE_SCALE_BOUND](MIXED_REVERSE_CENTRE_SCALE_BOUND.md),
equations (2)--(3), using the local equations of
[MIXED_REVERSE_CENTRE_PHASE_BOUND](MIXED_REVERSE_CENTRE_PHASE_BOUND.md).
The strict centre minimum in item 1 is the local conclusion for every
surviving length-two reverse run in
[MIXED_GLOBAL_MINIMUM_STRUCTURE](MIXED_GLOBAL_MINIMUM_STRUCTURE.md),
Section 6. Its proof does not assume that this run contains the
minimum of the whole period. Item 5 is a whole-period input; the same
conserved Casimir occurs in the identities at every selected centre.

## No global-minimum hypothesis enters the scalar comparison

The sharpened argument first lowers u and v to 3/4 in the scalar
determinant expression. Its derivative signs follow only from
\(E<3r/2,3t/2\), which in turn follows from items 1--3.

If \(\rho\ge1/7\), the lower-norm diagonal obeys
\[
E_0\ge1+\rho-\frac1{8\rho}\ge\frac{15}{56}>0.
\]
The proof lowers the two scalar ratios until rt=rho and then uses
\((1/2-r)(1/2-t)\ge0\). These are consequences of items 1--2.
Raising the two ratios to 1/2 therefore lowers the scalar determinant,
giving the same one-variable function G(rho) displayed in the
refinements note.

The displayed logarithm inequality proves that G increases on
\([1/7,1/4)\). The exact endpoint estimate
\[
G(1/7)>\frac{18387201}{100000000}
       >\frac{9193}{50000}
\]
then contradicts item 5. None of these steps compares a with a remote
margin, chooses a smaller neighboring turn, or uses the location of
the period's global minimum.

Thus the original global-minimum wording was a narrower application
of the proved scalar argument. Stating the theorem for every actual
competitive reverse-run centre is justified by its original local
hypotheses. The extension does not assign a competitive cap or the
scale bound to an artificial comparison trajectory.
