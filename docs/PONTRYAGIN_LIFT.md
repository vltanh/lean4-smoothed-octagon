# The remaining Pontryagin-lift construction

The geometric/control comparison now constructs an actual global control minimizer.
It does **not** construct its costates. This file records the exact next interface and
the hypotheses that a valid maximum-principle argument must preserve.

The missing assertion is

```lean
∀ {T : ℝ} {u : ℝ → Fin 3 → ℝ} {g X : ℝ → Mat2},
  IsReinhardtMinimizer T u g X →
    ∃ Λ₁ ΛR lam, IsPontryaginExtremal T u g X Λ₁ ΛR lam
```

This is a documented obligation, not an asserted theorem or an added assumption in
the geometric/control equivalence. The singular-interval results retain an actual
`IsPontryaginExtremal` input until this obligation has been discharged.

## What is already available

`exists_worstDisk_controlMinimizer` in
[`ReverseComparison.lean`](../SmoothedOctagon/ReverseComparison.lean) supplies a full
`IsReinhardtMinimizer`. The admissibility component supplies a positive terminal time,
a measurable simplex-valued control, the two integral state equations, the star state,
and the endpoint relations

\[
g(0)=I,\qquad g(T)=R,\qquad X(T)=R^{-1}X(0)R.
\]

[`AdmissibleRegularity.lean`](../SmoothedOctagon/AdmissibleRegularity.lean) derives the
needed continuity, Lipschitz state regularity, and classical frame equation from these
integral inputs. The state curve on a compact time interval stays in the open star
domain. Its product with the compact control simplex has a strictly negative
denominator in the normalized control vector field; this is the same compactness
argument used for the velocity bound in that module.

Those facts prepare a maximum-principle application. They do not produce a covector.

## What the actual extremal predicate still requires

The pinned `IsPontryaginExtremal` in `SmoothedPolygons/Defs.lean` requires all the
following additional data. Each row is an obligation on the same original trajectory.

| Requirement | Exact content |
| --- | --- |
| Constant multiplier | A scalar `lam ≤ 0`; normality is not assumed. |
| Reduced cotangent constraints | Both costates are traceless and `traceForm (ΛR t) (X t) = 0` at every time in `[0,T]`. |
| Reduced nontriviality | `lam ≠ 0 ∨ Λ₁ t ≠ 0 ∨ ΛR t ≠ 0` at every time, including endpoints. |
| First costate dynamics | The integral equation for `Λ₁′ = [Λ₁,X]`, with integrable entries. |
| Reduced costate dynamics | The exact integral equation for the normalized control-dependent reduced costate, with integrable entries. |
| Maximum condition | For almost every interior time, the original `u t` maximizes the Hamiltonian over the entire control simplex. |
| Zero Hamiltonian | The same Hamiltonian is zero almost everywhere on the interior. |
| Costate endpoints | `Λ₁(T) = R⁻¹Λ₁(0)R` and `ΛR(T) = R⁻¹ΛR(0)R`. |

The reduced equation uses `P = controlP (u t) (X t)` and is

\[
\Lambda_R'=[P,\Lambda_R]
-\operatorname{tr}(\Lambda_R P)[P,X]
+[-\Lambda_1+(3\lambda/2)J,X].
\]

The first-costate endpoint relation has a separate algebraic explanation. Once its
integral equation is available, continuity of its right-hand side gives the classical
equation, including derivatives within the closed interval. The existing
`corollary6_5_3` then gives

\[
\Lambda_1(t)=g(t)^{-1}\Lambda_1(0)g(t).
\]

Together with `g(T)=R`, this supplies its terminal relation. The reduced-costate
endpoint relation remains a transversality requirement of the variational problem.

## Two conditions that cannot be dropped

### Use the actual free-time, coupled-endpoint problem

The definition of global control minimality compares against every positive terminal
time. A fixed-terminal-time maximum principle alone does not supply the required
zero-Hamiltonian condition. Likewise, the initial state `X(0)` is free and its terminal
state is coupled to it by conjugation with `R`. Fixing `X(0)` independently changes
the endpoint variation and does not supply the required reduced-costate transversality.

### Preserve nontriviality after passing to the orbit

The physical state `X` belongs to the determinant-one adjoint orbit. An ambient
matrix covector can be nonzero while representing zero in the reduced cotangent space.
For example, the pointwise choice

\[
\lambda=0,\qquad \Lambda_1=0,\qquad \Lambda_2=X
\]

has a nonzero ambient `Λ₂` because `det X = 1`, but its reduced costate is

\[
\Lambda_R=[\Lambda_2,X]=[X,X]=0.
\]

Consequently nontriviality of `(lam,Λ₁,Λ₂)` by itself does not imply the nontriviality
required by `IsPontryaginExtremal`. A valid argument must apply the principle on the
orbit or the equivalent upper half-plane state space, or explicitly preserve the
nonzero cotangent class when passing to reduced coordinates. The pinned definition
already identifies this issue; it must not be weakened to accommodate an ambient lift.

Normalizing `lam` to `-1` also requires a separate proof that `lam ≠ 0`. The
singular-interval rigidity theorem proves this only under its own interval hypothesis;
it does not exclude all abnormal minimizers.

## Existing source interfaces and their limits

| Pinned declaration | What it supplies | What it does not supply |
| --- | --- | --- |
| `lemma6_8_1` in `Ch6/HalfPlane.lean` | A linear equivalence between the quotient dual and trace-perpendicular reduced matrices | Existence or nontriviality of a costate trajectory |
| `proposition6_5_1` in `Ch6/Hamiltonian.lean` | Transformation of already supplied Hamilton equations into the reduced equation | A maximum-principle application to a minimizer |
| `corollary6_5_3` in `Ch6/Hamiltonian.lean` | Adjoint evolution and constant determinant of the first costate | Existence of that costate |
| `theorem6_8_3` in `Ch6/HalfPlane.lean` | A coordinate transformation for already supplied costate equations | A lift-existence theorem |
| `poly_isPontryaginExtremal`, `theorem7_5_6` in `Ch7/SmoothedPolygon.lean` | Explicit extremal lifts for the constructed polygon family | A lift of an arbitrary global minimizer |

The pinned reference source has no identified general theorem that closes this
interface. The published maximum-principle discussion is mathematical background;
it is not a Lean dependency that can silently discharge the missing construction.

## Source references and validation

- [Pinned extremal definition](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Defs.lean).
- [Pinned admissibility and global minimization](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch3/ControlProblem.lean).
- [Pinned Hamiltonian and costate identities](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch6/Hamiltonian.lean).
- [Pinned quotient-dual and half-plane transformations](https://github.com/vltanh/lean4-smoothed-polygon/blob/8ce732873a1aa054e98dac46cfaa8d7bb96ffa6f/SmoothedPolygons/Ch6/HalfPlane.lean).
- Hales–Vajjha, [Chapter 6, especially Sections 6.2 and 6.6](https://arxiv.org/html/2405.04331v1#Ch6).

This is a source-interface audit. No Lean compilation, Lake command, typecheck, or CI
was run, and no maximum-principle theorem is asserted by this document.
