# The Reinhardt conjecture, in Lean 4

Which centrally symmetric convex shape packs the plane worst? Pack copies of a disk as tightly as
possible and they cover `π/√12 = 90.69…%` of the plane; a regular octagon does a little worse. In
1934 Karl Reinhardt conjectured that the worst of all is the *smoothed octagon*, a regular octagon
whose corners are cut off by arcs of hyperbolas, with greatest packing density

  `δ_oct = (8 − 4√2 − log 2)/(2√2 − 1) = 0.902414…`,

and that it is the only worst shape up to affine maps. Kurt Mahler reached the same octagon
independently in 1947. The conjecture has been open since.

This repository proves the conjecture in Lean 4, with Mathlib, together with its equality case. The
informal proof it formalizes was written by ChatGPT (ChatGPT Pro, OpenAI). No person has checked
the proofs; Lean's kernel checks all of them, and every theorem depends only on Lean's standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

![The smoothed octagon in its densest packing, the copies sliding through the continuum of densest packings while staying in contact](docs/figures/worst-packer.gif)

The smoothed octagon packs most densely as a lattice packing, and it can do so in a continuum of
ways: the copies slide while always touching their six neighbours.

## The smoothed octagon

![A regular octagon, one corner rounded by the hyperbola that touches the two sides at the corner and approaches the next two sides, and the smoothed octagon](docs/figures/octagon-construction.svg)

Take the regular octagon whose sides lie on the lines `x cos(kπ/4) + y sin(kπ/4) = 1`. Replace each
corner by the arc of the hyperbola `d · d' = √2/4` whose asymptotes are the next two side lines
(`d`, `d'` the distances to them); it touches the two sides at the corner. Each side keeps a
straight middle part of length `2 − √2`.

![Densest packings of the disk, the regular octagon, the smoothed 14-gon and the smoothed octagon, with densities 0.906900, 0.906164, 0.906052 and 0.902414](docs/figures/packing-densities.svg)

## Statements

All definitions are in [`ReinhardtChallenge.lean`](ReinhardtChallenge.lean), which imports only Mathlib. They are
copied word for word from [lean4-smoothed-polygon](https://github.com/vltanh/lean4-smoothed-polygon),
the formalization of Hales and Vajjha's *Packings of Smoothed Polygons* on which this project
builds. `greatestPackingDensity K` is the supremum of the densities of packings of the plane by
congruent copies of `K`.

```lean
theorem reinhardt (K : Set (Fin 2 → ℝ)) (hK : IsConvexDisk K)
    (hsymm : ∃ c : Fin 2 → ℝ, ∀ x ∈ K, (2 : ℝ) • c - x ∈ K) :
    (8 - 4 * √2 - Real.log 2) / (2 * √2 - 1) ≤ greatestPackingDensity K
```

| Theorem | In words |
| --- | --- |
| `reinhardt` | every centrally symmetric convex disk has greatest packing density at least `δ_oct` |
| `reinhardt_equality` | equality holds exactly for the images of the smoothed octagon under invertible affine maps |
| `reinhardt_cost` | every trajectory of Hales's control problem with the boundary conditions costs at least `√12 δ_oct` |
| `octagon_area` | the smoothed octagon, defined from its trajectory, has area `√12 δ_oct` and density `δ_oct` |

The smoothed octagon is defined as the convex hull of the six arcs `t ↦ g(t) s_j`, `t ∈ [0, t_f]`,
of the trajectory `g` of Hales's control problem with the octagon's bang-bang control; `octagon_area`
identifies it with Reinhardt's octagon.

## Proof outline

Following Hales, the problem becomes optimal control on `SL₂(ℝ)`. A worst disk, normalized so that
its critical hexagon is regular, is traced by six points `g(t) s_j` that slide along its boundary,
and its area is the cost `−(3/2) ∫ tr(J X)` of the trajectory `(g, X)`. Conversely every trajectory
of cost below `π`, with any measurable control, bounds such a disk.

![The six contact points of the smoothed octagon moving around its boundary through one period, with the six neighbouring copies of its densest packing and the control word e₃ e₁ e₂ e₃](docs/figures/multipoint.gif)

1. **Foundations.** The conjecture is equivalent to a lower bound on the cost of every admissible
   trajectory, and the realization of a worst disk is a global minimizer of the control problem.
2. **Reduction.** A global minimizer stays in a compact part of the state space, lifts to a
   Pontryagin extremal (proved in lean4-smoothed-polygon from the maximum principle of
   [lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control)), switches between the
   three vertices of the control simplex finitely many times, and is normal.
3. **Five cases.** Read cyclically, the switches of a minimizing period are forward or reverse.
   With six or more pieces the sign sequence falls in one of five classes, and each is excluded.
4. **Terminal comparison.** A period with at most five pieces costs at least `√12 δ_oct`, with
   equality only for the octagon's four-piece word `e₂ e₀ e₁ e₂` with equal durations.
5. **Equality.** The boundary realization of any worst disk is then the octagon's trajectory, so
   the disk is a linear image of the octagon; conversely linear images pack equally badly.

![The state of the smoothed octagon's trajectory as a path in the upper half-plane, inside the star domain, with its four control arcs](docs/figures/upper-half-plane.svg)

## Status

[`ReinhardtSolution.lean`](ReinhardtSolution.lean) restates the four theorems of
[`ReinhardtChallenge.lean`](ReinhardtChallenge.lean) word for word and proves them from the library,
with no hypothesis and no `sorry`. `scripts/Audit.lean` checks that all 96,916 declarations of the
library, and the four theorems, depend only on the standard axioms.

| Stage | Lean |
| --- | --- |
| Foundations: realization of a worst disk, reverse comparison for arbitrary measurable controls | [`Foundations/`](SmoothedOctagon/Foundations) |
| Reduction: compact domain (Hales–Vajjha's Theorem 5.0.2), Pontryagin lift, clearance, edge bound, finitely many switches, normality | [`Reduction/`](SmoothedOctagon/Reduction) |
| The partition of switch-sign sequences into five classes | [`Period/Partition.lean`](SmoothedOctagon/Period/Partition.lean) |
| Cases R, M3, M1, F, M2 | [`Exclusion/`](SmoothedOctagon/Exclusion) |
| Terminal comparison: at most five pieces | [`Terminal/`](SmoothedOctagon/Terminal) |
| Equality and its converse | [`Equality/`](SmoothedOctagon/Equality) |
| The statements in the Challenge's vocabulary | [`Main.lean`](SmoothedOctagon/Main.lean), [`Bridge/`](SmoothedOctagon/Bridge) |

The informal proof was at first partly computer-assisted: it used seven interval-arithmetic covers
run in C++ with MPFR. Six of them have been replaced by hand arguments (case F, and the reverse,
low-scale and forward parts of case M2), and their Lean proofs follow those arguments. The seventh,
the smaller-short cover of case M2, is checked by Lean's kernel itself:
[`Interval/`](SmoothedOctagon/Interval) is a verified interval arithmetic (outward-rounded
fixed-point intervals, proved enclosures of `√`, `log` and `arctan`, a sound branch-and-bound checker),
and [`Interval/SmallerShort/`](SmoothedOctagon/Interval/SmallerShort) is a certificate of 337,399 boxes
checked by `decide`, without `native_decide`. The notes have since proved that case by hand too
([`MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION`](archive/notes/MIXED_SMALLER_SHORT_HAND_PERIOD_EXCLUSION.md));
formalizing that proof, which will remove the certificate, is in progress. Several steps of the
informal proof are proved by shorter routes than the notes; each docstring that departs from them
says so in a `Route:` line.

## Prior work

Reinhardt (1934) and Mahler (1947) posed the problem and found the octagon; Fejes Tóth showed that
densest packings of centrally symmetric disks can be taken to be lattice packings; Ledermann,
Ennola and Tammela proved lower bounds (Tammela's `0.8926`, 1970, stood for decades), and Nazarov
showed the smoothed octagon is a local minimum (1986). Hales recast the problem as optimal control
(2011, 2017), and Hales and Vajjha studied its Pontryagin extremals in *Packings of Smoothed
Polygons* (2024). [docs/prior-work.md](docs/prior-work.md) gives the full history with references.

## Verification

```sh
lake exe cache get
lake build
lake env lean scripts/Audit.lean          # every declaration uses only the standard axioms
lake env lake comparator --config=comparator.json   # needs bubblewrap; the Solution proves the Challenge
python3 scripts/sync_challenge_defs.py --check     # the Challenge's definitions are the library's
python3 scripts/figures/make_figures.py   # the figures, with every illustrated fact asserted
```

Lean and Mathlib are pinned at `v4.36.0-rc2`. The project depends on
[lean4-smoothed-polygon](https://github.com/vltanh/lean4-smoothed-polygon) (Hales–Vajjha's book,
including the Pontryagin lift of a minimizer and Theorem 5.0.2) and, through it, on
[lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control) (the maximum principle).
A full build takes about an hour on 16 cores: the interval certificate alone is about 4 CPU-hours of
kernel time, and some certificate files need up to 10 GB of memory each.

## Layout

```text
ReinhardtChallenge.lean        the statements of record, in Mathlib's vocabulary
ReinhardtSolution.lean         their proofs from the library
SmoothedOctagon/
  Foundations/                 geometry ↔ control: realization, reverse comparison
  Reduction/                   minimizer → finite normal period
  Period/                      vertex periods, flows, twist, Hamiltonians, the sign partition
  Exclusion/                   the five cases R, M3, M1, F, M2
  Terminal/                    periods with at most five pieces
  Equality/                    rigidity and its converse
  Certificates/                the scalar statements of the informal proof's interval covers
  Interval/                    verified interval arithmetic and the kernel-checked certificate
  Bridge/                      translation, affine maps and the octagon in the Challenge's terms
  LowerBound.lean, Main.lean   the assembly
Cited/HalesVajjha/             Definition 5.0.1 of Hales–Vajjha (the compact domain)
docs/                          prior work and the figures
archive/                       the informal proof notes (ChatGPT Pro) and their computations
scripts/                       the audit, the definitions check, the figures and the certificate generators
```

## Credits

The-Anh Vu-Le directed the work. ChatGPT Pro (OpenAI) found the proof, in the notes of
[`archive/`](archive/README.md), first with computer-assisted parts and then replacing all of them
by hand. Claude Opus 5.5 (Anthropic), in Claude Code, wrote the Lean formalization (with sub-agents),
the verified interval arithmetic and certificate, the figures and this documentation. The geometric
and control-theoretic foundations come from lean4-smoothed-polygon and lean4-optimal-control.

## License

Apache-2.0 ([`LICENSE`](LICENSE)).
