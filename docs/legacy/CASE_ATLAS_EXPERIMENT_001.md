# Experiment 001: exact-flow, finite-window PMP screen and octagon boundary

Date: 2026-11-07 UTC. **Exploration only**, not interval certification
or an unrestricted cost comparison. No Lean, Lake, typechecking, or CI.

## Reproduction

From the repository root:

    python explorations/structural_case_probe.py
    python explorations/octagon_boundary_probe.py

The actual execution used Python 3.13.5, NumPy 2.3.5, and
SciPy 1.17.0. No randomness, sampled optimization domain, or numerical
integration of a PMP ODE was used. The second script uses SciPy root
only to solve one five-coordinate local endpoint system at four
prescribed inputs. Endpoints are calculated with the exact algebraic
vertex-transfer formulas but evaluated in IEEE double arithmetic.

The first script checks five fixed six-piece words using the control
matrices D_i of [LOCAL_L2_RANK_DROP](LOCAL_L2_RANK_DROP.md).
The normalized physical cost is C/sqrt(12). For a fixed initial
determinant-one state, the endpoint data are a three-coordinate chart
of the tangent frame plus two final-state margins. It computes the
5-by-6 factor differential by complex-step at step 10^-28 and the
normalized cost gradient. With a full-rank Jacobian, it solves the
linear multiplier system and prints its stationarity residual. **It
does not infer PMP inequalities from nonstationary samples.**

When rank and stationarity pass numerical thresholds, an inserted
factor exp(epsilon) at a cut gives a compensated first variation

    Delta = d(C/sqrt(12))/d epsilon - nu d(endpoint)/d epsilon.

For a *true* normal maximizing lift, Delta>=0 for every missing
control. An actual external switch requires Delta=0 for the
appropriate neighboring vertex. The sign convention is therefore
that positive Delta is a cost penalty, not an improvement. Other
necessary checks (continuous PMP lift, all times of each arc,
geometric sector, full-period cost and twisted seam) are **not**
certified by this script. Midpoint and internal-cut signs are only
necessary samples, not a whole-arc proof.

## 1. Five generic finite inputs: no candidate accepted

All five generic windows start at physical margins (1,1,3/2)
(the determinant-one invariant is 4) with six factors 1.08.

| Six-word | Physical window cost | Least-squares stationarity residual | Smallest singular value of 5x6 endpoint differential |
|---|---:|---:|---:|
| L1 012012 | 0.855313426 | 0.001369 | 0.1038 |
| L2 021021 | 0.763630645 | 0.000075691 | 0.09918 |
| L3 021210 | 0.776736902 | 0.00045391 | 0.07259 |
| L4 010201 | 0.772198724 | 0.00054381 | 0.06956 |
| L5 021012 | 0.808935500 | 0.00029117 | 0.09952 |

All samples have positive factor logs and positive endpoint margins;
they fail the *numerical* stationarity threshold. No PMP gap claim is
made for these samples. The table is a unit/regression test, not
evidence that any full case is impossible.

## 2. Known stationary windows: external-switch filter is necessary

The two source examples already have exact hand certificates.
The deterministic screen reproduces their stationarity to roundoff:

| Exact input | Physical cost | Stationarity residual | Exterior missing-control gaps at first and last cuts |
|---|---:|---:|---|
| L1 factor (11/10,11/10,121/100,121/100,11/10,121/100), initial margins sqrt(1975/1684)*(1,1,4761/3950) | 1.601458184 | 7.2e-16 | start (0.00079473,0.00337210), end (0.00676433,0.00137229) |
| L3 six factors 5/4, initial margins sqrt(448/803)*(1,2,193/112) | 2.121257129 | 2.1e-15 | start (0.02430307,0.00553541), end (0.00553541,0.02430307) |

Every listed exterior gap is positive, so neither input satisfies the
two genuine exterior ties required of a selected complete window.
These conclusions were already proved in the cited L1 and PMP window
notes; the floating-point screen is an independent regression check,
not a new proof. In each displayed case the computed minimum internal
missing-control gap is positive too.

## 3. A genuinely switch-complete six-window can still fail the period budget

The standard forward N=7 family has common factor

    q7 = 2*cos(2*pi/7)

and initial margins (a,b,a), where

    a^2=4*q7/(4-q7),  b=a*(2/q7-1).

Its first six labels are L1=012012. The numerical screen gives:

- six-window cost 2.690276007;
- normal stationarity residual 2.0e-15;
- first exterior gaps (0.00143928, approximately 0);
- last exterior gaps (approximately 0,0.00143928);
- minimum internal missing-vertex gap 0.00143928;
- minimum sampled midpoint missing-vertex gap 0.00143497.

The entire **seven-piece** standard closed period has physical cost
3.138655342, whereas the octagon has 3.126054429. Direct
floating-point closure residuals are below 1.2e-15 for the frame
and 5e-16 for the two state values. The exact-family closure and
cost exclusion are established separately in the existing standard
polygon comparison; the numerical values here are diagnostics.

This is why a computer strategy must not stop at local stationarity,
external ties, and switch signs: a candidate can pass those checks
and still exceed the **complete-period** minimizing budget.

## 4. Octagon boundary degeneration into an all-reverse period

The second script tests the already proved insertion phenomenon of
[VERTEX_INSERTION_OBSTRUCTION](VERTEX_INSERTION_OBSTRUCTION.md).
Start from the octagon word 0120 with factor sqrt(2), and insert four
new positive factors at the forward transitions, including the
twisted seam. The refined one-period word is

    0,2,1,0,2,1,0,2

with original positions 0,2,4,6 and inserted positions 1,3,5,7.

Parameterize the initial physical state by p0,p1 and
p2=(4-p0*p1)/(p0+p1). For fixed inserted log factors epsilon,
correct five original coordinates (p0,p1 and three old log factors)
using the five actual closed-endpoint residual equations:
three entries of F R^-1 - I and
(p_end,0-p_start,2, p_end,1-p_start,0).

At zero insertion length, all four *compensated first derivatives of
the physical cost* are approximately

    dC/d epsilon = +0.022354869166.

At four prescribed positive equal insertions, SciPy finds the
following local endpoint branches:

| Inserted log factor epsilon | Residual max | C - A_oct | Smallest positive margin |
|---|---:|---:|---:|
| 0.001 | 4.5e-16 | +0.000089394933 | 0.61346426 |
| 0.005 | 8.9e-16 | +0.000446474649 | 0.61672493 |
| 0.015 | 1.7e-14 | +0.001335477145 | 0.62502576 |
| 0.040 | 4.5e-16 | +0.003531482583 | 0.64677257 |

All four solver runs report success; the four retained original
log factors also remain above 0.34. These are positive-margin,
numerically closed *candidate refinements*. Unlike the general
insertion theorem, this experiment suggests that the cost increases
along this particular small all-reverse branch.

**No assertion here extends the sign to all positive insertions or
all reverse words**, and the floating-point root residuals are not
proofs of exact endpoints. An analytic positivity certificate for
a neighborhood of the octagon would need interval/root-existence
bounds and boundary faces. The general theorem already proves
that exact closed insertions exist and their cost approaches
A_oct from an unspecified side.

## 5. Full-period constrained Hessian: method validation

The additional script
[closed_period_index_probe.py](../explorations/closed_period_index_probe.py)
computes the *complete* five-dimensional twisted closed-endpoint
residual, including two free initial-state variables. It uses
complex-step first derivatives, solves the normal endpoint multiplier
system, constructs the curvature-corrected Hessian of

    L = C/sqrt(12) - nu dot endpoint,

and restricts this Hessian to the numerical nullspace of the five
endpoint constraints. Its Hessian uses central differences of the
complex-step gradient with step 10^-4; independent checks at
3*10^-4 and 3*10^-5 preserve every displayed inertia count.

These are three **already known** exact standard forward families
(k=1,2,3 with N=3k+1, common factor 2cos(pi*k/N)):

| Period length | Physical cost | Endpoint rank | Stationarity residual | Numerical constrained eigenvalues | Negative index |
|---:|---:|---:|---:|---|---:|
| 4 (octagon) | 3.126054429 | 5 | 2.4e-15 | +0.0235112 | 0 |
| 7 | 3.138655342 | 5 | 1.9e-15 | -0.0826154, -0.0394188, +0.0187055, +0.0435372 | 2 |
| 10 | 3.140577469 | 5 | 3.4e-15 | -0.0747698, -0.0515440, -0.0227700, -0.0123483, +0.0080512, +0.0347043, +0.0539848 | 4 |

All full endpoint closure residuals are below 1.2e-15 at the
displayed inputs. The negative counts match the retained exact hand
theorem [GLOBAL_FORWARD_INDEX](GLOBAL_FORWARD_INDEX.md), which
supplies at least 2(k-1) negative constrained directions for the
standard k>=2 family. The octagon's positive numerical eigenvalue
is consistent with its known strict micro-local minimality.

**This is a regression test of the closed-period index oracle, not
a new exclusion.** In particular, the listed families are symmetric,
and the calculation does not justify a negative-index theorem for
asymmetric forward words, mixed words, singular endpoint fibers, or
general measurable controls. Numeric Hessian eigenvalues are not
verified interval enclosures.

## 6. Next computational test (not yet implemented)

Implement an **event-driven complete-period PMP return/escape oracle**
on the normal initial-phase manifold. For each of the five templates:
derive an exact local cotangent from an admissible stationary window;
check both exterior ties and whole-arc inactive gaps; extend the **same**
cotangent through its uniquely maximizing vertices; record star
escape, cost budget exhaustion, twisted return, triple-tie,
nontransverse root, or UNKNOWN. Preserve all abnormal/rank-degenerate
possibilities until the independent normality audit is complete.

Search should be deterministic, with transparent inputs and failures.
Use symbolic algebra to derive root equations, high-precision numerics
to select plausible inequalities, and interval arithmetic/rational
hand tables to certify uniform regions. No increasing-length closed
word catalogue is authorized.

## Status of proof gates

No entire F/R/M1/M2/M3 analytic case was closed by this experiment.
The full Reinhardt inequality and affine equality remain OPEN.
The scripts are small reproducible screening oracles, not rigorous
numerical certificates, and no Lean typecheck, compilation, Lake
command, or CI was performed.
