# Directed MPFR interval arithmetic for scalar certificates

Date: 2026-11-07. Arithmetic implementation and independent regression
checks. This file supplies no new M2 exclusion theorem. No Lean, Lake,
typechecking, or CI was run.

## Scope and trust boundary

[`certified_mpfr_interval.hpp`](../explorations/certified_mpfr_interval.hpp)
provides finite closed intervals, second-order automatic differentiation,
and a Taylor enclosure using **80 significand bits** by default. Every
arithmetic bound is computed with an explicit MPFR rounding direction.
The backend uses MPFR's documented public Custom Interface for fixed-size
stack storage; it does not guess an ABI, access private fields, change a
number's precision, swap its storage pointer, or clear custom storage.

This is a directed-rounding certificate backend. Its proof boundary
includes the correctness of the installed MPFR/GMP libraries, C++ compiler
and execution platform. It is not a Lean kernel check, and it is not the
integer-only verifier used for the earlier F certificate. The published F
verifier is unchanged.

MPFR specifies that the functions used here act on exact input values and
round their result to the destination precision in the requested direction.
The guarantee covers the elementary operations, square root, logarithm,
arctangent, exponential, and the constant pi. The relevant primary source
is the [MPFR 4.2.2 manual](https://www.mpfr.org/mpfr-4.2.2/mpfr.html),
especially **Rounding**, **Arithmetic Functions**, **Transcendental
Functions**, and **Custom Interface**. The interface documentation requires
custom significand storage to have the size returned by
`mpfr_custom_get_size`, with alignment suitable for `mp_limb_t`; the engine
allocates an array of that type and checks the size.

The workspace runtime is MPFR **4.2.2**, and the compiler used for the
reported checks is GCC **14.2.0**. Its development header was absent. A
matching, unmodified upstream header was recovered from two independently
maintained source distributions, and the contents matched byte for byte:

- [TeX Live, fixed commit a553f86ad9f31c0a70b94c0245ab8247ff8b8c56](https://github.com/TeX-Live/texlive-source/blob/a553f86ad9f31c0a70b94c0245ab8247ff8b8c56/libs/mpfr/mpfr-src/src/mpfr.h).
- [DragonFlyBSD, fixed commit d82ad2ebde4cf877dbf8a53ec8beaa5e1cb214f4](https://github.com/DragonFlyBSD/DragonFlyBSD/blob/d82ad2ebde4cf877dbf8a53ec8beaa5e1cb214f4/contrib/mpfr/src/mpfr.h).

The upstream Git blob is
`117673b2c9833b855689748fccb8f0beae8cdfad` and the file has **57,588 bytes**.
The header remains an external build dependency; it is not copied into
this repository. A normal installation of matching MPFR development
headers is sufficient.

## Arithmetic rules

`certified::R` stores one finite MPFR number. Integral input is exact; the
precision is at least 64 bits, and the supported integral types have at
most 64 bits. Point comparisons and sign changes are exact. Binary64
conversion is explicit and represents the supplied binary64 value exactly;
it does not reinterpret a decimal literal as its intended rational value.

There are deliberately no ordinary point `+`, `-`, `*` or `/` operators.
A wrapper such as `rd(a+b)` would be unsound if `a+b` had already rounded
in the wrong direction. Instead the primitive point operations take their
rounding mode explicitly. Most callers should use interval arithmetic
throughout.

`certified::I` stores endpoints `l,h`. For finite nonempty intervals:

- Addition and subtraction round the corresponding extreme endpoint
  expressions downward and upward.
- Multiplication selects its extreme products by endpoint signs, then
  evaluates those products in the required directions. If both intervals
  straddle zero, both candidate products are retained for each extremum.
- Reciprocal is decreasing on each component of its domain, so its bounds
  are the directed evaluations of `1/h` and `1/l`. Division rejects a
  denominator containing zero.
- Squaring uses zero as the exact lower bound when the interval crosses
  zero. Otherwise it uses the endpoint of smaller absolute value for the
  lower bound.
- Square root, logarithm, arctangent and exponential use monotonicity and
  directed endpoint evaluations. Their domains are checked before calling
  MPFR. A square-root **jet** requires a strictly positive box.

Exact rational constants should be written `I::rational(n,d)`, and exact
decimal input may be written `I::decimal("0.15")`. Implicit binary64
constants are rejected. `I::binary64(x)` is appropriate for a deliberately
chosen dyadic search weight; it is not a replacement for exact input
constants.

Finite outputs are required. Empty-interval arithmetic and invalid domains
throw exceptions. The caller must treat domain overlap as an unresolved
box to subdivide, and a range or runtime error as a failed run. It must
never turn an exception into a successful exclusion.

Call `check_environment()` at the start of a run and `check_flags()` before
accepting a completed certificate. The first checks the matching
header/runtime version and GMP limb size, and clears flags once. The
second rejects underflow, overflow, invalid values, division by zero and
range errors. Inexact rounding is expected and is not an error. Do not
change the exponent range or clear flags during the run. Ordinary
floating-point calculations may choose split axes or propose LP weights,
but no proof sign can depend on them.

## Jets and the Taylor enclosure

`Jet<N>` stores a value interval, `N` first derivatives, and the full
symmetric Hessian. Its sum, product, quotient and composition rules are
exact differentiation identities evaluated with the interval operations
above. The Hessian's lower triangle copies the upper triangle; it does
not repeat an approximate calculation.

For a scalar smooth function `f`, `fun(a,value,deriv,deriv2)` requires
interval enclosures of **the actual function and its actual derivatives**
on `a.v`. It returns the chain-rule jet. Providing the derivatives of an
approximation in place of the true derivatives would invalidate the
Taylor certificate.

The supplied `logdiv(h)` is the analytic continuation of
`log(h)/(h-1)` through `h=1`. It avoids cancellation there. With
`t=(h-1)/(h+1)`,

\[
\frac{\log h}{h-1}
=(1-t)\sum_{n=0}^{\infty}\frac{t^{2n}}{2n+1}.
\]

After retaining the terms through `n=M`, the omitted tail, at
`|t|<=tau<1`, is bounded by

\[
\frac{\tau^{2M+2}}{(2M+3)(1-\tau^2)}.
\]

This follows coefficient by coefficient in the positive even power series.
Differentiating that coefficient majorant once and twice gives valid
bounds on the first and second derivative tails. The first derivative
uses a symmetric remainder interval, which also covers negative `t`;
the value and second derivative tails are nonnegative. The implementation
computes this univariate series in `Jet<1>` and then composes it into the
requested `Jet<N>`. The midpoint value and derivatives are enclosed too;
no truncation is silently taken as an equality.

Choose an actual representable point `c` in a box `B`, evaluate `at` at
that same point, and evaluate `all` on the whole box. For `dx=B-c`, the
Taylor routine encloses

\[
f(c)+\sum_i f_i(c)dx_i
 +\frac12\sum_i f_{ii}(B)dx_i^2
 +\sum_{i<j}f_{ij}(B)dx_i dx_j.
\]

The line segment from `c` to every point of `B` stays inside `B`, so the
standard integral Taylor remainder justifies the Hessian enclosure. The
result is intersected with the natural value interval. The displacement
intervals are computed by directed subtraction from the **chosen point**.
They are not replaced by an assumed exact symmetric half-width after a
rounded midpoint operation.

Minimal usage:

```cpp
#include "certified_mpfr_interval.hpp"
using namespace certified;
using J = Jet<2>;

std::array<I,2> box = { I(1,2), I(2,3) };
auto center = centers(box);
auto f = [](const std::array<J,2>& x) {
    return lg(x[0] + x[1]) / (1 + sq(x[0]));
};
auto all = f(variables(box));
auto at = f(variables_at(center));
I enclosure = taylor(at, all, box, center);
```

The routine encloses a function on the supplied box. The mathematical
reduction establishing that an actual PMP trajectory belongs to that box,
the necessary constraint signs, and any domain contractors remain separate
proof obligations.

## Checks and performance

[`certified_mpfr_interval_check.cpp`](../explorations/certified_mpfr_interval_check.cpp)
completed **116,914 checks**, with zero MPFR range/domain flags:

- Exact GMP rational endpoint extrema verify addition, subtraction,
  multiplication, division, sign change and squaring across sign cases.
- Rational squares verify the directions of the square-root endpoints.
- Exact rational series independently bound logarithm, arctangent,
  exponential and pi (using Machin's identity).
- Explicit rational derivative formulas verify the jet value, gradient,
  Hessian and arctangent derivatives.
- The removable logarithm quotient is checked at its joining value and
  against its actual first and second derivative formulas on both sides.
- Taylor checks include adjacent representable endpoints, where the chosen
  midpoint rounds to one endpoint, plus exact rational evaluations.
- Copy/move and vector-reallocation checks exercise the nonaliasing custom
  storage. Invalid domains and empty arithmetic must fail.

The same checks passed under AddressSanitizer and UndefinedBehaviorSanitizer.
The leak detector was disabled because LeakSanitizer is unsupported under
this environment's ptrace setup; no successful leak-detector run is claimed.

These tests are implementation regression evidence. The universal enclosure
argument is the directed-arithmetic and differentiation reasoning above;
a finite test sample does not replace it.

A comparison on 500 identical four-variable forward expressions, each
including natural interval evaluation, midpoint derivatives and the Taylor
bound, took **6.767 seconds** with the published GMP fixed-dyadic engine and
**0.396661 seconds** with this MPFR80 engine, a factor of **17.06** in that
run. This benchmark is not a mathematical proof premise. The earlier
published F source was included unchanged in the separate scratch benchmark.

With development headers installed, the check command is:

```sh
g++ -std=c++17 -O3 -Wall -Wextra -Wpedantic \
  explorations/certified_mpfr_interval_check.cpp \
  -lmpfr -lgmpxx -lgmp -o /tmp/certified_mpfr_interval_check
/tmp/certified_mpfr_interval_check
```

In the present workspace, the external matching header is in
`/workspace/scratch/5efeb2d2f42f/m2_mpfr_vendor`, and the versioned shared
library is available without an unversioned linker symlink. Add
`-I /workspace/scratch/5efeb2d2f42f/m2_mpfr_vendor` and use
`-l:libmpfr.so.6` in place of `-lmpfr` for that environment. Neither the
external header nor a compiled binary is required in the repository.
