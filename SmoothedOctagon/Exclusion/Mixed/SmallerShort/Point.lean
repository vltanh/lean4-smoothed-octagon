module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.Real.Sqrt

/-!
# Case M2, smaller-short branch: the six-variable point

The coordinates `(r, δ, α, ρ, v, E)` of a smaller-short window and the quantities derived from
them, with ASCII names (`delta = δ`, `al = α`, `rho = ρ`, …). `M2Short` states its middle-switch
slack (`Point.fmid`) and its window-defect inequality (`Point.AA`, `Point.BB`, `Point.Tk`,
`Point.cost`, `Point.kap`) with them. The residuals `f₀, …, f₂₇` are inequalities that the point of
every smaller-short window satisfies (`Exclusion/Mixed/Short/Cover.lean`).

Smaller-short windows are excluded by the hand proof in `Exclusion/Mixed/ShortHand/`. `logDiv` is
the analytic continuation of `log q/(q - 1)`, equal to `1` at `q = 1`.
-/

@[expose] public section

namespace SmoothedOctagon.Certificates

namespace SmallerShort

/-- `logdiv(q)`: the analytic continuation of `log q/(q - 1)`, equal to `1` at `q = 1`. -/
noncomputable def logDiv (q : ℝ) : ℝ := if q = 1 then 1 else Real.log q / (q - 1)

/-- The six coordinates of a smaller-short window, with ASCII names:
`r, delta, al, rho, v, E` are `r, δ, α, ρ, v, E`. -/
structure Point where
  /-- `r`. -/
  r : ℝ
  /-- `delta = δ`. -/
  delta : ℝ
  /-- `al = α`. -/
  al : ℝ
  /-- `rho = ρ`. -/
  rho : ℝ
  /-- `v`. -/
  v : ℝ
  /-- `E`. -/
  E : ℝ

namespace Point

/-- `x = 1/r - 1`. -/
noncomputable def x (p : Point) : ℝ := 1 / p.r - 1

/-- `be = (1 + delta)x`. -/
noncomputable def be (p : Point) : ℝ := (1 + p.delta) * p.x

/-- `S = 1 + x`. -/
noncomputable def S (p : Point) : ℝ := 1 + p.x

/-- `A = al + be`. -/
noncomputable def A (p : Point) : ℝ := p.al + p.be

/-- `B = be + x`. -/
noncomputable def B (p : Point) : ℝ := p.be + p.x

/-- `xi = 1 - r`. -/
noncomputable def xi (p : Point) : ℝ := 1 - p.r

/-- `h = xi(2 + delta)`. -/
noncomputable def h (p : Point) : ℝ := p.xi * (2 + p.delta)

/-- `u = 1 + xi/(2 + delta) - xi·logdiv(h)`. -/
noncomputable def u (p : Point) : ℝ := 1 + p.xi / (2 + p.delta) - p.xi * logDiv p.h

/-- `ax = al·r/(1 - r)`, that is `α/x`. -/
noncomputable def ax (p : Point) : ℝ := p.al * p.r / (1 - p.r)

/-- `ha = (2 + delta)/(1 + delta + ax)`. -/
noncomputable def ha (p : Point) : ℝ := (2 + p.delta) / (1 + p.delta + p.ax)

/-- `xa = (1 + delta)/(1 + delta + ax)`. -/
noncomputable def xa (p : Point) : ℝ := (1 + p.delta) / (1 + p.delta + p.ax)

/-- `ua = 1 + xa²/ha - xa·logdiv(ha)`. -/
noncomputable def ua (p : Point) : ℝ := 1 + p.xa ^ 2 / p.ha - p.xa * logDiv p.ha

/-- `Eupperpoly = r(u + v - 2) + 2r·r² - rho·r² + rho - r²E`. -/
noncomputable def Eupperpoly (p : Point) : ℝ :=
  p.r * (p.u + p.v - 2) + 2 * p.r * p.r ^ 2 - p.rho * p.r ^ 2 + p.rho - p.r ^ 2 * p.E

/-- The Casimir `gam = (4uv - E²)/(16(1 - rho)²)`. -/
noncomputable def gam (p : Point) : ℝ := (4 * p.u * p.v - p.E ^ 2) / (16 * (1 - p.rho) ^ 2)

/-- `D = al² + 2·al·be + 1 + 2x - 2·be·x`. -/
noncomputable def D (p : Point) : ℝ :=
  p.al ^ 2 + 2 * p.al * p.be + 1 + 2 * p.x - 2 * p.be * p.x

/-- `lambda = 1/(1 + rho(al² - 1))`. -/
noncomputable def lam (p : Point) : ℝ := 1 / (1 + p.rho * (p.al ^ 2 - 1))

/-- `ed = rho·D`. -/
noncomputable def ed (p : Point) : ℝ := p.rho * p.D

/-- `w = lambda²(v - ed·E + ed²u)`. -/
noncomputable def w (p : Point) : ℝ := p.lam ^ 2 * (p.v - p.ed * p.E + p.ed ^ 2 * p.u)

/-- `EL = lambda(2·ed·u - E)`. -/
noncomputable def EL (p : Point) : ℝ := p.lam * (2 * p.ed * p.u - p.E)

/-- `rhoA = al²·lambda·rho`. -/
noncomputable def rhoA (p : Point) : ℝ := p.al ^ 2 * p.lam * p.rho

/-- `ti = lambda·rho·al·A`. -/
noncomputable def ti (p : Point) : ℝ := p.lam * p.rho * p.al * p.A

/-- `TB = A/al`. -/
noncomputable def TB (p : Point) : ℝ := p.A / p.al

/-- `zeta = (1 - 2ti)/(1 + 2ti)`. -/
noncomputable def zeta (p : Point) : ℝ := (1 - 2 * p.ti) / (1 + 2 * p.ti)

/-- `m0 = 2(1 + zeta) + (2/3)zeta(1 + zeta)²`. -/
noncomputable def m0 (p : Point) : ℝ := 2 * (1 + p.zeta) + 2 / 3 * p.zeta * (1 + p.zeta) ^ 2

/-- `Rbar = m0(w - 3/4) + (u - 1)TB + 1 + 1/TB - rhoA - EL - 2zeta - (2/3)zeta·zeta²`. -/
noncomputable def Rbar (p : Point) : ℝ :=
  p.m0 * (p.w - 3 / 4) + (p.u - 1) * p.TB + 1 + 1 / p.TB - p.rhoA - p.EL - 2 * p.zeta
    - 2 / 3 * p.zeta * p.zeta ^ 2

/-- `gap1 = (1 - rho - v)r² + rho(E - 1 + rho)r + rho(1 - rho - u)`. -/
noncomputable def gap1 (p : Point) : ℝ :=
  (1 - p.rho - p.v) * p.r ^ 2 + p.rho * (p.E - 1 + p.rho) * p.r + p.rho * (1 - p.rho - p.u)

/-- `pmid`. -/
noncomputable def pmid (p : Point) : ℝ :=
  p.be ^ 2 * p.rho * p.x ^ 2 - p.be ^ 2 * p.rho + p.be ^ 2 - 4 * p.be * p.rho * p.x ^ 2
    - 4 * p.be * p.rho * p.x + 2 * p.be * p.x + 3 * p.rho * p.x ^ 2 + 4 * p.rho * p.x + p.rho
    + p.x ^ 2

/-- `fmid = (1 - rho)(be²rho + be·rho·x + rho·x² - rho + 1) - v - rho·E(be·x - 2x - 1)
- rho·u·pmid`. -/
noncomputable def fmid (p : Point) : ℝ :=
  (1 - p.rho) * (p.be ^ 2 * p.rho + p.be * p.rho * p.x + p.rho * p.x ^ 2 - p.rho + 1) - p.v
    - p.rho * p.E * (p.be * p.x - 2 * p.x - 1) - p.rho * p.u * p.pmid

/-- `ra = al/A`. -/
noncomputable def ra (p : Point) : ℝ := p.al / p.A

/-- `fouter = (1 - rhoA - w)ra² + rhoA(EL - 1 + rhoA)ra + rhoA(1 - rhoA - u)`. -/
noncomputable def fouter (p : Point) : ℝ :=
  (1 - p.rhoA - p.w) * p.ra ^ 2 + p.rhoA * (p.EL - 1 + p.rhoA) * p.ra
    + p.rhoA * (1 - p.rhoA - p.u)

/-- `kap = √(12·gam)`. -/
noncomputable def kap (p : Point) : ℝ := Real.sqrt (12 * p.gam)

/-- `U = (1 - rho)/rho`. -/
noncomputable def U (p : Point) : ℝ := (1 - p.rho) / p.rho

/-- `N = (U - x)/S`. -/
noncomputable def N (p : Point) : ℝ := (p.U - p.x) / p.S

/-- `Z = (U - al·be)/A`. -/
noncomputable def Z (p : Point) : ℝ := (p.U - p.al * p.be) / p.A

/-- Entry `(0, 0)` of `P = [[-N - 2, x + 2], [N, x]]`. -/
noncomputable def P00 (p : Point) : ℝ := -p.N - 2

/-- Entry `(0, 1)` of `P`. -/
noncomputable def P01 (p : Point) : ℝ := p.x + 2

/-- Entry `(1, 0)` of `P`. -/
noncomputable def P10 (p : Point) : ℝ := p.N

/-- Entry `(1, 1)` of `P`. -/
noncomputable def P11 (p : Point) : ℝ := p.x

/-- Entry `(0, 0)` of `Qinv = [[-al/(2U), (al + 2be)/(2U)], [Z/(2U), (Z + 2be)/(2U)]]`. -/
noncomputable def Qi00 (p : Point) : ℝ := -p.al / (2 * p.U)

/-- Entry `(0, 1)` of `Qinv`. -/
noncomputable def Qi01 (p : Point) : ℝ := (p.al + 2 * p.be) / (2 * p.U)

/-- Entry `(1, 0)` of `Qinv`. -/
noncomputable def Qi10 (p : Point) : ℝ := p.Z / (2 * p.U)

/-- Entry `(1, 1)` of `Qinv`. -/
noncomputable def Qi11 (p : Point) : ℝ := (p.Z + 2 * p.be) / (2 * p.U)

/-- Entry `(0, 0)` of `FF = [[S/A, 0], [(S² - B²)/(SA), A/S]]`. -/
noncomputable def F00 (p : Point) : ℝ := p.S / p.A

/-- Entry `(0, 1)` of `FF`. -/
noncomputable def F01 (_p : Point) : ℝ := 0

/-- Entry `(1, 0)` of `FF`. -/
noncomputable def F10 (p : Point) : ℝ := (p.S ^ 2 - p.B ^ 2) / (p.S * p.A)

/-- Entry `(1, 1)` of `FF`. -/
noncomputable def F11 (p : Point) : ℝ := p.A / p.S

/-- Entry `(0, 0)` of `P·FF`. -/
noncomputable def PF00 (p : Point) : ℝ := p.P00 * p.F00 + p.P01 * p.F10

/-- Entry `(0, 1)` of `P·FF`. -/
noncomputable def PF01 (p : Point) : ℝ := p.P00 * p.F01 + p.P01 * p.F11

/-- Entry `(1, 0)` of `P·FF`. -/
noncomputable def PF10 (p : Point) : ℝ := p.P10 * p.F00 + p.P11 * p.F10

/-- Entry `(1, 1)` of `P·FF`. -/
noncomputable def PF11 (p : Point) : ℝ := p.P10 * p.F01 + p.P11 * p.F11

/-- Entry `(0, 0)` of `mm = (P·FF)·Qinv`. -/
noncomputable def m00 (p : Point) : ℝ := p.PF00 * p.Qi00 + p.PF01 * p.Qi10

/-- Entry `(0, 1)` of `mm`. -/
noncomputable def m01 (p : Point) : ℝ := p.PF00 * p.Qi01 + p.PF01 * p.Qi11

/-- Entry `(1, 0)` of `mm`. -/
noncomputable def m10 (p : Point) : ℝ := p.PF10 * p.Qi00 + p.PF11 * p.Qi10

/-- Entry `(1, 1)` of `mm`. -/
noncomputable def m11 (p : Point) : ℝ := p.PF10 * p.Qi01 + p.PF11 * p.Qi11

/-- `h11 = E(r - rho·S) - u(1 - (rho·S)²) + v(1 - r²)`. -/
noncomputable def h11 (p : Point) : ℝ :=
  p.E * (p.r - p.rho * p.S) - p.u * (1 - (p.rho * p.S) ^ 2) + p.v * (1 - p.r ^ 2)

/-- `h12 = u(1 + rho·S)² + v(1 + r)² - E(1 + r)(1 + rho·S)`. -/
noncomputable def h12 (p : Point) : ℝ :=
  p.u * (1 + p.rho * p.S) ^ 2 + p.v * (1 + p.r) ^ 2 - p.E * (1 + p.r) * (1 + p.rho * p.S)

/-- `h21 = -u(1 - rho·S)² - v(1 - r)² - E(1 - r)(1 - rho·S)`. -/
noncomputable def h21 (p : Point) : ℝ :=
  -p.u * (1 - p.rho * p.S) ^ 2 - p.v * (1 - p.r) ^ 2 - p.E * (1 - p.r) * (1 - p.rho * p.S)

/-- `Tk = 2·kap·(1 - rho)²`. -/
noncomputable def Tk (p : Point) : ℝ := 2 * p.kap * (1 - p.rho) ^ 2

/-- `AA = Tk(m00 + m11) + h12·m11 - h11(m01 + 3m10) - 3·h21·m00`, the trace `𝒜`. -/
noncomputable def AA (p : Point) : ℝ :=
  p.Tk * (p.m00 + p.m11) + p.h12 * p.m11 - p.h11 * (p.m01 + 3 * p.m10) - 3 * p.h21 * p.m00

/-- `BB = h11(m11 - m00) + h12·m10 + h21·m01 + (Tk/3)(3m10 - m01)`, the trace `ℬ`. -/
noncomputable def BB (p : Point) : ℝ :=
  p.h11 * (p.m11 - p.m00) + p.h12 * p.m10 + p.h21 * p.m01 + p.Tk / 3 * (3 * p.m10 - p.m01)

/-- `cost = √3(rho·u/(1 - rho)·(2be·x - x - al·be) + (be·x - al)/(SA))`. -/
noncomputable def cost (p : Point) : ℝ :=
  Real.sqrt 3 * (p.rho * p.u / (1 - p.rho) * (2 * p.be * p.x - p.x - p.al * p.be)
    + (p.be * p.x - p.al) / (p.S * p.A))

/-- `theta_centered = arctan((3BB - AA)/(√3(AA + BB)))`. -/
noncomputable def thetaCentered (p : Point) : ℝ :=
  Real.arctan ((3 * p.BB - p.AA) / (Real.sqrt 3 * (p.AA + p.BB)))

/-- `excess = cost + (kap + 3/2)(6283/12000 - theta_centered) - 2501/800`. -/
noncomputable def excess (p : Point) : ℝ :=
  p.cost + (p.kap + 3 / 2) * (6283 / 12000 - p.thetaCentered) - 2501 / 800

/-- `f₀ = u - ua`. -/
noncomputable def f0 (p : Point) : ℝ := p.u - p.ua

/-- `f₁ = 1 - r + r² - u`. -/
noncomputable def f1 (p : Point) : ℝ := 1 - p.r + p.r ^ 2 - p.u

/-- `f₂ = r²(1 - v) - rho·r + rho²`. -/
noncomputable def f2 (p : Point) : ℝ := p.r ^ 2 * (1 - p.v) - p.rho * p.r + p.rho ^ 2

/-- `f₃ = A²(1 - u) - al·be`. -/
noncomputable def f3 (p : Point) : ℝ := p.A ^ 2 * (1 - p.u) - p.al * p.be

/-- `f₄ = gam - 27/256`. -/
noncomputable def f4 (p : Point) : ℝ := p.gam - 27 / 256

/-- `f₅ = 23/125 - gam`. -/
noncomputable def f5 (p : Point) : ℝ := 23 / 125 - p.gam

/-- `f₆ = w - 3/4`. -/
noncomputable def f6 (p : Point) : ℝ := p.w - 3 / 4

/-- `f₇ = 1 - ti + ti² - w`. -/
noncomputable def f7 (p : Point) : ℝ := 1 - p.ti + p.ti ^ 2 - p.w

/-- `f₈ = Rbar`. -/
noncomputable def f8 (p : Point) : ℝ := p.Rbar

/-- `f₉ = 3/20 - rhoA`. -/
noncomputable def f9 (p : Point) : ℝ := 3 / 20 - p.rhoA

/-- `f₁₀ = 3rhoA - EL`. -/
noncomputable def f10 (p : Point) : ℝ := 3 * p.rhoA - p.EL

/-- `f₁₁ = gap1`. -/
noncomputable def f11 (p : Point) : ℝ := p.gap1

/-- `f₁₂ = Eupperpoly`. -/
noncomputable def f12 (p : Point) : ℝ := p.Eupperpoly

/-- `f₁₃ = 3rho - E`. -/
noncomputable def f13 (p : Point) : ℝ := 3 * p.rho - p.E

/-- `f₁₄ = fmid`. -/
noncomputable def f14 (p : Point) : ℝ := p.fmid

/-- `f₁₅ = fouter`. -/
noncomputable def f15 (p : Point) : ℝ := p.fouter

/-- `f₁₆ = r² - rho`. -/
noncomputable def f16 (p : Point) : ℝ := p.r ^ 2 - p.rho

/-- `f₁₇ = x - al`. -/
noncomputable def f17 (p : Point) : ℝ := p.x - p.al

/-- `f₁₈ = al - 1 - delta(1 + 2x/7)`. -/
noncomputable def f18 (p : Point) : ℝ := p.al - 1 - p.delta * (1 + 2 * p.x / 7)

/-- `f₁₉ = 1 - rho(al² + 2·al·be + 1)`. -/
noncomputable def f19 (p : Point) : ℝ := 1 - p.rho * (p.al ^ 2 + 2 * p.al * p.be + 1)

/-- `f₂₀ = 1 - rho(1 + be·x)`. -/
noncomputable def f20 (p : Point) : ℝ := 1 - p.rho * (1 + p.be * p.x)

/-- `f₂₁ = (u - 1)(2 + delta)² + (1 + delta)`. -/
noncomputable def f21 (p : Point) : ℝ := (p.u - 1) * (2 + p.delta) ^ 2 + (1 + p.delta)

/-- `f₂₂ = 13/16 - u`. -/
noncomputable def f22 (p : Point) : ℝ := 13 / 16 - p.u

/-- `f₂₃ = AA - 2Tk`. -/
noncomputable def f23 (p : Point) : ℝ := p.AA - 2 * p.Tk

/-- `f₂₄ = BB`. -/
noncomputable def f24 (p : Point) : ℝ := p.BB

/-- `f₂₅ = AA - BB`. -/
noncomputable def f25 (p : Point) : ℝ := p.AA - p.BB

/-- `f₂₆ = AA + BB - 4Tk`. -/
noncomputable def f26 (p : Point) : ℝ := p.AA + p.BB - 4 * p.Tk

/-- `f₂₇ = -excess`. -/
noncomputable def f27 (p : Point) : ℝ := -p.excess

/-- All 28 residuals `f₀, …, f₂₇` are nonnegative. -/
def AllResidualsNonneg (p : Point) : Prop :=
  0 ≤ p.f0 ∧ 0 ≤ p.f1 ∧ 0 ≤ p.f2 ∧ 0 ≤ p.f3 ∧ 0 ≤ p.f4 ∧ 0 ≤ p.f5 ∧ 0 ≤ p.f6 ∧ 0 ≤ p.f7 ∧
    0 ≤ p.f8 ∧ 0 ≤ p.f9 ∧ 0 ≤ p.f10 ∧ 0 ≤ p.f11 ∧ 0 ≤ p.f12 ∧ 0 ≤ p.f13 ∧ 0 ≤ p.f14 ∧
    0 ≤ p.f15 ∧ 0 ≤ p.f16 ∧ 0 ≤ p.f17 ∧ 0 ≤ p.f18 ∧ 0 ≤ p.f19 ∧ 0 ≤ p.f20 ∧ 0 ≤ p.f21 ∧
    0 ≤ p.f22 ∧ 0 ≤ p.f23 ∧ 0 ≤ p.f24 ∧ 0 ≤ p.f25 ∧ 0 ≤ p.f26 ∧ 0 ≤ p.f27

end Point

end SmallerShort

end SmoothedOctagon.Certificates
