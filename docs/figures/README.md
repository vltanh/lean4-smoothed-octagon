# Figures

The figures of the smoothed octagon, drawn from the definitions of the library SmoothedPolygons
(`.lake/packages/SmoothedPolygons/SmoothedPolygons/Defs.lean` and `Ch7/`). To regenerate them all:

```sh
python3 scripts/figures/make_figures.py
```

This needs Python 3 with numpy, scipy, matplotlib and Pillow, and takes about ten seconds.
[`scripts/figures/octagon.py`](../../scripts/figures/octagon.py) computes the trajectory `(g, X)` of the
smoothed octagon in two ways: from the closed forms of `Polygon.lean` (`segX_eq`, `segG_eq`, conjugated
by `R⁻ⁱ` on the `i`-th switching interval), and by integrating `g' = gX`, `X' = [P, X]` with scipy. The
two agree to 1e-11. `python3 scripts/figures/octagon.py` runs its checks alone.
[`make_figures.py`](../../scripts/figures/make_figures.py) checks each fact that a caption states with an
`assert`. [`reinhardt_figures.py`](../../scripts/figures/reinhardt_figures.py) is the SVG helper of
lean4-ambidextrous-sofa, so the figures of the two projects look alike.

All pictures are in the library's normalization. `K = smoothedPolygonDisk 1` is in circle
representation (`σ_j(0) = s_j*`), which makes it an affine image of Reinhardt's regular picture, not
that picture itself.

| Figure | What it shows | Checked by `assert` |
| --- | --- | --- |
| [`smoothed-octagon.svg`](smoothed-octagon.svg) | Left: `K` with its 8 straight edges (blue) and 8 hyperbolic arcs (orange), the octagon `O` of its edge lines (dashed) and the six points `s_j* = σ_j(0)` on the unit circle. Middle: `A K`, Reinhardt's smoothed octagon inside a regular octagon. Right: one corner of `A K`, magnified. | The curve `σ₀` is straight exactly while the control is `e₂` or `e₃`, and bends under `e₁`. Each edge is traced in `2 t_sw`, under `e₂` then `e₃`, with the switch at its midpoint. Each arc is traced in `t_sw` and lies on a hyperbola tangent to the two edges at the corner, whose asymptotes are the two flanking edge lines. The map `A = diag(0.973, 1.027)` has determinant 1 and makes `O` regular and `A K` invariant under the rotation by `π/4`; `K` itself is not. The arcs clip less than 3% of the inradius. |
| [`octagon-packing.svg`](octagon-packing.svg) | A patch of the lattice packing `K + 2Λ`, `Λ = ℤs₀* + ℤs₁*`, with the critical hexagon `s₀* … s₅*` of the central copy. | `2Λ` has covolume `√12`. The density is `area(K)/√12 = (8 − 4√2 − ln 2)/(2√2 − 1) ≈ 0.902414`. Two copies have disjoint interiors, and they touch exactly when they are neighbours. The hexagon has area `3√3/2` and its vertices lie on `∂K`. Every affinely regular hexagon inscribed in `K` has area `3√3/2`, so `Λ` is a critical lattice. |
| [`multipoint.gif`](multipoint.gif) | The balanced motion for `t ∈ [0, t_f]`: the contact points `σ_j(t)`, the inscribed hexagon and the six copies `K + 2σ_j(t)` touching `K`, with the control `e₃, e₁, e₂, e₃` on the timeline. It loops: at `t_f`, `σ_j` has reached `σ_{j+1}(0)`. | At every frame: the multi-point conditions hold, the seven copies do not overlap, and the hexagon has area `3√3/2`. Off the switching times exactly two opposite points lie on arcs. `σ_j(t_f) = s_{j+1}*`. The file is under 2 MB. |
| [`upper-half-plane.svg`](upper-half-plane.svg) | The state `X(t) = Φ(z(t))`, `t ∈ [0, t_f]`, as a path in the upper half-plane, inside the star domain `ρ₀, ρ₁, ρ₂ > 0` (shaded). | The star domain is the ideal triangle `−1/√3, 1/√3, ∞`, and the path stays inside it. The path runs along a line through `−1/√3` under `e₃`, a circle through `±1/√3` under `e₁` and a line through `1/√3` under `e₂` (Lemma 7.2.1). The fourth arc, under `e₃` again, retraces the first, so `z(t_f) = R⁻¹·z(0)`. `R` fixes `i` and permutes the ideal vertices. |
| [`density-comparison.svg`](density-comparison.svg) | The densities `area/√12` of the smoothed `(6k+2)`-gons for `k = 1, …, 6`, the disk `π/√12` and the regular octagon `(4 + 4√2)/(5 + 4√2)`. | For each `k` the cost equals the area. The densities increase with `k` and stay below `π/√12`. The octagon's is the least, `δ_oct`. |

`octagon.py` also checks the facts that the figures rely on:

- the data `y₀ = √((√8 − 1)/3)` and `t_sw = ln 2/(2√(√8 − 1))`;
- `det g = 1`, `IsStarState X` and the conservation of `⟨X, Z_u⟩` on each switching interval;
- the endpoint conditions `g(t_f) = R` and `X(t_f) = R⁻¹X(0)R`;
- the cost `−(3/2)∫₀^{t_f}⟨J, X⟩ = ½∫₀^{6t_f} det(σ₀, σ₀') = √12 δ_oct ≈ 3.126054` (to 1e-10);
- `det(σ_j, σ_{j+1}) = √3/2`, `σ_j + σ_{j+2} + σ_{j+4} = 0` and `σ_{j+3} = −σ_j` along the whole trajectory;
- `σ_j(t + t_f) = σ_{j+1}(t)` and the period `6 t_f`;
- the star and curvature conditions of `IsBalancedPair`;
- winding number one for `σ₀`.
