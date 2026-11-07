# Figures

The figures of the smoothed octagon, drawn from the definitions of the library SmoothedPolygons
(`.lake/packages/SmoothedPolygons/SmoothedPolygons/Defs.lean` and `Ch7/`). To regenerate them all:

```sh
python3 scripts/figures/make_figures.py
```

This needs Python 3 with numpy, scipy, matplotlib and Pillow, and takes about a minute.
[`scripts/figures/octagon.py`](../../scripts/figures/octagon.py) computes the trajectory `(g, X)` of the
smoothed octagon in two ways: from the closed forms of `Polygon.lean` (`segX_eq`, `segG_eq`, conjugated
by `R⁻ⁱ` on the `i`-th switching interval), and by integrating `g' = gX`, `X' = [P, X]` with scipy. The
two agree to 1e-11. `python3 scripts/figures/octagon.py` runs its checks alone.
[`make_figures.py`](../../scripts/figures/make_figures.py) checks each fact that a caption states with an
`assert`. [`reinhardt_figures.py`](../../scripts/figures/reinhardt_figures.py) is the SVG helper of
lean4-ambidextrous-sofa, so the figures of the two projects look alike.

The technical figures (the first five below) are in the library's normalization. `K =
smoothedPolygonDisk 1` is in circle representation (`σ_j(0) = s_j*`), which makes it an affine image of
Reinhardt's regular picture, not that picture itself. The plain figures (the last five) use
Reinhardt's regular orientation. There the area-preserving map `A = classical_map` sends `K` to `A K`,
whose edge lines bound a regular octagon with horizontal and vertical edges, and it carries the
critical lattice `Λ = ℤs₀* + ℤs₁*` to `AΛ`. In `packing-densities.svg` the four shapes have equal
inradius 1, and `octagon-construction.svg` uses the same inradius-1 frame. Each smoothed polygon is scaled by `A/a₀₀`, the regular frame `regular_frame`, which puts
its edge through `s₀*` at `x = 1`.

`octagon.py` also computes critical lattices without the trajectory. For a centrally symmetric convex
disk with gauge `‖·‖`, `critical_determinant` minimizes `det(p, q)` over the inscribed affinely regular
hexagons `p, q, q − p, −p, −q, p − q` (Reinhardt, Mahler). The densest lattice packing then has density
area / (4 × critical determinant). The plain figures check their densities this way, independently of
the cost.

**How the smoothed octagon is made.** Take a regular octagon. Replace each corner by an arc of the
hyperbola that is tangent to the two sides meeting at that corner and has the lines of the next two
sides (one step further around the octagon on each side) as its asymptotes. The arc runs between its
two points of tangency. These points cut off `(1 − 1/√2)/2 ≈ 14.6%` of each side at each end, so the
straight part left of each side is `1/√2` of it. Asymptotes plus one tangency determine the hyperbola;
it then touches the other side too. `octagon.py` checks this construction against all eight arcs of the
library's trajectory, and `octagon-construction.svg` shows it for one corner.

| Figure | What it shows | Checked by `assert` |
| --- | --- | --- |
| [`smoothed-octagon.svg`](smoothed-octagon.svg) | Left: `K` with its 8 straight edges (blue) and 8 hyperbolic arcs (orange), the octagon `O` of its edge lines (dashed) and the six points `s_j* = σ_j(0)` on the unit circle. Middle: `A K`, Reinhardt's smoothed octagon inside a regular octagon. Right: one corner of `A K`, magnified. | The curve `σ₀` is straight exactly while the control is `e₂` or `e₃`, and bends under `e₁`. Each edge is traced in `2 t_sw`, under `e₂` then `e₃`, with the switch at its midpoint. Each arc is traced in `t_sw` and lies on a hyperbola tangent to the two edges at the corner, whose asymptotes are the two flanking edge lines. The map `A = diag(0.973, 1.027)` has determinant 1 and makes `O` regular and `A K` invariant under the rotation by `π/4`; `K` itself is not. The arcs clip less than 3% of the inradius. |
| [`octagon-packing.svg`](octagon-packing.svg) | A patch of the lattice packing `K + 2Λ`, `Λ = ℤs₀* + ℤs₁*`, with the critical hexagon `s₀* … s₅*` of the central copy. | `2Λ` has covolume `√12`. The density is `area(K)/√12 = (8 − 4√2 − ln 2)/(2√2 − 1) ≈ 0.902414`. Two copies have disjoint interiors, and they touch exactly when they are neighbours. The hexagon has area `3√3/2` and its vertices lie on `∂K`. Every affinely regular hexagon inscribed in `K` has area `3√3/2`, so `Λ` is a critical lattice. |
| [`multipoint.gif`](multipoint.gif) | The balanced motion for `t ∈ [0, t_f]`: the contact points `σ_j(t)`, the inscribed hexagon and the six copies `K + 2σ_j(t)` touching `K`, with the control `e₃, e₁, e₂, e₃` on the timeline. It loops: at `t_f`, `σ_j` has reached `σ_{j+1}(0)`. | At every frame: the multi-point conditions hold, the seven copies do not overlap, and the hexagon has area `3√3/2`. Off the switching times exactly two opposite points lie on arcs. `σ_j(t_f) = s_{j+1}*`. The file is under 2 MB. |
| [`upper-half-plane.svg`](upper-half-plane.svg) | The state `X(t) = Φ(z(t))`, `t ∈ [0, t_f]`, as a path in the upper half-plane, inside the star domain `ρ₀, ρ₁, ρ₂ > 0` (shaded). | The star domain is the ideal triangle `−1/√3, 1/√3, ∞`, and the path stays inside it. The path runs along a line through `−1/√3` under `e₃`, a circle through `±1/√3` under `e₁` and a line through `1/√3` under `e₂` (Lemma 7.2.1). The fourth arc, under `e₃` again, retraces the first, so `z(t_f) = R⁻¹·z(0)`. `R` fixes `i` and permutes the ideal vertices. |
| [`density-comparison.svg`](density-comparison.svg) | The densities `area/√12` of the smoothed `(6k+2)`-gons for `k = 1, …, 6`, the disk `π/√12` and the regular octagon `(4 + 4√2)/(5 + 4√2)`. | For each `k` the cost equals the area. The densities increase with `k` and stay below `π/√12`. The octagon's is the least, `δ_oct`. |
| [`smoothed-octagon-plain.svg`](smoothed-octagon-plain.svg) | Reinhardt's smoothed octagon `A K` alone, in its regular orientation: a soft fill, its 8 straight edges in blue and its 8 hyperbolic arcs in orange, and the 8 corners cut from the regular octagon as faint orange ghosts. | `det A = 1` and the area is `√12 δ_oct`. `A K` is centrally symmetric and invariant under the rotation by `π/4`. Its edge lines bound a regular octagon with horizontal and vertical edges. The 8 ghosts are congruent and their areas add up to `area(A O) − area(A K)`. Each side keeps a straight middle part of `1/√2` of its length. |
| [`octagon-construction.svg`](octagon-construction.svg) | How the corners are smoothed, in the regular frame of inradius 1: the regular octagon (grey), the smoothed octagon, and for the corner `(1, tan π/8)` the whole hyperbola branch (dashed orange), its asymptotes `y = 1` and `x − y = √2` (dashed) meeting at its centre `C = (1 + √2, 1)`, the tangency points `T₁`, `T₂` and the cut-off corner (shaded). Right: that corner, magnified. | The asymptotes are the lines of the two sides next to the sides at the corner, and `C` is where they meet. The classical construction, from the octagon alone, gives a hyperbola `uv = κ` that matches the library's arc to 1e-10; its tangency to the second side comes out of the computation. `T₁ = (1, 1 − 1/√2)` and `T₂ = (√2 − 1/2, 1/2)`, each `(3√2 − 4)/2` from the corner. The arc meets both sides with a common tangent (C¹). The straight part of each side is `2 − √2`, `1/√2` of the side. The cut-off corner has area `(area(O) − area(K))/8`. |
| [`octagon-tiling.svg`](octagon-tiling.svg) | The densest packing `A K + 2AΛ`, cropped to a rectangle: each copy shares a vertical edge with the copies beside it and touches the four above and below at single points. White gaps remain where copies do not touch. | The covolume is `√12` and the density `δ_oct`. `AΛ` is critical: its determinant `√3/2` equals the critical determinant of `A K`, and it is admissible with six points on `∂(A K)`. The six neighbours touch, and every other copy is farther apart (gauge distance > 2.3). The copies beside each other share a whole edge; the other contacts are single edge–arc junctions. |
| [`packing-densities.svg`](packing-densities.svg) | The disk, the regular octagon, the smoothed 14-gon (`k = 2`) and the smoothed octagon, all of inradius 1, in decreasing order of packing density. Each stands in front of a patch of its densest lattice packing, with its density to six digits underneath. | The densities `π/√12 = 0.906900`, `(4 + 4√2)/(5 + 4√2) = (12 − 4√2)/7 = 0.906164`, `0.906052` (the cost of the `k = 2` trajectory over `√12`) and `δ_oct = 0.902414` agree with area / (4 × critical determinant) to 2e-6. Each drawn lattice has the critical determinant as its determinant and is admissible with six boundary points. The order is strict. The regular octagon's critical determinant is `√2 − 1/2`. Each smoothed polygon's edge lines bound a regular polygon of inradius 1. |
| [`worst-packer.gif`](worst-packer.gif) | For the top of the README: copies of Reinhardt's smoothed octagon sliding through its one-parameter family of densest packings over one period `[0, t_f)` (the balanced motion). They keep their orientation and stay in contact, so the octagon visibly has a continuum of densest packings. One copy is tinted slightly deeper as an anchor; there are no lines, points or text. 120 frames at 60 ms (7.2 s, 16.7 fps), 600 × 340 px. | Every frame is a densest packing: covolume `√12`, density `δ_oct`, no overlaps, six contacts. The lattice at `t_f` is the lattice at 0 (a unimodular change of basis), so the loop is seamless. The frame rate is at least 15 fps, the loop lasts 6 to 10 s, and the file is under 2 MB. |

`octagon.py` also checks the facts that the figures rely on:

- the data `y₀ = √((√8 − 1)/3)` and `t_sw = ln 2/(2√(√8 − 1))`;
- `det g = 1`, `IsStarState X` and the conservation of `⟨X, Z_u⟩` on each switching interval;
- the endpoint conditions `g(t_f) = R` and `X(t_f) = R⁻¹X(0)R`;
- the cost `−(3/2)∫₀^{t_f}⟨J, X⟩ = ½∫₀^{6t_f} det(σ₀, σ₀') = √12 δ_oct ≈ 3.126054` (to 1e-10);
- `det(σ_j, σ_{j+1}) = √3/2`, `σ_j + σ_{j+2} + σ_{j+4} = 0` and `σ_{j+3} = −σ_j` along the whole trajectory;
- `σ_j(t + t_f) = σ_{j+1}(t)` and the period `6 t_f`;
- the star and curvature conditions of `IsBalancedPair`;
- winding number one for `σ₀`.
