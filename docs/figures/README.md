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

The technical figures (the first six below) are in the library's normalization. `K =
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

**How the smoothed octagon is made.** Take the regular octagon of inradius 1, whose side `k` lies on
the line `ℓ_k: x cos(kπ/4) + y sin(kπ/4) = 1` (`k = 0, …, 7`), and write `d_k` for the distance to
`ℓ_k`. The corner of `ℓ_k` and `ℓ_{k+1}` is replaced by an arc of the hyperbola `d_{k−1} · d_{k+2} = √2/4`.
Its asymptotes are the lines `ℓ_{k−1}` and `ℓ_{k+2}` of the next two sides, and it touches the two
sides at the corner. For the corner `(1, √2 − 1)` of `ℓ₀: x = 1` and `ℓ₁: x + y = √2`, this is
`(1 − y)(√2 − x + y) = 1/2`, with asymptotes `ℓ₂: y = 1` and `ℓ₇: x − y = √2` meeting at its centre
`(1 + √2, 1)`. The arc runs between the tangency points `T₁ = (1, 1 − 1/√2)` and `T₂ = (√2 − 1/2, 1/2)`,
where `d₂ d₇ = (1/√2)(1/2)`. Each tangency point is `(3√2 − 4)/2 ≈ 0.1213` from the corner. The straight
part kept of each side, of length `2(√2 − 1)`, is `2 − √2`, which is `1/√2` of the side. The corner is
cut to a depth of `sec(π/8) − (1 − 2^(−3/4))/sin(π/8) ≈ 0.0230`, about 2.3% of the inradius.
Where the formula comes from: for the corner of `ℓ₀` and `ℓ₁`, the distances to the two dashed lines are `d₂ = 1 − y` (to `ℓ₂: y = 1`) and `d₇ = (√2 − x + y)/√2` (to `ℓ₇: x − y = √2`). The arc is where their product is constant: `d₂ · d₇ = √2/4`, that is `(1 − y)(√2 − x + y) = ½`. The constant is forced. Along each side at the corner, `d₂ · d₇` is a quadratic that opens downward, and its largest value is exactly `√2/4`, reached at the tangency point (`T₁` on `ℓ₀`, `T₂` on `ℓ₁`). A smaller constant would make the curve cross the sides twice, a larger one would miss them. `√2/4` is the value at which it just touches both. At the middle of the arc, `d₂ = d₇ = 2^(−3/4)`.
`octagon.py` checks `d_{k−1} d_{k+2} = √2/4` along all eight arcs of the library's trajectory to 1e-10,
together with the tangency points, the depth and the classical construction from the octagon alone
(asymptotes plus one tangency, the second tangency then following).

| Figure | What it shows | Checked by `assert` |
| --- | --- | --- |
| [`smoothed-octagon.svg`](smoothed-octagon.svg) | Left: `K` with its 8 straight edges (blue) and 8 hyperbolic arcs (orange), the octagon `O` of its edge lines (dashed) and the six points `s_j* = σ_j(0)` on the unit circle. Middle: `A K`, Reinhardt's smoothed octagon inside a regular octagon. Right: one corner of `A K`, magnified. | The curve `σ₀` is straight exactly while the control is `e₂` or `e₃`, and bends under `e₁`. Each edge is traced in `2 t_sw`, under `e₂` then `e₃`, with the switch at its midpoint. Each arc is traced in `t_sw` and lies on a hyperbola tangent to the two edges at the corner, whose asymptotes are the two flanking edge lines. The map `A = diag(0.973, 1.027)` has determinant 1 and makes `O` regular and `A K` invariant under the rotation by `π/4`; `K` itself is not. The arcs clip less than 3% of the inradius. |
| [`octagon-packing.svg`](octagon-packing.svg) | A patch of the lattice packing `K + 2Λ`, `Λ = ℤs₀* + ℤs₁*`, with the critical hexagon `s₀* … s₅*` of the central copy. | `2Λ` has covolume `√12`. The density is `area(K)/√12 = (8 − 4√2 − ln 2)/(2√2 − 1) ≈ 0.902414`. Two copies have disjoint interiors, and they touch exactly when they are neighbours. The hexagon has area `3√3/2` and its vertices lie on `∂K`. Every affinely regular hexagon inscribed in `K` has area `3√3/2`, so `Λ` is a critical lattice. |
| [`multipoint.gif`](multipoint.gif) | The balanced motion for `t ∈ [0, t_f]`: the contact points `σ_j(t)`, the inscribed hexagon and the six copies `K + 2σ_j(t)` touching `K`, with the control `e₃, e₁, e₂, e₃` on the timeline. It loops: at `t_f`, `σ_j` has reached `σ_{j+1}(0)`. | At every frame: the multi-point conditions hold, the seven copies do not overlap, and the hexagon has area `3√3/2`. Off the switching times exactly two opposite points lie on arcs. `σ_j(t_f) = s_{j+1}*`. The file is under 2 MB. |
| [`upper-half-plane.svg`](upper-half-plane.svg) | The state `X(t) = Φ(z(t))`, `t ∈ [0, t_f]`, as a path in the upper half-plane, inside the star domain `ρ₀, ρ₁, ρ₂ > 0` (shaded). | The star domain is the ideal triangle `−1/√3, 1/√3, ∞`, and the path stays inside it. The path runs along a line through `−1/√3` under `e₃`, a circle through `±1/√3` under `e₁` and a line through `1/√3` under `e₂` (Lemma 7.2.1). The fourth arc, under `e₃` again, retraces the first, so `z(t_f) = R⁻¹·z(0)`. `R` fixes `i` and permutes the ideal vertices. |
| [`octagon-arcs.svg`](octagon-arcs.svg) | The definition of the smoothed octagon `K`: the six points `s_j*` of a regular hexagon on the unit circle (white dots, dashed hexagon), and the six arcs `g(t) s_j*`, `t ∈ [0, t_f]`, of its trajectory, each in its own colour with an arrow for its direction. `K`, their convex hull, is shaded. | Arc `j` runs from `s_j*` to `s_{j+1}*` and lies on `∂K`. The six arcs are `σ₀` over the whole period, since `σ_j(t) = σ₀(t + j t_f)`. Together they form a closed curve that never turns right and turns once in all, so it is convex and bounds its convex hull, whose area is `√12 δ_oct`. |
| [`density-comparison.svg`](density-comparison.svg) | The densities `area/√12` of the smoothed `(6k+2)`-gons for `k = 1, …, 6`, the disk `π/√12` and the regular octagon `(4 + 4√2)/(5 + 4√2)`. | For each `k` the cost equals the area. The densities increase with `k` and stay below `π/√12`. The octagon's is the least, `δ_oct`. |
| [`smoothed-octagon-plain.svg`](smoothed-octagon-plain.svg) | Reinhardt's smoothed octagon `A K` alone, in its regular orientation: a soft fill, its 8 straight edges in blue and its 8 hyperbolic arcs in orange, and the 8 corners cut from the regular octagon as faint orange ghosts. | `det A = 1` and the area is `√12 δ_oct`. `A K` is centrally symmetric and invariant under the rotation by `π/4`. Its edge lines bound a regular octagon with horizontal and vertical edges. The 8 ghosts are congruent and their areas add up to `area(A O) − area(A K)`. Each side keeps a straight middle part of `1/√2` of its length. |
| [`octagon-construction.svg`](octagon-construction.svg) | The construction in the regular frame of inradius 1. Shown: the regular octagon (grey), the smoothed octagon, the sides `ℓ₀: x = 1` and `ℓ₁: x + y = √2` of the corner `(1, √2 − 1)`, the asymptotes `ℓ₂: y = 1` and `ℓ₇: x − y = √2` (dashed) meeting at `C = (1 + √2, 1)`, and the whole hyperbola branch `(1 − y)(√2 − x + y) = ½` (dashed orange), with the caption "the product of the distances to the two dashed lines is constant". For the middle point of the arc, the perpendiculars to `ℓ₂` and `ℓ₇` are drawn and labelled `d₂` and `d₇`. A derivation block gives `d₂ = 1 − y`, `d₇ = (√2 − x + y)/√2`, `d₂ · d₇ = √2/4 ⇔ (1 − y)(√2 − x + y) = ½`, and states that `√2/4` makes the curve touch both sides. The cut-off corner is shaded. Right: the corner magnified ×4, with `T₁ = (1, 1 − 1/√2)` and `T₂ = (√2 − ½, ½)`. Every label sits in empty space, with a leader line where needed. | Side `k` lies on `ℓ_k`, and the asymptotes are `ℓ₇` and `ℓ₂`, meeting at `C`. The library's arc satisfies `d₂ d₇ = √2/4`, that is `(1 − y)(√2 − x + y) = ½`, to 1e-10, and also `uv = κ` of the classical construction. The drops from the sample point meet `ℓ₂` and `ℓ₇` at right angles, with lengths `d₂ = d₇ = 2^(−3/4)`. Along each side at the corner, `d₂ d₇` is a downward quadratic with top value `√2/4` at `T₁` and `T₂`. At those points `d₂ d₇ = (1/√2)(1/2)`; they lie `(3√2 − 4)/2` from the corner, with a common tangent (C¹). The whole branch keeps `d₂, d₇ > 0`. The straight part is `2 − √2 = (1/√2) ·` side. The depth is `sec(π/8) − (1 − 2^(−3/4))/sin(π/8)`, and the cut area is `(area(O) − area(K))/8`. No label box, padded by 4 px, meets any drawn line, curve, dot, fill, other label or other leader. |
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
