# Prior work

[Back to the README](../README.md)

The sources below come from a search on 7 November 2026 of arXiv, zbMATH Open, Crossref, Math-Net.Ru, publisher
pages, the digital libraries of the Royal Netherlands Academy of Arts and Sciences (KNAW) and of the University of
Szeged, the Kurt Mahler archive, GitHub, Google DeepMind's formal-conjectures repository, the Palomar registry,
MathOverflow, and press and blog coverage.

Throughout, `δ(K)` is the greatest density of a packing of the plane by congruent copies of a centrally symmetric
convex disk `K`. Reinhardt's conjecture says that `δ(K)` is least for the smoothed octagon, with
`δ = (8 − 4√2 − log 2)/(2√2 − 1) = 0.902414…`, against `π/√12 = 0.906899…` for the circular disk. Mahler and the
older literature use the affine invariant `Q(K) = V(K)/Δ(K)`, the area over the least determinant of a lattice with
no point other than `0` inside `K`; then `δ(K) = Q(K)/4` (Mahler, *On the area and the densest packing of convex
domains*, p. 118; Ledermann and Mahler, p. 320; both below).

## Origins, 1904-1949

- Hermann Minkowski, *Dichteste gitterförmige Lagerung kongruenter Körper*, Nachrichten von der Gesellschaft der
  Wissenschaften zu Göttingen, Mathematisch-Physikalische Klasse 1904, 311-355
  ([JFM 35.0508.02](https://zbmath.org/?q=an:35.0508.02)), posed the densest lattice packing of translates of a
  convex body and reduced it to centrally symmetric bodies.
  - His *Diophantische Approximationen* (Teubner, Leipzig, 1907,
    [doi:10.1007/978-3-663-16055-7](https://doi.org/10.1007/978-3-663-16055-7)) gave, in Mahler's words, "a simple
    rule for obtaining the critical lattices of a convex domain by means of the inscribed hexagons". Ledermann and
    Mahler call `Q(K) ≤ 4`, with equality only for parallelograms and hexagons, "Minkowski's classical theorem on
    convex domains".
- Mahler (1947, below) cites "W. Blaschke, Differentialgeometrie II, § 27, problem 17" as an earlier statement of
  the lattice-packing question: W. Blaschke, *Vorlesungen über Differentialgeometrie und geometrische Grundlagen von
  Einsteins Relativitätstheorie II: Affine Differentialgeometrie*, ed. K. Reidemeister (Springer, Berlin, 1923,
  [doi:10.1007/978-3-642-47392-0](https://doi.org/10.1007/978-3-642-47392-0)).
  - Hales and Vajjha (below, §1.2) write that the problem appears there as "Courant's conjecture", that the
    circular disk is the worst of all centrally symmetric convex disks. Hales's blog says that Courant
    "conjectured that the minimal Minkowski constant in two dimensions is obtained by a circular disk". We did not
    see Blaschke's text.
- Karl Reinhardt, *Über die dichteste gitterförmige Lagerung kongruenter Bereiche in der Ebene und eine besondere
  Art konvexer Kurven*, Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg 10 (1934), 216-230
  ([doi:10.1007/BF02940676](https://doi.org/10.1007/BF02940676)).
  - The Jahrbuch review ([JFM 60.0536.13](https://zbmath.org/?q=an:60.0536.13)) summarizes it: the densest lattice
    packing of a centrally symmetric convex disk comes from a circumscribed centrally symmetric hexagon of least
    area; through each boundary point of a disk of least density passes a single supporting line, which is a side
    of such a hexagon; such disks exist that are not circular; "Für welchen dieser Bereiche das Dichteminimum
    eintritt, bleibt offen."
  - On p. 230 Reinhardt proposed the figure "welche aus einem regelmässigen Achteck entsteht", each corner cut
    off by the hyperbola tangent to its two sides and asymptotic to the next two (quoted by Ledermann and Mahler,
    p. 320).
  - Hales's 2011 article (below, §2) restates Reinhardt's lemmas: a minimizer exists by Blaschke's selection
    theorem, has no corners, and every boundary point is the midpoint of a side of a circumscribed hexagon of
    least area.
- Kurt Mahler, independently, in three papers in the Proceedings of the Koninklijke Nederlandse Akademie van
  Wetenschappen 50 (1947):
  - *On irreducible convex domains*, 98-107 (communicated 21 December 1946,
    [KNAW scan](https://dwc.knaw.nl/DL/publications/PU00018298.pdf)): critical lattices and irreducible domains,
    those whose proper subdomains all have smaller determinant.
  - *On the area and the densest packing of convex domains*, 108-118 (communicated 21 December 1946,
    [KNAW scan](https://dwc.knaw.nl/DL/publications/PU00018299.pdf)). He reduces the least `Q(K)` to a problem in
    the calculus of variations and proves that it has a solution, an irreducible convex domain that "is *not* an
    ellipse, contrary to what might be expected". He writes "I have not succeeded in solving either of the two
    problems", and ends §6 with the "Final remark: It seems highly probable from the convexity condition, that the
    boundary of an extreme convex domain consists of line segments and arcs of hyperbolae. So far, however, I have
    not succeeded in proving this assertion" (p. 117). Hales and Vajjha call this Mahler's First conjecture.
  - *On the minimum determinant and the circumscribed hexagons of a convex domain*, 692-703 (communicated 31 May
    1947, [KNAW scan](https://dwc.knaw.nl/DL/publications/PU00018367.pdf)). The boundary of an irreducible
    domain other than a parallelogram has a continuous tangent everywhere. Over centrally symmetric octagons the
    least `Q` is `16(3 − √2)/7 = 3.6246…`, attained only by affine images of the regular octagon and below the
    ellipse's `2π/√3 = 3.6275…` ("This result is rather surprising"). §12 builds the smoothed octagon, with
    `Q ≈ 3.6096567`: "This is an upper bound for Q, and possibly even its exact value."
  - In 1946 Mahler had also proved `Q(K) ≥ √12`, that is `δ(K) ≥ √3/2`, against `π²/3` from the Minkowski-Hlawka
    theorem (*The theorem of Minkowski-Hlawka*, Duke Mathematical Journal 13 (1946), 611-621, Lemma 2,
    [doi:10.1215/S0012-7094-46-01351-8](https://doi.org/10.1215/S0012-7094-46-01351-8)).
- Walter Ledermann and Kurt Mahler, *On lattice points in a convex decagon*, Acta Mathematica 81 (1949), 319-351
  ([doi:10.1007/BF02395026](https://doi.org/10.1007/BF02395026)).
  - "Without knowledge of his paper, one of us recently rediscovered this formula and was led to the same
    conjecture"; "It was conjectured by Reinhardt that this lower bound is attained for the *smoothed octagon*,
    but no proof has so far been given." The name is theirs: "We call this figure the smoothed octagon."
  - Over centrally symmetric decagons the least `Q` is `3.62173…`, attained by a non-regular decagon. The smoothed
    decagon has `Q = 3.60974…`, larger than the smoothed octagon's `3.60965…`, "a result which seems to support
    Reinhardt's conjecture".
- Two slips in the later literature:
  - Hales and Vajjha (§1.2) cite the 692-703 paper for Mahler's calculus of variations and his final remark, and
    the 108-118 paper for the construction of the smoothed octagon; the KNAW scans show the reverse.
  - Hales's 2011 article lists the decagon paper under Ledermann alone; Crossref and zbMATH list both authors.

## Densest packings are lattice packings

- László Fejes Tóth, *Some packing and covering theorems*, Acta Scientiarum Mathematicarum (Szeged) 12 A (1950),
  62-67 ([record](http://acta.bibl.u-szeged.hu/13588/)), proved that "the density of an irregular packing of an
  infinite set of non-overlapping congruent convex domains having a centre of symmetry cannot exceed the density
  of the closest lattice of the domains". For centrally symmetric disks, Reinhardt's lattice problem is therefore
  the problem for all packings by congruent copies.
  - In a footnote he writes that, as he learned from I. Fáry, "this result was also found by K. Mahler who
    announced this fact during a lecture of Chabauty held in Paris in October 1949".
  - Gábor Fejes Tóth's survey states the theorem as `δ(K) ≤ a(K)/H(K)` for every convex disk, `H(K)` the least
    area of a circumscribed hexagon, sharp for centrally symmetric disks, where it gives `δ = δ_T = δ_L` (G. Fejes
    Tóth, *Packing and covering*, chapter 2 of *Handbook of Discrete and Computational Geometry*, 3rd edition, CRC
    Press, 2017, [doi:10.1201/9781315119601](https://doi.org/10.1201/9781315119601)).
- C. A. Rogers, *The closest packing of convex two-dimensional domains*, Acta Mathematica 86 (1951), 309-321
  ([doi:10.1007/BF02392671](https://doi.org/10.1007/BF02392671)); corrigendum, Acta Mathematica 104 (1960),
  305-306 ([doi:10.1007/BF02546391](https://doi.org/10.1007/BF02546391)).
  - A. Bezdek and W. Kuperberg write that the result of Fejes Tóth, "independently discovered also by Rogers", says
    that "the density of a packing with translates of a convex disk cannot exceed the maximum density attained in
    a lattice arrangement" (*Dense packing of space with various convex solids*, in *Geometry—Intuitive, Discrete,
    and Convex*, Bolyai Society Mathematical Studies 24, Springer, 2013, 65-90,
    [doi:10.1007/978-3-642-41498-5_3](https://doi.org/10.1007/978-3-642-41498-5_3);
    [arXiv:1008.2398](https://arxiv.org/abs/1008.2398)).
- G. Kuperberg and W. Kuperberg, *Double-lattice packings of convex bodies in the plane*, Discrete & Computational
  Geometry 5 (1990), 389-397 ([doi:10.1007/BF02187800](https://doi.org/10.1007/BF02187800)), proved that every
  convex disk, symmetric or not, has a double-lattice packing of density at least `√3/2`, which zbMATH describes as
  "extending a result of Mahler and Féjes Tòth" ([Zbl 0709.52007](https://zbmath.org/?q=an:0709.52007)).

## Lower bounds and local optimality

- Lower bounds for the least density, in Mahler's `Q`:
  - `π²/3` (`δ ≥ 0.822`) from the Minkowski-Hlawka theorem, and `√12` (`δ ≥ 0.866`) by Mahler in 1946 (above).
  - V. Ennola, *On the lattice constant of a symmetric convex domain*, Journal of the London Mathematical Society
    36 (1961), 135-138 ([doi:10.1112/jlms/s1-36.1.135](https://doi.org/10.1112/jlms/s1-36.1.135)). By the zbMATH
    review of Tammela's paper, Ennola proved `Q ≥ 3.52…` (`δ ≥ 0.88`) and "announced a further improvement to
    3.57… but the details were not published". We could not open Ennola's paper.
  - P. P. Tammela, *An estimate of the critical determinant of a two-dimensional convex symmetric domain*, Izvestiya
    Vysshikh Uchebnykh Zavedenii. Matematika 1970, no. 12 (103), 103-107, in Russian, received 25 March 1969
    ([Math-Net.Ru](https://www.mathnet.ru/eng/ivm3798); [Zbl 0217.03702](https://zbmath.org/?q=an:0217.03702)),
    "elaborates further the method of Mahler and Ennola" and proves `Q ≥ 3.570624`, that is `δ ≥ 0.892656`.
  - G. Fejes Tóth's survey of 2017 (above) still lists `0.892656…` [Tam70] as the bound.
  - Hales and Vajjha (§1.2) write that "V. Ennola in 1961 and Paul Tammela in 1969" showed `δ ≥ 0.8926…`. By the
    zbMATH review, Ennola's published bound is `0.88`, and Tammela's paper is dated 1969 by its receipt and 1970
    by its issue; Hales's 2011 article dates it 1970.
- F. L. Nazarov, *On the Reinhardt problem of the lattice packings of convex plots. The local extremality of the
  Reinhardt octagon*, Zapiski Nauchnykh Seminarov LOMI 151 (1986), 104-114, in Russian
  ([Math-Net.Ru](https://www.mathnet.ru/eng/znsl5050)); English translation, *Reinhardt's problem of lattice
  packings of convex domains: Local extremality of the Reinhardt octagon*, Journal of Soviet Mathematics 43 (1988),
  2687-2693 ([doi:10.1007/BF01727653](https://doi.org/10.1007/BF01727653)).
  - zbMATH: "He proves that the Reinhardt octagon is a local minimum for the problem"
    ([Zbl 0606.52008](https://zbmath.org/?q=an:0606.52008)). Hales and Vajjha describe it as a local minimum "in
    the space of convex disks equipped with the Hausdorff metric".
- We found no published improvement of Tammela's bound; the only later claim is M. Ho's unreviewed repository of
  November 2026 ([below](#claims-and-computations-since-2017)).

## Hales's optimal-control program

- Thomas C. Hales, *On the Reinhardt conjecture*, Vietnam Journal of Mathematics 39 (2011), no. 3, 287-307
  ([Zbl 1239.52002](https://zbmath.org/?q=an:1239.52002); [arXiv:1103.4518](https://arxiv.org/abs/1103.4518),
  March 2011).
  - The work was done in 2007 at the Hanoi Math Institute and presented in June 2008 at a conference in
    Budapest in honour of L. Fejes Tóth (first-page footnote).
  - It casts the problem as a problem of Bolza in the calculus of variations. The circle is, up to affine maps,
    the only solution of the Euler-Lagrange equations, and second-order conditions show that it does not minimize.
    The boundary of a minimizer is `C¹` with Lipschitz derivative, and "If a minimizer is piecewise analytic, then
    it is a smoothed polygon"; the analyticity assumption remains to be removed and the polygon shown to be an
    octagon (abstract).
- On 1 November 2014 John Baez quoted the proposal behind an NSF grant of Hales's, in which "The PI ... proposes to
  complete the proof of the Reinhardt conjecture", next to Greg Egan's animation of the octagon's one-parameter
  family of densest packings
  ([AMS Visual Insight](https://blogs.ams.org/visualinsight/2014/11/01/packing-smoothed-octagons/)).
- Thomas Hales, *The Reinhardt conjecture as an optimal control problem*,
  [arXiv:1703.01352](https://arxiv.org/abs/1703.01352) (3 March 2017, 41 pages). arXiv lists one version and no
  journal reference.
  - Its abstract states that the smoothed octagon, and more generally the smoothed regular `(6k+2)`-gon, is a
    Pontryagin extremal with bang-bang control; that the smoothed octagon is "a strict (micro) local minimum"; that
    the optimal solution has no singular arcs; that extremals avoiding the singular locus have finitely many
    switches; and that the problem reduces to an optimization on a five-dimensional manifold. Some proofs use a
    computer algebra system.
- Koundinya Vajjha, *On the Reinhardt Conjecture and Formal Foundations of Optimal Control*, PhD thesis, University
  of Pittsburgh, defended 25 July 2022 before T. C. Hales, K. Kaveh, A. Vainchtein and G. Kuperberg
  ([arXiv:2208.04443](https://arxiv.org/abs/2208.04443), 180 pages;
  [D-Scholarship](https://d-scholarship.pitt.edu/43482/)).
  - It gives the Hamiltonian structure and a Lax pair, confines the Pontryagin extremals to a compact domain, and
    recovers near the singular locus the Pontryagin system of the multi-dimensional Fuller problem, whose
    logarithmic-spiral trajectories, for a circular control set, perform "an infinite number of rotations on the
    boundary of the disk in finite time". Its second part is on the formalization of reinforcement-learning
    theory, not on the Reinhardt problem.
- Thomas Hales and Koundinya Vajjha, *Packings of Smoothed Polygons*,
  [arXiv:2405.04331](https://arxiv.org/abs/2405.04331) (7 May 2024, "283 page book"). arXiv lists one version and no
  journal reference.
  - Main theorem (16.3.1, Mahler's First conjecture): the global minimizer of the Reinhardt control problem is
    bang-bang with finitely many switches, so the minimizer is a finite-sided smoothed polygon. The abstract: "His
    second conjecture is identical to the Reinhardt conjecture, which remains open."
  - The obstacle is chattering, possible minimizers with infinitely many sides. The book finds the Fuller system
    (A. T. Fuller, 1963) near the singular locus and analyzes a Poincaré first-recurrence map on a blow-up, with
    computer-assisted proofs in a computer algebra system (Mathematica, by Hales's blog post).
  - The known extremals are the smoothed `(6k+2)`-gons and their limit, the circle; the octagon has the least
    density among them. "No other extremals have been found, but we have no proof that no other extremals exist.
    In light of our results, a proof that no other extremals exist would complete a proof of the Reinhardt
    conjecture" (§1.3). Remark 7.6.3 suggests that the smoothed `(6k−2)`-gons are extremals of the problem of
    maximizing the area.
  - Hales's blog post of 13 May 2024 repeats that the Reinhardt conjecture "remains open"
    ([Jigger Wit](https://jiggerwit.wordpress.com/2024/05/13/packings-of-smoothed-polygons/)). Quanta Magazine
    reported on 28 June 2024 that "The work has yet to be peer reviewed", that H. Cohn and G. Kuperberg had read it
    informally, and quoted Hales on the full conjecture: "Perhaps all the ideas are in place to complete Reinhardt.
    Perhaps not." (Gregory Barber,
    [*Why Is This Shape So Terrible to Pack?*](https://www.quantamagazine.org/why-is-this-shape-so-terrible-to-pack-20240628/)).
    Hales spoke on the book at the Pittsburgh colloquium on 20 September 2024
    ([abstract](https://www.mathematics.pitt.edu/node/4716)).
- Posters by the undergraduates Lark Song and Sasha Sluis-Cremer, with Hales as mentor
  ([lark-song/smoothed-decagon](https://github.com/lark-song/smoothed-decagon); the file names refer to MAA
  MathFest, 4 August 2023, and the Joint Mathematics Meetings, 5 January 2024; an earlier poster of 14 April 2023 is
  also by Neil MacLachlan), conjecture that "The smoothed decagon has the highest packing density among all
  balanced disks in the plane". They state as theorems that every smoothed `(6k−2)`-gon given by a bang-bang
  control is a Pontryagin extremal, and that a counterexample to their conjecture exists, for which "Final
  verification is being made". We found no paper.

## Claims and computations since 2017

- arXiv: a search of abstracts for "Reinhardt conjecture", "Reinhardt problem", "smoothed octagon" and "smoothed
  polygon" finds only the papers of 2011, 2017 and 2024 above and papers on unrelated uses of Reinhardt's name.
  The AlphaEvolve problem list of Georgiev, Gómez-Serrano, Tao and Wagner
  ([arXiv:2511.02864](https://arxiv.org/abs/2511.02864), version 3) does not mention the problem. We found no
  announced proof of the conjecture.
- Matthew Ho's [sunfishho/reinhardt-density-bound](https://github.com/sunfishho/reinhardt-density-bound), created
  2 November 2026, claims in Lean that every centrally symmetric convex disk has packing density greater than
  `0.8950112`, which would improve Tammela's `0.892656` of 1970. We found no review of it.
  - The theorem `Certificate.Packing.reinhardt_density_lower_bound` is stated for the supremum of the
    densities of packings by congruent copies, and the README says "No optimality of lattice packings is assumed".
  - The README describes the route ("As described by GPT Astra"): an exact certificate (Gram matrices and a
    polynomial potential) bounds the cost of control trajectories; "The published compact-domain confinement and
    the Hales–Vajjha area estimate are proved"; a global minimizer is constructed, and the bound passes from it to
    every disk.
  - It reports runs of Comparator and Nanoda on 30 October 2026, on macOS "without Linux sandbox isolation", and
    states that "A clean standalone `lake build` has not been validated". The lean4-smoothed-polygon README calls
    it an "independent, unreviewed Lean development".
- Jeewon Kim's expository LaTeX notes on the book, which do not claim the octagon case
  ([dylan0301/UnderstandingReinhardt](https://github.com/dylan0301/UnderstandingReinhardt), August 2026).

## Formalizations

- [vltanh/lean4-smoothed-polygon](https://github.com/vltanh/lean4-smoothed-polygon) (5-7 November 2026, written by
  Claude Opus 5.5 at the request of The-Anh Vu-Le) formalizes Chapters 2-4, 6 and 7 of Hales and Vajjha in Lean 4,
  without `sorry` or axioms outside its Challenge statements.
  - It proves Theorem 7.5.6 (the smoothed `(6k+2)`-gons are Pontryagin extremals with bang-bang control), the
    octagon's density `(8 − √32 − ln 2)/(√8 − 1)`, Theorem 7.7.1 in a corrected form (the octagon is an isolated
    extremal, up to time translation), and that every minimizer of the control problem lifts to a Pontryagin
    extremal.
  - It proves the classical results it uses, among them Fejes Tóth's theorem, Minkowski's and Mahler's theorems
    on critical lattices and circumscribed hexagons, and Mahler's Lemma 3 on irreducible domains.
  - Its report lists errors and gaps in the book; for instance, Lemma 2.2.1 (Reinhardt's tiling lemma) is false as
    printed and is refuted in Lean.
  - Mahler's First conjecture is not formalized, and "The Reinhardt conjecture itself (that the smoothed octagon is
    the least dense) remains open, and is not claimed here."
- [vltanh/lean4-optimal-control](https://github.com/vltanh/lean4-optimal-control) (7 November 2026) proves the
  Pontryagin maximum principle with free terminal time, an integral cost and mixed boundary conditions, by Agrachev
  and Sachkov's argument, and Filippov's theorem; Brouwer's fixed-point theorem comes from
  [vltanh/lean4-fixed-point](https://github.com/vltanh/lean4-fixed-point). An earlier Lean attempt,
  [willcforte/pontryagin-lean](https://github.com/willcforte/pontryagin-lean) (13 May 2026), "states its key steps
  as axioms", according to the lean4-smoothed-polygon README.
- Ho's repository (above) keeps in `reference/028_reinhardt.lean` an "original benchmark" from a list of open
  problems that it does not name: a Lean statement, with `sorry`, that every centrally symmetric convex disk has
  packing density at least `(8 − 4√2 − log 2)/(2√2 − 1)`, with packings by congruent copies and densities defined
  from scratch. Its header says "Verified 2026-09-19: open".
- Google DeepMind's [formal-conjectures](https://github.com/google-deepmind/formal-conjectures) has no statement
  of the problem at commit `2055e5a` (6 November 2026).
- The [Palomar registry](https://palomar-registry.org) lists nothing on the problem on 7 November 2026: a search of
  its 1013 results for "Reinhardt" finds only a formalization of several complex variables (Reinhardt domains), and
  searches for "smoothed octagon", "smoothed polygon", "packing density" and "Pontryagin" find nothing.
- Hales led the formal proof of the Kepler conjecture in HOL Light and Isabelle (T. Hales et al., *A formal proof of
  the Kepler conjecture*, Forum of Mathematics, Pi 5 (2017), e2,
  [doi:10.1017/fmp.2017.1](https://doi.org/10.1017/fmp.2017.1)). A web search and a GitHub code search found no
  formalization of the Reinhardt problem in Isabelle, Coq or HOL Light.

## Related problems

- Three dimensions. Yoav Kallus, *The 3-ball is a local pessimum for packing*, Advances in Mathematics 264 (2014),
  355-370 ([doi:10.1016/j.aim.2014.07.015](https://doi.org/10.1016/j.aim.2014.07.015);
  [arXiv:1212.2551](https://arxiv.org/abs/1212.2551)), proves that origin-symmetric convex solids close enough to the
  ball pack more densely than balls, a local form of the conjecture that the ball packs worst.
  - Kallus writes that the conjecture is known as Ulam's "due to a remark Gardner attributes to Ulam, though there is
    no evidence to confirm that Ulam ever stated it as a conjecture" (*Pessimal packing shapes*, Geometry & Topology
    19 (2015), 343-363, [doi:10.2140/gt.2015.19.343](https://doi.org/10.2140/gt.2015.19.343);
    [arXiv:1305.0289](https://arxiv.org/abs/1305.0289)).
- Disks without central symmetry. I. Fáry, *Sur la densité des réseaux de domaines convexes*, Bulletin de la
  Société Mathématique de France 78 (1950), 152-161 ([doi:10.24033/bsmf.1413](https://doi.org/10.24033/bsmf.1413)),
  showed that triangles, with `2/3`, have the least lattice packing density among all convex disks; Kallus also
  cites R. Courant, *The least dense lattice packing of two-dimensional convex bodies*, Communications on Pure and
  Applied Mathematics 18 (1965), 339-343 ([doi:10.1002/cpa.3160180125](https://doi.org/10.1002/cpa.3160180125)).
  - In *Pessimal packing shapes* Kallus proves that the regular heptagon, with `0.89269…`, is a local minimum of
    the double-lattice packing density, and conjectures that it is the global minimum. Kallus and Kusner show that
    the Kuperbergs' optimal double-lattice packing of a convex polygon is locally optimal among all packings
    (*The local optimality of the double lattice packing*, Discrete & Computational Geometry 56 (2016), 449-471,
    [doi:10.1007/s00454-016-9792-4](https://doi.org/10.1007/s00454-016-9792-4)).
  - Bezdek and Kuperberg (above) call the determination of the least packing densities in general "a very
    challenging problem, perhaps too difficult to expect to be solved in foreseeable future".
- Covering. G. Fejes Tóth's survey (above) states that for a centrally symmetric convex disk the thinnest covering
  by translates has the density `a(K)/h(K)` of the thinnest lattice covering, `h(K)` the greatest area of an
  inscribed hexagon, and lists `ϑ_L(K) ≤ 2π/√27` (citing L. Fejes Tóth, *Lagerungen*, 2nd edition, 1972, p. 103),
  where `2π/√27` is Kershner's covering density of the circle: for lattice coverings the circle is the worst.
  D. Ismailescu and B. Kim proved `1 ≤ δ_L(K)ϑ_L(K) ≤ 1.172559…` (*Packing and covering with
  centrally symmetric convex disks*, Discrete & Computational Geometry 51 (2014), 495-508,
  [doi:10.1007/s00454-013-9562-5](https://doi.org/10.1007/s00454-013-9562-5)).
- Polygons. Mahler's octagons and Ledermann and Mahler's decagons are above. Thomas Hales and Wöden Kusner,
  *Packings of regular pentagons in the plane* ([arXiv:1602.07220](https://arxiv.org/abs/1602.07220), version 2,
  September 2016, no journal reference), prove with computer assistance that the regular pentagon packs at most at
  density `(5 − √5)/3 ≈ 0.92`, by a double lattice.

## This repository

- The proof formalized here comes from hand and computer-assisted notes written by ChatGPT (OpenAI, ChatGPT Pro) in
  pull request [vltanh/lean4-smoothed-octagon#1](https://github.com/vltanh/lean4-smoothed-octagon/pull/1), opened on
  6 November 2026.
  - The notes state that every centrally symmetric convex disk `K` has `δ(K) ≥ (8 − 4√2 − log 2)/(2√2 − 1)`, with
    equality exactly for affine images of the smoothed octagon. They rest on classical geometric and maximum
    principle inputs that they list. They first used interval-arithmetic computations in C++ with MPFR and GMP,
    and by 8 November 2026 replaced every one of them by hand arguments; pull request
    [#2](https://github.com/vltanh/lean4-smoothed-octagon/pull/2) rewrote the largest polynomial signs with small
    identities.
  - The pull request says: "This is not a claim of Lean-kernel verification or external peer review."
- The Lean formalization of that proof is complete and unconditional, and uses no interval cover. It builds on
  [lean4-smoothed-polygon](https://github.com/vltanh/lean4-smoothed-polygon), and
  [`Palomar/Challenge.lean`](../Palomar/Challenge.lean) states the conjecture, its equality case, and the density of
  Reinhardt's smoothed octagon. The library also proves the conjecture's form as a control problem
  (`SmoothedOctagon.reinhardt_cost`).
