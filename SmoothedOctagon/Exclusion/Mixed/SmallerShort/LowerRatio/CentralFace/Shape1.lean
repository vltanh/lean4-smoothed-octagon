module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.LowerRatio.CentralFace.Beta

/-!
# Smaller-short window, lower ratio, central face: the shape step

* First test: along `β₊ = x + (10/13)(α - 1)` at a fixed norm, `(r₀)_α + (10/13)(r₀)_β ≥ 1/40 + 2/625`
  below the tangent chord `α_U` of the cap (affine in `u`; two-variable signs at `u = 3/4, 19/25`),
  so `F₀` decreases with slope `≤ -c/40`; along the ceiling `u_ℓ(x, β₊)` the norm motion costs at
  most `(1/5)(15/1992)(10/13)` per unit: `lrc_F0_astep`.
* Second test at `u = 19/25`: `F₁(x, α, β₊, 19/25) = Γ - c φ(α) - g` with
  `φ = N/V + ℓ(Y/K)`, `V = αBK`, `Y = 2αB`; `φ″ ≥ (N/V)″ + (log y)″ - (1/625)y″/y`
  (`ℓ″ ≥ -1/y²`, `yℓ′(y) = 1 - ε ≥ 624/625`, `y″ ≥ 0`) and `V³((N/V)″ + (log y)″)` is the curvature
  circuit, at least `V³/700` below the cap (`SmallerShort/LowerRatio/CentralFace/Shape2`); so `φ` is convex and
  `F₁(α) ≥ min(F₁(1), F₁(α_c))`: `lrc_F1_conc`.

The convexity uses only the positivity of the circuit below the cap, and the slope of the first
test is bounded below the tangent chord `α_U` directly.

## Main API

* `lrPhi1`, `lrPhi2`, `lr_phi_hasDerivAt`, `lrcN`, `lrcV`, `lrcY`, `lrc_F1_phi`,
  `lrc_F0_astep`, `lrc_F1_conc`.
-/

@[expose] public section

namespace SmoothedOctagon

open Set Real

/-! ### A quotient plus a composed majorant, differentiated twice -/

/-- `φ′ = (N′V - NV′)/V² + ℓ′(Y/K)(Y′K - YK′)/K²`. -/
noncomputable def lrPhi1 (n n1 v v1 y y1 k k1 : ℝ) : ℝ :=
  (n1 * v - n * v1) / v ^ 2 + lrell1 (y / k) * ((y1 * k - y * k1) / k ^ 2)

/-- `φ″`. -/
noncomputable def lrPhi2 (n n1 n2 v v1 v2 y y1 y2 k k1 k2 : ℝ) : ℝ :=
  ((n2 * v - n * v2) * v - 2 * v1 * (n1 * v - n * v1)) / v ^ 3 +
    lrell2 (y / k) * ((y1 * k - y * k1) / k ^ 2) ^ 2 +
      lrell1 (y / k) * (((y2 * k - y * k2) * k - 2 * k1 * (y1 * k - y * k1)) / k ^ 3)

theorem lr_qphi_hasDerivAt {N N1 N2 V V1 V2 Y Y1 Y2 K K1 K2 : ℝ → ℝ} {t : ℝ}
    (hN : HasDerivAt N (N1 t) t) (hN1 : HasDerivAt N1 (N2 t) t) (hV : HasDerivAt V (V1 t) t)
    (hV1 : HasDerivAt V1 (V2 t) t) (hY : HasDerivAt Y (Y1 t) t) (hY1 : HasDerivAt Y1 (Y2 t) t)
    (hK : HasDerivAt K (K1 t) t) (hK1 : HasDerivAt K1 (K2 t) t) (hV0 : V t ≠ 0) (hK0 : K t ≠ 0)
    (hy : -1 < Y t / K t) :
    HasDerivAt (fun s => N s / V s + lrell (Y s / K s))
        (lrPhi1 (N t) (N1 t) (V t) (V1 t) (Y t) (Y1 t) (K t) (K1 t)) t ∧
      HasDerivAt (fun s => lrPhi1 (N s) (N1 s) (V s) (V1 s) (Y s) (Y1 s) (K s) (K1 s))
        (lrPhi2 (N t) (N1 t) (N2 t) (V t) (V1 t) (V2 t) (Y t) (Y1 t) (Y2 t) (K t) (K1 t)
          (K2 t)) t := by
  have hYK := hY.div hK hK0
  constructor
  · have h := (hN.div hV hV0).add ((lr_ell_hasDerivAt' hy).comp t hYK)
    convert h using 1
    · funext s
      simp only [Pi.add_apply, Pi.div_apply, Function.comp_apply]
    · unfold lrPhi1
      simp only [Function.comp_apply, Pi.div_apply]
  · have h1 := ((hN1.mul hV).sub (hN.mul hV1)).div (hV.pow 2) (pow_ne_zero 2 hV0)
    have h2 := ((lr_ell1_hasDerivAt hy).comp t hYK).mul
      (((hY1.mul hK).sub (hY.mul hK1)).div (hK.pow 2) (pow_ne_zero 2 hK0))
    have h := h1.add h2
    convert h using 1
    · funext s
      simp only [lrPhi1, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.div_apply,
        Function.comp_apply, Pi.pow_apply]
    · unfold lrPhi2
      simp only [Function.comp_apply, Pi.div_apply, Pi.pow_apply, Pi.mul_apply, Pi.sub_apply]
      field_simp
      ring


/-! ### The central circuit -/

/-- The numerator `N` of `φ = N/V + ℓ(Y/K)` at `u = 19/25`, as a quartic in the shape `t`. -/
noncomputable def lrcN (x t : ℝ) : ℝ :=
  (-12 / 25 * x ^ 5 + 3197 / 1300 * x ^ 4 - 88 / 25 * x ^ 3 + 17933 / 4225 * x ^ 2 - 1746 / 4225 * x) +
    (-42 / 325 * x ^ 4 + 79 / 65 * x ^ 3 + 51 / 169 * x ^ 2 - 808 / 325 * x + 12 / 65) * t +
    (12 / 65 * x ^ 3 - 17291 / 8450 * x ^ 2 + 23607 / 4225 * x - 276 / 845) * t ^ 2 +
    (-3522 / 845 * x + 308 / 169) * t ^ 3 + (-1643 / 676) * t ^ 4

noncomputable def lrcN1 (x t : ℝ) : ℝ :=
  (-42 / 325 * x ^ 4 + 79 / 65 * x ^ 3 + 51 / 169 * x ^ 2 - 808 / 325 * x + 12 / 65) +
    2 * (12 / 65 * x ^ 3 - 17291 / 8450 * x ^ 2 + 23607 / 4225 * x - 276 / 845) * t +
    3 * (-3522 / 845 * x + 308 / 169) * t ^ 2 + 4 * (-1643 / 676) * t ^ 3

noncomputable def lrcN2 (x t : ℝ) : ℝ :=
  2 * (12 / 65 * x ^ 3 - 17291 / 8450 * x ^ 2 + 23607 / 4225 * x - 276 / 845) +
    6 * (-3522 / 845 * x + 308 / 169) * t + 12 * (-1643 / 676) * t ^ 2

/-- `B = α + β₊`. -/
noncomputable def lrcB (x t : ℝ) : ℝ := t + (x + 10 / 13 * (t - 1))
/-- `V = αBK`. -/
noncomputable def lrcV (x t : ℝ) : ℝ := t * lrcB x t * lrcK x t
noncomputable def lrcV1 (x t : ℝ) : ℝ :=
  lrcB x t * lrcK x t + t * (23 / 13) * lrcK x t + t * lrcB x t * (2 * t)
noncomputable def lrcV2 (x t : ℝ) : ℝ :=
  2 * (23 / 13) * lrcK x t + 2 * lrcB x t * (2 * t) + 2 * t * (23 / 13) * (2 * t) +
    t * lrcB x t * 2
/-- `Y = 2αB`, so `y = Y/K = 2α(α + β₊)/K`. -/
noncomputable def lrcY (x t : ℝ) : ℝ := 2 * t * lrcB x t
noncomputable def lrcY1 (x t : ℝ) : ℝ := 2 * lrcB x t + 2 * t * (23 / 13)
noncomputable def lrcY2 (_x _t : ℝ) : ℝ := 4 * (23 / 13)

/-- Numerator of `(r₀)_α + (10/13)(r₀)_β - 1/40 - 2/625` along `β₊`, `u = 3/4`. -/
noncomputable def lrcPafx (x a : ℝ) : ℝ :=
  169 / 4 * x ^ 9 + 171171 / 5000 * x ^ 8 * a ^ 2 + 637 / 2 * x ^ 8 * a + 156 * x ^ 8 + 3276591 / 2500 * x ^ 7 * a ^ 3 + 1809343 / 2500 * x ^ 7 * a ^ 2 + 1421 * x ^ 7 * a - 3 * x ^ 7 + 68004003 / 16250 * x ^ 6 * a ^ 4 - 96495453 / 8125 * x ^ 6 * a ^ 3 + 128315339 / 16250 * x ^ 6 * a ^ 2 + 13916 / 13 * x ^ 6 * a - 5216 / 13 * x ^ 6 + 94713299 / 32500 * x ^ 5 * a ^ 5 - 1083499013 / 32500 * x ^ 5 * a ^ 4 + 280050743 / 16250 * x ^ 5 * a ^ 3 + 80916993 / 8125 * x ^ 5 * a ^ 2 - 28616 / 13 * x ^ 5 * a + 60 / 13 * x ^ 5 - 53439151 / 32500 * x ^ 4 * a ^ 6 - 837610673 / 105625 * x ^ 4 * a ^ 5 - 1138569553 / 105625 * x ^ 4 * a ^ 4 + 5343318911 / 211250 * x ^ 4 * a ^ 3 - 152691762 / 21125 * x ^ 4 * a ^ 2 - 21560 / 13 * x ^ 4 * a + 4800 / 13 * x ^ 4 - 36690451 / 32500 * x ^ 3 * a ^ 7 + 16720038761 / 422500 * x ^ 3 * a ^ 6 - 6597328228 / 105625 * x ^ 3 * a ^ 5 + 3144298419 / 105625 * x ^ 3 * a ^ 4 - 111316857 / 21125 * x ^ 3 * a ^ 3 - 10239316 / 4225 * x ^ 3 * a ^ 2 + 19600 / 13 * x ^ 3 * a - 2000 / 13 * x ^ 3 - 61899 / 1250 * x ^ 2 * a ^ 8 + 2537269446 / 105625 * x ^ 2 * a ^ 7 - 3901444863 / 211250 * x ^ 2 * a ^ 6 - 305582848 / 21125 * x ^ 2 * a ^ 5 + 41164226 / 4225 * x ^ 2 * a ^ 4 + 347210 / 169 * x ^ 2 * a ^ 3 - 263400 / 169 * x ^ 2 * a ^ 2 - 42159 / 2500 * x * a ^ 9 - 166150182 / 105625 * x * a ^ 8 + 1222932027 / 42250 * x * a ^ 7 - 197103887 / 4225 * x * a ^ 6 + 4716935 / 169 * x * a ^ 5 - 1195160 / 169 * x * a ^ 4 + 35900 / 169 * x * a ^ 3 + 2000 / 13 * x * a ^ 2 - 74589 / 5000 * a ^ 10 + 3243 / 250 * a ^ 9 + 21008523 / 4225 * a ^ 8 - 2371819 / 338 * a ^ 7 + 342970 / 169 * a ^ 6 + 93850 / 169 * a ^ 5 - 3000 / 13 * a ^ 4

/-- Its shift to the domain variables. -/
noncomputable def lrcPafs (t s : ℝ) : ℝ :=
  2378426580376559738094319174689923982193 / 8203653784311105663129600000000000000 * t ^ 10 - 34117853869477140799417386874873049 / 14023339802241206261760000000000 * t ^ 9 * s + 78864606080619488675666959764336610121413 / 20509134460777764157824000000000000000 * t ^ 9 + 251966343638916697445579643566113 / 33293779207600204800000000000 * t ^ 8 * s ^ 2 - 1052543707308223541169762472151621357 / 38953721672892239616000000000000 * t ^ 8 * s + 2364875836368948320452852740556239896019433 / 113939635893209800876800000000000000000 * t ^ 8 - 52856178460750142628193728497 / 5335541539679520000000000 * t ^ 7 * s ^ 3 + 8061880944426009799649927575954933 / 104043060023750640000000000000 * t ^ 7 * s ^ 2 - 401149830113719991305795166474332657 / 3745550160855023040000000000000 * t ^ 7 * s + 60845481805372877077132683704835127880328253 / 1068184086498841883220000000000000000000 * t ^ 7 + 22712574156993492115998007 / 9120583828512000000000 * t ^ 6 * s ^ 4 - 16612892607136895683697526239939 / 133388538491988000000000000 * t ^ 6 * s ^ 3 + 1538000341729025049104176526303349871 / 5202153001187532000000000000000 * t ^ 6 * s ^ 2 - 1939786345762839283554601282874201116451 / 18259557034168237320000000000000000 * t ^ 6 * s + 8332481597597090112192517268949540995614459111 / 106818408649884188322000000000000000000000 * t ^ 6 + 19996498850937697934953 / 3248071164000000000 * t ^ 5 * s ^ 5 + 5347819679051885753789459587 / 38002432618800000000000 * t ^ 5 * s ^ 4 - 774531512401315288352286198220799 / 1111571154099900000000000000 * t ^ 5 * s ^ 3 + 26450136335309931306535292108287962811 / 65026912514844150000000000000000 * t ^ 5 * s ^ 2 + 165482839702503872848251524101260932545153 / 304325950569470622000000000000000000 * t ^ 5 * s + 85081487073615506311831184152820291376026704051 / 2225383513539253923375000000000000000000000 * t ^ 5 - 1848950302977438949 / 333135504000000 * t ^ 4 * s ^ 6 - 1984682712885449253487427 / 16240355820000000000 * t ^ 4 * s ^ 5 + 458451566287665876700375386367 / 380024326188000000000000 * t ^ 4 * s ^ 4 - 2839281753788180399814437645987543 / 1282582100884500000000000000 * t ^ 4 * s ^ 3 - 623882721158940451091241614214103912649 / 1300538250296883000000000000000000 * t ^ 4 * s ^ 2 + 17203924342910038112305728367956248554937077 / 7608148764236765550000000000000000000 * t ^ 4 * s + 910316148040987802397545238598833371737160476591 / 66761505406177617701250000000000000000000000 * t ^ 4 + 277513426348879 / 177957000000 * t ^ 3 * s ^ 7 + 134584673041415980151 / 2082096900000000 * t ^ 3 * s ^ 6 - 237762667054607376468595007 / 203004447750000000000 * t ^ 3 * s ^ 5 + 31086919486770223032215966966347 / 7125456116025000000000000 * t ^ 3 * s ^ 4 - 1760179433110827097248003770601927719 / 416839182787462500000000000000 * t ^ 3 * s ^ 3 - 105846106870028193482419679798402140752509 / 40641820321777593750000000000000000 * t ^ 3 * s ^ 2 + 1134906594915607762695182436654943478549114521 / 285305578658878708125000000000000000000 * t ^ 3 * s + 56552550774865104121734771648793650077543930711533 / 417259408788610110632812500000000000000000000 * t ^ 3 - 48880738511 / 202800000 * t ^ 2 * s ^ 8 - 1190002183672697 / 114075000000 * t ^ 2 * s ^ 7 + 18742396408624223051651 / 34701615000000000 * t ^ 2 * s ^ 6 - 18032330919861845354669695787 / 5075111193750000000000 * t ^ 2 * s ^ 5 + 1878508153648321412589924468107527 / 237515203867500000000000000 * t ^ 2 * s ^ 4 - 82203280097985297644369636294827965779 / 17368299282810937500000000000000 * t ^ 2 * s ^ 3 - 8187340722658290811996894021716184015672769 / 2032091016088879687500000000000000000 * t ^ 2 * s ^ 2 + 1823847421276000451457611326877703333707802191 / 475509297764797846875000000000000000000 * t ^ 2 * s + 7991089054575424528367788656999593248365666839654353 / 27817293919240674042187500000000000000000000000 * t ^ 2 + 31763023 / 390000 * t * s ^ 9 - 6400388534651 / 2535000000 * t * s ^ 8 - 3307091897106430601 / 37074375000000 * t * s ^ 7 + 1527435499449337111347551 / 1301310562500000000 * t * s ^ 6 - 1161417831604065598389279417767 / 253755559687500000000000 * t * s ^ 5 + 8114982680549317962478145088479839 / 1141900018593750000000000000 * t * s ^ 4 - 3677362842927103326719242703229427668239 / 1302622446210820312500000000000000 * t * s ^ 3 - 5771941395391188554918012446765059731604719 / 1953933669316230468750000000000000000 * t * s ^ 2 + 472197872055215031548662236508453982973208080967 / 237754648882398923437500000000000000000000 * t * s + 742089270347687015576862232482855688988621565298599973 / 3129445565914575829746093750000000000000000000000 * t - 74589 / 5000 * s ^ 10 + 1595991643 / 9750000 * s ^ 9 + 184766152765609 / 126750000000 * s ^ 8 - 322060853903857031741 / 2780578125000000 * s ^ 7 + 103721266417920691075959851 / 130131056250000000000 * s ^ 6 - 68429833214556779468536433508947 / 31719444960937500000000000 * s ^ 5 + 431736276442169592272988429661623499 / 171285002789062500000000000000 * s ^ 4 - 21868467771294678715294418883517506370157 / 32565561155270507812500000000000000 * s ^ 3 - 342240074624019444495284267199847385942824379 / 390786733863246093750000000000000000000 * s ^ 2 + 23279688442489140643938829075155236816856619353139 / 53494795998539757773437500000000000000000000 * s + 56277285773243663720621192175505815556797018377095960393 / 782361391478643957436523437500000000000000000000000

theorem lrcPafs_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (9 / 25 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (31 / 200 : ℝ)) :
    (0 : ℝ) ≤ lrcPafs t s := by
  unfold lrcPafs
  have q0 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 8 * s)
  have q1 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 3)
  have q2 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 5)
  have q3 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 7)
  have q4 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 9)
  have q5 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 7 * s)
  have q6 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 3)
  have q7 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 4)
  have q8 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 6)
  have q9 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 7)
  have q10 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s)
  have q11 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 3)
  have q12 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 4)
  have q13 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 6)
  have q14 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s)
  have q15 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 3)
  have q16 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 4)
  have q17 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 6)
  have q18 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2)
  have q19 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3)
  have q20 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 4)
  have q21 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2)
  have q22 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2)
  have q23 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 4)
  have q24 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t * s ^ 2)
  have q25 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 2)
  have q26 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s)
  have q27 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 2)
  have q28 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s)
  have q29 := (by positivity : (0 : ℝ) ≤ t ^ 10)
  have q30 := (by positivity : (0 : ℝ) ≤ t ^ 9)
  have q31 := (by positivity : (0 : ℝ) ≤ t ^ 8 * s ^ 2)
  have q32 := (by positivity : (0 : ℝ) ≤ t ^ 8)
  have q33 := (by positivity : (0 : ℝ) ≤ t ^ 7 * s ^ 2)
  have q34 := (by positivity : (0 : ℝ) ≤ t ^ 7)
  have q35 := (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 4)
  have q36 := (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 2)
  have q37 := (by positivity : (0 : ℝ) ≤ t ^ 6)
  have q38 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 5)
  have q39 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 4)
  have q40 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 2)
  have q41 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s)
  have q42 := (by positivity : (0 : ℝ) ≤ t ^ 5)
  have q43 := (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 4)
  have q44 := (by positivity : (0 : ℝ) ≤ t ^ 4 * s)
  have q45 := (by positivity : (0 : ℝ) ≤ t ^ 4)
  have q46 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 7)
  have q47 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 6)
  have q48 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 4)
  have q49 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s)
  have q50 := (by positivity : (0 : ℝ) ≤ t ^ 3)
  have q51 := (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 6)
  have q52 := (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 4)
  have q53 := (by positivity : (0 : ℝ) ≤ t ^ 2 * s)
  have q54 := (by positivity : (0 : ℝ) ≤ t ^ 2)
  have q55 := (by positivity : (0 : ℝ) ≤ t * s ^ 9)
  have q56 := (by positivity : (0 : ℝ) ≤ t * s ^ 6)
  have q57 := (by positivity : (0 : ℝ) ≤ t * s ^ 4)
  have q58 := (by positivity : (0 : ℝ) ≤ t * s)
  have q59 := (by positivity : (0 : ℝ) ≤ t)
  have q60 := (by positivity : (0 : ℝ) ≤ s ^ 9)
  have q61 := (by positivity : (0 : ℝ) ≤ s ^ 8)
  have q62 := (by positivity : (0 : ℝ) ≤ s ^ 6)
  have q63 := (by positivity : (0 : ℝ) ≤ s ^ 4)
  have q64 := (by positivity : (0 : ℝ) ≤ s)
  ring_nf at *
  linarith

theorem lrcPafx_eq (x a : ℝ) : lrcPafx x a = lrcPafs (x - 41 / 25) ((1013 * x + 676) / 2340 - a) := by
  unfold lrcPafx lrcPafs
  ring

/-- Numerator of `(r₀)_α + (10/13)(r₀)_β - 1/40 - 2/625` along `β₊`, `u = 19/25`. -/
noncomputable def lrcPavx (x a : ℝ) : ℝ :=
  1014 / 25 * x ^ 9 + 163371 / 5000 * x ^ 8 * a ^ 2 + 7813 / 25 * x ^ 8 * a + 3744 / 25 * x ^ 8 + 3143841 / 2500 * x ^ 7 * a ^ 3 + 1763443 / 2500 * x ^ 7 * a ^ 2 + 34858 / 25 * x ^ 7 * a - 72 / 25 * x ^ 7 + 65264853 / 16250 * x ^ 6 * a ^ 4 - 98650478 / 8125 * x ^ 6 * a ^ 3 + 64231657 / 8125 * x ^ 6 * a ^ 2 + 341368 / 325 * x ^ 6 * a - 125184 / 325 * x ^ 6 + 90858999 / 32500 * x ^ 5 * a ^ 5 - 1113045763 / 32500 * x ^ 5 * a ^ 4 + 144040934 / 8125 * x ^ 5 * a ^ 3 + 80967018 / 8125 * x ^ 5 * a ^ 2 - 701968 / 325 * x ^ 5 * a + 288 / 65 * x ^ 5 - 51378351 / 32500 * x ^ 4 * a ^ 6 - 1811141271 / 211250 * x ^ 4 * a ^ 5 - 2157453481 / 211250 * x ^ 4 * a ^ 4 + 2696606868 / 105625 * x ^ 4 * a ^ 3 - 155013362 / 21125 * x ^ 4 * a ^ 2 - 105776 / 65 * x ^ 4 * a + 4608 / 13 * x ^ 4 - 35288601 / 32500 * x ^ 3 * a ^ 7 + 16994847361 / 422500 * x ^ 3 * a ^ 6 - 6689775753 / 105625 * x ^ 3 * a ^ 5 + 3251392219 / 105625 * x ^ 3 * a ^ 4 - 120171412 / 21125 * x ^ 3 * a ^ 3 - 9903796 / 4225 * x ^ 3 * a ^ 2 + 19232 / 13 * x ^ 3 * a - 1920 / 13 * x ^ 3 - 61899 / 1250 * x ^ 2 * a ^ 8 + 2588807271 / 105625 * x ^ 2 * a ^ 7 - 2014533544 / 105625 * x ^ 2 * a ^ 6 - 294030758 / 21125 * x ^ 2 * a ^ 5 + 40470178 / 4225 * x ^ 2 * a ^ 4 + 1717008 / 845 * x ^ 2 * a ^ 3 - 261504 / 169 * x ^ 2 * a ^ 2 - 42159 / 2500 * x * a ^ 9 - 675246853 / 422500 * x * a ^ 8 + 619782871 / 21125 * x * a ^ 7 - 200001351 / 4225 * x * a ^ 6 + 24101608 / 845 * x * a ^ 5 - 6220768 / 845 * x * a ^ 4 + 47264 / 169 * x * a ^ 3 + 1920 / 13 * x * a ^ 2 - 74589 / 5000 * a ^ 10 + 3243 / 250 * a ^ 9 + 42612171 / 8450 * a ^ 8 - 30300328 / 4225 * a ^ 7 + 1835856 / 845 * a ^ 6 + 83696 / 169 * a ^ 5 - 2880 / 13 * a ^ 4

/-- Its shift to the domain variables. -/
noncomputable def lrcPavs (t s : ℝ) : ℝ :=
  2281759391194395926178531381504614382193 / 8203653784311105663129600000000000000 * t ^ 10 - 32730093177756605200410641292207449 / 14023339802241206261760000000000 * t ^ 9 * s + 72975465372350201565023266104732485771413 / 20509134460777764157824000000000000000 * t ^ 9 + 241675263884066544450707634446113 / 33293779207600204800000000000 * t ^ 8 * s ^ 2 - 969298690807186184238909488397931757 / 38953721672892239616000000000000 * t ^ 8 * s + 2028311646386938022185905833698983311919433 / 113939635893209800876800000000000000000 * t ^ 8 - 50661501988281588264042828497 / 5335541539679520000000000 * t ^ 7 * s ^ 3 + 7455815206351528921387128195784933 / 104043060023750640000000000000 * t ^ 7 * s ^ 2 - 4283881077741547877097736886122889821 / 48692152091115299520000000000000 * t ^ 7 * s + 42480541398631977016663999166994703878978253 / 1068184086498841883220000000000000000000 * t ^ 7 + 21576770289097775142798007 / 9120583828512000000000 * t ^ 6 * s ^ 4 - 15775538185840517844816667439939 / 133388538491988000000000000 * t ^ 6 * s ^ 3 + 1306597561870349229648180062350809871 / 5202153001187532000000000000000 * t ^ 6 * s ^ 2 - 206829857320599674263809173885652993251 / 18259557034168237320000000000000000 * t ^ 6 * s + 1571653516379942086153422427360606780794259111 / 106818408649884188322000000000000000000000 * t ^ 6 + 19295359233058782134953 / 3248071164000000000 * t ^ 5 * s ^ 5 + 5345410455631735172492009587 / 38002432618800000000000 * t ^ 5 * s ^ 4 - 732317113322779931637610729420799 / 1111571154099900000000000000 * t ^ 5 * s ^ 3 + 14511231961774925536964265520402572811 / 65026912514844150000000000000000 * t ^ 5 * s ^ 2 + 254031651433543790548693131997788980396353 / 304325950569470622000000000000000000 * t ^ 5 * s - 259431469893448101766328772739327685361681745949 / 2225383513539253923375000000000000000000000 * t ^ 5 - 1784282195105070949 / 333135504000000 * t ^ 4 * s ^ 6 - 2065209092714700158287427 / 16240355820000000000 * t ^ 4 * s ^ 5 + 461161706573316518654608686367 / 380024326188000000000000 * t ^ 4 * s ^ 4 - 34918648694202505245741656224038059 / 16673567311498500000000000000 * t ^ 4 * s ^ 3 - 1212576961357647201895033224795911152649 / 1300538250296883000000000000000000 * t ^ 4 * s ^ 2 + 21575887458664678407998417993377638294636277 / 7608148764236765550000000000000000000 * t ^ 4 * s - 16150384051990373784056572481197453604761701223409 / 66761505406177617701250000000000000000000000 * t ^ 4 + 269837456488879 / 177957000000 * t ^ 3 * s ^ 7 + 10890402630002870627 / 160161300000000 * t ^ 3 * s ^ 6 - 243788453776462855839895007 / 203004447750000000000 * t ^ 3 * s ^ 5 + 31365085035256647919927598516347 / 7125456116025000000000000 * t ^ 3 * s ^ 4 - 1672235570296566163643631185340627719 / 416839182787462500000000000000 * t ^ 3 * s ^ 3 - 133715585240010076402020011444163606342509 / 40641820321777593750000000000000000 * t ^ 3 * s ^ 2 + 1344058081441048563319248365025217796205081721 / 285305578658878708125000000000000000000 * t ^ 3 * s - 4685555086341752296660927973412151212409274202959 / 32096877599123854664062500000000000000000000 * t ^ 3 - 48880738511 / 202800000 * t ^ 2 * s ^ 8 - 16378919919505061 / 1482975000000 * t ^ 2 * s ^ 7 + 19268292541053962159651 / 34701615000000000 * t ^ 2 * s ^ 6 - 18418376701792904463097495787 / 5075111193750000000000 * t ^ 2 * s ^ 5 + 1899442487546963398850360377907527 / 237515203867500000000000000 * t ^ 2 * s ^ 4 - 78620219797993981233947615530809165779 / 17368299282810937500000000000000 * t ^ 2 * s ^ 3 - 9454679035581063094992015790828934023612769 / 2032091016088879687500000000000000000 * t ^ 2 * s ^ 2 + 2101010302776106633768556409201808694468400911 / 475509297764797846875000000000000000000 * t ^ 2 * s + 2479869118289350238380257014729258689744785452054353 / 27817293919240674042187500000000000000000000000 * t ^ 2 + 31763023 / 390000 * t * s ^ 9 - 6464265284651 / 2535000000 * t * s ^ 8 - 260784436347199277 / 2851875000000 * t * s ^ 7 + 1561424063910579651525551 / 1301310562500000000 * t * s ^ 6 - 1184188876056736547056466217767 / 253755559687500000000000 * t * s ^ 5 + 106881876974241212444833251230787907 / 14844700241718750000000000000 * t * s ^ 4 - 3547837562071336038591889682156693868239 / 1302622446210820312500000000000000 * t * s ^ 3 - 82915330486184681002705128613916679936831347 / 25401137701110996093750000000000000000 * t * s ^ 2 + 534427758217328288244208170543562664237198218567 / 237754648882398923437500000000000000000000 * t * s + 490594996312866490620045372278357116637957811186249973 / 3129445565914575829746093750000000000000000000000 * t - 74589 / 5000 * s ^ 10 + 1595991643 / 9750000 * s ^ 9 + 188455134265609 / 126750000000 * s ^ 8 - 25250112787898507057 / 213890625000000 * s ^ 7 + 105735057029057138495007851 / 130131056250000000000 * s ^ 6 - 69705387174384045958976194308947 / 31719444960937500000000000 * s ^ 5 + 5698228475701791721948251185757405487 / 2226705036257812500000000000000 * s ^ 4 - 21343882153095715769467507578466692970157 / 32565561155270507812500000000000000 * s ^ 3 - 4774373355372453226668982365215758888590236927 / 5080227540222199218750000000000000000000 * s ^ 2 + 25974789552558778783726503643427117826074081394739 / 53494795998539757773437500000000000000000000 * s + 45140767810871997530161928688526473707620738422113860393 / 782361391478643957436523437500000000000000000000000

theorem lrcPavs_pos {t s : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ (9 / 25 : ℝ)) (hs0 : 0 ≤ s) (hs1 : s ≤ (31 / 200 : ℝ)) :
    (0 : ℝ) ≤ lrcPavs t s := by
  unfold lrcPavs
  have q0 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 8 * s)
  have q1 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 3)
  have q2 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 5)
  have q3 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 7)
  have q4 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 9)
  have q5 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 7 * s)
  have q6 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 3)
  have q7 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 4)
  have q8 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 6)
  have q9 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 7)
  have q10 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 6 * s)
  have q11 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 3)
  have q12 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 4)
  have q13 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 6)
  have q14 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 5 * s)
  have q15 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 3)
  have q16 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 4)
  have q17 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 6)
  have q18 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 2)
  have q19 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 3)
  have q20 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 4)
  have q21 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 4)
  have q22 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2)
  have q23 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 2)
  have q24 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 4)
  have q25 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 3)
  have q26 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t * s ^ 2)
  have q27 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s ^ 2)
  have q28 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t ^ 2)
  have q29 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ t * s)
  have q30 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s ^ 2)
  have q31 := mul_le_mul_of_nonneg_left ht1 (by positivity : (0 : ℝ) ≤ t)
  have q32 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ s)
  have q33 := (by positivity : (0 : ℝ) ≤ t ^ 10)
  have q34 := (by positivity : (0 : ℝ) ≤ t ^ 9)
  have q35 := (by positivity : (0 : ℝ) ≤ t ^ 8 * s ^ 2)
  have q36 := (by positivity : (0 : ℝ) ≤ t ^ 8)
  have q37 := (by positivity : (0 : ℝ) ≤ t ^ 7 * s ^ 2)
  have q38 := (by positivity : (0 : ℝ) ≤ t ^ 7)
  have q39 := (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 4)
  have q40 := (by positivity : (0 : ℝ) ≤ t ^ 6 * s ^ 2)
  have q41 := (by positivity : (0 : ℝ) ≤ t ^ 6)
  have q42 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 5)
  have q43 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 4)
  have q44 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s ^ 2)
  have q45 := (by positivity : (0 : ℝ) ≤ t ^ 5 * s)
  have q46 := (by positivity : (0 : ℝ) ≤ t ^ 4 * s ^ 4)
  have q47 := (by positivity : (0 : ℝ) ≤ t ^ 4 * s)
  have q48 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 7)
  have q49 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 6)
  have q50 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s ^ 4)
  have q51 := (by positivity : (0 : ℝ) ≤ t ^ 3 * s)
  have q52 := (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 6)
  have q53 := (by positivity : (0 : ℝ) ≤ t ^ 2 * s ^ 4)
  have q54 := (by positivity : (0 : ℝ) ≤ t ^ 2 * s)
  have q55 := (by positivity : (0 : ℝ) ≤ t * s ^ 9)
  have q56 := (by positivity : (0 : ℝ) ≤ t * s ^ 6)
  have q57 := (by positivity : (0 : ℝ) ≤ t * s ^ 4)
  have q58 := (by positivity : (0 : ℝ) ≤ t * s)
  have q59 := (by positivity : (0 : ℝ) ≤ t)
  have q60 := (by positivity : (0 : ℝ) ≤ s ^ 9)
  have q61 := (by positivity : (0 : ℝ) ≤ s ^ 8)
  have q62 := (by positivity : (0 : ℝ) ≤ s ^ 6)
  have q63 := (by positivity : (0 : ℝ) ≤ s ^ 4)
  have q64 := (by positivity : (0 : ℝ) ≤ s)
  ring_nf at *
  linarith

theorem lrcPavx_eq (x a : ℝ) : lrcPavx x a = lrcPavs (x - 41 / 25) ((1013 * x + 676) / 2340 - a) := by
  unfold lrcPavx lrcPavs
  ring


end SmoothedOctagon
