module

public import SmoothedOctagon.Exclusion.Mixed.SmallerShort.UpperRatio.Reductions

/-!
# Smaller-short window, upper ratio: the reciprocal-convexity polynomials

The eight bivariate polynomials `P_{A,0}`, …, `P_{D,1}` of the reciprocal convexity
(`OuterFace/Reciprocal`; variables `h = x - 2 ∈ [1/6, 2/5]`, `t = c - 5/8 ∈ [0, 1/4]`), each proved
positive by a termwise rule: a positive term with a positive power of `t` is dropped, `t^k` is
replaced by `4^{-k}` in a negative one, and the resulting univariate lower polynomial is bounded
with `h = 1/6` in positive and `h = 2/5` in negative terms.

## Main API

* `ur_box`: the monomial facts used by the termwise rule.
* The polynomials `urPA0`, …, `urPD1` and their positivity `ur_PA0_pos`, …, `ur_PD1_pos`.
-/

@[expose] public section

namespace SmoothedOctagon

/-- The monomial facts of the termwise rule on a box `hl ≤ h ≤ hu`, `0 ≤ t ≤ tu`. -/
theorem ur_box {h t hl hu tu : ℝ} (hh : hl ≤ h) (hh' : h ≤ hu) (hl0 : 0 ≤ hl) (ht : 0 ≤ t)
    (ht' : t ≤ tu) :
    (∀ n : ℕ, 0 ≤ h ^ n) ∧ (∀ n : ℕ, 0 ≤ t ^ n) ∧ (∀ n : ℕ, 0 ≤ tu ^ n - t ^ n) ∧
      (∀ n : ℕ, h ^ n ≤ hu ^ n) ∧ (∀ n : ℕ, hl ^ n ≤ h ^ n) := by
  have h0 : 0 ≤ h := hl0.trans hh
  exact ⟨fun n => pow_nonneg h0 n, fun n => pow_nonneg ht n,
    fun n => sub_nonneg.2 (pow_le_pow_left₀ ht ht' n), fun n => pow_le_pow_left₀ h0 hh' n,
    fun n => pow_le_pow_left₀ hl0 hh n⟩

/-- `PA0` (`392x²S(Q₀ - 5/8)` at `u = 3/4`, times 64). -/
noncomputable def urPA0 (h t : ℝ) : ℝ :=
  (3072*t - 5760) * h ^ 6 +
      (-1536*t^3 + 192*t^2 + 68088*t - 36231) * h ^ 5 +
      (-12288*t^3 - 2048*t^2 + 467136*t - 11808) * h ^ 4 +
      (-36864*t^3 - 18432*t^2 + 1469504*t + 343904) * h ^ 3 +
      (-52224*t^3 - 59520*t^2 + 2322928*t + 853370) * h ^ 2 +
      (-35328*t^3 - 85184*t^2 + 1768520*t + 705015) * h +
      (-9216*t^3 - 41856*t^2 + 506832*t + 144758)

theorem ur_PA0_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < urPA0 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := ur_box hh hh' (by norm_num) ht ht'
  unfold urPA0
  linarith [mul_nonneg (tp 1) (hp 6), mul_nonneg (tq 3) (hp 5), mul_nonneg (tp 2) (hp 5), mul_nonneg (tp 1) (hp 5), mul_nonneg (tq 3) (hp 4), mul_nonneg (tq 2) (hp 4), mul_nonneg (tp 1) (hp 4), mul_nonneg (tq 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tp 1) (hp 3), mul_nonneg (tq 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tp 1) (hp 2), mul_nonneg (tq 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tp 1) (hp 1), tq 3, tq 2, tp 1, hu 6, hu 5, hu 4, hl 3, hl 2, hl 1]

/-- `PA1` (`1960x²S(Q₀ - 5/8)` at `u = 4/5`, times 4). -/
noncomputable def urPA1 (h t : ℝ) : ℝ :=
  (768*t - 1440) * h ^ 6 +
      (-512*t^3 + 320*t^2 + 19176*t - 5929) * h ^ 5 +
      (-4096*t^3 + 2176*t^2 + 135168*t + 26694) * h ^ 4 +
      (-12288*t^3 + 5888*t^2 + 424000*t + 189648) * h ^ 3 +
      (-17408*t^3 + 4224*t^2 + 652048*t + 375906) * h ^ 2 +
      (-11776*t^3 - 5568*t^2 + 465624*t + 281547) * h +
      (-3072*t^3 - 5760*t^2 + 116208*t + 51682)

theorem ur_PA1_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < urPA1 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := ur_box hh hh' (by norm_num) ht ht'
  unfold urPA1
  linarith [mul_nonneg (tp 1) (hp 6), mul_nonneg (tq 3) (hp 5), mul_nonneg (tp 2) (hp 5), mul_nonneg (tp 1) (hp 5), mul_nonneg (tq 3) (hp 4), mul_nonneg (tp 2) (hp 4), mul_nonneg (tp 1) (hp 4), mul_nonneg (tq 3) (hp 3), mul_nonneg (tp 2) (hp 3), mul_nonneg (tp 1) (hp 3), mul_nonneg (tq 3) (hp 2), mul_nonneg (tp 2) (hp 2), mul_nonneg (tp 1) (hp 2), mul_nonneg (tq 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tp 1) (hp 1), tq 3, tq 2, tp 1, hu 6, hu 5, hl 4, hl 3, hl 2, hl 1]

/-- `PB0` (`28SL` at `u = 3/4`, times 4096). -/
noncomputable def urPB0 (h t : ℝ) : ℝ :=
  (-49152*t - 104448) * h ^ 6 +
      (245760*t^2 + 110592*t - 796928) * h ^ 5 +
      (-385024*t^3 + 1125376*t^2 + 2709888*t - 1719408) * h ^ 4 +
      (196608*t^4 - 2408448*t^3 - 643072*t^2 + 7191296*t - 91120) * h ^ 3 +
      (1343488*t^4 - 3768320*t^3 - 6216704*t^2 + 3953664*t + 3717096) * h ^ 2 +
      (2740224*t^4 - 489472*t^3 - 4194432*t^2 - 4303584*t + 4108621) * h +
      (1896448*t^4 + 1587200*t^3 + 1836672*t^2 - 3249952*t + 1371727)

theorem ur_PB0_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < urPB0 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := ur_box hh hh' (by norm_num) ht ht'
  unfold urPB0
  linarith [mul_nonneg (tq 1) (hp 6), mul_nonneg (tp 2) (hp 5), mul_nonneg (tp 1) (hp 5), mul_nonneg (tq 3) (hp 4), mul_nonneg (tp 2) (hp 4), mul_nonneg (tp 1) (hp 4), mul_nonneg (tp 4) (hp 3), mul_nonneg (tq 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tp 1) (hp 3), mul_nonneg (tp 4) (hp 2), mul_nonneg (tq 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tp 1) (hp 2), mul_nonneg (tp 4) (hp 1), mul_nonneg (tq 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tq 1) (hp 1), tp 4, tp 3, tp 2, tq 1, hu 6, hu 5, hu 4, hu 3, hl 2, hl 1]

/-- `PB1` (`140SL` at `u = 4/5`, times 4096). -/
noncomputable def urPB1 (h t : ℝ) : ℝ :=
  (-196608*t - 417792) * h ^ 6 +
      (1048576*t^2 + 720896*t - 2789376) * h ^ 5 +
      (-1736704*t^3 + 4067328*t^2 + 11624960*t - 3418432) * h ^ 4 +
      (933888*t^4 - 10215424*t^3 - 6949376*t^2 + 22857856*t + 9940580) * h ^ 3 +
      (6258688*t^4 - 12812288*t^3 - 30032896*t^2 - 9893888*t + 27646552) * h ^ 2 +
      (12341248*t^4 + 5179392*t^3 - 8252544*t^2 - 48897760*t + 22162581) * h +
      (8204288*t^4 + 10614784*t^3 + 19597440*t^2 - 24232736*t + 5703587)

theorem ur_PB1_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < urPB1 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := ur_box hh hh' (by norm_num) ht ht'
  unfold urPB1
  linarith [mul_nonneg (tq 1) (hp 6), mul_nonneg (tp 2) (hp 5), mul_nonneg (tp 1) (hp 5), mul_nonneg (tq 3) (hp 4), mul_nonneg (tp 2) (hp 4), mul_nonneg (tp 1) (hp 4), mul_nonneg (tp 4) (hp 3), mul_nonneg (tq 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tp 1) (hp 3), mul_nonneg (tp 4) (hp 2), mul_nonneg (tq 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tp 4) (hp 1), mul_nonneg (tp 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tq 1) (hp 1), tp 4, tp 3, tp 2, tq 1, hu 6, hu 5, hu 4, hl 3, hl 2, hl 1]

/-- `PC0` (`107520e²S𝒞` at `u = 3/4`, times 4096). -/
noncomputable def urPC0 (h t : ℝ) : ℝ :=
  (-19906560*t - 42301440) * h ^ 6 +
      (99532800*t^2 + 422277120*t + 290661120) * h ^ 5 +
      (-155934720*t^3 - 299197440*t^2 + 2796197760*t + 4340736720) * h ^ 4 +
      (79626240*t^4 - 597934080*t^3 - 4459991040*t^2 + 2945898240*t + 14653924688) * h ^ 3 +
      (544112640*t^4 + 361267200*t^3 - 9202437120*t^2 - 4610661376*t + 19816821256) * h ^ 2 +
      (1109790720*t^4 + 2066688000*t^3 - 5653973632*t^2 - 5398549600*t + 10230726353) * h +
      (768061440*t^4 + 642816000*t^3 - 2565453696*t^2 + 706472544*t + 822346491)

theorem ur_PC0_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < urPC0 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := ur_box hh hh' (by norm_num) ht ht'
  unfold urPC0
  linarith [mul_nonneg (tq 1) (hp 6), mul_nonneg (tp 2) (hp 5), mul_nonneg (tp 1) (hp 5), mul_nonneg (tq 3) (hp 4), mul_nonneg (tq 2) (hp 4), mul_nonneg (tp 1) (hp 4), mul_nonneg (tp 4) (hp 3), mul_nonneg (tq 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tp 1) (hp 3), mul_nonneg (tp 4) (hp 2), mul_nonneg (tp 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tp 4) (hp 1), mul_nonneg (tp 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tq 1) (hp 1), tp 4, tp 3, tq 2, tp 1, hu 6, hl 5, hl 4, hl 3, hl 2, hl 1]

/-- `PC1` (`107520e²S𝒞` at `u = 4/5`, times 4096). -/
noncomputable def urPC1 (h t : ℝ) : ℝ :=
  (-15925248*t - 33841152) * h ^ 6 +
      (84934656*t^2 + 461045760*t + 428371968) * h ^ 5 +
      (-140673024*t^3 - 475852800*t^2 + 2753561088*t + 5070844608) * h ^ 4 +
      (75644928*t^4 - 424796160*t^3 - 5042416128*t^2 + 1945858176*t + 16354258340) * h ^ 3 +
      (506953728*t^4 + 975470592*t^3 - 9604924416*t^2 - 7197718528*t + 21631866328) * h ^ 2 +
      (999641088*t^4 + 2835449856*t^3 - 5045212288*t^2 - 7703610592*t + 10999601957) * h +
      (664547328*t^4 + 859797504*t^3 - 2080526208*t^2 + 45695712*t + 860023443)

theorem ur_PC1_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < urPC1 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := ur_box hh hh' (by norm_num) ht ht'
  unfold urPC1
  linarith [mul_nonneg (tq 1) (hp 6), mul_nonneg (tp 2) (hp 5), mul_nonneg (tp 1) (hp 5), mul_nonneg (tq 3) (hp 4), mul_nonneg (tq 2) (hp 4), mul_nonneg (tp 1) (hp 4), mul_nonneg (tp 4) (hp 3), mul_nonneg (tq 3) (hp 3), mul_nonneg (tq 2) (hp 3), mul_nonneg (tp 1) (hp 3), mul_nonneg (tp 4) (hp 2), mul_nonneg (tp 3) (hp 2), mul_nonneg (tq 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tp 4) (hp 1), mul_nonneg (tp 3) (hp 1), mul_nonneg (tq 2) (hp 1), mul_nonneg (tq 1) (hp 1), tp 4, tp 3, tq 2, tp 1, hu 6, hl 5, hl 4, hl 3, hl 2, hl 1]

/-- `PD0` (`324S𝒟` at `u = 3/4`, times 4096). -/
noncomputable def urPD0 (h t : ℝ) : ℝ :=
  (3981312*t + 8460288) * h ^ 6 +
      (-19906560*t^2 - 8957952*t + 182565120) * h ^ 5 +
      (31186944*t^3 - 91155456*t^2 - 455528832*t + 1191563120) * h ^ 4 +
      (-15925248*t^4 + 195084288*t^3 + 170102784*t^2 - 2460883712*t + 3527515632) * h ^ 3 +
      (-108822528*t^4 + 305233920*t^3 + 1329650688*t^2 - 5621040128*t + 5210711192) * h ^ 2 +
      (-221958144*t^4 + 39647232*t^3 + 2227972224*t^2 - 5878050592*t + 3679676067) * h +
      (-153612288*t^4 - 128563200*t^3 + 1267396992*t^2 - 2229096160*t + 972792065)

theorem ur_PD0_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < urPD0 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := ur_box hh hh' (by norm_num) ht ht'
  unfold urPD0
  linarith [mul_nonneg (tp 1) (hp 6), mul_nonneg (tq 2) (hp 5), mul_nonneg (tq 1) (hp 5), mul_nonneg (tp 3) (hp 4), mul_nonneg (tq 2) (hp 4), mul_nonneg (tq 1) (hp 4), mul_nonneg (tq 4) (hp 3), mul_nonneg (tp 3) (hp 3), mul_nonneg (tp 2) (hp 3), mul_nonneg (tq 1) (hp 3), mul_nonneg (tq 4) (hp 2), mul_nonneg (tp 3) (hp 2), mul_nonneg (tp 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tq 4) (hp 1), mul_nonneg (tp 3) (hp 1), mul_nonneg (tp 2) (hp 1), mul_nonneg (tq 1) (hp 1), tq 4, tq 3, tp 2, tq 1, hl 6, hl 5, hl 4, hl 3, hl 2, hl 1]

/-- `PD1` (`1620S𝒟` at `u = 4/5`, times 4096). -/
noncomputable def urPD1 (h t : ℝ) : ℝ :=
  (15925248*t + 33841152) * h ^ 6 +
      (-84934656*t^2 - 58392576*t + 855347200) * h ^ 5 +
      (140673024*t^3 - 329453568*t^2 - 2200437248*t + 5862886720) * h ^ 4 +
      (-75644928*t^4 + 827449344*t^3 + 1192307200*t^2 - 11843334272*t + 17762341468) * h ^ 3 +
      (-506953728*t^4 + 1037795328*t^3 + 6838518784*t^2 - 27285915648*t + 26553223720) * h ^ 2 +
      (-999641088*t^4 - 419530752*t^3 + 10738979968*t^2 - 28805012256*t + 18859731163) * h +
      (-664547328*t^4 - 859797504*t^3 + 5965500288*t^2 - 10970915552*t + 5009150317)

theorem ur_PD1_pos {h t : ℝ} (hh : 1 / 6 ≤ h) (hh' : h ≤ 2 / 5) (ht : 0 ≤ t) (ht' : t ≤ 1 / 4) :
    0 < urPD1 h t := by
  obtain ⟨hp, tp, tq, hu, hl⟩ := ur_box hh hh' (by norm_num) ht ht'
  unfold urPD1
  linarith [mul_nonneg (tp 1) (hp 6), mul_nonneg (tq 2) (hp 5), mul_nonneg (tq 1) (hp 5), mul_nonneg (tp 3) (hp 4), mul_nonneg (tq 2) (hp 4), mul_nonneg (tq 1) (hp 4), mul_nonneg (tq 4) (hp 3), mul_nonneg (tp 3) (hp 3), mul_nonneg (tp 2) (hp 3), mul_nonneg (tq 1) (hp 3), mul_nonneg (tq 4) (hp 2), mul_nonneg (tp 3) (hp 2), mul_nonneg (tp 2) (hp 2), mul_nonneg (tq 1) (hp 2), mul_nonneg (tq 4) (hp 1), mul_nonneg (tq 3) (hp 1), mul_nonneg (tp 2) (hp 1), mul_nonneg (tq 1) (hp 1), tq 4, tq 3, tp 2, tq 1, hl 6, hl 5, hl 4, hl 3, hl 2, hl 1]

end SmoothedOctagon
