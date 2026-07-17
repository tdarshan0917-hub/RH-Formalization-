import Mathlib
import RHFormalization.EtaContinuation

open Filter Topology

namespace RHFormalization

/-- The real-variable absolute term `1/(n+1)^x` of the eta series. -/
noncomputable def etaAbsTerm (x : ℝ) (n : ℕ) : ℝ := 1 / (((n : ℝ) + 1) ^ x)

/-- For `x ≥ 0`, the absolute term `1/(n+1)^x` is antitone in `n`. -/
theorem etaAbsTerm_antitone {x : ℝ} (hx : 0 ≤ x) :
    Antitone (etaAbsTerm x) := by
  intro m n hmn
  simp only [etaAbsTerm]
  apply one_div_le_one_div_of_le
  · exact Real.rpow_pos_of_pos (by positivity) x
  · apply Real.rpow_le_rpow (by positivity) _ hx
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith

/-- For `x > 0`, the absolute term tends to `0`. -/
theorem etaAbsTerm_tendsto_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (etaAbsTerm x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun y : ℝ => y ^ x) atTop atTop := tendsto_rpow_atTop hx
  have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ x) atTop atTop := h2.comp h1
  have h4 : Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹) atTop (𝓝 0) := h3.inv_tendsto_atTop
  have heq : etaAbsTerm x = fun n : ℕ => (((n : ℝ) + 1) ^ x)⁻¹ := by
    funext n; simp only [etaAbsTerm, one_div]
  rw [heq]; exact h4

/-- The eta series partial sums converge (conditionally) for `x > 0`. -/
theorem etaSeries_converges {x : ℝ} (hx : 0 < x) :
    ∃ l : ℝ, Tendsto (fun N => ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * etaAbsTerm x i)
      atTop (𝓝 l) :=
  (etaAbsTerm_antitone hx.le).tendsto_alternating_series_of_tendsto_zero
    (etaAbsTerm_tendsto_zero hx)

/-- `etaAbsTerm x 0 = 1`. -/
theorem etaAbsTerm_zero (x : ℝ) : etaAbsTerm x 0 = 1 := by
  simp only [etaAbsTerm, Nat.cast_zero, zero_add, Real.one_rpow, div_one]

/-- For `0 < x`, `etaAbsTerm x 1 < 1`, i.e. `1/2^x < 1`. -/
theorem etaAbsTerm_one_lt {x : ℝ} (hx : 0 < x) : etaAbsTerm x 1 < 1 := by
  simp only [etaAbsTerm, Nat.cast_one]
  rw [div_lt_one (by positivity)]
  calc (1 : ℝ) = (1 : ℝ) ^ x := (Real.one_rpow x).symm
    _ < (1 + 1 : ℝ) ^ x := by
        apply Real.rpow_lt_rpow (by norm_num) (by norm_num) hx

/-- STAGE 3a (positivity): the eta series limit is strictly positive on `(0,1)`,
in fact for all `x > 0`. -/
theorem etaSeries_pos {x : ℝ} (hx : 0 < x) {l : ℝ}
    (hl : Tendsto (fun N => ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * etaAbsTerm x i) atTop (𝓝 l)) :
    0 < l := by
  have hlb : ∑ i ∈ Finset.range (2 * 1), (-1 : ℝ) ^ i * etaAbsTerm x i ≤ l :=
    (etaAbsTerm_antitone hx.le).alternating_series_le_tendsto hl 1
  have hcalc : ∑ i ∈ Finset.range (2 * 1), (-1 : ℝ) ^ i * etaAbsTerm x i
      = etaAbsTerm x 0 - etaAbsTerm x 1 := by
    simp [Finset.sum_range_succ]
    ring
  rw [hcalc] at hlb
  have : 0 < etaAbsTerm x 0 - etaAbsTerm x 1 := by
    rw [etaAbsTerm_zero]
    linarith [etaAbsTerm_one_lt hx]
  linarith

#print axioms etaAbsTerm_antitone
#print axioms etaAbsTerm_tendsto_zero
#print axioms etaSeries_converges
#print axioms etaSeries_pos

/-- Closed form `∑_{k=1}^n (-1)^(k+1) = if Even n then 0 else 1`, by induction. -/
theorem altSum_Icc_closed (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (k + 1) = if Even n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ m IH =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), IH]
      rcases Nat.even_or_odd m with hm | hm
      · -- m even: IH-term = 0, new exponent m+2 even so (-1)^(m+2)=1, goal if(Even (m+1))=if false=1
        have he2 : Even (m + 1 + 1) := by simpa [Nat.even_add_one] using hm
        rw [if_pos hm, if_neg (by simp [Nat.even_add_one, hm]), he2.neg_one_pow]
        ring
      · -- m odd: IH-term = 1, new exponent m+2 odd so (-1)^(m+2)=-1, goal if(Even (m+1))=if true=0
        have ho2 : Odd (m + 1 + 1) := by simpa [Nat.odd_add_one, Nat.not_odd_iff_even] using hm
        have he1 : Even (m + 1) := by simpa [Nat.even_add_one, Nat.not_even_iff_odd] using hm
        rw [if_neg (by simp [Nat.not_even_iff_odd, hm]), if_pos he1, ho2.neg_one_pow]
        ring

/-- The signed partial sums `∑_{k=1}^n etaCoeff k` are bounded by 1 in norm. -/
theorem etaCoeff_partialSum_bound (n : ℕ) :
    ‖∑ k ∈ Finset.Icc 1 n, etaCoeff (k : ZMod 2)‖ ≤ 1 := by
  have hrw : (∑ k ∈ Finset.Icc 1 n, etaCoeff (k : ZMod 2))
           = ∑ k ∈ Finset.Icc 1 n, (-1 : ℂ) ^ (k + 1) :=
    Finset.sum_congr rfl (fun k _ => etaCoeff_natCast k)
  rw [hrw, altSum_Icc_closed]
  split_ifs
  · simp
  · simp

#print axioms etaSeries_pos
#print axioms altSum_Icc_closed
#print axioms etaCoeff_partialSum_bound

/-- The bounded step-function of partial sums of `etaCoeff`. -/
noncomputable def etaA (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, etaCoeff (k : ZMod 2)

/-- The integral representation function. -/
noncomputable def etaI (s : ℂ) : ℂ :=
  s * ∫ t in Set.Ioi (1 : ℝ), etaA t * t ^ (-(s + 1))

/-- The partial sums of `etaCoeff` are `O(n^0)` (i.e. bounded). -/
theorem etaCoeff_sum_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, etaCoeff (k : ZMod 2)) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (0 : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hb : ‖∑ k ∈ Finset.Icc 1 n, etaCoeff (k : ZMod 2)‖ ≤ 1 := etaCoeff_partialSum_bound n
  have hpow : ‖(n : ℝ) ^ (0 : ℝ)‖ = 1 := by
    rw [Real.rpow_zero]; simp
  rw [hpow, mul_one]
  exact hb

/-- STAGE 3b-3: on `re > 1`, the integral representation equals the eta L-function. -/
theorem etaI_eq_LFunction_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    etaI s = ZMod.LFunction etaCoeff s := by
  rw [ZMod.LFunction_eq_LSeries etaCoeff hs]
  simp only [etaI, etaA]
  exact (LSeries_eq_mul_integral (etaCoeff ·) (le_refl (0:ℝ)) (by linarith)
        (ZMod.LSeriesSummable_of_one_lt_re etaCoeff hs) etaCoeff_sum_isBigO).symm

#print axioms etaCoeff_sum_isBigO
#print axioms etaI_eq_LFunction_of_one_lt_re

/-- STAGE 3b-4 (conditional): given `etaI` is analytic on the right half-plane `re > 0`,
the identity theorem extends the `re > 1` agreement to all of `re > 0`.
The analyticity hypothesis `h_analytic` is discharged separately by the Mellin step (3b-2b). -/
theorem etaI_eq_LFunction_of_re_pos
    (h_analytic : AnalyticOnNhd ℂ etaI {s : ℂ | 0 < s.re})
    {s : ℂ} (hs : 0 < s.re) :
    etaI s = ZMod.LFunction etaCoeff s := by
  have hU : IsPreconnected {s : ℂ | 0 < s.re} :=
    (convex_halfSpace_re_gt 0).isPreconnected
  -- LFunction etaCoeff is entire, hence analytic on the half-plane
  have hLF : AnalyticOnNhd ℂ (ZMod.LFunction etaCoeff) {s : ℂ | 0 < s.re} :=
    etaLFunction_analytic.mono (Set.subset_univ _)
  -- agreement on {re > 1}
  have hagree : Set.EqOn etaI (ZMod.LFunction etaCoeff) {s : ℂ | 1 < s.re} := by
    intro z hz
    exact etaI_eq_LFunction_of_one_lt_re hz
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    rw [Set.mem_setOf_eq]; norm_num
  have heq : Set.EqOn etaI (ZMod.LFunction etaCoeff) {s : ℂ | 0 < s.re} := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      h_analytic hLF hU (z₀ := 2) ?_ ?_
    · rw [Set.mem_setOf_eq]; norm_num
    · exact hagree.eventuallyEq_of_mem (hopen.mem_nhds hz2)
  exact heq hs

#print axioms etaI_eq_LFunction_of_re_pos

/-- `etaA` vanishes on `(0,1)`: for `t < 1`, `⌊t⌋₊ = 0` so the sum is over `Icc 1 0 = ∅`. -/
theorem etaA_eq_zero_of_lt_one {t : ℝ} (ht : t < 1) : etaA t = 0 := by
  unfold etaA
  have h0 : ⌊t⌋₊ = 0 := by
    rw [Nat.floor_eq_zero]; exact ht
  rw [h0]
  simp [Finset.Icc_eq_empty]

/-- `etaA` is bounded by 1 in norm everywhere. -/
theorem etaA_norm_le_one (t : ℝ) : ‖etaA t‖ ≤ 1 := by
  unfold etaA
  exact etaCoeff_partialSum_bound ⌊t⌋₊

#print axioms etaA_eq_zero_of_lt_one
#print axioms etaA_norm_le_one

/-- `etaA` is measurable (it factors through `⌊·⌋₊` which is measurable). -/
theorem etaA_measurable : Measurable etaA := by
  have h : etaA = (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, etaCoeff (k : ZMod 2)) ∘ (Nat.floor) := by
    funext t; rfl
  rw [h]
  exact (measurable_from_nat).comp Nat.measurable_floor

#print axioms etaA_measurable

/-- `etaA` is integrable on any bounded interval `Ioo 0 b` (bounded × finite measure). -/
theorem etaA_integrableOn_Ioo (b : ℝ) :
    MeasureTheory.IntegrableOn etaA (Set.Ioo 0 b) := by
  apply MeasureTheory.Measure.integrableOn_of_bounded (M := 1)
  · -- finite measure
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  · -- ae strongly measurable
    exact etaA_measurable.aestronglyMeasurable
  · -- bounded by 1
    filter_upwards with a using etaA_norm_le_one a

/-- R1: `etaA` is locally integrable on `Ioi 0`. -/
theorem etaA_locallyIntegrableOn :
    MeasureTheory.LocallyIntegrableOn etaA (Set.Ioi 0) := by
  intro x hx
  -- x > 0; use the neighborhood Ioo 0 (x+1)
  refine ⟨Set.Ioo 0 (x + 1), ?_, ?_⟩
  · -- Ioo 0 (x+1) ∈ 𝓝[Ioi 0] x
    apply nhdsWithin_le_nhds
    apply IsOpen.mem_nhds isOpen_Ioo
    constructor
    · exact hx
    · linarith
  · exact etaA_integrableOn_Ioo (x + 1)

#print axioms etaA_integrableOn_Ioo
#print axioms etaA_locallyIntegrableOn

/-- R4a-top: `etaA` is `O(t^0)` at infinity (it is bounded). -/
theorem etaA_isBigO_atTop :
    etaA =O[Filter.atTop] (fun t : ℝ => t ^ (-(0:ℝ))) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
  have hb : ‖etaA t‖ ≤ 1 := etaA_norm_le_one t
  have hpow : ‖t ^ (-(0:ℝ))‖ = 1 := by
    rw [neg_zero, Real.rpow_zero]; simp
  rw [hpow, mul_one]
  exact hb

/-- R4a-bot: `etaA` is `O(t^(-(-1)))` near `0⁺` (it vanishes on a right-neighborhood of 0). -/
theorem etaA_isBigO_zero :
    etaA =O[nhdsWithin 0 (Set.Ioi 0)] (fun t : ℝ => t ^ (-(-1:ℝ))) := by
  have hzero : etaA =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ => (0 : ℂ)) := by
    have hIoo : Set.Ioo 0 1 ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hIoo] with t ht
    exact etaA_eq_zero_of_lt_one ht.2
  exact hzero.trans_isBigO (Asymptotics.isBigO_zero _ _)

#print axioms etaA_isBigO_atTop
#print axioms etaA_isBigO_zero

/-- R4a-bot parametrized: for ANY exponent `b`, `etaA` is `O(t^(-b))` near `0⁺`,
since it vanishes on a right-neighborhood of 0. -/
theorem etaA_isBigO_zero_param (b : ℝ) :
    etaA =O[nhdsWithin 0 (Set.Ioi 0)] (fun t : ℝ => t ^ (-b)) := by
  have hzero : etaA =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun _ => (0 : ℂ)) := by
    have hIoo : Set.Ioo 0 1 ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hIoo] with t ht
    exact etaA_eq_zero_of_lt_one ht.2
  exact hzero.trans_isBigO (Asymptotics.isBigO_zero _ _)

#print axioms etaA_isBigO_zero_param

/-- The Mellin integrand for `etaA` is integrable on `Ioi 0` for `0 < s.re`. -/
theorem etaA_mellin_integrableOn {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t : ℂ) ^ ((-s) - 1) • etaA t) (Set.Ioi 0) := by
  have hconv : MellinConvergent etaA (-s) := by
    apply mellinConvergent_of_isBigO_rpow (a := 0) (b := (-s.re - 1))
      etaA_locallyIntegrableOn etaA_isBigO_atTop ?_ (etaA_isBigO_zero_param (-s.re - 1)) ?_
    · -- (-s).re < 0
      rw [Complex.neg_re]; linarith
    · -- -s.re - 1 < (-s).re
      rw [Complex.neg_re]; linarith
  exact hconv

#print axioms etaA_mellin_integrableOn

/-- R3a: the Mellin integral over `Ioi 0` equals the integral over `Ioi 1`
(since `etaA` vanishes on `(0,1)` and `{1}` is null). -/
theorem etaA_mellin_Ioi_zero_eq_Ioi_one {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ ((-s) - 1) • etaA t)
      = ∫ t in Set.Ioi (1:ℝ), (t : ℂ) ^ ((-s) - 1) • etaA t := by
  have hconv := etaA_mellin_integrableOn hs
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  have hint_Ioc : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ ((-s) - 1) • etaA t) (Set.Ioc 0 1) :=
    hconv.mono_set (by rw [hsplit]; exact Set.subset_union_left)
  have hint_Ioi1 : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ ((-s) - 1) • etaA t) (Set.Ioi 1) :=
    hconv.mono_set (by rw [hsplit]; exact Set.subset_union_right)
  rw [hsplit, MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi_same) measurableSet_Ioi
    hint_Ioc hint_Ioi1]
  have hzero : (∫ t in Set.Ioc (0:ℝ) 1, (t : ℂ) ^ ((-s) - 1) • etaA t) = 0 := by
    apply MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero
    have hne : ∀ᵐ x : ℝ, x ≠ 1 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]
        using MeasureTheory.compl_mem_ae_iff.mpr (Real.volume_singleton (a := 1))
    filter_upwards [hne] with x hxne
    intro hxIoc
    have hlt : x < 1 := lt_of_le_of_ne hxIoc.2 hxne
    rw [etaA_eq_zero_of_lt_one hlt, smul_zero]
  rw [hzero, zero_add]

#print axioms etaA_mellin_Ioi_zero_eq_Ioi_one

/-- R3b: the bridge `etaI s = s * mellin etaA (-s)` for `0 < s.re`. -/
theorem etaI_eq_mellin {s : ℂ} (hs : 0 < s.re) :
    etaI s = s * mellin etaA (-s) := by
  rw [etaI, mellin, etaA_mellin_Ioi_zero_eq_Ioi_one hs]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  ring

#print axioms etaI_eq_mellin

/-- The Mellin transform of `etaA` is differentiable at `-s` for `0 < s.re`. -/
theorem mellin_etaA_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin etaA) (-s) :=
  mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := (-s.re - 1))
    etaA_locallyIntegrableOn etaA_isBigO_atTop (by rw [Complex.neg_re]; linarith)
    (etaA_isBigO_zero_param (-s.re - 1)) (by rw [Complex.neg_re]; linarith)

/-- `etaI` is differentiable at every point of the right half-plane `0 < s.re`. -/
theorem etaI_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ etaI s := by
  have hmellin : DifferentiableAt ℂ (fun z : ℂ => mellin etaA (-z)) s := by
    have hcomp : DifferentiableAt ℂ (mellin etaA) ((fun z : ℂ => -z) s) :=
      mellin_etaA_differentiableAt hs
    exact hcomp.comp s (differentiable_neg.differentiableAt)
  have hid : DifferentiableAt ℂ (fun z : ℂ => z) s := differentiableAt_id
  have hmul : DifferentiableAt ℂ (fun z : ℂ => z * mellin etaA (-z)) s := hid.mul hmellin
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have heq : etaI =ᶠ[nhds s] (fun z : ℂ => z * mellin etaA (-z)) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact etaI_eq_mellin hz
  exact hmul.congr_of_eventuallyEq heq

/-- R4: `etaI` is analytic on the right half-plane `0 < s.re`.
This discharges the hypothesis of `etaI_eq_LFunction_of_re_pos`. -/
theorem etaI_analyticOnNhd :
    AnalyticOnNhd ℂ etaI {s : ℂ | 0 < s.re} := by
  apply DifferentiableOn.analyticOnNhd ?_ (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  exact (etaI_differentiableAt hs).differentiableWithinAt

#print axioms mellin_etaA_differentiableAt
#print axioms etaI_differentiableAt
#print axioms etaI_analyticOnNhd

/-- R5a: the factor `(1 - 2·2^(-x))` is nonzero for real `x ∈ (0,1)`.
For such `x`, `2^(-x) ∈ (1/2, 1)`, so `2·2^(-x) ∈ (1,2)`, so the factor is in `(-1,0)`. -/
theorem factor_ne_zero {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (1 - 2 * (2 : ℂ) ^ (-(x : ℂ))) ≠ 0 := by
  -- 2^(-x) as a real number, and the complex power is its cast
  have hb : (2 : ℂ) ^ (-(x : ℂ)) = ((2 : ℝ) ^ (-x) : ℝ) := by
    have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
    have hnx : (-(x : ℂ)) = ((-x : ℝ) : ℂ) := by push_cast; ring
    rw [h2, hnx, ← Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2)]
  rw [hb]
  -- reduce to a real statement: 1 - 2 * 2^(-x) ≠ 0
  have hlt1 : (2 : ℝ) ^ (-x) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgt : (1 / 2 : ℝ) < (2 : ℝ) ^ (-x) := by
    rw [show (1/2 : ℝ) = (2:ℝ)^(-1 : ℝ) by rw [Real.rpow_neg_one]; norm_num]
    rw [Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ) < 2)]
    linarith
  -- so 2 * 2^(-x) > 1, hence 1 - 2*2^(-x) < 0, hence ≠ 0
  have hreal : (1 : ℝ) - 2 * (2 : ℝ) ^ (-x) ≠ 0 := by
    have : 1 < 2 * (2 : ℝ) ^ (-x) := by linarith
    linarith
  intro hcontra
  apply hreal
  have : ((1 : ℝ) - 2 * (2 : ℝ) ^ (-x) : ℝ) = 0 := by
    have hcast : ((1 - 2 * (2:ℝ)^(-x) : ℝ) : ℂ) = 0 := by push_cast; push_cast at hcontra; linear_combination hcontra
    exact_mod_cast hcast
  exact this

#print axioms factor_ne_zero

/-- R5b-1: the real eta partial sum at `x` equals the real-cast complex LSeries partial sum.
3a term i = (-1)^i/(i+1)^x; LSeries term (i+1) = etaCoeff(i+1)/(i+1)^x = (-1)^(i+2)/(i+1)^x. -/
theorem etaRealPartial_eq {x : ℝ} (N : ℕ) :
    (∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * etaAbsTerm x i)
      = ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i / (((i : ℝ) + 1) ^ x) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [etaAbsTerm]
  ring

#print axioms etaRealPartial_eq

/-- R5b-2: the complex `etaCoeff` LSeries partial sum (over `Icc 1 N`) at real `x`
equals 3a's real alternating sum (over `range N`), cast to `ℂ`. By induction on `N`. -/
theorem etaLSeries_partial_eq_ofReal {x : ℝ} (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, etaCoeff (n : ZMod 2) * (n : ℂ) ^ (-(x : ℂ)))
      = ((∑ i ∈ Finset.range N, (-1 : ℝ) ^ i / (((i : ℝ) + 1) ^ x) : ℝ) : ℂ) := by
  induction N with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le M)), ih,
        Finset.sum_range_succ, Complex.ofReal_add]
    congr 1
    -- the new top term: etaCoeff(M+1) * (M+1)^(-x) = ofReal((-1)^M / (M+1)^x)
    have hk : etaCoeff (((M + 1 : ℕ)) : ZMod 2) = (-1 : ℂ) ^ M := by
      rw [etaCoeff_natCast, pow_succ]; ring
    rw [hk]
    rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
    rw [Complex.ofReal_cpow (by positivity : (0:ℝ) ≤ (M:ℝ) + 1)]
    push_cast
    rw [Complex.cpow_neg]
    rw [div_eq_mul_inv]

#print axioms etaLSeries_partial_eq_ofReal

/-- R5b-3: there is a positive real `l` to which the complex `etaCoeff` LSeries partial sums
(over `Icc 1 N`) converge, for `0 < x`. Packages 3a (convergence + positivity) with step 2. -/
theorem etaLSeries_partial_tendsto_pos {x : ℝ} (hx : 0 < x) :
    ∃ l : ℝ, 0 < l ∧
      Filter.Tendsto
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, etaCoeff (n : ZMod 2) * ((n : ℕ) : ℂ) ^ (-(x : ℂ)))
        Filter.atTop (𝓝 (l : ℂ)) := by
  obtain ⟨l, hl⟩ := etaSeries_converges hx
  refine ⟨l, etaSeries_pos hx hl, ?_⟩
  have hreal : Filter.Tendsto
      (fun N => ((∑ i ∈ Finset.range N, (-1 : ℝ) ^ i / (((i : ℝ) + 1) ^ x) : ℝ)))
      Filter.atTop (𝓝 l) := by
    simp_rw [etaRealPartial_eq] at hl
    exact hl
  have hcomplex : Filter.Tendsto
      (fun N => (((∑ i ∈ Finset.range N, (-1 : ℝ) ^ i / (((i : ℝ) + 1) ^ x) : ℝ)) : ℂ))
      Filter.atTop (𝓝 (l : ℂ)) :=
    (Complex.continuous_ofReal.tendsto l).comp hreal
  -- convert via the pointwise equality from step 2
  refine hcomplex.congr (fun N => ?_)
  exact (etaLSeries_partial_eq_ofReal N).symm

#print axioms etaLSeries_partial_tendsto_pos

/-- The zero-padded coefficient `etaCoeff'` (= etaCoeff except 0 at n=0), for the Abel engine
which requires `c 0 = 0`. Its `Icc 1 n` partial sums equal etaCoeff's. -/
noncomputable def etaCoeff' (n : ℕ) : ℂ := if n = 0 then 0 else etaCoeff (n : ZMod 2)

theorem etaCoeff'_zero : etaCoeff' 0 = 0 := by simp [etaCoeff']

theorem etaCoeff'_sum_eq (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, etaCoeff' k) = ∑ k ∈ Finset.Icc 1 n, etaCoeff (k : ZMod 2) := by
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_Icc] at hk
  simp only [etaCoeff', if_neg (by omega : k ≠ 0)]

theorem etaCoeff'_sum_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, etaCoeff' k) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (0 : ℝ)) := by
  have : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, etaCoeff' k)
      = (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, etaCoeff (k : ZMod 2)) := by
    funext n; exact etaCoeff'_sum_eq n
  rw [this]; exact etaCoeff_sum_isBigO

theorem etaCoeff'_Icc_zero_eq (n : ℕ) :
    (∑ k ∈ Finset.Icc 0 n, etaCoeff' k) = ∑ k ∈ Finset.Icc 1 n, etaCoeff' k := by
  cases n with
  | zero => simp [etaCoeff'_zero]
  | succ m =>
    rw [show Finset.Icc 0 (m + 1) = insert 0 (Finset.Icc 1 (m + 1)) from ?_]
    · rw [Finset.sum_insert (by simp), etaCoeff'_zero, zero_add]
    · ext k
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega

#print axioms etaCoeff'_sum_isBigO
#print axioms etaCoeff'_Icc_zero_eq

/-- R5b-4 piece 2: the Abel engine applied to `etaCoeff'` at real `x > 0`.
The partial sums `∑_{Icc 0 n} (t↦t^(-x))(k) · etaCoeff'(k)` converge to
`0 - ∫ deriv(t^(-x)) · (partial sums of etaCoeff')`. -/
theorem etaCoeff'_engine_tendsto {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, ((k : ℝ) : ℂ) ^ (-(x : ℂ)) * etaCoeff' k)
      Filter.atTop
      (𝓝 (0 - ∫ t in Set.Ioi (1:ℝ),
          deriv (fun u : ℝ => (u : ℂ) ^ (-(x:ℂ))) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, etaCoeff' k)) := by
  have h₂ : (-(x:ℂ)) ≠ 0 := by
    rw [neg_ne_zero, Ne, Complex.ofReal_eq_zero]; linarith
  have h₃ : ∀ t ∈ Set.Ici (1:ℝ), DifferentiableAt ℝ (fun u : ℝ => (u : ℂ) ^ (-(x:ℂ))) t := by
    intro t ht
    exact differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht).ne' h₂
  have h₁ : (-(x:ℂ) - 1).re + (0:ℝ) < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re, add_zero]
    linarith
  refine tendsto_sum_mul_atTop_nhds_one_sub_integral₀ (𝕜 := ℂ)
    (c := etaCoeff') (f := fun u : ℝ => (u : ℂ) ^ (-(x:ℂ))) (l := 0)
    etaCoeff'_zero h₃ ?_ ?_ ?_ (integrableAtFilter_rpow_atTop_iff.mpr h₁)
  · -- hf_int: LocallyIntegrableOn (deriv f) (Ici 1)
    refine (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi <|
      integrableOn_Ioi_deriv_ofReal_cpow zero_lt_one ?_).locallyIntegrableOn
    · simp only [Complex.neg_re, Complex.ofReal_re]; linarith
  · -- h_lim: f(n) * (Icc 0 n sum) → 0
    have hlim : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(x - 0))) Filter.atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    refine (Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow
      (a := -x) (b := 0) (c := -x) ?_ ?_ (by linarith)).trans_tendsto ?_
    · exact Asymptotics.isBigO_norm_left.mp <|
        (Complex.norm_ofReal_cpow_eventually_eq_atTop _).isBigO.natCast_atTop
    · simp_rw [etaCoeff'_Icc_zero_eq]; exact etaCoeff'_sum_isBigO
    · simpa using hlim
  · -- hg_dom
    have hfloor : (fun t : ℝ => deriv (fun u : ℝ => (u:ℂ)^(-(x:ℂ))) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, etaCoeff' k)
        = (fun t : ℝ => deriv (fun u : ℝ => (u:ℂ)^(-(x:ℂ))) t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, etaCoeff' k) := by
      funext t; rw [etaCoeff'_Icc_zero_eq ⌊t⌋₊]
    rw [hfloor]
    have hexp : ((-(x:ℂ) - 1).re + (0:ℝ)) = -x - 1 := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.one_re, add_zero]
    rw [show (fun t : ℝ => t ^ ((-(x:ℂ) - 1).re + (0:ℝ)))
        = (fun t : ℝ => t ^ (-x - 1)) from by rw [hexp]]
    refine Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow
      (a := -x - 1) (b := 0) (c := -x - 1) ?_ ?_ (by linarith)
    · simpa using isBigO_deriv_ofReal_cpow_const_atTop (-(x:ℂ))
    · simpa using (etaCoeff'_sum_isBigO.comp_tendsto tendsto_nat_floor_atTop).trans
        (Asymptotics.isEquivalent_nat_floor.isBigO.rpow le_rfl (Filter.eventually_ge_atTop 0))

#print axioms etaCoeff'_engine_tendsto

/-- R5b-4 piece 3: the engine's integral equals `etaI x`. The engine output
`0 - ∫ deriv(t^(-x))·(partial sums)` rewrites to `x · ∫ etaA·t^(-(x+1))` = `etaI x`. -/
theorem engine_integral_eq_etaI {x : ℝ} (hx : 0 < x) :
    (0 - ∫ t in Set.Ioi (1:ℝ),
        deriv (fun u : ℝ => (u : ℂ) ^ (-(x:ℂ))) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, etaCoeff' k)
      = etaI (x : ℂ) := by
  have hxne : (x : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; linarith
  -- rewrite the integrand: deriv = -x·t^(-x-1), and Icc 0 sum = etaA t
  have hintegrand : ∀ t ∈ Set.Ioi (1:ℝ),
      deriv (fun u : ℝ => (u : ℂ) ^ (-(x:ℂ))) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, etaCoeff' k
        = -(x:ℂ) * (etaA t * t ^ (-((x:ℂ) + 1))) := by
    intro t ht
    simp only [Set.mem_Ioi] at ht
    rw [Complex.deriv_ofReal_cpow_const (by linarith : t ≠ 0) (neg_ne_zero.mpr hxne)]
    rw [etaCoeff'_Icc_zero_eq, etaCoeff'_sum_eq]
    have hA : (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, etaCoeff (k : ZMod 2)) = etaA t := rfl
    rw [hA]
    have hexp : (-(x:ℂ)) - 1 = -((x:ℂ) + 1) := by ring
    rw [hexp]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hintegrand]
  rw [MeasureTheory.integral_const_mul]
  rw [etaI]
  ring

#print axioms engine_integral_eq_etaI

/-- R5b-4 piece 4: the `etaCoeff` partial sums tend to `etaI x` (combining engine + integral id). -/
theorem etaLSeries_partial_tendsto_etaI {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, ((k : ℝ) : ℂ) ^ (-(x : ℂ)) * etaCoeff' k)
      Filter.atTop (𝓝 (etaI (x : ℂ))) := by
  have h := etaCoeff'_engine_tendsto hx
  rwa [engine_integral_eq_etaI hx] at h

#print axioms etaLSeries_partial_tendsto_etaI

/-- R5b-4 finish: `etaI x = (l:ℂ)` for some `l > 0`, hence `etaI x ≠ 0`, for real `x ∈ (0,1)`. -/
theorem etaI_ne_zero_of_real {x : ℝ} (hx0 : 0 < x) : etaI (x : ℂ) ≠ 0 := by
  obtain ⟨l, hlpos, hltends⟩ := etaLSeries_partial_tendsto_pos hx0
  have hEtends := etaLSeries_partial_tendsto_etaI hx0
  -- the two sequences agree: ∑ Icc 0 n, k^(-x)·etaCoeff' k = ∑ Icc 1 n, etaCoeff(k)·k^(-x)
  have hseq : (fun n : ℕ => ∑ k ∈ Finset.Icc 0 n, ((k : ℝ) : ℂ) ^ (-(x : ℂ)) * etaCoeff' k)
      = (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, etaCoeff (n : ZMod 2) * ((n : ℕ) : ℂ) ^ (-(x : ℂ))) := by
    funext n
    have hbridge : (∑ k ∈ Finset.Icc 0 n, ((k : ℝ) : ℂ) ^ (-(x : ℂ)) * etaCoeff' k)
        = ∑ k ∈ Finset.Icc 1 n, ((k : ℝ) : ℂ) ^ (-(x : ℂ)) * etaCoeff' k := by
      cases n with
      | zero => simp [etaCoeff'_zero]
      | succ m =>
        rw [show Finset.Icc 0 (m+1) = insert 0 (Finset.Icc 1 (m+1)) from by
              ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega]
        rw [Finset.sum_insert (by simp), etaCoeff'_zero, mul_zero, zero_add]
    rw [hbridge]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hk
    rw [mul_comm]
    simp only [etaCoeff', if_neg (by omega : k ≠ 0)]
    norm_cast
  rw [hseq] at hEtends
  -- both limits exist; uniqueness gives etaI x = (l:ℂ)
  have heq : etaI (x : ℂ) = (l : ℂ) := tendsto_nhds_unique hEtends hltends
  rw [heq]
  rw [Ne, Complex.ofReal_eq_zero]
  linarith

#print axioms etaI_ne_zero_of_real

/-- R5b-5: the eta L-function is nonzero at real `x ∈ (0,1)`. -/
theorem etaLFunction_ne_zero_of_real {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ZMod.LFunction etaCoeff (x : ℂ) ≠ 0 := by
  rw [← etaI_eq_LFunction_of_re_pos etaI_analyticOnNhd
        (by rw [Complex.ofReal_re]; linarith)]
  exact etaI_ne_zero_of_real hx0

#print axioms etaLFunction_ne_zero_of_real

/-- R5c: ζ ≠ 0 on the real segment (0,1) — the deliverable `h_real_zero_free`. -/
theorem h_real_zero_free (s : ℂ) (hs_im : s.im = 0) (hs_re0 : 0 < s.re) (hs_re1 : s.re < 1) :
    riemannZeta s ≠ 0 := by
  -- s = (s.re : ℂ) since imaginary part is 0
  have hs : s = (s.re : ℂ) := by
    apply Complex.ext
    · simp [Complex.ofReal_re]
    · simp [Complex.ofReal_im, hs_im]
  set x := s.re with hxdef
  rw [hs]
  -- LFunction etaCoeff x = (1 - 2·2^(-x))·ζ(x); LHS ≠ 0, factor ≠ 0 ⟹ ζ(x) ≠ 0
  intro hzero
  have hfactor := factor_ne_zero hs_re0 hs_re1
  have hLF := etaLFunction_ne_zero_of_real hs_re0 hs_re1
  rw [etaLFunction_eq_factor_zeta (by rw [Ne, Complex.ofReal_eq_one]; linarith)] at hLF
  rw [hzero, mul_zero] at hLF
  exact hLF rfl
end RHFormalization

#print axioms RHFormalization.h_real_zero_free
