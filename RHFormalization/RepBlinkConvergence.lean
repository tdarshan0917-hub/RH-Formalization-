/-
RepBlinkConvergence.lean

Honest `ZeroPoleLocalUniformConvergenceAPI` for `ZpoleRepSeries M` along a
custom "blink" zero-exhaustion:

  zeroSet n := (rep image at stage n) ∪ (first-appearance band at stage n)

Bands partition all zeros, so band envelope sums are summable and tend to 0
uniformly on any compact avoiding the pole set; the rep part converges by the
banked `repZpole_luc`. No raw-Bshared statement appears anywhere.
-/
import RHFormalization.HMeromorphicPackage
import RHFormalization.ShiftedLaplaceRepLUC
import RHFormalization.ShiftedLaplaceRepMeromorphic
import RHFormalization.ShiftedLaplaceRepMeromorphicDirect
import RHFormalization.HsumUnconditional

namespace RHFormalization

noncomputable section

open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

/-! ## First-appearance bands along the default exhaustion -/

/-- Union of all default stages strictly before `n`, at the subtype level. -/
def prevSubtypeStages (n : ℕ) : Finset {ρ : ℂ // IsNontrivialZetaZero ρ} :=
  (Finset.range n).biUnion subtypeStage

/-- First-appearance band at stage `n`. -/
def bandSubtypeStage (n : ℕ) : Finset {ρ : ℂ // IsNontrivialZetaZero ρ} :=
  subtypeStage n \ prevSubtypeStages n

theorem bandSubtypeStage_subset (n : ℕ) :
    bandSubtypeStage n ⊆ subtypeStage n :=
  Finset.sdiff_subset

theorem subtypeStage_subset_prevSubtypeStages {m n : ℕ} (h : m < n) :
    subtypeStage m ⊆ prevSubtypeStages n := fun ρ hρ =>
  Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr h, hρ⟩

theorem bandSubtypeStage_disjoint {m n : ℕ} (h : m < n) :
    Disjoint (bandSubtypeStage m) (bandSubtypeStage n) := by
  refine Finset.disjoint_left.mpr fun ρ hm hn => ?_
  exact (Finset.mem_sdiff.mp hn).2
    (subtypeStage_subset_prevSubtypeStages h (bandSubtypeStage_subset m hm))

/-! ## The blink exhaustion -/

/-- Representatives at every stage, plus the first-appearance band. -/
def repBlinkExhaustion : ZeroExhaustion where
  zeroSet n :=
    (repSubtypeStage n).image (fun ρ => ρ.1) ∪
      (bandSubtypeStage n).image (fun ρ => ρ.1)
  h_all_zeros := by
    intro n ρ h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp h
      exact σ.2.1
    · obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp h
      exact σ.2
  h_eventually_contains := by
    classical
    intro ρ hρ
    obtain ⟨n₀, hn₀⟩ := defaultZeroExhaustion.h_eventually_contains ρ hρ
    have hex : ∃ n, ρ ∈ defaultZeroExhaustion.zeroSet n := ⟨n₀, hn₀⟩
    refine ⟨Nat.find hex, Finset.mem_union.mpr (Or.inr ?_)⟩
    refine Finset.mem_image.mpr ⟨⟨ρ, hρ⟩, ?_, rfl⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simp only [subtypeStage, Finset.mem_subtype]
      exact Nat.find_spec hex
    · intro hmem
      obtain ⟨m, hm, hmem'⟩ := Finset.mem_biUnion.mp hmem
      have hρm : ρ ∈ defaultZeroExhaustion.zeroSet m := by
        simpa [subtypeStage, Finset.mem_subtype] using hmem'
      exact Nat.find_min hex (Finset.mem_range.mp hm) hρm

@[simp] theorem repBlinkExhaustion_zeroSet (n : ℕ) :
    repBlinkExhaustion.zeroSet n =
      (repSubtypeStage n).image (fun ρ => ρ.1) ∪
        (bandSubtypeStage n).image (fun ρ => ρ.1) := rfl

/-- Band remainder of the blink partial sum. -/
def blinkRemainder (M : ZeroMultiplicityData) (n : ℕ) (s : ℂ) : ℂ :=
  ∑ ρ ∈ ((bandSubtypeStage n).image (fun ρ => ρ.1) \
      (repSubtypeStage n).image (fun ρ => ρ.1)),
    zeroPoleSummand M ρ s

theorem blink_partial_decomp (M : ZeroMultiplicityData) (n : ℕ) (s : ℂ) :
    zeroPolePartial M repBlinkExhaustion n s =
      repZeroPolePartial M n s + blinkRemainder M n s := by
  have hU :
      (repSubtypeStage n).image (fun ρ => ρ.1) ∪
        (bandSubtypeStage n).image (fun ρ => ρ.1) =
      (repSubtypeStage n).image (fun ρ => ρ.1) ∪
        ((bandSubtypeStage n).image (fun ρ => ρ.1) \
          (repSubtypeStage n).image (fun ρ => ρ.1)) :=
    Finset.union_sdiff_self_eq_union.symm
  have hrep :
      ∑ ρ ∈ (repSubtypeStage n).image (fun ρ => ρ.1),
        zeroPoleSummand M ρ s = repZeroPolePartial M n s :=
    Finset.sum_image (fun x _ y _ h => Subtype.coe_injective h)
  calc zeroPolePartial M repBlinkExhaustion n s
      = ∑ ρ ∈ ((repSubtypeStage n).image (fun ρ => ρ.1) ∪
          (bandSubtypeStage n).image (fun ρ => ρ.1)),
          zeroPoleSummand M ρ s := rfl
    _ = ∑ ρ ∈ ((repSubtypeStage n).image (fun ρ => ρ.1) ∪
          ((bandSubtypeStage n).image (fun ρ => ρ.1) \
            (repSubtypeStage n).image (fun ρ => ρ.1))),
          zeroPoleSummand M ρ s := by rw [← hU]
    _ = (∑ ρ ∈ (repSubtypeStage n).image (fun ρ => ρ.1),
          zeroPoleSummand M ρ s) +
        ∑ ρ ∈ ((bandSubtypeStage n).image (fun ρ => ρ.1) \
          (repSubtypeStage n).image (fun ρ => ρ.1)),
          zeroPoleSummand M ρ s :=
        Finset.sum_union Finset.disjoint_sdiff
    _ = repZeroPolePartial M n s + blinkRemainder M n s := by
        rw [hrep]; rfl

/-- Blink partials converge locally uniformly to the rep series on every
compact avoiding the pole set. -/
theorem repBlink_luc
    (M : ZeroMultiplicityData) (D : ZeroPoleEnvelopeData M)
    (K : CompactAwayFromZeroPoles) :
    LocallyUniformConvergesOnC
      (fun n s => zeroPolePartial M repBlinkExhaustion n s)
      (ZpoleRepSeries M) K.K := by
  have hrepTU : TendstoUniformlyOn
      (fun n s => repZeroPolePartial M n s)
      (ZpoleRepSeries M) atTop K.K :=
    tendstoUniformlyOn_of_tlu_isCompact (repZpole_luc M D K) K.h_compact
  rcases Set.eq_empty_or_nonempty K.K with hKe | ⟨x₀, hx₀⟩
  · intro u hu x hx
    rw [hKe] at hx
    simp only [Set.mem_empty_iff_false] at hx
  · have hu0 : ∀ ρ : {ρ : ℂ // IsNontrivialZetaZero ρ}, 0 ≤ D.u K ρ :=
      fun ρ => le_trans (norm_nonneg _) (D.h_bound K ρ x₀ hx₀)
    have hbdd : ∀ N, ∑ k ∈ Finset.range N,
        (∑ ρ ∈ bandSubtypeStage k, D.u K ρ) ≤ ∑' ρ, D.u K ρ := by
      intro N
      have hdisj : (↑(Finset.range N) : Set ℕ).PairwiseDisjoint
          bandSubtypeStage := by
        intro m _ n _ hmn
        rcases lt_or_gt_of_ne hmn with h | h
        · exact bandSubtypeStage_disjoint h
        · exact (bandSubtypeStage_disjoint h).symm
      rw [← Finset.sum_biUnion hdisj]
      first
        | exact sum_le_tsum _ (fun ρ _ => hu0 ρ) (D.h_summable K)
        | exact Finset.sum_le_tsum _ (fun ρ _ => hu0 ρ) (D.h_summable K)
        | exact (D.h_summable K).sum_le_tsum _ (fun ρ _ => hu0 ρ)
        | exact Summable.sum_le_tsum (D.h_summable K) _ (fun ρ _ => hu0 ρ)
    have hbsum : Summable (fun n => ∑ ρ ∈ bandSubtypeStage n, D.u K ρ) :=
      summable_of_sum_range_le
        (fun n => Finset.sum_nonneg fun ρ _ => hu0 ρ) hbdd
    have hb0lim : Tendsto (fun n => ∑ ρ ∈ bandSubtypeStage n, D.u K ρ)
        atTop (𝓝 0) := hbsum.tendsto_atTop_zero
    have hXTU : TendstoUniformlyOn
        (fun n s => blinkRemainder M n s) (fun _ => (0 : ℂ)) atTop K.K := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hb0lim.eventually_lt_const hε] with n hn x hx
      show dist (0 : ℂ) (blinkRemainder M n x) < ε
      rw [dist_zero_left]
      calc ‖blinkRemainder M n x‖
          ≤ ∑ ρ ∈ ((bandSubtypeStage n).image (fun ρ => ρ.1) \
              (repSubtypeStage n).image (fun ρ => ρ.1)),
              ‖zeroPoleSummand M ρ x‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ (bandSubtypeStage n).image (fun ρ => ρ.1),
              ‖zeroPoleSummand M ρ x‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
              (fun ρ _ _ => norm_nonneg _)
        _ = ∑ ρ ∈ bandSubtypeStage n, ‖zeroPoleSummand M ρ.1 x‖ :=
            Finset.sum_image (fun a _ c _ h => Subtype.coe_injective h)
        _ ≤ ∑ ρ ∈ bandSubtypeStage n, D.u K ρ :=
            Finset.sum_le_sum fun ρ _ => D.h_bound K ρ x hx
        _ < ε := hn
    have hsumTU : TendstoUniformlyOn
        (fun n s => zeroPolePartial M repBlinkExhaustion n s)
        (ZpoleRepSeries M) atTop K.K := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards
        [Metric.tendstoUniformlyOn_iff.mp hrepTU (ε / 2) (half_pos hε),
         Metric.tendstoUniformlyOn_iff.mp hXTU (ε / 2) (half_pos hε)]
        with n h1 h2 x hx
      have e1 : dist (ZpoleRepSeries M x) (repZeroPolePartial M n x) < ε / 2 :=
        h1 x hx
      have e2 : dist (0 : ℂ) (blinkRemainder M n x) < ε / 2 := h2 x hx
      rw [dist_zero_left] at e2
      show dist (ZpoleRepSeries M x)
        (zeroPolePartial M repBlinkExhaustion n x) < ε
      rw [blink_partial_decomp M n x]
      have tri := dist_triangle (ZpoleRepSeries M x)
        (repZeroPolePartial M n x)
        (repZeroPolePartial M n x + blinkRemainder M n x)
      have hd2 : dist (repZeroPolePartial M n x)
          (repZeroPolePartial M n x + blinkRemainder M n x)
          = ‖blinkRemainder M n x‖ := dist_self_add_right _ _
      linarith
    exact hsumTU.tendstoLocallyUniformlyOn

/-- Honest convergence API: zero hypotheses (envelope is unconditional). -/
def repBlinkConvergenceAPI :
    ZeroPoleLocalUniformConvergenceAPI
      defaultZeroMultiplicityData
      repBlinkExhaustion
      (ZpoleRepSeries defaultZeroMultiplicityData) where
  h_luc K :=
    repBlink_luc defaultZeroMultiplicityData unconditionalZeroPoleEnvelope K

/-- Direct rep meromorphy re-typed at the blink exhaustion (proof ignores E). -/
def repZpoleMeromorphicFromSeriesAPI_blink :
    ZpoleMeromorphicFromSeriesAPI
      defaultZeroMultiplicityData
      repBlinkExhaustion
      (ZpoleRepSeries defaultZeroMultiplicityData) where
  h_meromorphic := by
    intro _convergence _h_genuine_poles
    exact ZpoleRepSeries_meromorphicOn_Omega_direct

#print axioms repBlink_luc
#print axioms repBlinkConvergenceAPI
#print axioms repZpoleMeromorphicFromSeriesAPI_blink

end
end RHFormalization
