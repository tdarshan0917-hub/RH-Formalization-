import RHFormalization.ShiftedLaplaceFiniteOperatorLayerSigma1
import RHFormalization.ShiftedLaplaceModelPackageProbe
import RHFormalization.ShiftedLaplaceSqrtReLowerBound
import RHFormalization.SummableSupportExhaustion
import RHFormalization.ShiftedLaplacePatchMTest
import RHFormalization.ShiftedLaplaceBridge
import RHFormalization.ShiftedLaplaceDSharedBridge
import RHFormalization.CanonicalPrimePowerExhaustion
import RHFormalization.PrimePowerDFiniteStage
import RHFormalization.AppendixDPrimePowerPairCode
import RHFormalization.ConcretePrimePowerEnumeration
import Mathlib

namespace RHFormalization
noncomputable section
open Complex Set Topology Filter

/-- Summability of the prime-power family at `s` in the abs-conv region. -/
theorem shiftedLaplace_family_summable {s : ℂ}
    (hs : s ∈ shiftedLaplaceAbsConvRegion) :
    Summable (fun q : PrimePowerPair => q.weightC * shiftedLaplaceHeatKernelC q.center s) := by
  have hpiece : (1:ℝ) < (Complex.sqrt (s + (1/4:ℂ)) + (1/2:ℂ)).re :=
    (absConvRegion_eq_piece2 s).mp hs
  set σ : ℝ := (Complex.sqrt (s + (1/4:ℂ))).re with hσdef
  have hσ_gt : (1:ℝ)/2 < σ := by
    have h12 : ((1/2:ℂ)).re = (1/2:ℝ) := by norm_num
    rw [Complex.add_re, h12] at hpiece
    rw [hσdef]; linarith
  have hmem : s ∈ patchAt σ := by
    show σ ≤ (Complex.sqrt (s + (1/4:ℂ))).re
    rw [hσdef]
  refine Summable.of_norm_bounded (patchMajorant_summable σ hσ_gt) ?_
  intro q
  -- (patchMTestData σ hσ_gt).u = patchMajorant σ by rfl; bridge the bound.
  have hb : ‖q.weightC * shiftedLaplaceHeatKernelC q.center s‖ ≤ (patchMTestData σ hσ_gt).u q :=
    (patchMTestData σ hσ_gt).h_bound q s hmem
  exact hb

/-- The stage index image equals the concrete prime-power enumeration below cutoff. -/
theorem ppIndices_primePowerStage_eq (n : ℕ) :
    (designedSpikeWitness.activeIndices (primePowerStage n)).image
        (designedSpikeWitness.toPP (primePowerStage n))
      = concretePrimePowerBelowCutoff ((n : ℝ) + 1) := by
  -- activeIndices(primePowerStage n) = ppStageCodes n = (below).image ppCode
  -- toPP(primePowerStage n) = ppDecode
  -- image of image, ppDecode ∘ ppCode = id
  show (ppStageCodes n).image ppDecode = concretePrimePowerBelowCutoff ((n:ℝ)+1)
  rw [ppStageCodes, Finset.image_image]
  rw [show (ppDecode ∘ ppCode) = id from funext (fun q => ppDecode_ppCode q)]
  rw [Finset.image_id]

/-- The shifted-Laplace finite-canonical exhaustion data at σ = 1. -/
def shiftedLaplaceModelExhaustionSigma1 :
    CanonicalPrimePowerExhaustionData
      shiftedLaplaceFiniteOperatorLayerSigma1
      (shiftedLaplaceModelPackageAt 1) where
  alpha := primePowerStage
  h_Cshared_sigma_le := by
    show (shiftedLaplaceModelPackageAt 1).sigma0 ≤
      shiftedLaplaceFiniteOperatorLayerSigma1.toStagePackage.sigma0
    have h1 : (shiftedLaplaceModelPackageAt 1).sigma0 = 1 := rfl
    have h2 : shiftedLaplaceFiniteOperatorLayerSigma1.toStagePackage.sigma0 = 1 := rfl
    rw [h1, h2]
  h_tendsto := by
    intro s hs
    have hs1 : s ∈ RightHalfPlane (1:ℝ) := hs
    have hsabs : s ∈ shiftedLaplaceAbsConvRegion :=
      rightHalfPlane_one_subset_shiftedLaplaceAbsConvRegion hs1
    -- the summable family and its tsum = model
    have hsumm := shiftedLaplace_family_summable hsabs
    -- cover: nonzero weight ⟹ valid ⟹ eventually in the stage image
    have hcover : ∀ q : PrimePowerPair,
        (q.weightC * shiftedLaplaceHeatKernelC q.center s) ≠ 0 →
        ∀ᶠ n in atTop, q ∈ (designedSpikeWitness.activeIndices (primePowerStage n)).image
          (designedSpikeWitness.toPP (primePowerStage n)) := by
      intro q hqne
      have hvalid : IsPrimePowerPair q := by
        by_contra hbad
        apply hqne
        have hw0 : q.weightReal = 0 := by simp [PrimePowerPair.weightReal, hbad]
        simp [PrimePowerPair.weightC, hw0]
      -- eventually n+1 ≥ q.center
      have hev : ∀ᶠ n : ℕ in atTop, q.center ≤ (n:ℝ) + 1 := by
        filter_upwards [eventually_ge_atTop ⌈q.center⌉₊] with n hn
        have : q.center ≤ (⌈q.center⌉₊ : ℝ) := Nat.le_ceil _
        have hcast : ((⌈q.center⌉₊ : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        linarith
      filter_upwards [hev] with n hn
      rw [ppIndices_primePowerStage_eq]
      exact concretePrimePowerEnum.h_mem_belowCutoff ((n:ℝ)+1) q hvalid hn
    -- apply the convergence engine
    have hconv := tendsto_sum_of_eventually_covers_support hsumm hcover
    -- match: the finite sum is finiteCanonicalPrimePowerPackage; tsum = model
    have htsum_model :
        (∑' q : PrimePowerPair, q.weightC * shiftedLaplaceHeatKernelC q.center s)
          = (shiftedLaplaceModelPackageAt 1).Bshared s := by
      rw [← shiftedLaplacePrimePackageAt_Bshared_eq_tsum 1 s]
      show (shiftedLaplacePrimePackageAt 1).Bshared s = shiftedLaplaceLogDerivModel s
      exact shiftedLaplace_Bshared_eqOn_model 1 hsabs
    rw [htsum_model] at hconv
    -- the obligation's summand is finiteCanonicalPrimePowerPackage indices kernel s
    -- which is definitionally ∑_{q ∈ indices} weightC q * kernel q.center s
    convert hconv using 2 with n

end
end RHFormalization

namespace RHFormalization
noncomputable section

/-- D-side finite-canonical limit data for the σ=1 shifted-Laplace layer,
in the form consumed by the D operator construction. -/
def shiftedLaplaceModelFiniteCanonicalLimitSigma1 :
    DOperatorFiniteCanonicalLimitAtOverlapData
      shiftedLaplaceFiniteOperatorLayerSigma1
      (shiftedLaplaceModelPackageAt 1) :=
  shiftedLaplaceModelExhaustionSigma1.toDOperatorFiniteCanonicalLimit

#print axioms shiftedLaplaceModelExhaustionSigma1
#print axioms shiftedLaplaceModelFiniteCanonicalLimitSigma1

end
end RHFormalization
