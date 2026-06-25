import RHFormalization.ResolventDFHLimit
import RHFormalization.ResolventDOverlapInput
import RHFormalization.ShiftedLaplaceAbsConvMTest
import RHFormalization.CorrectedResolventPayload
import Mathlib

/-!
# h_conv core: compact-uniform residual convergence on the abs-conv region

R_stage = F_stage - B_stage converges compact-uniformly to resolventRH = resolventFH - Bshared
on the shifted-Laplace abs-conv region, assembled by Tendsto.sub at the UNIFORM level from:
* F-side: resolvent_F_stage_to_FH (compact-uniform on all Omega, banked);
* B-side: shiftedLaplace uniform convergence on the abs-conv region (banked M-test).
This is the genuine analytic core of h_conv; all-Omega is the Vitali/Montel extension.
-/

namespace RHFormalization
open Filter Topology Complex

/-- The B-side patch M-test data, if available as a hypothesis, gives compact-uniform
B convergence. We package h_conv on a region U where BOTH F and B converge uniformly. -/
theorem resolvent_R_stage_conv_on_region
    (U : Set ℂ) (hUΩ : U ⊆ Ω)
    (hBunif : ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K →
          dist (finiteCanonicalPrimePowerPackage
                  (resolventIndices (primePowerStage n)) shiftedLaplaceHeatKernelC s)
               ((shiftedLaplaceModelPackageAt 1).Bshared s) < ε) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ s : ℂ, s ∈ K →
          dist (spectralResolventPartial (primePowerStage n) s -
                  finiteCanonicalPrimePowerPackage
                    (resolventIndices (primePowerStage n)) shiftedLaplaceHeatKernelC s)
               (resolventRH s) < ε := by
  intro K hK hKU ε hε
  have hKΩ : K ⊆ Ω := hKU.trans hUΩ
  -- F-side uniform on K (banked), with ε/2
  have hF := resolvent_F_stage_to_FH K hK hKΩ (ε/2) (by linarith)
  -- B-side uniform on K (hypothesis), with ε/2
  have hB := hBunif K hK hKU (ε/2) (by linarith)
  filter_upwards [hF, hB] with n hFn hBn
  intro s hs
  have hf := hFn s hs
  have hb := hBn s hs
  -- dist of differences <= dist F + dist B
  have hsplit : dist (spectralResolventPartial (primePowerStage n) s -
        finiteCanonicalPrimePowerPackage
          (resolventIndices (primePowerStage n)) shiftedLaplaceHeatKernelC s)
        (resolventRH s)
      ≤ dist (spectralResolventPartial (primePowerStage n) s) (resolventFH s)
        + dist (finiteCanonicalPrimePowerPackage
            (resolventIndices (primePowerStage n)) shiftedLaplaceHeatKernelC s)
            ((shiftedLaplaceModelPackageAt 1).Bshared s) := by
    rw [resolventRH]
    simp only [dist_eq_norm]
    have : (spectralResolventPartial (primePowerStage n) s -
              finiteCanonicalPrimePowerPackage
                (resolventIndices (primePowerStage n)) shiftedLaplaceHeatKernelC s)
            - (resolventFH s - (shiftedLaplaceModelPackageAt 1).Bshared s)
          = (spectralResolventPartial (primePowerStage n) s - resolventFH s)
            - (finiteCanonicalPrimePowerPackage
                (resolventIndices (primePowerStage n)) shiftedLaplaceHeatKernelC s
               - (shiftedLaplaceModelPackageAt 1).Bshared s) := by ring
    rw [this]
    exact le_trans (norm_sub_le _ _) (le_refl _)
  calc dist _ (resolventRH s) ≤ _ := hsplit
    _ < ε/2 + ε/2 := by exact add_lt_add hf hb
    _ = ε := by ring

#print axioms resolvent_R_stage_conv_on_region

end RHFormalization
