import RHFormalization.CanonicalPackageTailLimit
import RHFormalization.DMROverlapLedger
import RHFormalization.AdmissibleRStageOverlapLimit
import RHFormalization.GalerkinSpikeShortTimeCalculus

/-!
# GalOmegaCoreOverlapLimit — the core's overlap limit; Bcan CANCELS

ROUTE CARD
1. Target: on RHP(1), galOmegaCore n → FHadmFree − shortPackageLimit
   spikeT0. Proof: ledger core = R_stage + tail (banked), R_stage →
   FHadmFree − Bcan (banked), tail → Bcan − shortLimit (banked): the
   arithmetic Bcan cancels in the sum.
2. Consumer: the core-Montel convergence theorem (all inputs banked).
3. Raw B on Ω? NO — the limit object is arithmetic-free.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- The core's overlap limit: free minus short — NO arithmetic object. -/
def galOmegaCoreLimit (s : ℂ) : ℂ :=
  FHadmFree s - shortPackageLimit spikeT0 s

/-- **The core's overlap limit on RHP(1)**: Bcan cancels between the
residual limit and the tail limit. -/
theorem galOmegaCore_overlap_limit
    (s : ℂ) (hs : s ∈ RightHalfPlane (1 : ℝ)) :
    Tendsto (fun n : ℕ => galOmegaCore n s)
      Filter.atTop (𝓝 (galOmegaCoreLimit s)) := by
  have hsre : 0 < s.re := by
    have h1 : (1:ℝ) < s.re := hs
    linarith
  have hcore_eq : ∀ n : ℕ, galOmegaCore n s
      = galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
        + canonicalPackageTail (activePrimePowerPairsCenterBelow (admR n))
            spikeT0 s :=
    fun n => core_eq_R_stage_add_packageTail n s hsre
  have hR := admissible_R_stage_overlap_limit s hs
  have hT := canonicalPackageTail_tendsto spikeT0 spikeT0_pos s hs
  have hsum := hR.add hT
  have hlim : admissibleRHcand s
      + (galerkinBcanLimitData.Bcan s - shortPackageLimit spikeT0 s)
      = galOmegaCoreLimit s := by
    unfold admissibleRHcand galOmegaCoreLimit
    ring
  rw [← hlim]
  refine hsum.congr ?_
  intro n
  exact (hcore_eq n).symm

#print axioms galOmegaCore_overlap_limit

end

end RHFormalization
