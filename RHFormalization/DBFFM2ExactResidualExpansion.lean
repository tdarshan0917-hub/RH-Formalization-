import RHFormalization.SpikeSumPrimeReindex
import RHFormalization.PrimeSpikeProfileSplit
import RHFormalization.DBFFDecodedProfilesLoc
import RHFormalization.AdmissibleGalerkinStage
import Mathlib

/-!
# DBFFM2ExactResidualExpansion — Phase 1: the exact stage F-slot expansion

ROUTE CARD
1. Target: EXACT identity at the admissible stage, `Re(s + SupVConst) > 0`,
   nonneg perturbed spectrum as explicit hypothesis (no bare-Prop
   discharge; shift-spec route to remove it queued):
   `F_stage(stage n)(s) = (1/(2L_n)) · [ FstageFinite(free)(s+SupV)
      − Σ_{k ∈ codes(admR n)} w(k)·(density − osc + err)(k)(s+SupV)
      + spikeE2Transform(s+SupV) ]`
   — every sign, the 1/(2L) constant, the SupVConst shift, and Nat-code
   indexing pinned. NO estimates; frozen target for Priority-2
   continuum match.
2. Raw B on Ω? NO. B−M bare Prop? NO — composition of banked exact
   identities. Ω-extension deferred (identity theorem later, per audit);
   honest Re > 0 domain.
3. Consumer: PrimeSpikeContinuumMatch (Priority 2) + provider h_expansion.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

/-- **Phase 1: the exact expanded stage F-slot** (Re-shifted half-plane). -/
theorem stage_F_slot_M2_expansion (n : ℕ) (s : ℂ)
    (hs : 0 < (s + (SupVConst : ℂ)).re)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues
        (galerkinFreeMu (admN n) (admL n))
        (galerkinVC_isHermitian (N := admN n) 1
          (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n)) i) :
    galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
      = admDensityC n *
          (FstageFinite (fun m : Fin (admN n) =>
              galerkinLam (admL n) (m : ℕ)) (s + (SupVConst : ℂ))
            - (∑ k ∈ activePrimePowerCodesCenterBelow (admR n),
                ((ppWeightReal k : ℝ) : ℂ) *
                  (primeSpikeDensityPart (N := admN n) (admL n)
                      (s + (SupVConst : ℂ))
                    - primeSpikeOscPart (N := admN n) 1 k (admL n)
                        (s + (SupVConst : ℂ))
                    + primeSpikeErrPart (N := admN n) 1 k (admL n)
                        (s + (SupVConst : ℂ))))
            + spikeE2Transform (N := admN n) 1
                (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal
                (admL n) (s + (SupVConst : ℂ))) := by
  rw [galerkinStagePackage_F_at_admissible]
  congr 1
  unfold galerkinPerturbedFStage
  rw [perturbedFStage_M2_split_prime 1
      (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n)
      (s + (SupVConst : ℂ)) hs hpos
      (fun m => by
        unfold galerkinLam
        positivity)]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [primeSpikeResolventSq_eq_split 1 one_pos k (admL n) (s + (SupVConst : ℂ))]

#print axioms stage_F_slot_M2_expansion

end

end RHFormalization
