import RHFormalization.AdaptivePrimeSplitIdentity
import RHFormalization.DBFFO3HstarFromCompensatedB
import Mathlib

/-!
# AdaptiveFMRBridge — compensated-B bound from the adaptive net

The adaptive FMR identity: on Ω,
  `B − M = (adaptiveFree − M) + adaptiveShortResidual − R_stage(adaptive)`,
using `B_stage(adaptive) = B_stage(admissible)` (rfl) so the LEFT side is
the SAME `DBFFO3CompensatedB` the banked O3 layer consumes.

Consequence: compact-uniform bounds on the three adaptive pieces give
`DBFFO3CompensatedBBound` — closing step 8 of the adaptive route, with the
existing `DBFFO3Hstar_from_compensatedB_bound` closure downstream.

The three hypotheses are the remaining analytic frontier:
  * adaptive Hfree  (free minus compensator at the adaptive window),
  * adaptive Hshort (first-order window + D.LOC all-orders second residual,
    consuming `adaptiveGalerkinStage_DADM`),
  * adaptive HR     (residual stage bound).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology BigOperators

/-- **Adaptive FMR identity**: on Ω,
`compensatedB = (adaptiveFree − M) + adaptiveShort − R_stage(adaptive)`. -/
theorem adaptive_compensatedB_eq_FMR
    (c : ℝ) (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    DBFFO3CompensatedB n s =
      (adaptiveFreeStage c n s - compensatorM n s)
        + adaptiveShortResidual c n s
        - galerkinStagePackage.R_stage (adaptiveGalerkinStageSeq c n) s := by
  have hR :
      galerkinStagePackage.R_stage (adaptiveGalerkinStageSeq c n) s =
        galerkinStagePackage.F_stage (adaptiveGalerkinStageSeq c n) s
          - galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s := by
    rfl
  have hF := adaptive_package_F_stage_eq_free_add_prime c n s
  have hP := adaptiveFadmPrimeStage_eq_shortResidual c n hs
  rw [← adaptive_compensatedB_eq c n s]
  rw [hR, hF, hP]
  ring

/-- **Adaptive FMR boundedness bridge**: compact-uniform bounds on the three
adaptive pieces give the compensated-B bound the O3 layer consumes. -/
theorem adaptive_compensatedB_bounded_from_FMR
    (c : ℝ)
    (HfreeA :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cfree : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖adaptiveFreeStage c n s - compensatorM n s‖ ≤ Cfree)
    (HshortA :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cshort : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖adaptiveShortResidual c n s‖ ≤ Cshort)
    (HRA :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ CR : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖galerkinStagePackage.R_stage (adaptiveGalerkinStageSeq c n) s‖ ≤ CR) :
    DBFFO3CompensatedBBound := by
  intro K hK hKO
  obtain ⟨Cfree, hfree⟩ := HfreeA K hK hKO
  obtain ⟨Cshort, hshort⟩ := HshortA K hK hKO
  obtain ⟨CR, hR⟩ := HRA K hK hKO
  refine ⟨Cfree + Cshort + CR, ?_⟩
  intro n s hs
  let A : ℂ := adaptiveFreeStage c n s - compensatorM n s
  let B : ℂ := adaptiveShortResidual c n s
  let C : ℂ := galerkinStagePackage.R_stage (adaptiveGalerkinStageSeq c n) s
  have hEq : DBFFO3CompensatedB n s = A + B - C := by
    simpa [A, B, C] using
      adaptive_compensatedB_eq_FMR c n (s := s) (hKO hs)
  have hA : ‖A‖ ≤ Cfree := by simpa [A] using hfree n s hs
  have hB : ‖B‖ ≤ Cshort := by simpa [B] using hshort n s hs
  have hC : ‖C‖ ≤ CR := by simpa [C] using hR n s hs
  calc
    ‖DBFFO3CompensatedB n s‖
        = ‖A + B - C‖ := by rw [hEq]
    _ ≤ ‖A + B‖ + ‖C‖ := by simpa using norm_sub_le (A + B) C
    _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := add_le_add (norm_add_le A B) le_rfl
    _ ≤ (Cfree + Cshort) + CR := add_le_add (add_le_add hA hB) hC
    _ = Cfree + Cshort + CR := by ring

#print axioms adaptive_compensatedB_eq_FMR
#print axioms adaptive_compensatedB_bounded_from_FMR

end

end RHFormalization
