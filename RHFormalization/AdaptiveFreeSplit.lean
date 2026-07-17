import RHFormalization.AdaptiveGalerkinStage
import RHFormalization.AdmissibleFreeRiemannSum
import RHFormalization.DBFFO3FMRBridge
import Mathlib

/-!
# AdaptiveFreeSplit — free/prime layer split on the adaptive net

Mirrors `admissibleFreeStage` / `FadmPrimeStage` /
`package_F_stage_eq_free_add_prime` at the adaptive parameters
`(adaptiveN c n, adaptiveL c n)`. The compensator `compensatorM` is a
cutoff-only object and is NOT redefined; the free-minus-compensator
geometry (adaptive Hfree) will pair `adaptiveFreeStage` with the same
`compensatorM n`.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/-- **The adaptive free stage**: density-normalized free Dirichlet resolvent
sum at the adaptive window and dimension (same `s + SupVConst` shift). -/
def adaptiveFreeStage (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  adaptiveDensityC c n *
    ∑ i : Fin (adaptiveN c n),
      (s + ((SupVConst + galerkinFreeMu (adaptiveN c n) (adaptiveL c n) i : ℝ) : ℂ))⁻¹

/-- The adaptive prime layer: everything in the adaptive F-stage beyond the
free density-normalized part. -/
def adaptiveFadmPrimeStage (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  galerkinStagePackage.F_stage (adaptiveGalerkinStageSeq c n) s
    - adaptiveFreeStage c n s

/-- **Exact layer split of the adaptive F-slot**: `F = free + prime`. -/
theorem adaptive_package_F_stage_eq_free_add_prime
    (c : ℝ) (n : ℕ) (s : ℂ) :
    galerkinStagePackage.F_stage (adaptiveGalerkinStageSeq c n) s
      = adaptiveFreeStage c n s + adaptiveFadmPrimeStage c n s := by
  unfold adaptiveFadmPrimeStage
  ring

/-- The adaptive compensated-B object EQUALS the admissible one — B-stage
reads only the shared cutoff, and the compensator is cutoff-only. Recorded
here so the FMR bridge on the adaptive net lands on the SAME
`DBFFO3CompensatedB` the O3 layer already consumes. -/
theorem adaptive_compensatedB_eq (c : ℝ) (n : ℕ) (s : ℂ) :
    galerkinStagePackage.B_stage (adaptiveGalerkinStageSeq c n) s
        - compensatorM n s
      = DBFFO3CompensatedB n s := rfl

#print axioms adaptiveFreeStage
#print axioms adaptive_package_F_stage_eq_free_add_prime
#print axioms adaptive_compensatedB_eq

end

end RHFormalization
