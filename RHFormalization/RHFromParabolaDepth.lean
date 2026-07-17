-- SENTINEL: rh-from-parabola-depth-v1
import RHFormalization.CompensatedBDecisiveEndpoint
import RHFormalization.DBFFO3ParabolaDepthReduction
import RHFormalization.GalerkinCanonicalResidualBound
import Mathlib

/-!
# RH FROM PARABOLA-DEPTH HSTAR — the narrowest frontier
Chain (everything banked): Hpar ⟹ DBFFO3Hstar (off-parabola banked +
reduction banked) ⟹ ‖B − M‖ ≤ C on Ω-compacts (kernel prefactor via
kernelDenom_min) ⟹ RH_from_compensatedB_locbdd ⟹ RiemannHypothesis.
Remaining obligation after this file: DBFFO3ParabolaDepthHstar ONLY —
the star bound on compacts reaching parabola depth (D.TAIL-DENSITY /
D.UNIFORM-CAN). Off-parabola: DONE.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology

/-- **RiemannHypothesis from the parabola-depth star bound alone.** -/
theorem RH_from_parabola_depth_hstar
    (Hpar : DBFFO3ParabolaDepthHstar) : RiemannHypothesis := by
  apply RH_from_compensatedB_locbdd
  intro K hK hKΩ
  obtain ⟨c, hc, hcK⟩ := kernelDenom_min K hK hKΩ
  obtain ⟨C, hC⟩ :=
    DBFFO3_compensated_B_bounded_from_parabola_depth Hpar K hK hKΩ c hc
      (fun s hs => by
        rw [one_div, norm_inv]
        exact inv_anti₀ hc (hcK s hs))
  refine ⟨C, fun n s hs => ?_⟩
  first
    | exact hC n s hs
    | (show ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
          - compensatorM n s‖ ≤ C
       exact hC n s hs)
    | (unfold compensatedBFamily; exact hC n s hs)

#print axioms RH_from_parabola_depth_hstar

end

end RHFormalization
