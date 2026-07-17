import RHFormalization.AdaptiveFMRBridge
import Mathlib

/-!
# AdaptiveCombinedFreeR — the corrected combined object

`compensatorM` carries the growing arithmetic main term while the free stage
tends to a fixed limit, so `‖free − M‖` alone is NOT compact-bounded in the
depth region. The manuscript's cancellation lives in the COMBINED object

  `adaptiveCombinedFreeR = (adaptiveFree − M) − R_stage(adaptive)`,

which by the banked FMR identity equals `CompensatedB − ShortResidual`
(`adaptiveCombinedFreeR_eq`). The analytic target is a direct sector bound
(D.LOC/D.DISP/D.TAIL, consuming the D.ADM certificate) on this combined
object — NOT separate bounds on its two divergent-in-isolation pieces.

Also recorded: combined bound + short bound ⇒ `DBFFO3CompensatedBBound`
(pure triangle inequality), landing on the O3 layer's exact Prop.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Filter
open scoped Topology BigOperators

/-- The adaptive corrected combined object: `(free − M) − R`. -/
def adaptiveCombinedFreeR (c : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  (adaptiveFreeStage c n s - compensatorM n s)
    - galerkinStagePackage.R_stage (adaptiveGalerkinStageSeq c n) s

/-- **Exact rewrite**: on Ω, `combined = CompensatedB − ShortResidual`.
Bookkeeping only — the analytic content is the sector bound on the left. -/
theorem adaptiveCombinedFreeR_eq
    (c : ℝ) (n : ℕ) {s : ℂ} (hs : s ∈ Ω) :
    adaptiveCombinedFreeR c n s
      = DBFFO3CompensatedB n s - adaptiveShortResidual c n s := by
  unfold adaptiveCombinedFreeR
  rw [adaptive_compensatedB_eq_FMR c n hs]
  ring

/-- **Combined route to the O3 input**: compact-uniform bounds on the
combined object and the short residual give `DBFFO3CompensatedBBound`. -/
theorem adaptive_compensatedB_bounded_from_combined
    (c : ℝ)
    (Hcomb :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cc : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖adaptiveCombinedFreeR c n s‖ ≤ Cc)
    (HshortA :
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∃ Cs : ℝ,
          ∀ n : ℕ, ∀ s ∈ K,
            ‖adaptiveShortResidual c n s‖ ≤ Cs) :
    DBFFO3CompensatedBBound := by
  intro K hK hKO
  obtain ⟨Cc, hc⟩ := Hcomb K hK hKO
  obtain ⟨Cs, hsB⟩ := HshortA K hK hKO
  refine ⟨Cc + Cs, ?_⟩
  intro n s hs
  have hEq : DBFFO3CompensatedB n s
      = adaptiveCombinedFreeR c n s + adaptiveShortResidual c n s := by
    rw [adaptiveCombinedFreeR_eq c n (hKO hs)]
    ring
  calc ‖DBFFO3CompensatedB n s‖
      = ‖adaptiveCombinedFreeR c n s + adaptiveShortResidual c n s‖ := by
        rw [hEq]
    _ ≤ ‖adaptiveCombinedFreeR c n s‖ + ‖adaptiveShortResidual c n s‖ :=
        norm_add_le _ _
    _ ≤ Cc + Cs := add_le_add (hc n s hs) (hsB n s hs)

#print axioms adaptiveCombinedFreeR_eq
#print axioms adaptive_compensatedB_bounded_from_combined

end

end RHFormalization
