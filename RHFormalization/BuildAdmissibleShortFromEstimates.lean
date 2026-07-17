import RHFormalization.AppendixDKeyFormShortContract
import Mathlib

/-!
# buildDAdmissibleShortResidualData from the three Appendix-D sector estimates.

This is the deferred builder (AppendixDKeyFormShortContract.lean:9). It takes the
three manuscript Appendix-D sector estimates as premises:
  D.LOC  : ‖Q_loc (alpha n) s‖  ≤ anchor n * factor K   (density-normalized, p174)
  D.DISP : ‖Q_disp (alpha n) s‖ ≤ anchor n * factor K   (Gaussian super-poly, p175)
  D.TAIL : ‖R_tail (alpha n) s‖ ≤ anchor n * factor K   (Feynman-Kac, p179-180)
plus the decomposition R_stage = Q_loc + Q_disp + R_tail, and combines them by the
triangle inequality into ‖R_stage‖ ≤ anchor n * (3 * factor K), producing the contract.

The three sector estimates are the manuscript's PREMISES (each a proven Appendix-D bound,
factored as anchor*factor); the conclusion ‖R_stage‖≤... is DERIVED by triangle, not assumed.
-/

namespace RHFormalization
open Complex
open scoped BigOperators

/-- **The deferred builder.** Three factored sector estimates + decomposition ⇒ the contract. -/
noncomputable def buildDAdmissibleShortResidualData_from_AppendixD_estimates
    (alpha : ℕ → DFiniteStage)
    (Rstage Qloc Qdisp Rtail : DFiniteStage → ℂ → ℂ)
    (anchor : ℕ → ℝ) (factor : Set ℂ → ℝ)
    (h_anchor_nonneg : ∀ n, 0 ≤ anchor n)
    (h_anchor_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ n, anchor n ≤ A)
    (h_factor_nonneg : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → 0 ≤ factor K)
    (h_decomp : ∀ n s, Rstage (alpha n) s = Qloc (alpha n) s + Qdisp (alpha n) s + Rtail (alpha n) s)
    (h_loc_le : ∀ K, IsCompact K → K ⊆ Ω → ∀ n, ∀ s ∈ K, ‖Qloc (alpha n) s‖ ≤ anchor n * factor K)
    (h_disp_le : ∀ K, IsCompact K → K ⊆ Ω → ∀ n, ∀ s ∈ K, ‖Qdisp (alpha n) s‖ ≤ anchor n * factor K)
    (h_tail_le : ∀ K, IsCompact K → K ⊆ Ω → ∀ n, ∀ s ∈ K, ‖Rtail (alpha n) s‖ ≤ anchor n * factor K) :
    DAdmissibleShortResidualData where
  alpha := alpha
  shortResidual := Rstage
  densityAnchor := anchor
  compactFactor := fun K => 3 * factor K
  h_densityAnchor_nonneg := h_anchor_nonneg
  h_densityAnchor_bound := h_anchor_bound
  h_compactFactor_nonneg := by
    intro K hK hKΩ
    have := h_factor_nonneg K hK hKΩ
    positivity
  h_shortResidual_le := by
    intro K hK hKΩ n s hs
    rw [h_decomp n s]
    have hl := h_loc_le K hK hKΩ n s hs
    have hd := h_disp_le K hK hKΩ n s hs
    have ht := h_tail_le K hK hKΩ n s hs
    calc
      ‖Qloc (alpha n) s + Qdisp (alpha n) s + Rtail (alpha n) s‖
          ≤ ‖Qloc (alpha n) s‖ + ‖Qdisp (alpha n) s‖ + ‖Rtail (alpha n) s‖ := by
            refine le_trans (norm_add_le _ _) ?_
            gcongr
            exact norm_add_le _ _
      _ ≤ anchor n * factor K + anchor n * factor K + anchor n * factor K := by
            gcongr
      _ = anchor n * (3 * factor K) := by ring

#print axioms buildDAdmissibleShortResidualData_from_AppendixD_estimates

end RHFormalization
