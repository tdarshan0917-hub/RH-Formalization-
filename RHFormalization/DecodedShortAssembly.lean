-- SENTINEL: decoded-short-assembly-v2
import RHFormalization.DecodedFirstOrderVanish
import RHFormalization.DecodedResidualUniform
import Mathlib

/-!
# hShort CLOSED

`decodedAdaptiveShortResidual = FOW + O2res` (definitional), so the
triangle inequality against the two banked uniform bounds
(`decodedFirstOrderWindow_uniform_bound`, decay `C/(n+2)` dominated by `C`;
`decodedSecondResolventResidual_uniform_bound`, flat `C₀³·146`) delivers
the exact hypothesis shape `RH_from_decoded_combined_and_short` consumes
in its hShort slot.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/-- **hShort (DONE).** Uniform boundedness of the decoded short residual
on every Ω-compact — the second input of the live endpoint. -/
theorem decoded_hShort (c : ℝ) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C2 : ℝ, ∀ n, ∀ s ∈ K,
        ‖decodedAdaptiveShortResidual c n s‖ ≤ C2 := by
  intro K hK hKO
  obtain ⟨Cf, hCfpos, hCf⟩ := decodedFirstOrderWindow_uniform_bound c K hK hKO
  obtain ⟨Co, hCopos, hCo⟩ :=
    decodedSecondResolventResidual_uniform_bound c K hK hKO
  refine ⟨Cf + Co, fun n s hs => ?_⟩
  have hfow : ‖decodedAdaptiveFirstOrderWindow c n s‖ ≤ Cf := by
    refine le_trans (hCf n s hs) ?_
    have h1 : (1:ℝ) ≤ (n:ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    calc Cf / ((n:ℝ) + 2) ≤ Cf / 1 := by
          apply div_le_div_of_nonneg_left hCfpos.le ?_ h1 <;> norm_num
      _ = Cf := div_one Cf
  have ho2 : ‖decodedAdaptiveSecondResolventResidual c n s‖ ≤ Co :=
    hCo n s hs
  calc ‖decodedAdaptiveShortResidual c n s‖
      = ‖decodedAdaptiveFirstOrderWindow c n s
          + decodedAdaptiveSecondResolventResidual c n s‖ := by
        unfold decodedAdaptiveShortResidual
        rfl
      _ ≤ ‖decodedAdaptiveFirstOrderWindow c n s‖
          + ‖decodedAdaptiveSecondResolventResidual c n s‖ := norm_add_le _ _
      _ ≤ Cf + Co := add_le_add hfow ho2

#print axioms decoded_hShort

end

end RHFormalization
