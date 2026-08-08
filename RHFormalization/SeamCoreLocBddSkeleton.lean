import RHFormalization.ObstructionHalfplaneBound
import RHFormalization.SeamCoreReduction
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex

/-!
# SeamCoreLocBddSkeleton — the terminal theorem's skeleton

TERMINAL: seamCore_locbdd (= hSC) ⟹ RH_of_seamCore_locbdd (certified).
This file: (1) seamCore = B_stage − compensatorM (exact); (2) the
half-plane case of hSC, unconditional; (3) THE COMPACT SPLIT: hSC in full
follows from its near-cut strip case alone. The near-cut strip estimate is
the single remaining sublemma of the project.
-/

/-- seamCore is exactly `B_stage − compensatorM`. -/
theorem seamCore_eq_Bstage_sub_compensatorM (n : ℕ) (s : ℂ) :
    seamCore n s
      = galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
        - compensatorM n s := by
  unfold seamCore
  rfl

/-- **hSC, half-plane case (unconditional)**: on compacts within
`Re s ≥ σ > 0`. -/
theorem seamCore_uniform_bound_on_halfplane
    (σ : ℝ) (hσ : 0 < σ) (K : Set ℂ) (hK : IsCompact K)
    (hKσ : ∀ s ∈ K, σ ≤ s.re) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖seamCore n s‖ ≤ C := by
  obtain ⟨CB, hCB⟩ := B_stage_uniform_bound_on_halfplane σ hσ K hKσ
  obtain ⟨CM, _, hCM⟩ := compensatorM_uniform_bound_on_halfplane σ hσ
  refine ⟨CB + CM, fun n s hs => ?_⟩
  rw [seamCore_eq_Bstage_sub_compensatorM]
  calc ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
        - compensatorM n s‖
      ≤ ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s‖
        + ‖compensatorM n s‖ := norm_sub_le _ _
    _ ≤ CB + CM := add_le_add (hCB n s hs) (hCM n s (hKσ s hs))

/-- **THE COMPACT SPLIT**: full hSC follows from the near-cut strip case.
`hNC` — the SINGLE remaining sublemma — bounds seamCore on Ω-compacts
lying in the strip `Re s ≤ 1`. -/
theorem seamCore_locbdd_of_nearcut
    (hNC : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      (∀ s ∈ K, s.re ≤ 1) →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖seamCore n s‖ ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K, ‖seamCore n s‖ ≤ C := by
  intro K hK hKΩ
  set K1 := K ∩ {s : ℂ | 1 ≤ s.re} with hK1def
  set K2 := K ∩ {s : ℂ | s.re ≤ 1} with hK2def
  have hK1c : IsCompact K1 :=
    hK.inter_right (isClosed_le continuous_const Complex.continuous_re)
  have hK2c : IsCompact K2 :=
    hK.inter_right (isClosed_le Complex.continuous_re continuous_const)
  obtain ⟨C1, h1⟩ := seamCore_uniform_bound_on_halfplane 1 one_pos K1 hK1c
    (fun s hs => hs.2)
  obtain ⟨C2, h2⟩ := hNC K2 hK2c
    (fun s hs => hKΩ hs.1) (fun s hs => hs.2)
  refine ⟨max C1 C2, fun n s hs => ?_⟩
  rcases le_total 1 s.re with hre | hre
  · exact le_trans (h1 n s ⟨hs, hre⟩) (le_max_left _ _)
  · exact le_trans (h2 n s ⟨hs, hre⟩) (le_max_right _ _)

#print axioms seamCore_eq_Bstage_sub_compensatorM
#print axioms seamCore_uniform_bound_on_halfplane
#print axioms seamCore_locbdd_of_nearcut

end

end RHFormalization
