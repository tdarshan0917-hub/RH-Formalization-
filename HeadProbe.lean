import Mathlib
import RHFormalization.DBFFAdmissibleVanishingError
import RHFormalization.DBFFO3CombinedFreeRBridge
import RHFormalization.DBFFStarObject
import RHFormalization.DBFFCompensatorHolo
open RHFormalization Complex Filter
open scoped Topology BigOperators
set_option autoImplicit false

-- G1: THE COLLAPSE. (F_free − M) − R_stage = (B_stage − M) − vanishing
example (n : ℕ) (s : ℂ) (hs : s ∈ Ω) :
    (admissibleFreeStage n s - compensatorM n s)
      - galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
    = (galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s - compensatorM n s)
      - admissibleDBFFVanishingError n s := by
  rw [admissible_R_stage_eq_core_plus_vanishing n hs]; ring

-- G2: therefore DBFFO3CombinedFreeRBound reduces to (B_stage − M) bounded
--     (since vanishing is bounded, being → 0). Prove the reduction.
example (H : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
      ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s - compensatorM n s‖ ≤ C) :
    DBFFO3CombinedFreeRBound := by
  intro K hK hKO
  obtain ⟨CB, hCB⟩ := H K hK hKO
  obtain ⟨N₀, hN₀⟩ := admissibleDBFFVanishingError_epsN K hK hKO 1 one_pos
  -- vanishing bounded: eventually ≤1, head finite. Package a uniform bound.
  sorry

-- G3: is B_stage − compensatorM ALREADY bounded on Ω-compacts (banked)?
--     = (2√)⁻¹·starObject via B_sub_compensator_eq
#check @B_sub_compensator_eq
example : True := trivial
