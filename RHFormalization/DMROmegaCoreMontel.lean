-- SENTINEL: dmr-omegacore-montel-v1
import RHFormalization.DMRFTailOmegaBound
import RHFormalization.AscoliLocBddBridge
import Mathlib

/-! # B1: Ascoli extraction for the Ω-core — proven inputs, zero hypotheses.
The banked Montel machinery consumes step 3a's normal family. First
extraction in the project fed by theorems instead of assumptions. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/-- The Ω-core family. -/
noncomputable def galOmegaCore (n : ℕ) (s : ℂ) : ℂ :=
  galHead n s + galFTailClosed n s

/-- Per-stage Ω-holomorphy of the core. -/
theorem galOmegaCore_holo (n : ℕ) : HolomorphicOnC (galOmegaCore n) Ω := by
  intro z hz
  have h1 := galHead_holo n z hz
  have h2 := galFTailClosed_holo n z hz
  first
    | exact h1.add h2
    | (unfold galOmegaCore; exact h1.add h2)
    | (show AnalyticWithinAt ℂ (fun s => galHead n s + galFTailClosed n s) Ω z
       exact h1.add h2)

/-- Loc-bdd in the exact shape the Ascoli bridge consumes (empty K trivial). -/
theorem galOmegaCore_loc_bdd :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖galOmegaCore n s‖ ≤ C := by
  intro K hK hKO
  rcases K.eq_empty_or_nonempty with hemp | hne
  · exact ⟨1, by simp [hemp]⟩
  · obtain ⟨C, _, hC⟩ := galOmegaCore_uniform_bound K hK hKO hne
    exact ⟨C, fun n s hs => hC n s hs⟩

/-- **B1: THE PROVEN-INPUT ASCOLI EXTRACTION.** -/
theorem galOmegaCore_ascoli : AscoliExtraction galOmegaCore :=
  ascoliExtraction_of_loc_bdd galOmegaCore galOmegaCore_loc_bdd

#print axioms galOmegaCore_holo
#print axioms galOmegaCore_loc_bdd
#print axioms galOmegaCore_ascoli

end

end RHFormalization
