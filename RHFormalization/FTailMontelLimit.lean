import RHFormalization.DMRFTailOmegaBound
import RHFormalization.AscoliLocBddBridge
import RHFormalization.GalOmegaCoreCompactUniform

/-!
# FTailMontelLimit — N2: the operator tail limit T exists on Ω

ROUTE CARD
1. Target: extract T ∈ O(Ω) with galFTailClosed (ψ n) → T compact-uniformly
   on Ω, from the BANKED holo + Ω-uniform bound. Subsequential is enough:
   the endgame identity (N3) pins any such T on the overlap.
2. Consumer: N3 — THE FINAL TARGET (see FinalTargetSignature file).
3. Raw B on Ω? NO.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Topology Filter

/-- **N2: the operator-tail Montel limit.** -/
theorem galFTail_montel_limit :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ T : ℂ → ℂ, HolomorphicOnC T Ω ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in Filter.atTop,
            ∀ s : ℂ, s ∈ K → dist (galFTailClosed (ψ n) s) (T s) < ε := by
  have h_holo : ∀ n, HolomorphicOnC (galFTailClosed n) Ω :=
    fun n => galFTailClosed_holo n
  have h_bdd : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n, ∀ s ∈ K, ‖galFTailClosed n s‖ ≤ C := by
    intro K hK hKO
    rcases K.eq_empty_or_nonempty with hemp | hne
    · exact ⟨1, by simp [hemp]⟩
    · obtain ⟨C, _, hC⟩ := galFTailClosed_omega_uniform_bound K hK hKO hne
      exact ⟨C, hC⟩
  have hAsc : AscoliExtraction galFTailClosed :=
    ascoliExtraction_of_loc_bdd galFTailClosed h_bdd
  obtain ⟨ψ, hψ, T, hT_holo, hT_conv⟩ :=
    hAsc h_holo h_bdd id strictMono_id
  refine ⟨ψ, hψ, T, hT_holo, ?_⟩
  intro K hK hKO ε hε
  have := hT_conv K hK hKO ε hε
  simpa using this

#print axioms galFTail_montel_limit

end

end RHFormalization
