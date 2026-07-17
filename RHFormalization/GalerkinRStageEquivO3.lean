import RHFormalization.GalerkinFStageUniformBound
import RHFormalization.GalerkinStagePackage
import RHFormalization.DBFFO3ParabolaDepthReduction
import Mathlib

/-!
# GalerkinRStageEquivO3 — `R_stage` bounded ⟺ `B_stage` bounded

ROUTE CARD
1. Target: on every Ω-compact, `R_stage` is `n`-uniformly bounded iff `B_stage` is.
2. Objects: `F_stage_uniform_bound_on_compacts` (banked), and the DEFINITIONAL
   identity `R_stage = F_stage − B_stage` (`rfl`, verified).
3. Raw B on Ω? The statement mentions it, but assumes nothing about it.
4. R = F − raw B? YES — and that is the whole point.
5. True outright.
6. Manuscript: none. This is a fact about the LEAN package, not about `R^can`.
7. Consumer: an audit gate.

## WHY THIS FILE EXISTS

`DBFFO3ParabolaDepthHstar_from_free_and_R`, `DBFFO3Hstar_from_free_and_R`, and
`DBFFO3_compensatedB_bound_from_free_and_R` each take

    HR : ∀ K compact ⊆ Ω, ∃ CR, ∀ n, ∀ s ∈ K, ‖R_stage n s‖ ≤ CR

and conclude a form of O3. This file proves `HR` is EQUIVALENT to `B_stage`
bounded, hence (via `B_sub_compensator_eq` + `DBFFO3_sqrtFactorBound`) equivalent
to O3 itself modulo the compensator. Those three theorems therefore derive O3
from O3. They are green, axiom-clean, and prove nothing.

    MARK: DBFFO3ParabolaDepthHstar_from_free_and_R  — VACUOUS-BY-AUDIT (HR ⟺ O3)
    MARK: DBFFO3Hstar_from_free_and_R               — VACUOUS-BY-AUDIT (HR ⟺ O3)
    MARK: DBFFO3_compensatedB_bound_from_free_and_R — VACUOUS-BY-AUDIT (HR ⟺ O3)

Do not consume them. Do not write another `_from_X` reduction whose hypothesis is
`R_stage` bounded, `B_stage` bounded, `starObject` bounded, or the B-tail bounded.
All four are the same proposition.
-/

set_option autoImplicit false

namespace RHFormalization

open Complex

/-- `R_stage = F_stage − B_stage`, definitionally, at the admissible stage. -/
theorem galerkin_R_stage_eq_F_sub_B (n : ℕ) (s : ℂ) :
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
      = galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
        - galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s := rfl

/-- **THE AUDIT GATE.** On Ω-compacts, `R_stage` is `n`-uniformly bounded iff
`B_stage` is. Consequence: any theorem deriving O3 from `HR` is circular. -/
theorem R_stage_bounded_iff_B_stage_bounded
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    (∃ CR : ℝ, ∀ (n : ℕ), ∀ s ∈ K,
        ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s‖ ≤ CR)
      ↔ (∃ CB : ℝ, ∀ (n : ℕ), ∀ s ∈ K,
        ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s‖ ≤ CB) := by
  obtain ⟨CF, hCF0, hF⟩ := F_stage_uniform_bound_on_compacts K hK hKΩ
  constructor
  · rintro ⟨CR, hR⟩
    refine ⟨CF + CR, fun n s hs => ?_⟩
    have hsplit : galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
        = galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          - galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s := by
      rw [galerkin_R_stage_eq_F_sub_B]; ring
    rw [hsplit]
    exact le_trans (norm_sub_le _ _) (add_le_add (hF n s hs) (hR n s hs))
  · rintro ⟨CB, hB⟩
    refine ⟨CF + CB, fun n s hs => ?_⟩
    rw [galerkin_R_stage_eq_F_sub_B]
    exact le_trans (norm_sub_le _ _) (add_le_add (hF n s hs) (hB n s hs))

#print axioms galerkin_R_stage_eq_F_sub_B
#print axioms R_stage_bounded_iff_B_stage_bounded

end RHFormalization
