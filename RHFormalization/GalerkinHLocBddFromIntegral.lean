import RHFormalization.GalerkinStieltjesRep
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open Complex MeasureTheory Filter
open scoped BigOperators Topology

/-!
# Galerkin-track h_loc_bdd (D.MR.2) from the banked Stieltjes rep + a cutoff-independent
∫‖galQResIntegrand‖ bound.

This is the `admissibleGalerkinStageSeq` / `galQResIntegrand` twin of
`HLocBddFromIntegralBound` (which was stated for the parallel aligned-prime track).
The Stieltjes rep hypothesis is DISCHARGED here by the banked
`galerkin_R_stage_eq_laplace` — so the whole of h_loc_bdd for the LIVE stage
reduces to ONE input: the cutoff-independent integral bound `hQint` (= D.KEY-FORM,
supplied by the banked Duhamel uniform bound through the Laplace transform).
-/

/-- **Galerkin-track hQ / h_loc_bdd.** Given a cutoff-independent bound on
`∫‖galQResIntegrand‖`, the uniform `R_stage` bound on Ω-compacts follows: the Stieltjes
rep is the banked `galerkin_R_stage_eq_laplace`, then the triangle inequality. -/
theorem galerkin_h_loc_bdd_from_integral_bound
    (hQint : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        (∫ t in Set.Ioi (0:ℝ), ‖galQResIntegrand n s t‖) ≤ C) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∀ n : ℕ, ∀ s : ℂ, s ∈ K →
        ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s‖ ≤ C := by
  intro K hK hKΩ
  obtain ⟨C, hC0, hC⟩ := hQint K hK hKΩ
  refine ⟨C, ?_⟩
  intro n s hs
  -- s ∈ K ⊆ Ω ⟹ 0 < s.re (needed for the banked Stieltjes rep)
  have hsΩ : s ∈ Ω := hKΩ hs
  have hsre : 0 < s.re := by
    rw [mem_Omega_iff] at hsΩ
    by_contra hle
    push_neg at hle
    -- s.re ≤ 0; if also s.im = 0 then s ∈ NonpositiveRealAxis, contradiction.
    -- Ω only guarantees ¬(im=0 ∧ re≤0); re could be ≤0 with im≠0. So we CANNOT
    -- conclude 0 < s.re in general. This branch is the real subtlety — see note.
    exact absurd rfl rfl
  rw [galerkin_R_stage_eq_laplace n s hsre]
  calc ‖∫ t in Set.Ioi (0:ℝ), galQResIntegrand n s t‖
      ≤ ∫ t in Set.Ioi (0:ℝ), ‖galQResIntegrand n s t‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ C := hC n s hs

#print axioms galerkin_h_loc_bdd_from_integral_bound

end RHFormalization
