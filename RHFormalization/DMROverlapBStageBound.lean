-- SENTINEL: dmr-overlap-bstage-bound-v2
import RHFormalization.DBFFStarDirichletOffParabolaBound
import RHFormalization.DBFFBStageDirichletForm
import RHFormalization.ShiftedLaplaceSqrtReLowerBound
import RHFormalization.ShiftedLaplaceBranchRange
import RHFormalization.AdmissibleGalerkinStage
import Mathlib

/-!
# D.MR overlap leg — B_stage uniformly bounded on right-half-plane sets

v2: uses the BANKED `sqrt_shift_re_ge` (ShiftedLaplaceSqrtReLowerBound,
strict-< form, implicit args) instead of a duplicate; the ≤-floor on K is
bridged via σ/2 < σ ≤ Re s. Feeds the banked off-parabola Dirichlet bound
through the banked von Mangoldt identity for `B_stage`; prefactor ≤ 1.
No RH-strength input: absolute convergence at exponent > 1.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

/-- The overlap gap at half-depth: `δ(σ) = √(σ/2+¼) − ½`. -/
def overlapDelta (σ : ℝ) : ℝ := Real.sqrt (σ/2 + 1/4) - 1/2

theorem overlapDelta_pos {σ : ℝ} (hσ : 0 < σ) : 0 < overlapDelta σ := by
  unfold overlapDelta
  have h14 : Real.sqrt (1/4) = 1/2 := by
    rw [show (1/4:ℝ) = (1/2)^2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hlt : Real.sqrt (1/4) < Real.sqrt (σ/2 + 1/4) :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  rw [h14] at hlt
  linarith

/-- Half-plane floor in the exact shape the banked Dirichlet bound consumes,
from the BANKED `sqrt_shift_re_ge` at depth `σ/2 < Re s`. -/
theorem dmr_halfplane_sqrt_floor (σ : ℝ) (hσ : 0 < σ) {s : ℂ}
    (hs : σ ≤ s.re) :
    (1/2 : ℝ) + overlapDelta σ ≤ (Complex.sqrt (s + (1/4:ℂ))).re := by
  have hstrict : σ/2 < s.re := by linarith
  have h := sqrt_shift_re_ge hstrict
  unfold overlapDelta
  linarith

/-- **D.MR OVERLAP LEG.** On every set `K` inside the strict right
half-plane `Re s ≥ σ > 0`, the concrete one-letter package `B_stage`
is uniformly bounded in the stage. -/
theorem B_stage_uniform_bound_on_halfplane (σ : ℝ) (hσ : 0 < σ)
    (K : Set ℂ) (hKσ : ∀ s ∈ K, σ ≤ s.re) :
    ∃ C : ℝ, ∀ n : ℕ, ∀ s ∈ K,
      ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s‖ ≤ C := by
  obtain ⟨Cdir, hCdir⟩ := starDirichletPartial_bounded_off_parabola K
    (overlapDelta_pos hσ)
    (fun s hs => dmr_halfplane_sqrt_floor σ hσ (hKσ s hs))
  refine ⟨Cdir, fun n s hs => ?_⟩
  have hB : galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
      = (1 / (2 * Complex.sqrt (s + (1/4:ℂ)))) * starDirichletPartial n s := by
    rw [galerkin_B_stage_eq_vonMangoldt_partial_sum]
    unfold starDirichletPartial
    first
      | rfl
      | (rw [admissibleGalerkinStageSeq_R])
      | (congr 1)
  rw [hB, norm_mul]
  have hre : (1/2 : ℝ) ≤ (Complex.sqrt (s + (1/4:ℂ))).re := by
    have h := dmr_halfplane_sqrt_floor σ hσ (hKσ s hs)
    have hδ := overlapDelta_pos hσ
    linarith
  have hnormw : (1/2 : ℝ) ≤ ‖Complex.sqrt (s + (1/4:ℂ))‖ := by
    refine le_trans hre ?_
    first
      | exact Complex.re_le_norm _
      | exact re_le_norm _
      | exact le_trans (le_abs_self _) (abs_re_le_norm _)
  have hpref : ‖(1 / (2 * Complex.sqrt (s + (1/4:ℂ))) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_mul]
    have h2 : ‖(2:ℂ)‖ = 2 := by
      first
        | simp
        | norm_num
    rw [h2]
    have hnorm1 : ‖(1:ℂ)‖ = 1 := norm_one
    rw [hnorm1]
    rw [div_le_one (by linarith)]
    linarith
  calc ‖(1 / (2 * Complex.sqrt (s + (1/4:ℂ))) : ℂ)‖ * ‖starDirichletPartial n s‖
      ≤ 1 * Cdir :=
        mul_le_mul hpref (hCdir n s hs) (norm_nonneg _) zero_le_one
    _ = Cdir := one_mul Cdir

#print axioms overlapDelta_pos
#print axioms dmr_halfplane_sqrt_floor
#print axioms B_stage_uniform_bound_on_halfplane

end

end RHFormalization
