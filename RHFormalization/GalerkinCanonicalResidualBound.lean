import RHFormalization.GalerkinRStageEquivO3
import RHFormalization.GalerkinFStageUniformBound
import RHFormalization.DBFFCompensatorHolo
import RHFormalization.DBFFStarObject
import RHFormalization.DBFFO3ParabolaDepthReduction
import RHFormalization.DBFFDeficitVanishing
import RHFormalization.DBFFDeficitCompactBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

open Complex Filter
open scoped Topology BigOperators

theorem BcorrWin_uniform_bound (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), ∀ s ∈ K, ‖BcorrWin n s‖ ≤ C := by
  obtain ⟨N, hN⟩ :=
    (BcorrWin_vanishes_on_compacts K hK hKΩ 1 one_pos).exists_forall_of_atTop
  have hhead : ∀ n : ℕ, ∃ Mn : ℝ, 0 ≤ Mn ∧ ∀ s ∈ K, ‖BcorrWin n s‖ ≤ Mn :=
    fun n => exists_bound_of_holo_on_compact (fun s => BcorrWin n s)
      (BcorrWin_holo n) K hK hKΩ
  choose M hM0 hMbd using hhead
  set C : ℝ := 1 + ∑ k ∈ Finset.range N, |M k| with hC
  have hCsum_nonneg : (0:ℝ) ≤ ∑ k ∈ Finset.range N, |M k| :=
    Finset.sum_nonneg (fun k _ => abs_nonneg _)
  refine ⟨C, by rw [hC]; linarith, fun n s hs => ?_⟩
  rcases lt_or_ge n N with hlt | hge
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr hlt
    have hMn_le : |M n| ≤ ∑ k ∈ Finset.range N, |M k| :=
      Finset.single_le_sum (f := fun k => |M k|) (fun k _ => abs_nonneg _) hmem
    have hstep : ‖BcorrWin n s‖ ≤ ∑ k ∈ Finset.range N, |M k| :=
      le_trans (hMbd n s hs) (le_trans (le_abs_self _) hMn_le)
    rw [hC]; linarith
  · have hstep : ‖BcorrWin n s‖ ≤ 1 := hN n hge s hs
    rw [hC]; linarith

theorem canonicalResidual_eq_F_sub_star (n : ℕ) (s : ℂ) (hs : s ∈ Ω) :
    galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
      + BcorrWin n s + compensatorM n s
    = galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
      + BcorrWin n s
      - (galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
          - compensatorM n s) := by
  have hR := galerkin_R_stage_eq_F_sub_B n s
  rw [hR]; ring

theorem canonicalResidual_bounded_of_hstar (H : DBFFO3Hstar)
    (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ, ∀ (n : ℕ), ∀ s ∈ K,
      ‖galerkinStagePackage.R_stage (admissibleGalerkinStageSeq n) s
        + BcorrWin n s + compensatorM n s‖ ≤ C := by
  obtain ⟨CF, hCF0, hF⟩ := F_stage_uniform_bound_on_compacts K hK hKΩ
  obtain ⟨Cw, hCw0, hw⟩ := BcorrWin_uniform_bound K hK hKΩ
  obtain ⟨c, hc, hcK⟩ := kernelDenom_min K hK hKΩ
  obtain ⟨CB, hCB⟩ := DBFFO3_compensated_B_bounded_of_hstar H K hK hKΩ c hc
    (fun s hs => by
      rw [one_div, norm_inv]
      exact inv_anti₀ hc (hcK s hs))
  refine ⟨CF + Cw + CB, fun n s hs => ?_⟩
  have hmem : s ∈ Ω := hKΩ hs
  rw [canonicalResidual_eq_F_sub_star n s hmem]
  calc ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
          + BcorrWin n s
          - (galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
              - compensatorM n s)‖
      ≤ ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s + BcorrWin n s‖
          + ‖galerkinStagePackage.B_stage (admissibleGalerkinStageSeq n) s
              - compensatorM n s‖ := norm_sub_le _ _
    _ ≤ (‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s‖
          + ‖BcorrWin n s‖) + CB :=
          add_le_add (norm_add_le _ _) (hCB n s hs)
    _ ≤ (CF + Cw) + CB := add_le_add (add_le_add (hF n s hs) (hw n s hs)) le_rfl
    _ = CF + Cw + CB := by ring

#print axioms canonicalResidual_bounded_of_hstar

end RHFormalization
