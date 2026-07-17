import RHFormalization.GalerkinFSideLaplace
import RHFormalization.DTailPerturbedTraceDomination
import RHFormalization.GalerkinFConvergence
import RHFormalization.CoordSpanMinMax
import Mathlib

/-!
# GalerkinFStageCompactBound — F-side of h_eps_bdd, step 1

`‖F_stage (admissibleGalerkinStageSeq n) s‖` majorized by the density-normalized
FREE resolvent sum, uniformly on Ω-compacts.

Donors (all cold-build clean):
* `galerkinStagePackage_F_at_admissible` (rfl), `perturbedFStage_shift_eq`
* `inv_norm_le_on_compact`
* `freeEigenvalues_le_perturbed`          (needs Λ(q)/√q ≥ 0)
* `freeEigenvalues_galerkinFreeMu_eq`     (sorted enum = reversed Dirichlet level)
* `admShiftedLam_nonneg`, `SupVConst_nonneg_adm`
-/

set_option autoImplicit false

namespace RHFormalization

open Complex Finset
open scoped BigOperators

/-- The admissible free spectral values (Mathlib's sorted enumeration). -/
noncomputable def admFreeEig (n : ℕ) : Fin (admN n) → ℝ :=
  freeEigenvalues (galerkinFreeMu (admN n) (admL n))

theorem admFreeEig_le_admPerturbedLam (n : ℕ) (i : Fin (admN n)) :
    admFreeEig n i ≤ admPerturbedLam n i := by
  unfold admFreeEig admPerturbedLam
  exact freeEigenvalues_le_perturbed (galerkinFreeMu (admN n) (admL n))
    (activePrimePowerCodesCenterBelow (admR n)) (admL n) (admL_pos n)
    (galerkinVC_isHermitian (N := admN n) 1
      (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n)) i

/-- Sorted enumeration is the REVERSED Dirichlet level; then it is a square. -/
theorem admFreeEig_nonneg (n : ℕ) (i : Fin (admN n)) : 0 ≤ admFreeEig n i := by
  unfold admFreeEig
  rw [freeEigenvalues_galerkinFreeMu_eq (admL n) (admL_pos n) i]
  first
    | exact galerkinFreeMu_nonneg _ _ (Fin.rev i)
    | (unfold galerkinFreeMu; positivity)
    | exact sq_nonneg _

/-- **F-side termwise bound on an Ω-compact**, majorized by the FREE spectrum. -/
theorem F_stage_term_norm_le (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n : ℕ) (s : ℂ), s ∈ K → ∀ i : Fin (admN n),
      ‖(s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ))⁻¹‖
        ≤ C₀ * (1 + admFreeEig n i)⁻¹ := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := inv_norm_le_on_compact K hK hKΩ
  refine ⟨C₀, hC₀pos, fun n s hs i => ?_⟩
  have hlam : (0:ℝ) ≤ admPerturbedLam n i + SupVConst := admShiftedLam_nonneg n i
  have h1 := hC₀ s hs (admPerturbedLam n i + SupVConst) hlam
  refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hC₀pos.le)
  have hfree := admFreeEig_nonneg n i
  have hmono := admFreeEig_le_admPerturbedLam n i
  have hsv := SupVConst_nonneg_adm
  have hpos : (0:ℝ) < 1 + admFreeEig n i := by linarith
  have hle : (1:ℝ) + admFreeEig n i ≤ 1 + (admPerturbedLam n i + SupVConst) := by
    linarith
  gcongr

/-- **F-side compact bound, reduced to the free spectral sum.** -/
theorem F_stage_norm_le_free_sum (K : Set ℂ) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n : ℕ) (s : ℂ), s ∈ K →
      ‖galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s‖
        ≤ ‖admDensityC n‖ * (C₀ * ∑ i : Fin (admN n), (1 + admFreeEig n i)⁻¹) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := F_stage_term_norm_le K hK hKΩ
  refine ⟨C₀, hC₀pos, fun n s hs => ?_⟩
  have hF : galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
      = admDensityC n * FstageFinite (fun i => admPerturbedLam n i + SupVConst) s := by
    rw [galerkinStagePackage_F_at_admissible n s]
    congr 1
    unfold admPerturbedLam
    exact perturbedFStage_shift_eq (galerkinFreeMu (admN n) (admL n))
      (galerkinVC_isHermitian (N := admN n) 1
        (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
      SupVConst s
  rw [hF, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  unfold FstageFinite
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => hC₀ n s hs i)

#print axioms admFreeEig_le_admPerturbedLam
#print axioms admFreeEig_nonneg
#print axioms F_stage_term_norm_le
#print axioms F_stage_norm_le_free_sum

end RHFormalization
