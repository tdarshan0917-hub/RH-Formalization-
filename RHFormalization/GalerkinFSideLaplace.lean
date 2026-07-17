import RHFormalization.AdmissiblePrimeStageIdentity
import RHFormalization.AdmissibleEigenvalueFloor
import RHFormalization.DA2HeatTrace
import Mathlib

/-!
# RHFormalization.GalerkinFSideLaplace

**Galerkin Stieltjes rep, F-side.** The genuine perturbed F-stage at the
admissible net is the density-normalized Laplace transform of its shifted
heat trace on `re s > 0`.

Donors (all banked, cold-build clean):
* `galerkinStagePackage_F_at_admissible` (rfl)
* `perturbedFStage_shift_eq`
* `admissibleEigenvalue_nonneg` — UNSHIFTED, L-generic, via `Λ(q)/√q ≥ 0`
* `FstageFinite_eq_laplace_heatTrace`
-/

set_option autoImplicit false

namespace RHFormalization

open Complex MeasureTheory Set
open scoped BigOperators

/-- The shifted admissible perturbed spectrum is nonnegative. The floor is
`admissibleEigenvalue_nonneg` (unshifted, every window); `SupVConst` only
pushes further right. -/
theorem admShiftedLam_nonneg (n : ℕ) :
    ∀ i : Fin (admN n), 0 ≤ admPerturbedLam n i + SupVConst := by
  intro i
  have hnn : 0 ≤ admPerturbedLam n i := by
    unfold admPerturbedLam
    refine admissibleEigenvalue_nonneg (admL n) (admL_pos n) _ _ (fun k => ?_) i
    first
      | exact galerkinFreeMu_nonneg _ _ k
      | (unfold galerkinFreeMu; positivity)
      | exact sq_nonneg _
  have h2 := SupVConst_nonneg_adm
  linarith

/-- **F-side Galerkin Stieltjes rep.** -/
theorem galerkin_F_stage_eq_laplace_heatTrace (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
      = admDensityC n *
          ∫ t in Ioi (0:ℝ), ∑ i : Fin (admN n),
            Complex.exp (-(s + ((admPerturbedLam n i + SupVConst : ℝ) : ℂ)) * (t:ℂ)) := by
  have h1 : galerkinStagePackage.F_stage (admissibleGalerkinStageSeq n) s
      = admDensityC n *
          FstageFinite (fun i => admPerturbedLam n i + SupVConst) s := by
    rw [galerkinStagePackage_F_at_admissible n s]
    congr 1
    unfold admPerturbedLam
    first
      | exact perturbedFStage_shift_eq (galerkinFreeMu (admN n) (admL n))
          (galerkinVC_isHermitian (N := admN n) 1
            (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
          SupVConst s
      | (unfold galerkinPerturbedFStage
         exact perturbedFStage_shift_eq (galerkinFreeMu (admN n) (admL n))
           (galerkinVC_isHermitian (N := admN n) 1
             (activePrimePowerCodesCenterBelow (admR n)) ppWeightReal (admL n))
           SupVConst s)
  rw [h1]
  congr 1
  first
    | exact FstageFinite_eq_laplace_heatTrace
        (fun i => admPerturbedLam n i + SupVConst) (admShiftedLam_nonneg n) s hs
    | exact FstageFinite_eq_laplace_heatTrace (n := admN n)
        (fun i => admPerturbedLam n i + SupVConst) (admShiftedLam_nonneg n) s hs

#print axioms admShiftedLam_nonneg
#print axioms galerkin_F_stage_eq_laplace_heatTrace

end RHFormalization
