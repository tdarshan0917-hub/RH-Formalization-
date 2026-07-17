import RHFormalization.GrowthEngine
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.Analysis.MellinTransform

namespace RHFormalization

open MeasureTheory Real Set Complex HurwitzZeta Asymptotics Filter

/-- **G3a: the `f_modif` Mellin integrand `t^(σ-1)·‖f_modif t‖` is integrable on `Ioi 0`.**
This is the convergence of the integral defining `G(σ)` (the bound from `norm_completedRiemannZeta0_le`).
Extracted directly from Mathlib's `StrongFEPair.hasMellin`: since `Λ₀ = mellin f_modif` and the
strong FE-pair has unconditional Mellin convergence, the integrand is integrable for every real `σ`. -/
theorem fmodif_mellin_integrable (σ : ℝ) :
    IntegrableOn (fun t => t ^ (σ - 1) * ‖(hurwitzEvenFEPair 0).f_modif t‖) (Ioi 0) := by
  -- MellinConvergent f_modif (σ:ℂ) from the strong FE-pair
  have hconv : MellinConvergent (hurwitzEvenFEPair 0).f_modif (σ : ℂ) :=
    ((hurwitzEvenFEPair 0).toStrongFEPair.hasMellin (σ : ℂ)).1
  -- unfold MellinConvergent = IntegrableOn (t^(s-1) • f_modif)
  rw [MellinConvergent] at hconv
  -- aestronglyMeasurable of f_modif on Ioi 0 (from local integrability)
  have hmeas : AEStronglyMeasurable (hurwitzEvenFEPair 0).f_modif (volume.restrict (Ioi 0)) :=
    ((hurwitzEvenFEPair 0).hf_modif_int).aestronglyMeasurable
  -- convert via mellin_convergent_iff_norm
  have hiff := mellin_convergent_iff_norm (f := (hurwitzEvenFEPair 0).f_modif)
    (T := Ioi 0) (s := (σ : ℂ)) Subset.rfl measurableSet_Ioi hmeas
  rw [hiff] at hconv
  -- (σ:ℂ).re = σ
  simpa using hconv

#print axioms fmodif_mellin_integrable

end RHFormalization
