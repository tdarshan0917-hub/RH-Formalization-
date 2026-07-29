import RHFormalization.ResolventTraceHolo
import RHFormalization.FiniteStageSpectrum
namespace RHFormalization
noncomputable section
open Complex Finset
example (s : ℂ) (lam : ℝ) (hlam : 0 ≤ lam) :
    |Complex.im s| ≤ ‖s + (lam : ℂ)‖ := by
  have him : (s + (lam : ℂ)).im = s.im := by simp
  rw [← him]
  exact?
