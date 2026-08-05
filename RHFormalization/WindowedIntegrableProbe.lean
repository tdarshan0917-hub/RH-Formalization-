import RHFormalization.GalerkinDisplacementKernel
import RHFormalization.GalerkinPairingBounds

set_option autoImplicit false
namespace RHFormalization
open MeasureTheory

/-- The windowed eigenfunction is measurable. -/
theorem measurable_dirichletEigenfunWindowed (n : ℕ) (L : ℝ) :
    Measurable (dirichletEigenfunWindowed n L) := by
  unfold dirichletEigenfunWindowed
  apply Measurable.ite
  · exact measurableSet_Icc
  · unfold dirichletEigenfun
    fun_prop
  · exact measurable_const

/-- Any shifted windowed eigenfunction is interval-integrable. -/
theorem windowed_intervalIntegrable (n : ℕ) (L a : ℝ) (u v : ℝ) :
    IntervalIntegrable (fun x => dirichletEigenfunWindowed n L (x - a))
      MeasureTheory.volume u v := by
  apply IntervalIntegrable.mono_fun'
    (g := fun _ : ℝ => (1:ℝ))
  · exact intervalIntegrable_const
  · apply Measurable.aestronglyMeasurable
    have hcomp : (fun x : ℝ => dirichletEigenfunWindowed n L (x - a))
        = (dirichletEigenfunWindowed n L) ∘ (fun x : ℝ => x - a) := rfl
    rw [hcomp]
    exact (measurable_dirichletEigenfunWindowed n L).comp (by fun_prop)
  · filter_upwards with x
    rw [Real.norm_eq_abs]
    exact dirichletEigenfunWindowed_abs_le n L (x - a)

#print axioms measurable_dirichletEigenfunWindowed
#print axioms windowed_intervalIntegrable
end RHFormalization
