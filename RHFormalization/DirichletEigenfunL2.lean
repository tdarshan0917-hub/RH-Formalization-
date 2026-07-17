import RHFormalization.DirichletEigenfunOrthogonal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# RHFormalization.DirichletEigenfunL2
**Foundation brick 3, stone 1.** Place the Dirichlet eigenfunctions into
`L²([0,L])` as genuine elements and record their continuity / membership.
Builds on bricks 1–2; pure measure-theory plumbing, no operator theory.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open MeasureTheory Real
open scoped Real

/-- The interval measure on `[0,L]`: Lebesgue volume restricted to `Set.Icc 0 L`. -/
noncomputable def intervalMeasure (L : ℝ) : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Icc 0 L)

instance (L : ℝ) : IsFiniteMeasure (intervalMeasure L) := by
  unfold intervalMeasure
  exact ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_Icc_lt_top⟩

/-- The eigenfunction is continuous (hence strongly measurable, hence in every Lᵖ
on the finite interval measure). -/
theorem continuous_dirichletEigenfun (n : ℕ) (L : ℝ) :
    Continuous (dirichletEigenfun n L) := by
  unfold dirichletEigenfun
  fun_prop

/-- The eigenfunction is bounded by 1 in norm (it is a sine). -/
theorem dirichletEigenfun_abs_le (n : ℕ) (L : ℝ) (x : ℝ) :
    |dirichletEigenfun n L x| ≤ 1 := by
  unfold dirichletEigenfun
  exact Real.abs_sin_le_one _

/-- The eigenfunction is in `L²` of the finite interval measure. -/
theorem memLp_dirichletEigenfun (n : ℕ) (L : ℝ) :
    MemLp (dirichletEigenfun n L) 2 (intervalMeasure L) := by
  apply MemLp.of_bound
    (continuous_dirichletEigenfun n L).aestronglyMeasurable 1
  filter_upwards with x
  simpa using dirichletEigenfun_abs_le n L x

#print axioms continuous_dirichletEigenfun
#print axioms dirichletEigenfun_abs_le
#print axioms memLp_dirichletEigenfun

end

end RHFormalization
