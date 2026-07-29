import RHFormalization.ShiftedLaplaceSqrtBranch
import Mathlib.Analysis.RCLike.Sqrt

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter Metric
open scoped BigOperators

#check Complex.sqrt_eq_exp
#check Complex.exp_ne_zero

example (x : ℂ) (hx : x ≠ 0) :
    Complex.sqrt x ≠ 0 := by
  rw [Complex.sqrt_eq_exp hx]
  exact Complex.exp_ne_zero _

example (z : ℂ) (hz : shiftedLaplaceShift z ≠ 0) :
    shiftedLaplaceSqrt z ≠ 0 := by
  have hsqrt_exp :
      shiftedLaplaceSqrt z =
        Complex.exp (Complex.log (shiftedLaplaceShift z) / 2) := by
    simpa [shiftedLaplaceSqrt, shiftedLaplaceShift] using
      (Complex.sqrt_eq_exp (z := shiftedLaplaceShift z) hz)
  rw [hsqrt_exp]
  exact Complex.exp_ne_zero _

end

end RHFormalization
