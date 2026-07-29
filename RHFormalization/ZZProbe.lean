import Mathlib
open Complex
#check @differentiableAt_sqrt
#check @Complex.sqrt
example (z : ℂ) (hz : z ∈ slitPlane) : AnalyticAt ℂ Complex.sqrt z := by
  exact?
