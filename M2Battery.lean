import RHFormalization.MeromorphyOffCritical
open Complex Set Topology Filter Metric RHFormalization
-- A: the boundary killers
#check @riemannZeta_ne_zero_of_one_le_re
#check @riemannZeta_ne_zero_of_one_lt_re
-- B: continuity of zeta off 1 (for passing zeros to the limit)
example (a : ℂ) (ha : a ≠ 1) : ContinuousAt riemannZeta a :=
  (differentiableAt_riemannZeta ha).continuousAt
-- C: limits of zero-values along a convergent sequence
#check @ContinuousAt.tendsto
#check @Filter.Tendsto.comp
-- D: the strip-closure bound from the rectangle (just membership form)
#check @Complex.mem_reProdIm
-- E: eventually-equal extraction (frequently vs eventually for the self-closing corner)
#check @Filter.Eventually.exists
#check @Filter.frequently_atTop
