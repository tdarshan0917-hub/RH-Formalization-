import RHFormalization.DefaultZeroMultiplicity
open Complex RHFormalization
#check @Finset.sum_pair
#check @Finset.mem_insert
#check @Finset.mem_singleton
#check @Complex.Gamma_ne_zero
#check @Complex.cos_ne_zero_iff
example (ρ : ℂ) : polePoint (1 - ρ) = polePoint ρ := by
  unfold polePoint; ring
