import RHFormalization.DefaultZeroMultiplicity
open Complex RHFormalization
#check @polePoint
#check @riemannZeta_one_sub
#check @riemannCompletedZeta
#check @completedRiemannZeta
#check @riemannZeta_def_of_ne_zero
example (ρ ρ' : ℂ) (h : ρ * (1 - ρ) = ρ' * (1 - ρ')) : ρ' = ρ ∨ ρ' = 1 - ρ := by
  have : (ρ' - ρ) * (ρ' - (1 - ρ)) = 0 := by ring_nf; linear_combination h
  rcases mul_eq_zero.mp this with h1 | h2
  · left; linarith [sub_eq_zero.mp h1]
  · right; exact sub_eq_zero.mp h2
