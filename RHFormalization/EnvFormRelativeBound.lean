import RHFormalization.EnvFormBound
import RHFormalization.PerturbedFormBound

-- A.ENV-FORM relative bound. Probe: does pertOp_form_lower_bound compose with
-- the absolute form bound to give the relative θ<1 form the KLMN spine needs?
theorem galerkinV_form_le_relative
    (L : ℝ) (qs : Finset ℕ) (a : Fin N → ℝ) :
    ∑ m, ∑ n, a m * a n * galerkinV 1 qs ppWeightReal 1 m n
      ≤ (1/2 : ℝ) * (∑ m, ∑ n, a m * a n * galerkinK L m n)
        + SupVConst * (∑ i, a i ^ 2) := by
  sorry
