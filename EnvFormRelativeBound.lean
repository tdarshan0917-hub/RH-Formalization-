import RHFormalization.EnvFormBound
import RHFormalization.SupVBound

-- A.ENV-FORM relative bound (manuscript p.56): ∫V_R|f|² ≤ θ·H_base[f] + C₀‖f‖², θ<1
-- Upgrading galerkinV_form_le_supV (absolute) to the relative form the KLMN spine needs.
theorem galerkinV_form_le_relative
    (L : ℝ) (qs : Finset ℕ) (a : Fin N → ℝ) :
    ∑ m, ∑ n, a m * a n * galerkinV 1 qs ppWeightReal 1 m n
      ≤ (1/2 : ℝ) * galerkinBaseForm L a + galerkinC0 qs * (∑ i, a i ^ 2) := by
  sorry
