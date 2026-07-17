/-
GalerkinSpectrumGrowth.lean

CONCRETE WEYL GROWTH OF THE GENUINE SPECTRUM: combining the banked
Weyl-at-SupVConst bound with the diagonal identification, every genuine
galerkin eigenvalue at box width L = 1 satisfies

  lambda_k >= pi^2 * (rev k + 1)^2 - SupVConst,

and the SHIFTED spectrum (the package F-slot's spectrum) has full free
Weyl growth pi^2 * (rev k + 1)^2 -- the exact hypothesis shape of the
banked resolvent summability engine, in the increasing orientation via
Fin.rev. This is the D.R->infty tail fuel for Front F.
-/
import RHFormalization.GalerkinWeylSupV
import RHFormalization.CoordSpanMinMax

namespace RHFormalization

noncomputable section

open Complex

variable {N : ℕ}

/-- The free Dirichlet level at L = 1, in closed form. -/
theorem galerkinFreeMu_one_eq (m : Fin N) :
    galerkinFreeMu N 1 m = Real.pi ^ 2 * (((m : ℕ) : ℝ) + 1) ^ 2 := by
  simp only [galerkinFreeMu]
  rw [div_one]
  ring

/-- **Concrete Weyl floor for the genuine spectrum.** -/
theorem galerkinEigenvalue_ge_pi_sq (qs : Finset ℕ) (k : Fin N) :
    Real.pi ^ 2 * (((Fin.rev k : ℕ) : ℝ) + 1) ^ 2 - SupVConst
      ≤ perturbedEigenvalues (galerkinFreeMu N 1)
          (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal 1) k := by
  have h1 := galerkinEigenvalue_ge_free_sub (galerkinFreeMu N 1) qs k
  have h2 := freeEigenvalues_galerkinFreeMu_eq (N := N) 1 one_pos k
  rw [h2, galerkinFreeMu_one_eq] at h1
  linarith

/-- **Full Weyl growth of the SHIFTED genuine spectrum** (the package
F-slot's spectrum): the SupVConst shift restores the free growth exactly. -/
theorem galerkinShiftedEigenvalue_ge_pi_sq (qs : Finset ℕ) (k : Fin N) :
    Real.pi ^ 2 * (((Fin.rev k : ℕ) : ℝ) + 1) ^ 2
      ≤ perturbedEigenvalues (galerkinFreeMu N 1)
          (galerkinVC_isHermitian (N := N) 1 qs ppWeightReal 1) k
        + SupVConst := by
  have h := galerkinEigenvalue_ge_pi_sq (N := N) qs k
  linarith

#print axioms galerkinFreeMu_one_eq
#print axioms galerkinEigenvalue_ge_pi_sq
#print axioms galerkinShiftedEigenvalue_ge_pi_sq

end

end RHFormalization
