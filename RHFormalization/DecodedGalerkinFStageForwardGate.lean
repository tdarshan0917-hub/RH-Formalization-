-- SENTINEL: decoded-fstage-forward-gate-v1
import RHFormalization.PrimePotentialDecodedCenter
import RHFormalization.GalerkinFStageForwardGate
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

variable {N : ℕ}

/-- Complexification of the manuscript-faithful decoded-center matrix. -/
noncomputable def decodedGalerkinVC
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    ((decodedGalerkinV (N := N) δ qs w L i j : ℝ) : ℂ)

/-- The decoded-center complexified potential is Hermitian. -/
theorem decodedGalerkinVC_isHermitian
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    (decodedGalerkinVC (N := N) δ qs w L).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  rw [Matrix.conjTranspose_apply]
  show
    (starRingEnd ℂ)
        (((decodedGalerkinV (N := N) δ qs w L j i : ℝ) : ℂ))
      =
    (((decodedGalerkinV (N := N) δ qs w L i j : ℝ) : ℂ))
  rw [Complex.conj_ofReal]
  congr 1
  exact decodedGalerkinV_symm
    (N := N) δ qs w L j i

#print axioms decodedGalerkinVC
#print axioms decodedGalerkinVC_isHermitian

end

end RHFormalization
