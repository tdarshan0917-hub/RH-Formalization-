import RHFormalization.GalerkinMatrices
import RHFormalization.PerturbedResidual
import Mathlib

/-!
# Genuine Galerkin (position-space) F-stage — the keystone bridge.

The diagonal `primePotential` is the manuscript's "bookkeeping model only" (p101).
The GENUINE perturbation is the off-diagonal position-space bump matrix `galerkinV`
(= ∫₀^L φ_m · V_pp · φ_n, the manuscript's V_R = ∑ w(q) W_α(u − log q)).

This file complexifies `galerkinV`, proves it Hermitian (from the banked real
symmetry `galerkinV_symm`), and feeds it into the generic `perturbedFStage`
machinery — giving the genuine operator a real F-stage with holomorphy on Ω.

This is the operator on which the banked Duhamel tower (Stone 8
`abs_trace_galerkin_duhamel_uniform`) is the load-bearing remainder.
-/

set_option autoImplicit false

namespace RHFormalization
noncomputable section
open Matrix Complex
open scoped BigOperators

variable {N : ℕ}

/-- The complexified genuine Galerkin bump matrix: `galerkinV` with entries cast to ℂ. -/
noncomputable def galerkinVC
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (galerkinV (N := N) δ qs w L i j : ℂ)

/-- **The keystone.** The complexified genuine Galerkin operator is Hermitian.
Real symmetric (banked `galerkinV_symm`) ⟹ complexified Hermitian: conjugation
acts trivially on real entries, transpose trivially by symmetry. -/
theorem galerkinVC_isHermitian
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    (galerkinVC (N := N) δ qs w L).IsHermitian := by
  have hsymm := galerkinV_symm (N := N) δ qs w L
  rw [Matrix.IsHermitian]
  ext i j
  rw [Matrix.conjTranspose_apply]
  show (starRingEnd ℂ) ((galerkinV (N := N) δ qs w L j i : ℝ) : ℂ)
      = ((galerkinV (N := N) δ qs w L i j : ℝ) : ℂ)
  rw [Complex.conj_ofReal]
  congr 1
  have : galerkinV (N := N) δ qs w L j i = galerkinV (N := N) δ qs w L i j := by
    have h := hsymm
    rw [Matrix.IsSymm] at h
    calc galerkinV (N := N) δ qs w L j i
        = (galerkinV (N := N) δ qs w L)ᵀ i j := by rw [Matrix.transpose_apply]
      _ = galerkinV (N := N) δ qs w L i j := by rw [h]
  rw [this]

/-- **Genuine position-space Galerkin F-stage.** The resolvent trace of the
non-commuting operator `K + galerkinV` (free Dirichlet diagonal + genuine bump
perturbation), via the generic perturbed F-stage on the Hermitian `galerkinVC`. -/
noncomputable def galerkinPerturbedFStage
    (μ : Fin N → ℝ)
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    ℂ → ℂ :=
  perturbedFStage μ (galerkinVC_isHermitian (N := N) δ qs w L)

/-- **The genuine operator's F-stage is holomorphic on Ω** (nonnegative shifted
spectrum). Inherited from the generic `perturbedFStage_holo`, now on the genuine
non-commuting position-space operator. -/
theorem galerkinPerturbedFStage_holo
    (μ : Fin N → ℝ)
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues μ (galerkinVC_isHermitian (N := N) δ qs w L) i) :
    HolomorphicOnC (galerkinPerturbedFStage (N := N) μ δ qs w L) Ω :=
  perturbedFStage_holo μ (galerkinVC_isHermitian (N := N) δ qs w L) hpos

#print axioms galerkinVC
#print axioms galerkinVC_isHermitian
#print axioms galerkinPerturbedFStage
#print axioms galerkinPerturbedFStage_holo

end
end RHFormalization
