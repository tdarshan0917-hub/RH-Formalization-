-- SENTINEL: real-spectral-trace-bridge-v2
import RHFormalization.FrobExpSemigroup
import RHFormalization.GalerkinSpikeComplexify
import RHFormalization.PairedTraceExpBridge
import Mathlib

/-! # Core brick 6b-iv — the REAL spectral trace bridge.
`Tr(exp(t•(−(K+V)))) = Σᵢ e^{−t·λᵢ}` over the perturbed eigenvalues, by
complexifying through the banked `matC` toolkit into the banked ℂ-typed
paired bridge at `T = 1`. Hands `Tr(exp(2S))` to the banked FK chain. -/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix Complex
open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- The paired coefficient at `T = 1` is `1` (orthonormality). -/
theorem pairedEigenCoeff_one (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian) (i : Fin N) :
    pairedEigenCoeff (N := N) μ hV (1 : Matrix (Fin N) (Fin N) ℂ) i = 1 := by
  have hON :
      Orthonormal ℂ
        ⇑((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank) :=
    ((perturbedOp_isSymmetric μ hV).eigenvectorBasis perturbedOp_finrank).orthonormal
  have hvv := orthonormal_iff_ite.mp hON i i
  rw [if_pos rfl] at hvv
  unfold pairedEigenCoeff
  first
    | (simp
       exact hvv)
    | (simp [hvv])
    | (simpa using hvv)

/-- **CORE BRICK 6b-iv: the real spectral trace bridge.** -/
theorem trace_exp_neg_KV_eq_eigen_sum
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    (NormedSpace.exp (t • (-(galerkinK (N := N) L
        + galerkinV (N := N) δ qs w L)))).trace
      = ∑ i : Fin N, Real.exp (-t * perturbedEigenvalues (galerkinFreeMu N L)
          (galerkinVC_isHermitian (N := N) δ qs w L) i) := by
  have hV := galerkinVC_isHermitian (N := N) δ qs w L
  -- cast the real trace into ℂ
  have hcast : (((NormedSpace.exp (t • (-(galerkinK (N := N) L
        + galerkinV (N := N) δ qs w L)))).trace : ℝ) : ℂ)
      = ((NormedSpace.exp ((-(t:ℂ)) • perturbedMatrix (galerkinFreeMu N L)
          (galerkinVC (N := N) δ qs w L))) * 1).trace := by
    rw [matC_trace, matC_exp, matC_scaled, mul_one]
  rw [trace_exp_mul_eq_pairedHeatTrace (galerkinFreeMu N L) hV 1 t] at hcast
  unfold pairedPerturbedHeatTrace at hcast
  simp only [pairedEigenCoeff_one, one_mul] at hcast
  -- both sides are casts of real sums; strip ofReal
  have hsum : (((NormedSpace.exp (t • (-(galerkinK (N := N) L
        + galerkinV (N := N) δ qs w L)))).trace : ℝ) : ℂ)
      = ((∑ i : Fin N, Real.exp (-t * perturbedEigenvalues (galerkinFreeMu N L)
          hV i) : ℝ) : ℂ) := by
    rw [hcast]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    first
      | rfl
      | ring_nf
      | (rw [← Complex.ofReal_exp]; push_cast; ring_nf)
  exact_mod_cast hsum

#print axioms pairedEigenCoeff_one
#print axioms trace_exp_neg_KV_eq_eigen_sum

end

end RHFormalization
