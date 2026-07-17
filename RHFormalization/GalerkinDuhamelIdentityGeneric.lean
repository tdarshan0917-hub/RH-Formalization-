-- SENTINEL: generic-matrix-duhamel-v1
import RHFormalization.GalerkinDysonInterpDeriv
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Matrix MeasureTheory intervalIntegral

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Dyson interpolation with an arbitrary finite perturbation matrix `V`. -/
noncomputable def dysonInterpWithV
    (L : ℝ) (V : Matrix (Fin N) (Fin N) ℝ) (t u : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
    * NormedSpace.exp (u • (-(galerkinK (N := N) L + V)))

theorem dysonInterpWithV_zero
    (L : ℝ) (V : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    dysonInterpWithV (N := N) L V t 0
      = NormedSpace.exp (t • (-(galerkinK (N := N) L))) := by
  unfold dysonInterpWithV
  rw [sub_zero, zero_smul, NormedSpace.exp_zero, mul_one]

theorem dysonInterpWithV_self
    (L : ℝ) (V : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    dysonInterpWithV (N := N) L V t t
      = NormedSpace.exp (t • (-(galerkinK (N := N) L + V))) := by
  unfold dysonInterpWithV
  rw [sub_self, zero_smul, NormedSpace.exp_zero, one_mul]

/-- Perturbed heat derivative for an arbitrary finite matrix `V`,
in left-multiplication form. -/
theorem hasDerivAt_perturbedHeat_left_of_matrix
    (L : ℝ) (V : Matrix (Fin N) (Fin N) ℝ) (u : ℝ) :
    HasDerivAt
      (fun v : ℝ =>
        NormedSpace.exp (v • (-(galerkinK (N := N) L + V))))
      ((-(galerkinK (N := N) L + V))
        * NormedSpace.exp
          (u • (-(galerkinK (N := N) L + V)))) u := by
  set B : Matrix (Fin N) (Fin N) ℝ :=
    -(galerkinK (N := N) L + V)
  change HasDerivAt
    (fun v : ℝ => NormedSpace.exp (v • B))
    (B * NormedSpace.exp (u • B)) u
  have h := hasDerivAt_exp_smul_const B u
  convert h using 1
  have hc : Commute B (NormedSpace.exp (u • B)) :=
    ((Commute.refl B).smul_right u).exp_right
  exact hc.eq

/-- Generic Dyson derivative in the exact `-V` sandwich form. -/
theorem hasDerivAt_dysonInterpWithV_sandwich
    (L : ℝ) (V : Matrix (Fin N) (Fin N) ℝ) (t u : ℝ) :
    HasDerivAt
      (fun v : ℝ => dysonInterpWithV (N := N) L V t v)
      (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
        * (-V)
        * NormedSpace.exp
          (u • (-(galerkinK (N := N) L + V)))) u := by
  have hfree :=
    hasDerivAt_dysonInterp_freeFactor (N := N) L t u
  have hpert :=
    hasDerivAt_perturbedHeat_left_of_matrix
      (N := N) L V u
  have hmul := hfree.mul hpert
  unfold dysonInterpWithV
  convert hmul using 1
  noncomm_ring

/-- **Generic finite-matrix Duhamel identity.**
This is the existing Galerkin identity with `galerkinV` replaced by an
arbitrary matrix, allowing specialization to `decodedGalerkinV`. -/
theorem galerkinDuhamel_identity_of_matrix
    (L : ℝ) (V : Matrix (Fin N) (Fin N) ℝ) (t : ℝ) :
    NormedSpace.exp
        (t • (-(galerkinK (N := N) L + V)))
      - NormedSpace.exp
        (t • (-(galerkinK (N := N) L)))
      =
    ∫ u in (0 : ℝ)..t,
      NormedSpace.exp
          ((t - u) • (-(galerkinK (N := N) L)))
        * (-V)
        * NormedSpace.exp
          (u • (-(galerkinK (N := N) L + V))) := by
  have hderiv :
      ∀ u ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt
          (fun v : ℝ =>
            dysonInterpWithV (N := N) L V t v)
          (NormedSpace.exp
              ((t - u) • (-(galerkinK (N := N) L)))
            * (-V)
            * NormedSpace.exp
              (u • (-(galerkinK (N := N) L + V)))) u :=
    fun u _ =>
      hasDerivAt_dysonInterpWithV_sandwich
        (N := N) L V t u

  have hcont : ContinuousOn
      (fun u : ℝ =>
        NormedSpace.exp
            ((t - u) • (-(galerkinK (N := N) L)))
          * (-V)
          * NormedSpace.exp
            (u • (-(galerkinK (N := N) L + V))))
      (Set.uIcc 0 t) := by
    apply Continuous.continuousOn
    fun_prop

  rw [integral_eq_sub_of_hasDerivAt
    hderiv (hcont.intervalIntegrable)]
  rw [dysonInterpWithV_self, dysonInterpWithV_zero]

#print axioms dysonInterpWithV
#print axioms hasDerivAt_perturbedHeat_left_of_matrix
#print axioms hasDerivAt_dysonInterpWithV_sandwich
#print axioms galerkinDuhamel_identity_of_matrix

end

end RHFormalization
