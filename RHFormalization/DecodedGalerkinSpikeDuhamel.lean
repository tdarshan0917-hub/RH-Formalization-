-- SENTINEL: decoded-galerkin-spike-duhamel-v4
import RHFormalization.DecodedGalerkinDuhamelIdentity
import RHFormalization.GalerkinDisplacementKernel
import RHFormalization.GalerkinDuhamelTraceIdentity
import RHFormalization.AppendixDActiveSpikeCodesFromCenterCutoff
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- Perturbed displacement kernel using the decoded-center matrix. -/
def decodedGalerkinSpikeKernelPerturbed
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t a : ℝ) : ℝ :=
  (NormedSpace.exp
      (t • (-(galerkinK (N := N) L
        + decodedGalerkinV (N := N) δ qs w L)))
    * galerkinT (N := N) L a).trace

/-- Decoded one-letter package using the physical center of each code. -/
def decodedGalerkinOneLetterPerturbedRaw
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t : ℝ) : ℝ :=
  ∑ k ∈ qs,
    w k *
      decodedGalerkinSpikeKernelPerturbed
        (N := N) δ qs w L t (ppDecode k).center

/-- Paired Duhamel identity for the decoded-center operator. -/
theorem decodedGalerkinSpikeKernel_duhamel
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t a : ℝ) :
    decodedGalerkinSpikeKernelPerturbed
        (N := N) δ qs w L t a
      =
    galerkinSpikeKernel (N := N) L t a
      + ∫ u in (0 : ℝ)..t,
          (NormedSpace.exp
              ((t - u) • (-(galerkinK (N := N) L)))
            * (-(decodedGalerkinV (N := N) δ qs w L))
            * NormedSpace.exp
              (u • (-(galerkinK (N := N) L
                + decodedGalerkinV (N := N) δ qs w L)))
            * galerkinT (N := N) L a).trace := by
  have hid :=
    decodedGalerkinDuhamel_identity
      (N := N) δ qs w L t

  set T : Matrix (Fin N) (Fin N) ℝ :=
    galerkinT (N := N) L a with hT

  set F : ℝ → Matrix (Fin N) (Fin N) ℝ :=
    fun u =>
      NormedSpace.exp
          ((t - u) • (-(galerkinK (N := N) L)))
        * (-(decodedGalerkinV (N := N) δ qs w L))
        * NormedSpace.exp
          (u • (-(galerkinK (N := N) L
            + decodedGalerkinV (N := N) δ qs w L))) with hF

  have hFcont : Continuous F := by
    rw [hF]
    fun_prop

  have hFTcont : Continuous (fun u => F u * T) := by
    fun_prop

  have hmul :=
    congrArg
      (fun M : Matrix (Fin N) (Fin N) ℝ => M * T)
      hid

  simp only [sub_mul] at hmul

  have hI : IntervalIntegrable F MeasureTheory.volume 0 t :=
    hFcont.intervalIntegrable 0 t

  have hint :
      (∫ u in (0 : ℝ)..t, F u) * T
        =
      ∫ u in (0 : ℝ)..t, F u * T := by
    exact
      (ContinuousLinearMap.intervalIntegral_comp_comm
        (LinearMap.mulRight ℝ T).toContinuousLinearMap hI).symm

  rw [hint] at hmul

  have htr := congrArg Matrix.trace hmul

  have hcomm :
      (∫ u in (0 : ℝ)..t, F u * T).trace
        =
      ∫ u in (0 : ℝ)..t, (F u * T).trace := by
    rw [trace_integral_comm_real
      (N := N) t (fun u => F u * T) hFTcont]

  rw [Matrix.trace_sub, hcomm] at htr

  unfold decodedGalerkinSpikeKernelPerturbed galerkinSpikeKernel
  linear_combination htr

/-- Displacements outside the finite window vanish. -/
theorem decodedGalerkinSpikeKernelPerturbed_eq_zero_of_gt
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ)
    (L t a : ℝ)
    (hL : 0 < L) (ha : L < a) :
    decodedGalerkinSpikeKernelPerturbed
        (N := N) δ qs w L t a = 0 := by
  unfold decodedGalerkinSpikeKernelPerturbed
  have hz : galerkinT (N := N) L a = 0 := by
    ext m n
    exact
      galerkinT_eq_zero_of_gt
        (N := N) L a hL ha m n
  rw [hz, mul_zero]
  simp [Matrix.trace]

#print axioms decodedGalerkinSpikeKernelPerturbed
#print axioms decodedGalerkinOneLetterPerturbedRaw
#print axioms decodedGalerkinSpikeKernel_duhamel
#print axioms decodedGalerkinSpikeKernelPerturbed_eq_zero_of_gt

end

end RHFormalization
