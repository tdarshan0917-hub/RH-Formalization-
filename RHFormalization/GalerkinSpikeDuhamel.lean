import RHFormalization.GalerkinDisplacementKernel
import RHFormalization.GalerkinDuhamelTraceIdentity
import Mathlib

/-!
# T_a-paired Duhamel — BRICK 2 of the canonical-F route

ROUTE CARD
1. Target: the perturbed spike functional `Tr(exp(−t(K+V))·T_a)` and its
   exact Duhamel expansion — the finite analogue of the manuscript's
   perturbed displacement trace whose word sorting is D.ONE-STEP′′.
2. Proof: banked `galerkinDuhamel_identity` right-multiplied by `galerkinT`,
   integral commuted via `LinearMap.mulRight` CLM, trace commuted via banked
   `trace_integral_comm_real`. Pure plumbing on banked analytic content.
3. Consumer: Brick 3 (shifted-Laplace bridge to B_stage − BcorrWin),
   Galerkin ONE-STEP′′ (word sorting of the integral term).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- **Perturbed Galerkin spike kernel**: `Tr(exp(−t(K+V))·T_a)` — the
displacement-paired trace of the genuine operator. -/
def galerkinSpikeKernelPerturbed
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t a : ℝ) : ℝ :=
  (NormedSpace.exp (t • (-(galerkinK (N := N) L + galerkinV (N := N) δ qs w L)))
    * galerkinT (N := N) L a).trace

/-- **Perturbed one-letter package (raw)**: the displacement-paired
functional summed over the active prime-power spikes. -/
def galerkinOneLetterPerturbedRaw
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t : ℝ) : ℝ :=
  ∑ q ∈ qs, w q * galerkinSpikeKernelPerturbed (N := N) δ qs w L t (Real.log q)

/-- **BRICK 2 — the T_a-paired Duhamel identity.**
`Tr(E(t)·T_a) = Tr(D(t)·T_a) + ∫₀ᵗ Tr(D(t−u)·(−V)·E(u)·T_a) du`. -/
theorem galerkinSpikeKernel_duhamel
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t a : ℝ) :
    galerkinSpikeKernelPerturbed (N := N) δ qs w L t a
      = galerkinSpikeKernel (N := N) L t a
        + ∫ u in (0:ℝ)..t,
            (NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
              * (-(galerkinV (N := N) δ qs w L))
              * NormedSpace.exp (u • (-(galerkinK (N := N) L
                  + galerkinV (N := N) δ qs w L)))
              * galerkinT (N := N) L a).trace := by
  have hid := galerkinDuhamel_identity (N := N) δ qs w L t
  set T : Matrix (Fin N) (Fin N) ℝ := galerkinT (N := N) L a with hT
  set F : ℝ → Matrix (Fin N) (Fin N) ℝ :=
    fun u => NormedSpace.exp ((t - u) • (-(galerkinK (N := N) L)))
      * (-(galerkinV (N := N) δ qs w L))
      * NormedSpace.exp (u • (-(galerkinK (N := N) L
          + galerkinV (N := N) δ qs w L))) with hF
  have hFcont : Continuous F := by rw [hF]; fun_prop
  have hFTcont : Continuous (fun u => F u * T) := by fun_prop
  -- right-multiply the operator identity by T
  have hmul := congrArg (fun M : Matrix (Fin N) (Fin N) ℝ => M * T) hid
  simp only [sub_mul] at hmul
  -- push T through the interval integral
  have hI : IntervalIntegrable F MeasureTheory.volume 0 t :=
    hFcont.intervalIntegrable 0 t
  have hint : (∫ u in (0:ℝ)..t, F u) * T = ∫ u in (0:ℝ)..t, F u * T := by
    first
      | exact ((LinearMap.mulRight ℝ T).toContinuousLinearMap.intervalIntegral_comp_comm
          hI).symm
      | exact (ContinuousLinearMap.intervalIntegral_comp_comm
          (LinearMap.mulRight ℝ T).toContinuousLinearMap hI).symm
      | · have h := (ContinuousLinearMap.intervalIntegral_comp_comm
            (LinearMap.mulRight ℝ T).toContinuousLinearMap hI).symm
          simpa [LinearMap.mulRight_apply] using h
      | · have h := ((LinearMap.mulRight ℝ T).toContinuousLinearMap.intervalIntegral_comp_comm
            hI).symm
          simpa [LinearMap.mulRight_apply] using h
  rw [hint] at hmul
  -- trace both sides, commute trace with the integral
  have htr := congrArg Matrix.trace hmul
  have hcomm : (∫ u in (0:ℝ)..t, F u * T).trace
      = ∫ u in (0:ℝ)..t, (F u * T).trace := by
    rw [trace_integral_comm_real (N := N) t (fun u => F u * T) hFTcont]
  rw [Matrix.trace_sub, hcomm] at htr
  unfold galerkinSpikeKernelPerturbed galerkinSpikeKernel
  linear_combination htr

/-- Far-window vanishing transfers to the perturbed kernel. -/
theorem galerkinSpikeKernelPerturbed_eq_zero_of_gt
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L t a : ℝ)
    (hL : 0 < L) (ha : L < a) :
    galerkinSpikeKernelPerturbed (N := N) δ qs w L t a = 0 := by
  unfold galerkinSpikeKernelPerturbed
  have hz : galerkinT (N := N) L a = 0 := by
    ext m n
    exact galerkinT_eq_zero_of_gt (N := N) L a hL ha m n
  rw [hz, mul_zero]
  simp [Matrix.trace]

#print axioms galerkinSpikeKernelPerturbed
#print axioms galerkinOneLetterPerturbedRaw
#print axioms galerkinSpikeKernel_duhamel
#print axioms galerkinSpikeKernelPerturbed_eq_zero_of_gt

end

end RHFormalization
