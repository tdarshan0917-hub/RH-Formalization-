import RHFormalization.PerturbedFStageHeatTrace
import RHFormalization.RealSpectralTraceBridge
import RHFormalization.SpikeTransferM2Closed
import RHFormalization.LaplaceHeatSumKit
import Mathlib

/-!
# PerturbedFStageM2Split — the s-side M=2 split of the genuine F-stage

ROUTE CARD
1. Target: EXACT identity, per stage, Re s > 0, nonneg perturbed spectrum:
   `perturbedFStage (galerkinFreeMu N L) (galerkinVC_isHermitian δ qs w L) s
      = FstageFinite (galerkinLam L ·) s
        − Σ_m V_mm·(s+λ_m)⁻²  +  ∫₀^∞ e^{−st}·(E2(t):ℂ) dt`
   — the Laplace transform of spikeTransfer_M2_closed. The operator-side
   one-letter extraction: the F-stage CONTAINS the diagonal spike sum at
   the identity level, before any estimate (the B−M cancellation
   mechanism, D.BFF.1/D.MR.2 shape).
2. Raw B on Ω? NO. B−M bare Prop? NO — exact identity at Re s > 0.
3. Consumer: spike-transfer-to-prime-centers brick
   (VmatrixElement_eq_sum_bumps) → h_expansion of
   DBFFCorrectedBulkProvider → hSC → HtailExists.
Route: perturbedFStage_eq_laplace_diagHeatTrace → trace_exp_neg_KV_eq_eigen_sum
→ spikeTransfer_M2_closed → three-way split (kit integrabilities) →
laplace_heatSum_eq + laplace_t_heatSum_eq.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex MeasureTheory Set Matrix
open scoped BigOperators

attribute [local instance]
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

variable {N : ℕ}

/-- The E2 Laplace transform (per stage; the s-side quadratic remainder). -/
def spikeE2Transform (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0:ℝ),
    Complex.exp (-s * (t : ℂ)) * ((spikeTransferE2 (N := N) δ qs w L t : ℝ) : ℂ)

/-- The perturbed heat trace as a real heat sum (bridge, cast form). -/
theorem perturbed_integrand_eq_heatSum
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (t : ℝ) :
    ((NormedSpace.exp (t • (-(galerkinK (N := N) L
        + galerkinV (N := N) δ qs w L)))).trace : ℂ)
      = ((∑ i : Fin N, Real.exp (-(t * perturbedEigenvalues (galerkinFreeMu N L)
          (galerkinVC_isHermitian (N := N) δ qs w L) i)) : ℝ) : ℂ) := by
  rw [trace_exp_neg_KV_eq_eigen_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

/-- The free heat trace as a real heat sum. -/
theorem free_trace_eq_heatSum (L : ℝ) (t : ℝ) :
    ((NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace : ℂ)
      = ((∑ m : Fin N, Real.exp (-(t * galerkinLam L (m : ℕ))) : ℝ) : ℂ) := by
  rw [galerkinFreeHeat_eq_diagonal, Matrix.trace_diagonal]
  push_cast
  apply Finset.sum_congr rfl
  intro m _
  unfold heatWeight
  norm_num

/-- **THE s-SIDE M=2 SPLIT** (exact; the operator one-letter extraction). -/
theorem perturbedFStage_M2_split
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) (s : ℂ) (hs : 0 < s.re)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues (galerkinFreeMu N L)
        (galerkinVC_isHermitian (N := N) δ qs w L) i)
    (hlam : ∀ m : Fin N, 0 ≤ galerkinLam L (m : ℕ)) :
    perturbedFStage (galerkinFreeMu N L)
        (galerkinVC_isHermitian (N := N) δ qs w L) s
      = FstageFinite (fun m : Fin N => galerkinLam L (m : ℕ)) s
        - (∑ m : Fin N,
            ((galerkinV (N := N) δ qs w L m m : ℝ) : ℂ)
              * ((s + ((galerkinLam L (m : ℕ) : ℝ) : ℂ)) ^ 2)⁻¹)
        + spikeE2Transform (N := N) δ qs w L s := by
  -- integrability of the three pieces
  have hI1 := integrableOn_cexp_heatSum
    (fun m : Fin N => galerkinLam L (m : ℕ)) hlam s hs
  have hI2 := integrableOn_t_cexp_heatSum
    (fun m : Fin N => galerkinV (N := N) δ qs w L m m)
    (fun m : Fin N => galerkinLam L (m : ℕ)) hlam s hs
  have hI3 : IntegrableOn (fun t : ℝ =>
      Complex.exp (-s * (t : ℂ)) *
        ((spikeTransferE2 (N := N) δ qs w L t : ℝ) : ℂ)) (Ioi (0:ℝ)) := by
    have hI0 := integrableOn_cexp_heatSum
      (fun i : Fin N => perturbedEigenvalues (galerkinFreeMu N L)
        (galerkinVC_isHermitian (N := N) δ qs w L) i) hpos s hs
    have hdiff := (hI0.sub hI1).add hI2
    refine hdiff.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have hM2 := spikeTransfer_M2_closed (N := N) δ qs w L t
    have hE2 : (spikeTransferE2 (N := N) δ qs w L t : ℝ)
        = (NormedSpace.exp (t • (-(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L)))).trace
          - (NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace
          + t * (∑ m : Fin N, galerkinV (N := N) δ qs w L m m
              * heatWeight (N := N) L t m) := by
      linarith [hM2]
    calc Complex.exp (-s * (t : ℂ)) *
          ((∑ i : Fin N, Real.exp (-(t * perturbedEigenvalues
              (galerkinFreeMu N L)
              (galerkinVC_isHermitian (N := N) δ qs w L) i)) : ℝ) : ℂ)
        - Complex.exp (-s * (t : ℂ)) *
            ((∑ m : Fin N, Real.exp (-(t * galerkinLam L (m : ℕ))) : ℝ) : ℂ)
        + Complex.exp (-s * (t : ℂ)) * (t : ℂ) *
            ((∑ m : Fin N, galerkinV (N := N) δ qs w L m m
              * Real.exp (-(t * galerkinLam L (m : ℕ))) : ℝ) : ℂ)
        = Complex.exp (-s * (t : ℂ)) *
            (((NormedSpace.exp (t • (-(galerkinK (N := N) L
                + galerkinV (N := N) δ qs w L)))).trace : ℂ)
              - ((NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace : ℂ)
              + ((t * (∑ m : Fin N, galerkinV (N := N) δ qs w L m m
                  * heatWeight (N := N) L t m) : ℝ) : ℂ)) := by
          rw [perturbed_integrand_eq_heatSum, free_trace_eq_heatSum]
          unfold heatWeight
          push_cast
          ring
      _ = Complex.exp (-s * (t : ℂ)) *
            ((spikeTransferE2 (N := N) δ qs w L t : ℝ) : ℂ) := by
          congr 1
          rw_mod_cast [← hE2]
  -- Step 1: F = Laplace of perturbed heat trace, then rewrite integrand
  rw [perturbedFStage_eq_laplace_diagHeatTrace _ _ s hs hpos]
  have hint : ∀ t : ℝ,
      Complex.exp (-s * (t : ℂ)) *
        (Matrix.diagonal (fun i : Fin N =>
          Complex.exp (-(t : ℂ) * ((perturbedEigenvalues (galerkinFreeMu N L)
            (galerkinVC_isHermitian (N := N) δ qs w L) i : ℝ) : ℂ)))).trace
      = (Complex.exp (-s * (t : ℂ)) *
          ((∑ m : Fin N, Real.exp (-(t * galerkinLam L (m : ℕ))) : ℝ) : ℂ)
        - Complex.exp (-s * (t : ℂ)) * (t : ℂ) *
            ((∑ m : Fin N, galerkinV (N := N) δ qs w L m m
              * Real.exp (-(t * galerkinLam L (m : ℕ))) : ℝ) : ℂ))
        + Complex.exp (-s * (t : ℂ)) *
            ((spikeTransferE2 (N := N) δ qs w L t : ℝ) : ℂ) := by
    intro t
    have htr : (Matrix.diagonal (fun i : Fin N =>
        Complex.exp (-(t : ℂ) * ((perturbedEigenvalues (galerkinFreeMu N L)
          (galerkinVC_isHermitian (N := N) δ qs w L) i : ℝ) : ℂ)))).trace
        = ((∑ i : Fin N, Real.exp (-(t * perturbedEigenvalues
            (galerkinFreeMu N L)
            (galerkinVC_isHermitian (N := N) δ qs w L) i)) : ℝ) : ℂ) := by
      rw [Matrix.trace_diagonal]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      push_cast
      ring
    rw [htr]
    have hM2 := spikeTransfer_M2_closed (N := N) δ qs w L t
    have hE2 : (spikeTransferE2 (N := N) δ qs w L t : ℝ)
        = (NormedSpace.exp (t • (-(galerkinK (N := N) L
            + galerkinV (N := N) δ qs w L)))).trace
          - (NormedSpace.exp (t • (-(galerkinK (N := N) L)))).trace
          + t * (∑ m : Fin N, galerkinV (N := N) δ qs w L m m
              * heatWeight (N := N) L t m) := by
      linarith [hM2]
    have hpert := perturbed_integrand_eq_heatSum (N := N) δ qs w L t
    have hfree := free_trace_eq_heatSum (N := N) L t
    calc Complex.exp (-s * (t : ℂ)) *
          ((∑ i : Fin N, Real.exp (-(t * perturbedEigenvalues
              (galerkinFreeMu N L)
              (galerkinVC_isHermitian (N := N) δ qs w L) i)) : ℝ) : ℂ)
        = Complex.exp (-s * (t : ℂ)) *
            (((NormedSpace.exp (t • (-(galerkinK (N := N) L
              + galerkinV (N := N) δ qs w L)))).trace : ℝ) : ℂ) := by
          rw [hpert]
      _ = (Complex.exp (-s * (t : ℂ)) *
            ((∑ m : Fin N, Real.exp (-(t * galerkinLam L (m : ℕ))) : ℝ) : ℂ)
          - Complex.exp (-s * (t : ℂ)) * (t : ℂ) *
              ((∑ m : Fin N, galerkinV (N := N) δ qs w L m m
                * Real.exp (-(t * galerkinLam L (m : ℕ))) : ℝ) : ℂ))
          + Complex.exp (-s * (t : ℂ)) *
              ((spikeTransferE2 (N := N) δ qs w L t : ℝ) : ℂ) := by
          rw_mod_cast [hE2]
          rw [← hfree]
          unfold heatWeight
          push_cast
          ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    (fun t _ => hint t)]
  -- Step 2: three-way split, grouped as (f − g) + h
  rw [MeasureTheory.integral_add
      (f := fun t : ℝ =>
        Complex.exp (-s * (t : ℂ)) *
            ((∑ m : Fin N, Real.exp (-(t * galerkinLam L (m : ℕ))) : ℝ) : ℂ)
          - Complex.exp (-s * (t : ℂ)) * (t : ℂ) *
              ((∑ m : Fin N, galerkinV (N := N) δ qs w L m m
                * Real.exp (-(t * galerkinLam L (m : ℕ))) : ℝ) : ℂ))
      (g := fun t : ℝ =>
        Complex.exp (-s * (t : ℂ)) *
          ((spikeTransferE2 (N := N) δ qs w L t : ℝ) : ℂ))
      (hI1.sub hI2) hI3]
  rw [MeasureTheory.integral_sub
      (f := fun t : ℝ =>
        Complex.exp (-s * (t : ℂ)) *
          ((∑ m : Fin N, Real.exp (-(t * galerkinLam L (m : ℕ))) : ℝ) : ℂ))
      (g := fun t : ℝ =>
        Complex.exp (-s * (t : ℂ)) * (t : ℂ) *
          ((∑ m : Fin N, galerkinV (N := N) δ qs w L m m
            * Real.exp (-(t * galerkinLam L (m : ℕ))) : ℝ) : ℂ))
      hI1 hI2]
  -- Step 3: identify each piece
  rw [laplace_heatSum_eq (fun m : Fin N => galerkinLam L (m : ℕ)) hlam s hs,
    laplace_t_heatSum_eq (fun m : Fin N => galerkinV (N := N) δ qs w L m m)
      (fun m : Fin N => galerkinLam L (m : ℕ)) hlam s hs]
  rfl

#print axioms spikeE2Transform
#print axioms perturbed_integrand_eq_heatSum
#print axioms free_trace_eq_heatSum
#print axioms perturbedFStage_M2_split

end

end RHFormalization
