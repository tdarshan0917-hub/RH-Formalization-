import RHFormalization.GalerkinCanonicalFSlot
import RHFormalization.FiniteStageSpectrum
import RHFormalization.ResolventTraceHolo
import Mathlib

/-!
# Canonical F-slot holomorphy — BRICK 6 of the canonical-F route
SENTINEL: canonical-fholo-v3

ROUTE CARD
1. `pairedPerturbedSpikeTransform` is Ω-holomorphic under the nonnegative-
   spectrum hypothesis — poles at `−1/4 − λᵢ ⊂ (−∞,−1/4]`, inside the cut.
2. `galerkinCanonicalOneLetterF` inherits Ω-holomorphy (finite weighted sum).
3. `pairedEigenCoeff_sum_eq_trace`: paired coefficients resum to `Tr T`
   (via `LinearMap.trace_eq_sum_inner`, the v1 first-block winner).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- Termwise analyticity of the paired transform at points of Ω. -/
theorem pairedPerturbedSpikeTransform_analyticAt (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (T : Matrix (Fin N) (Fin N) ℂ)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues μ hV i)
    {z : ℂ} (hz : z ∈ Ω) :
    AnalyticAt ℂ (pairedPerturbedSpikeTransform (N := N) μ hV T) z := by
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      AnalyticAt ℂ (fun s =>
        pairedEigenCoeff (N := N) μ hV T i *
          (1 / (s + (1 / 4 : ℂ) +
            ((perturbedEigenvalues μ hV i : ℝ) : ℂ)))) z := by
    intro i _
    have hlam : (0 : ℝ) ≤ 1 / 4 + perturbedEigenvalues μ hV i := by
      have := hpos i
      linarith
    have hbase : AnalyticAt ℂ
        (fun s : ℂ => s + (1 / 4 : ℂ) +
          ((perturbedEigenvalues μ hV i : ℝ) : ℂ)) z :=
      (analyticAt_id.add analyticAt_const).add analyticAt_const
    have hshape : z + (1 / 4 : ℂ) + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)
        = z + (((1 / 4 + perturbedEigenvalues μ hV i : ℝ)) : ℂ) := by
      push_cast
      ring
    have hne : z + (1 / 4 : ℂ) +
        ((perturbedEigenvalues μ hV i : ℝ) : ℂ) ≠ 0 := by
      rw [hshape]
      exact add_real_ne_zero_of_mem_Omega hz hlam
    have hinv : AnalyticAt ℂ
        (fun s : ℂ => (s + (1 / 4 : ℂ) +
          ((perturbedEigenvalues μ hV i : ℝ) : ℂ))⁻¹) z :=
      hbase.inv hne
    have hrw : (fun s : ℂ =>
        pairedEigenCoeff (N := N) μ hV T i *
          (1 / (s + (1 / 4 : ℂ) +
            ((perturbedEigenvalues μ hV i : ℝ) : ℂ))))
        = fun s : ℂ =>
            pairedEigenCoeff (N := N) μ hV T i *
              (s + (1 / 4 : ℂ) +
                ((perturbedEigenvalues μ hV i : ℝ) : ℂ))⁻¹ := by
      funext s
      rw [one_div]
    rw [hrw]
    exact analyticAt_const.mul hinv
  have hsum : AnalyticAt ℂ (fun s => ∑ i : Fin N,
      pairedEigenCoeff (N := N) μ hV T i *
        (1 / (s + (1 / 4 : ℂ) +
          ((perturbedEigenvalues μ hV i : ℝ) : ℂ)))) z :=
    Finset.analyticAt_fun_sum _ hterm
  exact hsum.congr (by rfl)

/-- **Ω-holomorphy of the paired perturbed spike transform**. -/
theorem pairedPerturbedSpikeTransform_holo (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (T : Matrix (Fin N) (Fin N) ℂ)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues μ hV i) :
    HolomorphicOnC (pairedPerturbedSpikeTransform (N := N) μ hV T) Ω := by
  intro z hz
  exact (pairedPerturbedSpikeTransform_analyticAt μ hV T hpos hz).analyticWithinAt

/-- **Ω-holomorphy of the canonical one-letter F object**. -/
theorem galerkinCanonicalOneLetterF_holo
    (δ : ℝ) (qs : Finset ℕ) (w : ℕ → ℝ) (L R : ℝ)
    (hpos : ∀ i, 0 ≤ perturbedEigenvalues (galerkinFreeMu N L)
      (galerkinVC_isHermitian (N := N) δ qs w L) i) :
    HolomorphicOnC (galerkinCanonicalOneLetterF (N := N) δ qs w L R) Ω := by
  intro z hz
  have hterm : ∀ q ∈ activePrimePowerPairsCenterBelow R,
      AnalyticAt ℂ (fun s =>
        q.weightC *
          pairedPerturbedSpikeTransform (N := N)
            (galerkinFreeMu N L)
            (galerkinVC_isHermitian (N := N) δ qs w L)
            (galerkinTC (N := N) L q.center) s) z := by
    intro q _
    exact analyticAt_const.mul
      (pairedPerturbedSpikeTransform_analyticAt _ _ _ hpos hz)
  have hsum : AnalyticAt ℂ (fun s => ∑ q ∈ activePrimePowerPairsCenterBelow R,
      q.weightC *
        pairedPerturbedSpikeTransform (N := N)
          (galerkinFreeMu N L)
          (galerkinVC_isHermitian (N := N) δ qs w L)
          (galerkinTC (N := N) L q.center) s) z :=
    Finset.analyticAt_fun_sum _ hterm
  have hconst : AnalyticAt ℂ
      (fun _ : ℂ => (((1 / (2 * L) : ℝ) : ℂ))) z := analyticAt_const
  have hfull0 : AnalyticAt ℂ (fun s : ℂ =>
      (((1 / (2 * L) : ℝ) : ℂ)) *
        ∑ q ∈ activePrimePowerPairsCenterBelow R,
          q.weightC *
            pairedPerturbedSpikeTransform (N := N)
              (galerkinFreeMu N L)
              (galerkinVC_isHermitian (N := N) δ qs w L)
              (galerkinTC (N := N) L q.center) s) z :=
    hconst.mul hsum
  have hfull : AnalyticAt ℂ
      (galerkinCanonicalOneLetterF (N := N) δ qs w L R) z :=
    hfull0.congr (by rfl)
  exact hfull.analyticWithinAt

/-- **Paired coefficients resum to the trace of the observable**. -/
theorem pairedEigenCoeff_sum_eq_trace (μ : Fin N → ℝ)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (T : Matrix (Fin N) (Fin N) ℂ) :
    ∑ i : Fin N, pairedEigenCoeff (N := N) μ hV T i
      = LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
          (Matrix.toEuclideanLin T) := by
  exact (LinearMap.trace_eq_sum_inner (Matrix.toEuclideanLin T)
    (((perturbedOp_isSymmetric μ hV).eigenvectorBasis
      perturbedOp_finrank))).symm

#print axioms pairedPerturbedSpikeTransform_analyticAt
#print axioms pairedPerturbedSpikeTransform_holo
#print axioms galerkinCanonicalOneLetterF_holo
#print axioms pairedEigenCoeff_sum_eq_trace

end

end RHFormalization
