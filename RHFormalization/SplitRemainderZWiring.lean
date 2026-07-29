-- SENTINEL: ZWIRE-v1
import RHFormalization.FreeResolventMassBound
import RHFormalization.AdaptivePairedResolventSplit
import Mathlib

/-!
# SplitRemainderZWiring — the JOIN test

Bounds the remainder term EXACTLY as it appears in the banked
`paired_resolvent_split`, with the mass input discharged by MASSBOUND.

CONSUMER: `hr` of `seam_bdd_of_parts` (after stage instantiation).

REMAINING INPUTS after this file (the honest ledger):
  δ  — spectral gap, free and perturbed, uniform on K   [input 2]
  CV — Euclidean operator bound for V                    [input 3]
  CT — Euclidean operator bound for T                    [input 4]
Everything else in the Z estimate is now discharged.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators

variable {N : ℕ}

/-- **The join**: Z bounded in the split's own term shape. -/
theorem norm_split_remainder_trace_le
    (μ : Fin N → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (s : ℂ) (M : ℝ) (hM : ‖s‖ ≤ M)
    {δ : ℝ} (hδ : 0 < δ)
    (hlowF : ∀ i, δ ≤ ‖s + ((μ i : ℝ) : ℂ)‖)
    (hlowP : ∀ i, δ ≤ ‖s + ((perturbedEigenvalues μ hV i : ℝ) : ℂ)‖)
    {c : ℝ} (hc : 0 < c)
    (hgrow : ∀ i : Fin N, c * (((i : ℕ) : ℝ) + 1) ^ 2 ≤ μ i)
    (T : EuclideanSpace ℂ (Fin N) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (CV CT : ℝ) (hCV : 0 ≤ CV) (hCT : 0 ≤ CT)
    (hVop : ∀ x, ‖Matrix.toEuclideanLin V x‖ ≤ CV * ‖x‖)
    (hTop : ∀ x, ‖T x‖ ≤ CT * ‖x‖) :
    ‖LinearMap.trace ℂ (EuclideanSpace ℂ (Fin N))
        (freeResolventOpE μ s * Matrix.toEuclideanLin V
          * perturbedResolventOp μ hV s * T)‖
      ≤ ((2 * (1 + M + δ) / δ)
            * ∑' n : ℕ, (1 + c * (((n : ℕ) : ℝ) + 1) ^ 2)⁻¹)
          * (CV * (δ⁻¹ * CT)) := by
  have hM0 : (0:ℝ) ≤ M := le_trans (norm_nonneg s) hM
  set Cm : ℝ := (2 * (1 + M + δ) / δ)
      * ∑' n : ℕ, (1 + c * (((n : ℕ) : ℝ) + 1) ^ 2)⁻¹ with hCmdef
  have hmass := free_resolvent_mass_le μ hμ s M hM hδ hlowF hc hgrow
  have hCm : (0:ℝ) ≤ Cm := by
    rw [hCmdef]
    have hA : (0:ℝ) ≤ 2 * (1 + M + δ) / δ := by positivity
    have hT : (0:ℝ) ≤ ∑' n : ℕ, (1 + c * (((n : ℕ) : ℝ) + 1) ^ 2)⁻¹ :=
      tsum_nonneg (fun n => by positivity)
    exact mul_nonneg hA hT
  have hkey := norm_remainder_trace_le μ hV s hδ hlowP
      (Matrix.toEuclideanLin V) T CV CT Cm hCV hCT hVop hTop hmass hCm
  have hassoc :
      freeResolventOpE μ s * Matrix.toEuclideanLin V
          * perturbedResolventOp μ hV s * T
        = freeResolventOpE μ s
            * (Matrix.toEuclideanLin V * (perturbedResolventOp μ hV s * T)) := by
    rw [mul_assoc, mul_assoc]
  rw [hassoc]
  exact hkey

#print axioms norm_split_remainder_trace_le

end

end RHFormalization
