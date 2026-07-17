import RHFormalization.ArithmeticPrimeFStageBound

/-!
# ArithmeticPrimeGenericDExportBounds

This file removes the bad dependency on `stageFieldSpikeExtractionWitness.B_stage`.

It proves the D.EXPORT bound for an arbitrary comparison package `B`, from:

  F-bound + B-bound.

This prevents the displacement-kernel witness from being baked into the theorem.
The live shifted-Laplace B-stage can be plugged in afterward.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped BigOperators Classical

/--
Generic arithmetic-prime D.EXPORT theorem.

For ANY comparison package `B`, if the arithmetic prime F-stage and `B`
are bounded on `K`, then `ArithmeticPrimeDExport n μ B K` holds.

This is the safe replacement for the earlier stageField-specific theorem.
-/
theorem ArithmeticPrimeDExport_of_generic_F_B_bounds
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (B : ℂ → ℂ)
    (K : Set ℂ)
    (CF CB : ℝ)
    (hCF : 0 ≤ CF)
    (hCB : 0 ≤ CB)
    (hF : ∀ s ∈ K, ‖arithmeticPrimeFStage n μ s‖ ≤ CF)
    (hB : ∀ s ∈ K, ‖B s‖ ≤ CB) :
    ArithmeticPrimeDExport n μ B K := by
  unfold ArithmeticPrimeDExport
  unfold PerturbedDExport
  refine ⟨CF + CB, add_nonneg hCF hCB, ?_⟩
  intro s hs
  rw [← arithmeticPrimeResidual_eq_perturbedResidual (N := N) n μ B s]
  unfold arithmeticPrimeResidual
  calc
    ‖arithmeticPrimeFStage n μ s - B s‖
        ≤ ‖arithmeticPrimeFStage n μ s‖ + ‖B s‖ := by
          simpa [sub_eq_add_neg, norm_neg] using
            norm_add_le (arithmeticPrimeFStage n μ s) (-(B s))
    _ ≤ CF + CB := add_le_add (hF s hs) (hB s hs)

/--
Generic fixed-stage D.EXPORT from an imaginary-axis F-bound and an arbitrary B-bound.
Still not the final Ω-compact version; this is just the safe kernel-agnostic bridge.
-/
theorem ArithmeticPrimeDExport_of_im_lower_and_generic_B_bound
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (B : ℂ → ℂ)
    (K : Set ℂ)
    (δ : ℝ)
    (hδ : 0 < δ)
    (hK : ∀ s ∈ K, δ ≤ |Complex.im s|)
    (CB : ℝ)
    (hCB : 0 ≤ CB)
    (hB : ∀ s ∈ K, ‖B s‖ ≤ CB) :
    ArithmeticPrimeDExport n μ B K := by
  let CF : ℝ := (N : ℝ) / δ
  have hCF : 0 ≤ CF := by
    unfold CF
    exact div_nonneg (by exact_mod_cast Nat.zero_le N) (le_of_lt hδ)
  have hF : ∀ s ∈ K, ‖arithmeticPrimeFStage n μ s‖ ≤ CF := by
    unfold CF
    exact arithmeticPrimeFStage_bound_on_K_of_im_lower n μ K δ hδ hK
  exact ArithmeticPrimeDExport_of_generic_F_B_bounds
    n μ B K CF CB hCF hCB hF hB

#print axioms ArithmeticPrimeDExport_of_generic_F_B_bounds
#print axioms ArithmeticPrimeDExport_of_im_lower_and_generic_B_bound

end

end RHFormalization
