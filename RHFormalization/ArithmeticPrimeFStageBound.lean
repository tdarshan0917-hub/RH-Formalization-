import RHFormalization.ArithmeticPrimeRStageBoundSplit
import RHFormalization.FstageResolventBound

/-!
# ArithmeticPrimeFStageBound

This file proves the first of the two estimates needed by

  ArithmeticPrimeDExport_of_F_B_bounds.

It bounds the real arithmetic prime operator F-stage off the real axis using
the existing finite resolvent trace bound:

  ‖FstageFinite lam s‖ ≤ N / |Im s|.

This is a genuine bound on the arithmetic prime resolvent trace. It is still
a fixed finite-stage/off-real-axis estimate, not the final cutoff-limit theorem.
-/

namespace RHFormalization

noncomputable section

open Complex
open scoped Classical

/--
Pointwise arithmetic prime F-stage bound off the real axis.

The arithmetic prime F-stage unfolds to the finite resolvent trace of the
perturbed prime spectrum, so the existing `FstageFinite_norm_le` applies.
-/
theorem arithmeticPrimeFStage_norm_le
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (s : ℂ)
    (hs : Complex.im s ≠ 0) :
    ‖arithmeticPrimeFStage n μ s‖ ≤
      N / |Complex.im s| := by
  unfold arithmeticPrimeFStage
  rw [primePerturbedFStage_eq]
  exact
    FstageFinite_norm_le
      s
      hs
      (perturbedEigenvalues μ
        (primePotential_isHermitian (primeStageWeights (N := N) n)))

/--
A packaged F-bound hypothesis on a set `K`, from a uniform imaginary-axis
lower bound. This is useful for applying `ArithmeticPrimeDExport_of_F_B_bounds`.
-/
theorem arithmeticPrimeFStage_bound_on_K_of_im_lower
    {N : ℕ}
    (n : ℕ)
    (μ : Fin N → ℝ)
    (K : Set ℂ)
    (δ : ℝ)
    (hδ : 0 < δ)
    (hK : ∀ s ∈ K, δ ≤ |Complex.im s|) :
    ∀ s ∈ K,
      ‖arithmeticPrimeFStage n μ s‖ ≤
        N / δ := by
  intro s hsK
  have him_ne : Complex.im s ≠ 0 := by
    intro hzero
    have habs : |Complex.im s| = 0 := by simp [hzero]
    have hδle0 : δ ≤ 0 := by
      simpa [habs] using hK s hsK
    linarith
  have hpoint :=
    arithmeticPrimeFStage_norm_le n μ s him_ne
  have hden_pos : 0 < |Complex.im s| := abs_pos.mpr him_ne
  have hmono :
      (N : ℝ) / |Complex.im s| ≤ (N : ℝ) / δ := by
    have hN : 0 ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
    exact div_le_div_of_nonneg_left hN hδ (hK s hsK)
  exact le_trans hpoint hmono

#print axioms arithmeticPrimeFStage_norm_le
#print axioms arithmeticPrimeFStage_bound_on_K_of_im_lower

end

end RHFormalization
