import RHFormalization.PerturbedResidual

namespace RHFormalization
noncomputable section
open Complex

variable {N : ℕ}

/-- **The generic D.EXPORT splitter.** For ANY comparison function `G`, the perturbed
residual bound `PerturbedDExport` follows from two sub-bounds:
  (A) `‖perturbedFStage − G‖ ≤ C₁`  (perturbation control — Weyl/Lipschitz route)
  (B) `‖G − B‖ ≤ C₂`                (the chosen-decomposition error)
via the triangle inequality. This factors the open D.EXPORT obligation into two named
subproblems WITHOUT committing to what `G` is — leaving the choice of the correct
intermediate object (free resolvent, Duhamel spike approximation, or finite canonical
package) open for the right analytic decomposition. -/
theorem PerturbedDExport_of_split_bound
    (μ : Fin N → ℝ) {V : Matrix (Fin N) (Fin N) ℂ} (hV : V.IsHermitian)
    (B G : ℂ → ℂ) (K : Set ℂ) (C1 C2 : ℝ) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (h1 : ∀ s ∈ K, ‖perturbedFStage μ hV s - G s‖ ≤ C1)
    (h2 : ∀ s ∈ K, ‖G s - B s‖ ≤ C2) :
    PerturbedDExport μ hV B K := by
  refine ⟨C1 + C2, add_nonneg hC1 hC2, ?_⟩
  intro s hs
  unfold perturbedResidual
  calc ‖perturbedFStage μ hV s - B s‖
      = ‖(perturbedFStage μ hV s - G s) + (G s - B s)‖ := by congr 1; ring
    _ ≤ ‖perturbedFStage μ hV s - G s‖ + ‖G s - B s‖ := norm_add_le _ _
    _ ≤ C1 + C2 := add_le_add (h1 s hs) (h2 s hs)

#print axioms PerturbedDExport_of_split_bound
end
end RHFormalization
