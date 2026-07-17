-- SENTINEL: decoded-galerkin-stage-shift-v1
import RHFormalization.DecodedGalerkinFStageForwardGate
import RHFormalization.PerturbedGroundStateFormBound
import Mathlib

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped Classical

variable {N : ℕ}

/-- A spectral shift always exists for the decoded-center Galerkin matrix. -/
theorem exists_shift_making_decoded_galerkin_nonneg
    (μ : Fin N → ℝ)
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L : ℝ) :
    ∃ M : ℝ,
      ∀ k : Fin N,
        growthDrop
            (decodedGalerkinVC (N := N) δ qs w L)
          ≤ μ k + M := by
  rcases Finset.exists_le
      (Finset.univ.image
        (fun k : Fin N =>
          growthDrop
              (decodedGalerkinVC (N := N) δ qs w L)
            - μ k)) with
    ⟨M, hM⟩

  refine ⟨M, fun k => ?_⟩

  have hk :=
    hM
      (growthDrop
          (decodedGalerkinVC (N := N) δ qs w L)
        - μ k)
      (Finset.mem_image_of_mem
        (fun j : Fin N =>
          growthDrop
              (decodedGalerkinVC (N := N) δ qs w L)
            - μ j)
        (Finset.mem_univ k))

  linarith

/-- The definite nonnegativity shift for the decoded-center operator. -/
noncomputable def decodedGalerkinStageShift
    (N : ℕ)
    (μ : Fin N → ℝ)
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L : ℝ) : ℝ :=
  Classical.choose
    (exists_shift_making_decoded_galerkin_nonneg
      μ δ qs w L)

/-- Specification of the decoded-center stage shift. -/
theorem decodedGalerkinStageShift_spec
    (N : ℕ)
    (μ : Fin N → ℝ)
    (δ : ℝ)
    (qs : Finset ℕ)
    (w : ℕ → ℝ)
    (L : ℝ) :
    ∀ k : Fin N,
      growthDrop
          (decodedGalerkinVC (N := N) δ qs w L)
        ≤
      μ k
        + decodedGalerkinStageShift
            N μ δ qs w L :=
  Classical.choose_spec
    (exists_shift_making_decoded_galerkin_nonneg
      μ δ qs w L)

#print axioms exists_shift_making_decoded_galerkin_nonneg
#print axioms decodedGalerkinStageShift
#print axioms decodedGalerkinStageShift_spec

end

end RHFormalization
