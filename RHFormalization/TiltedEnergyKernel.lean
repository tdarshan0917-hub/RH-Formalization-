-- SENTINEL: E4a-tilted-energy-kernel-v1
import RHFormalization.TiltedEnergyDefinitions
import Mathlib

/-!
# E4a — The finite energy kernel and its symmetry
`tiltedEnergyKernel L a u v = (1/2L)·Σ_k (λ_k+a)⁻¹·Σ_j T(u)_{kj}·T(v)_{kj}` —
the exact finite-N pair kernel `G_{n,a}(u,v)`. Symmetry is per-term
`mul_comm`. Positive-definiteness and the bilinear expansion of Q are
separate bricks (E4b).
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- **E4a — the finite energy kernel** `G_{n,a}(u,v)`. -/
def tiltedEnergyKernel (L a u v : ℝ) : ℝ :=
  (1 / (2 * L)) * ∑ k : Fin N,
    (1 / (galerkinLam L (k : ℕ) + a)) * ∑ j : Fin N,
      galerkinT (N := N) L u k j * galerkinT (N := N) L v k j

/-- **E4a — symmetry**: `G(u,v) = G(v,u)`. -/
theorem tiltedEnergyKernel_symm (L a u v : ℝ) :
    tiltedEnergyKernel (N := N) L a u v
      = tiltedEnergyKernel (N := N) L a v u := by
  unfold tiltedEnergyKernel
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **E4a — diagonal nonnegativity**: `0 ≤ G(u,u)` for `0 < a`
(each summand is a reciprocal of a positive number times a sum of squares). -/
theorem tiltedEnergyKernel_diag_nonneg (L a u : ℝ) (hL : 0 < L) (ha : 0 < a) :
    0 ≤ tiltedEnergyKernel (N := N) L a u u := by
  unfold tiltedEnergyKernel
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg
    · apply le_of_lt
      apply div_pos one_pos
      have h : 0 ≤ galerkinLam L (k : ℕ) := by
        unfold galerkinLam; exact sq_nonneg _
      linarith
    · apply Finset.sum_nonneg
      intro j _
      exact mul_self_nonneg _

#print axioms tiltedEnergyKernel_symm
#print axioms tiltedEnergyKernel_diag_nonneg

end

end RHFormalization
