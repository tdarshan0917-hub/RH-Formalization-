-- SENTINEL: E1-E2-tilted-energy-definitions-v1
import RHFormalization.GalerkinDisplacementKernel
import RHFormalization.GalerkinDuhamelUniformBound
import Mathlib

/-!
# E1+E2 — Tilted centered observable and energy (basis-sum form)
`tiltedCenteredEntry (k,j)` = Σ_q w(q)e^{−η log q}·T(log q)_{kj}
  − ∫₀^R e^{(1/2−η)u}·T(u)_{kj} du  (scalar interval integral, entrywise).
`tiltedEnergy` = (1/2L)·Σ_k (λ_k+a)⁻¹·Σ_j C_{kj}² — definitionally the
diagonal-resolvent trace form; no matrix inverse. Positivity is arithmetic only.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

variable {N : ℕ}

/-- **E1 — tilted centered entry**: the (k,j) entry of the tilted centered
observable `C_{n,η}`, defined entrywise to avoid matrix-valued integration. -/
def tiltedCenteredEntry (qs : Finset ℕ) (w : ℕ → ℝ) (L R η : ℝ)
    (k j : Fin N) : ℝ :=
  (∑ q ∈ qs, w q * Real.exp (-η * Real.log q)
      * galerkinT (N := N) L (Real.log q) k j)
    - ∫ u in (0:ℝ)..R, Real.exp ((1/2 - η) * u) * galerkinT (N := N) L u k j

/-- **E1 — tilted centered matrix**: assembled entrywise. -/
def tiltedCenteredMatrix (qs : Finset ℕ) (w : ℕ → ℝ) (L R η : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun k j => tiltedCenteredEntry (N := N) qs w L R η k j

theorem tiltedCenteredMatrix_apply (qs : Finset ℕ) (w : ℕ → ℝ) (L R η : ℝ)
    (k j : Fin N) :
    tiltedCenteredMatrix (N := N) qs w L R η k j
      = tiltedCenteredEntry (N := N) qs w L R η k j := rfl

/-- **E2 — tilted energy, basis-sum form**:
`(1/2L)·Σ_k (λ_k+a)⁻¹·Σ_j C_{kj}²`. Definitionally equivalent to
`(2L)⁻¹Tr[Cᵀ(K+aI)⁻¹C]` since `galerkinK` is diagonal (theorem E3, later). -/
def tiltedEnergy (qs : Finset ℕ) (w : ℕ → ℝ) (L R η a : ℝ) : ℝ :=
  (1 / (2 * L)) * ∑ k : Fin N,
    (1 / (galerkinLam L (k : ℕ) + a)) * ∑ j : Fin N,
      (tiltedCenteredEntry (N := N) qs w L R η ((k : Fin N)) j) ^ 2

/-- `galerkinLam` is nonnegative: it is a square. -/
theorem galerkinLam_nonneg (L : ℝ) (m : ℕ) : 0 ≤ galerkinLam L m := by
  unfold galerkinLam
  exact sq_nonneg _

/-- **E2 — positivity**: `0 ≤ tiltedEnergy` for `0 < L`, `0 < a`.
Arithmetic only: positive spectral floor, reciprocals, squares, finite sums. -/
theorem tiltedEnergy_nonneg (qs : Finset ℕ) (w : ℕ → ℝ) (L R η a : ℝ)
    (hL : 0 < L) (ha : 0 < a) :
    0 ≤ tiltedEnergy (N := N) qs w L R η a := by
  unfold tiltedEnergy
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg
    · apply le_of_lt
      apply div_pos one_pos
      have h := galerkinLam_nonneg L (k : ℕ)
      linarith
    · apply Finset.sum_nonneg
      intro j _
      exact sq_nonneg _

#print axioms tiltedCenteredMatrix_apply
#print axioms galerkinLam_nonneg
#print axioms tiltedEnergy_nonneg

end

end RHFormalization
