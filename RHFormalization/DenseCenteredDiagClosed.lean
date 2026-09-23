import RHFormalization.DenseEnergyLowerBound
import RHFormalization.U4WitnessTransfer
import Mathlib

/-!
# DenseCenteredDiagClosed — KB2: closed form of the centered diagonal

`C_kk = Σ_q w(q)·φ_k(center q) − ∫₀^R e^{u/2} φ_k(u) du` with the explicit
profile `φ_k(u) = (1 − u/L)cos(κ_k u) + sin(κ_k u)/((k+1)π)`, `κ_k = (k+1)π/L`.
Pure rewriting through the banked `galerkinT_diag_closed`; second brick of the
B8 kill theorem.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open scoped BigOperators

/-- The diagonal Galerkin profile at mode `k`. -/
def diagProfile (n : ℕ) (k : Fin (denseN n)) (u : ℝ) : ℝ :=
  (1 - u / denseL n) * Real.cos (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)
    + Real.sin (((k : ℕ) + 1 : ℝ) * Real.pi * u / denseL n)
        / ((((k : ℕ) + 1 : ℝ)) * Real.pi)

theorem galerkinT_diag_eq_diagProfile (n : ℕ) (k : Fin (denseN n)) {u : ℝ}
    (hu0 : 0 ≤ u) (huL : u ≤ denseL n) :
    galerkinT (N := denseN n) (denseL n) u k k = diagProfile n k u :=
  galerkinT_diag_closed (denseL n) u (denseL_pos n) hu0 huL k

/-- **KB2**: the centered diagonal in closed form. -/
theorem denseCenteredMatrix_diag_closed (n : ℕ) (k : Fin (denseN n)) :
    denseCenteredMatrix n k k
      = (∑ q ∈ activePrimePowerPairsCenterBelow (admR n),
            q.weightReal * diagProfile n k q.center)
        - ∫ u in (0:ℝ)..(admR n), Real.exp (u / 2) * diagProfile n k u := by
  rw [denseCenteredMatrix_apply]
  unfold denseCenteredEntry
  congr 1
  · refine Finset.sum_congr rfl (fun q hq => ?_)
    rw [galerkinT_diag_eq_diagProfile n k (center_nonneg q) (center_le_denseL n q hq)]
  · refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (admR_pos n).le] at hu
    rw [galerkinT_diag_eq_diagProfile n k hu.1 (le_trans hu.2 (admR_lt_denseL n).le)]

#print axioms denseCenteredMatrix_diag_closed

end

end RHFormalization
