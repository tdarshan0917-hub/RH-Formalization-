import RHFormalization.DirichletPWQOModel
import RHFormalization.DirichletLaplacianEigenpairs

/-!
# Concrete free-Dirichlet PWQO instance (real brick, not a stub)

Builds a `DirichletPWQOData` from the genuine free-Dirichlet eigenvalues
`(nπ/L)²` of `−∂²` on `[0,L]`, with the A.GROWTH bound `(nπ/2L)² ≤ λₙ`
PROVED by algebra (since `2L > L`), not assumed.

NOTE: this is the FREE operator (no prime potential). Connecting the PERTURBED
operator's spectrum to A.GROWTH requires min-max for unbounded self-adjoint
operators, which Mathlib does not yet have.
-/

namespace RHFormalization
noncomputable section
open Real

/-- The free-Dirichlet PWQO data on `[0,L]`, eigenvalues `(nπ/L)²`. -/
noncomputable def freeDirichletPWQOData (L : ℝ) (hL : 0 < L) : DirichletPWQOData :=
{ L := L
  L_pos := hL
  lamShifted := fun n => dirichletEigenvalue n L
  nonneg := fun n => dirichletEigenvalue_nonneg n L
  growth := by
    intro n
    unfold dirichletEigenvalue
    have hbase : (n : ℝ) * Real.pi / (2 * L) ≤ (n : ℝ) * Real.pi / L := by
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hL
      · linarith
    have hnn : (0:ℝ) ≤ (n : ℝ) * Real.pi / (2 * L) := by positivity
    exact pow_le_pow_left₀ hnn hbase 2 }

/-- The free-Dirichlet resolvent trace is holomorphic on Ω (genuine theorem). -/
theorem freeDirichletPWQOData_FH_holo (L : ℝ) (hL : 0 < L) :
    HolomorphicOnC
      (fun s => ∑' n, (s + ((freeDirichletPWQOData L hL).lamShifted n : ℂ))⁻¹) Ω :=
  (freeDirichletPWQOData L hL).FH_holo

#print axioms freeDirichletPWQOData
#print axioms freeDirichletPWQOData_FH_holo

end
end RHFormalization
