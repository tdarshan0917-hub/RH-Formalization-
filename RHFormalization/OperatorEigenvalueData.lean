import RHFormalization.EigenvalueGrowthSummable

/-!
# RHFormalization.OperatorEigenvalueData

The SINGLE remaining operator-side input, named explicitly (no wrappers).

`OperatorEigenvalueData` bundles exactly what the paper's Appendix A must supply:
a real eigenvalue sequence with a Weyl growth lower bound. Given this — and
nothing else — the canonical operator transform `F_H^can(s) = ∑ₙ 1/(s+λₙ)` is
holomorphic on `Ω`. The holomorphy is fully proven (`Fstage_holo_from_weyl`);
this file makes the eigenvalue existence the one explicit obligation.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

/-- The one remaining operator-side input: the eigenvalue sequence of the
prime-weighted operator, with nonnegativity and the Weyl growth lower bound. -/
structure OperatorEigenvalueData where
  lam : ℕ → ℝ
  hnonneg : ∀ n, 0 ≤ lam n
  c : ℝ
  C : ℝ
  hc : 0 < c
  hweyl : ∀ n : ℕ, c * (n : ℝ) ^ 2 - C ≤ lam n

/-- The canonical operator transform built from the eigenvalue data:
`F_H^can(s) = ∑ₙ 1/(s+λₙ)`. -/
def OperatorEigenvalueData.FHcan (E : OperatorEigenvalueData) : ℂ → ℂ :=
  fun s => ∑' n, (s + (E.lam n : ℂ))⁻¹

/-- **Operator side closed, modulo eigenvalue existence.** Given the eigenvalue
data, the canonical transform is holomorphic on `Ω`. No further analytic input. -/
theorem OperatorEigenvalueData.FHcan_holo (E : OperatorEigenvalueData) :
    HolomorphicOnC E.FHcan Ω :=
  Fstage_holo_from_weyl E.lam E.hnonneg E.c E.C E.hc E.hweyl

#print axioms OperatorEigenvalueData.FHcan_holo

end

end RHFormalization
