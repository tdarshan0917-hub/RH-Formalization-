import RHFormalization.DirichletPWQOModel
import RHFormalization.OperatorEigenvalueData

/-!
# RHFormalization.DirichletPWQOToOperatorEigenvalue

Adapter from the manuscript's Dirichlet PWQO spectral data to the newer
`OperatorEigenvalueData` interface used by the honest FHcan route.
-/

set_option autoImplicit false

namespace RHFormalization

noncomputable section

open Complex Set Topology Filter

namespace DirichletPWQOData

/-- Convert the Dirichlet PWQO spectral package into `OperatorEigenvalueData`. -/
noncomputable def toOperatorEigenvalueData
    (D : DirichletPWQOData) :
    OperatorEigenvalueData :=
  { lam := D.lamShifted
    hnonneg := D.nonneg
    c := D.growthConst
    C := 0
    hc := D.growthConst_pos
    hweyl := by
      intro n
      have h := D.growth_sq n
      simpa using h }

/-- The `FHcan` route agrees definitionally with the Dirichlet shifted resolvent trace. -/
theorem FHcan_eq_dirichlet_resolvent
    (D : DirichletPWQOData) :
    (D.toOperatorEigenvalueData).FHcan =
      fun s => ∑' n, (s + (D.lamShifted n : ℂ))⁻¹ := by
  rfl

/-- Dirichlet PWQO data supplies the operator-side FHcan holomorphy theorem. -/
theorem FHcan_holo
    (D : DirichletPWQOData) :
    HolomorphicOnC (D.toOperatorEigenvalueData).FHcan Ω :=
  OperatorEigenvalueData.FHcan_holo D.toOperatorEigenvalueData

#print axioms DirichletPWQOData.toOperatorEigenvalueData
#print axioms DirichletPWQOData.FHcan_eq_dirichlet_resolvent
#print axioms DirichletPWQOData.FHcan_holo

end DirichletPWQOData

end

end RHFormalization
