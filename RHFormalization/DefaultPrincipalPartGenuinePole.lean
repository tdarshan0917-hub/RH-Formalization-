import RHFormalization.HSidePoleWitness

namespace RHFormalization

/-- `HasGenuinePole` is definitionally `∃ coeff ≠ 0, HasPrincipalPartAtC ...`,
so this API is theorem-backed by the anonymous constructor. -/
def defaultPrincipalPartImpliesGenuinePoleAPI :
    PrincipalPartImpliesGenuinePoleAPI :=
  { h_genuine := fun _f _s0 c hc hpp => ⟨c, hc, hpp⟩ }

#print axioms defaultPrincipalPartImpliesGenuinePoleAPI

end RHFormalization
