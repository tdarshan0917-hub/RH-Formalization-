import RHFormalization.OmegaPuncturedIdentityEndpoint

namespace RHFormalization

#check mainTheorem_from_default_connectedOmega_meromorphicAlgebra_omegaPuncturedIdentity

theorem RH_unconditional_probe : RiemannHypothesis := by
  refine
    mainTheorem_from_default_connectedOmega_meromorphicAlgebra_omegaPuncturedIdentity
      ?ZF ?Y ?X ?E ?OIP

end RHFormalization
