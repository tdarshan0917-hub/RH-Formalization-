import RHFormalization.MainTheorem
import RHFormalization.DefaultZetaZeroFacts

/-!
# RHFormalization.FinalSpineFromRealZeroFree

Top-level conditional spine with the ZetaZeroFacts slot reduced to one
explicit classical sentence: the Riemann zeta function has no zeros on
the real interval (0,1). This is a standard textbook fact (via the
Dirichlet eta factorization), currently not in Mathlib; it is stated
here as a named hypothesis rather than an abstract structure.
-/

namespace RHFormalization

noncomputable section

/--
RH follows from: (1) the classical fact that zeta has no real zeros in
(0,1), and (2) the five analytic API packages of the manuscript spine.
-/
theorem RH_follows_from_realZeroFree_and_APIs
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (D : OperatorResolventBridge)
    (H : ZeroPolePackageAPI)
    (E : InterfaceBridgeAPI D H)
    (P : PoleWitnessAPI H)
    (R : RigidityNoPoleAPI D H E) :
    RiemannHypothesis :=
  RH_follows_from_packaged_spine
    (defaultZetaZeroFacts_of_realZeroFree h_real_zero_free)
    D H E P R

#print axioms RH_follows_from_realZeroFree_and_APIs

end

end RHFormalization
