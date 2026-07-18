#!/bin/zsh
cat > RHFormalization/DefaultOmegaPreperfect.lean <<'EOF'
import RHFormalization.OmegaPuncturedIdentityFromCodiscrete
import RHFormalization.OmegaTopology
import Mathlib.Topology.Perfect

namespace RHFormalization
noncomputable section

theorem preperfect_Omega_native : Preperfect Ω :=
  isOpen_Omega_native.preperfect

def defaultOmegaPreperfectAPI : OmegaPreperfectAPI :=
  { h_preperfect_Omega := preperfect_Omega_native }

#print axioms defaultOmegaPreperfectAPI

end
end RHFormalization
EOF
cat > RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'
import RHFormalization.MainTheoremFromRealZeroFreeOmegaCodiscrete
import RHFormalization.DefaultOmegaPreperfect

namespace RHFormalization
noncomputable section
open Complex

theorem RH_current_frontier
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (E : InterfaceBridgeNonnegativeAPI
        Y.toOperatorResolventBridge X.toLegacyZeroPolePackageAPI)
    (OCI : OmegaCodiscreteMeromorphicIdentityAPI) :
    RiemannHypothesis :=
  mainTheorem_from_realZeroFree_omegaCodiscreteIdentity
    h_real_zero_free Y X E OCI defaultOmegaPreperfectAPI

#print axioms RH_current_frontier

end
end RHFormalization
EOF
grep -qxF "import RHFormalization.DefaultOmegaPreperfect" RHFormalization.lean || printf '\nimport RHFormalization.DefaultOmegaPreperfect\n' >> RHFormalization.lean
grep -qxF "import RHFormalization.CurrentFrontierEndpoint" RHFormalization.lean || printf '\nimport RHFormalization.CurrentFrontierEndpoint\n' >> RHFormalization.lean
lake build 2>&1 | tail -12 | tee opp2_build.log
grep -n -e "error" -e "RH_current_frontier" -e "defaultOmegaPreperfectAPI" -e "depends on axioms" -e "Build completed" opp2_build.log
