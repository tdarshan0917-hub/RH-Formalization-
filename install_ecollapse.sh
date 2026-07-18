#!/bin/zsh
echo "===== 0. ground truth: overlap Cshared field + builder name check ====="
grep -rn -A8 "structure HSideOverlapPackage" RHFormalization/*.lean | head -12
grep -rn "def buildInterfaceBridgeFromSharedPackageFunctionalCompatibility" RHFormalization/*.lean | head -2
echo "===== 1. create InterfaceFromCommonCshared.lean ====="
cat > RHFormalization/InterfaceFromCommonCshared.lean <<'EOF'
import RHFormalization.AppendixESharedPackageFunctionalCompatibility
import RHFormalization.InterfaceNonnegative

/-!
# RHFormalization.InterfaceFromCommonCshared

Appendix-E collapse: if the D-side and H-side packages are built against the
SAME shared canonical prime-power package, the full nonnegative interface
bridge follows with no further analytic input.

The only hypothesis is the package equation
`Y.B.Cshared = X.layer.overlap.Cshared`; the interface identity
`D.B = H.Bzero` then follows by transitivity through `Cshared.Bshared`,
and the threshold is `max 0 (max σ_D σ_H)`.
-/

namespace RHFormalization

noncomputable section

open Complex Topology Filter

def buildInterfaceBridgeNonnegativeFromCommonCshared
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (h_common : Y.B.Cshared = X.layer.overlap.Cshared) :
    InterfaceBridgeNonnegativeAPI
      Y.toOperatorResolventBridge
      X.toLegacyZeroPolePackageAPI :=
  { bridge :=
      buildInterfaceBridgeFromSharedPackageFunctionalCompatibility Y X
        { sigma :=
            max 0
              (max Y.toOperatorResolventBridge.sigma0
                X.toLegacyZeroPolePackageAPI.sigma0)
          hsigma_ge_D :=
            (le_max_left _ _).trans (le_max_right _ _)
          hsigma_ge_H :=
            (le_max_right _ _).trans (le_max_right _ _)
          h_shared_B := by
            intro s _
            rw [h_common] }
    h_sigma_nonneg := le_max_left _ _ }

#print axioms buildInterfaceBridgeNonnegativeFromCommonCshared

end

end RHFormalization
EOF
echo "===== 2. build module (live) ====="
lake build RHFormalization.InterfaceFromCommonCshared 2>&1 | tee ec_a.log | grep -e "error" -e "Built RHFormalization.InterfaceFromCommonCshared" -e "depends on axioms" -e "Build completed"
if grep -q "error" ec_a.log; then
  echo "MODULE FAILED -> parking, project untouched (full errors below)"
  grep -B2 -A6 "error" ec_a.log | head -40
  rm RHFormalization/InterfaceFromCommonCshared.lean
  exit 1
fi
echo "===== 3. rewire canonical endpoint: E -> common-Cshared equation ====="
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/cfe.bak
cat > RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'
import RHFormalization.MainTheoremFromRealZeroFreeOmegaCodiscrete
import RHFormalization.DefaultOmegaPreperfect
import RHFormalization.DefaultOmegaCodiscreteIdentity
import RHFormalization.InterfaceFromCommonCshared

namespace RHFormalization
noncomputable section
open Complex

theorem RH_current_frontier
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Y : DDetailedConstructionWithOperatorLegality)
    (X : HMeromorphicWithNormalFormPoles)
    (h_common : Y.B.Cshared = X.layer.overlap.Cshared) :
    RiemannHypothesis :=
  mainTheorem_from_realZeroFree_omegaCodiscreteIdentity
    h_real_zero_free Y X
    (buildInterfaceBridgeNonnegativeFromCommonCshared Y X h_common)
    defaultOmegaCodiscreteIdentityAPI defaultOmegaPreperfectAPI

#print axioms RH_current_frontier

end
end RHFormalization
EOF
grep -qxF "import RHFormalization.InterfaceFromCommonCshared" RHFormalization.lean || printf '\nimport RHFormalization.InterfaceFromCommonCshared\n' >> RHFormalization.lean
echo "===== 4. build endpoint (live) ====="
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee ec_b.log | grep -e "error" -e "RH_current_frontier" -e "depends on axioms" -e "Build completed"
if grep -q "error" ec_b.log; then
  echo "ENDPOINT FAILED -> restoring known-good endpoint (full errors below)"
  grep -B2 -A6 "error" ec_b.log | head -40
  cp /tmp/cfe.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -3
  exit 1
fi
echo "===== 5. warm root replay + snapshot ====="
lake build 2>&1 | tail -5 | tee ec_root.log
grep -q "Build completed successfully" ec_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_E_COLLAPSED.tar.gz . && echo "SNAPSHOT SAVED: E_COLLAPSED"
