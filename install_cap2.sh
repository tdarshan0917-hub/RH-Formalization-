#!/bin/zsh
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/endpoint2.bak
grep -qxF "import RHFormalization.DefaultZeroExhaustion" RHFormalization/CurrentFrontierEndpoint.lean || sed -i '' '1s/^/import RHFormalization.DefaultZeroExhaustion\n/' RHFormalization/CurrentFrontierEndpoint.lean
cat >> RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'

namespace RHFormalization
noncomputable section
open Complex

/-- The designed shared package has threshold 0. -/
theorem designedY_Cshared_sigma0 : designedY.B.Cshared.sigma0 = 0 := by
  first
    | rfl
    | simp [designedY,
        buildDDetailedConstructionWithOperatorLegalityFromRCutoffEstimate,
        buildDDetailedConstructionWithOperatorLegalityFromFiniteCanonicalLimit,
        buildDBcanLimitDataFromOperatorFiniteCanonicalLimit,
        buildDBcanLimitDataFromOperatorPrimePowerLimit,
        RCutoffEstimateSharedPackage,
        canonicalPrimePowerPackageFromKernelTsum,
        designedFiniteOperatorLayer_sigma0]

/--
TIGHTEST CAPSTONE: RH from the real-zero-free input and the residual H-side
analytic inputs. The D-side is the closed witness `designedY`; the zero
exhaustion is the PROVEN `defaultZeroExhaustion`; the threshold condition is
just nonnegativity of `sigmaH`.
-/
theorem RH_from_designed_D_default_Zex
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (M : ZeroMultiplicityData)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M defaultZeroExhaustion Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M defaultZeroExhaustion Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (hσH : 0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        designedY.B.Cshared.Bshared s =
          HarchPackage.Harch s - Zpole s)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC Zpole W.s0
          (groupedResidueCoeff M (defaultGroupedPoleClass M W))) :
    RiemannHypothesis :=
  RH_from_designed_D_and_H_raw_inputs h_real_zero_free
    M defaultZeroExhaustion Zpole convergence poleSeriesMeromorphic HarchPackage
    sigmaH (by rw [designedY_Cshared_sigma0]; exact hσH) h_split h_pp

#print axioms RH_from_designed_D_default_Zex

end
end RHFormalization
EOF
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee cap2_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" cap2_a.log; then
  echo "FAILED -> restoring (errors below)"
  grep -B3 -A14 "error" cap2_a.log | head -60
  cp /tmp/endpoint2.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -2
  exit 1
fi
if ! grep -q "RH_from_designed_D_default_Zex' depends on axioms: \[propext, Classical.choice, Quot.sound\]" cap2_a.log; then
  echo "AXIOM CHECK FAILED -> restoring"
  cp /tmp/endpoint2.bak RHFormalization/CurrentFrontierEndpoint.lean
  exit 1
fi
lake build 2>&1 | tee cap2_root.log | tail -3
grep -q "Build completed successfully" cap2_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_CAPSTONE_V2.tar.gz . && echo "SNAPSHOT SAVED: CAPSTONE_V2"
