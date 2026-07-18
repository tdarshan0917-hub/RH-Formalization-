#!/bin/zsh
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/endpoint.bak
cat >> RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'

namespace RHFormalization
noncomputable section
open Complex

/--
CAPSTONE MANIFEST (designed D-side): RH from the real-zero-free input and the
Appendix-H raw inputs ONLY. The entire D-side is supplied by the closed witness
`designedY`; its shared canonical package is the concrete tsum package over the
displacement Gaussian, so `h_split` below is an identity against the genuine
prime-power series Σ' Λ(q)/√q · G(log q).
-/
theorem RH_from_designed_D_and_H_raw_inputs
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    -- Appendix H raw inputs (the D-side is closed by designedY)
    (M : ZeroMultiplicityData)
    (Zex : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M Zex Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M Zex Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (h_C_sigma_le : designedY.B.Cshared.sigma0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        designedY.B.Cshared.Bshared s =
          HarchPackage.Harch s - Zpole s)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC Zpole W.s0
          (groupedResidueCoeff M (defaultGroupedPoleClass M W))) :
    RiemannHypothesis := by
  have h_gp : ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0 := fun W =>
    ⟨groupedResidueCoeff M (defaultGroupedPoleClass M W),
      groupedResidueCoeff_ne_zero M W (defaultGroupedPoleClass M W),
      h_pp W⟩
  exact RH_current_frontier h_real_zero_free
    designedY
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      M Zex Zpole convergence poleSeriesMeromorphic HarchPackage
      designedY.B.Cshared
      sigmaH h_C_sigma_le h_split h_gp
      (buildHSideGroupedPoleNormalFormDataFromPrincipalParts _ M h_pp))
    (by rfl)

/--
The shared B-function in the capstone manifest is the concrete prime-power
series: the `h_split` hypothesis is an identity against Σ' Λ(q)/√q · G(log q).
-/
theorem designed_Cshared_Bshared_eq (s : ℂ) :
    designedY.B.Cshared.Bshared s =
      ∑' q : PrimePowerPair,
        q.weightC * (displacementCanonicalKernel (heatKernelG 1)) q.center s := by
  first
    | rfl
    | simp [canonicalPrimePowerPackageFromKernelTsum, RCutoffEstimateSharedPackage]

#print axioms RH_from_designed_D_and_H_raw_inputs
#print axioms designed_Cshared_Bshared_eq

end
end RHFormalization
EOF
sed -i '' '1s/^/import RHFormalization.DesignedDetailedConstruction\n/' RHFormalization/CurrentFrontierEndpoint.lean
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee cap_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" cap_a.log; then
  echo "FAILED -> restoring (errors below)"
  grep -B3 -A14 "error" cap_a.log | head -70
  cp /tmp/endpoint.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -2
  exit 1
fi
if ! grep -q "RH_from_designed_D_and_H_raw_inputs' depends on axioms: \[propext, Classical.choice, Quot.sound\]" cap_a.log; then
  echo "AXIOM CHECK FAILED -> restoring"
  cp /tmp/endpoint.bak RHFormalization/CurrentFrontierEndpoint.lean
  exit 1
fi
lake build 2>&1 | tee cap_root.log | tail -3
grep -q "Build completed successfully" cap_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_DESIGNED_CAPSTONE.tar.gz . && echo "SNAPSHOT SAVED: DESIGNED_CAPSTONE"
