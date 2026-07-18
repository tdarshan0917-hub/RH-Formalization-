#!/bin/zsh
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/endpoint3.bak
grep -qxF "import RHFormalization.DefaultZeroMultiplicity" RHFormalization/CurrentFrontierEndpoint.lean || sed -i '' '1s/^/import RHFormalization.DefaultZeroMultiplicity\n/' RHFormalization/CurrentFrontierEndpoint.lean
cat >> RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'

namespace RHFormalization
noncomputable section
open Complex

/--
CAPSTONE V3 — the tightest manifest. RiemannHypothesis from:
the real-zero-free input; a pole-series candidate `Zpole` with its locally
uniform convergence (against the PROVEN exhaustion) and meromorphy APIs; the
archimedean package; the explicit-formula split against the CONSTRUCTED
prime-power series; and principal parts carrying the TRUE analytic
multiplicities. Everything else — the entire D-side, the zero exhaustion,
the multiplicity data, the threshold — is theorem.
-/
theorem RH_from_designed_D_default_Zex_M
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Zpole : ℂ → ℂ)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData
        defaultZeroExhaustion Zpole)
    (poleSeriesMeromorphic :
      ZpoleMeromorphicFromSeriesAPI defaultZeroMultiplicityData
        defaultZeroExhaustion Zpole)
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
          (groupedResidueCoeff defaultZeroMultiplicityData
            (defaultGroupedPoleClass defaultZeroMultiplicityData W))) :
    RiemannHypothesis :=
  RH_from_designed_D_default_Zex h_real_zero_free
    defaultZeroMultiplicityData Zpole convergence poleSeriesMeromorphic
    HarchPackage sigmaH hσH h_split h_pp

#print axioms RH_from_designed_D_default_Zex_M

end
end RHFormalization
EOF
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee cap3_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" cap3_a.log; then
  echo "FAILED -> restoring (errors below)"
  grep -B3 -A14 "error" cap3_a.log | head -60
  cp /tmp/endpoint3.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -2
  exit 1
fi
if ! grep -q "RH_from_designed_D_default_Zex_M' depends on axioms: \[propext, Classical.choice, Quot.sound\]" cap3_a.log; then
  echo "AXIOM CHECK FAILED -> restoring"
  cp /tmp/endpoint3.bak RHFormalization/CurrentFrontierEndpoint.lean
  exit 1
fi
lake build 2>&1 | tee cap3_root.log | tail -3
grep -q "Build completed successfully" cap3_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_CAPSTONE_V3.tar.gz . && echo "SNAPSHOT SAVED: CAPSTONE_V3"
