#!/bin/zsh
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/endpoint5.bak
grep -qxF "import RHFormalization.HPPEndgame" RHFormalization/CurrentFrontierEndpoint.lean || sed -i '' '1s/^/import RHFormalization.HPPEndgame\n/' RHFormalization/CurrentFrontierEndpoint.lean
cat >> RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'

namespace RHFormalization
noncomputable section
open Complex

/--
CAPSTONE V5 — h_pp is DERIVED, not assumed. RiemannHypothesis from: the
real-zero-free input; a pole-series candidate with its locally uniform
convergence and meromorphy APIs; the archimedean package; a nonnegative
threshold; and the explicit-formula split. The principal parts at every
witness pole point — with the honest reflection-pair coefficients carrying
the true analytic multiplicities — are supplied by the proven
`h_pp_from_convergence`, the conclusion of the five-installment reduction
campaign (isolation, stabilization, sphere convergence, maximum principle,
limit assembly).
-/
theorem RH_from_designed_D_convergence
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
          HarchPackage.Harch s - Zpole s) :
    RiemannHypothesis :=
  RH_from_designed_D_default_Zex_M_pair h_real_zero_free
    Zpole convergence poleSeriesMeromorphic HarchPackage sigmaH hσH h_split
    (fun W => h_pp_from_convergence defaultZeroMultiplicityData Zpole
      convergence W)

#print axioms RH_from_designed_D_convergence

end
end RHFormalization
EOF
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee cap5_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" cap5_a.log; then
  echo "FAILED -> restoring (errors below)"
  grep -B2 -A14 "error" cap5_a.log | head -60
  cp /tmp/endpoint5.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -2
  exit 1
fi
if ! grep -q "RH_from_designed_D_convergence' depends on axioms: \[propext, Classical.choice, Quot.sound\]" cap5_a.log; then
  echo "AXIOM CHECK FAILED -> restoring"
  cp /tmp/endpoint5.bak RHFormalization/CurrentFrontierEndpoint.lean
  exit 1
fi
lake build 2>&1 | tee cap5_root.log | tail -3
grep -q "Build completed successfully" cap5_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_CAPSTONE_V5.tar.gz . && echo "SNAPSHOT SAVED: CAPSTONE_V5"
