#!/bin/zsh
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/endpoint6.bak
grep -qxF "import RHFormalization.MeromorphyAssembly" RHFormalization/CurrentFrontierEndpoint.lean || sed -i '' '1s/^/import RHFormalization.MeromorphyAssembly\n/' RHFormalization/CurrentFrontierEndpoint.lean
cat >> RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'

namespace RHFormalization
noncomputable section
open Complex

/--
CAPSTONE V6 — meromorphy is DERIVED, not assumed. RiemannHypothesis from:
the real-zero-free input; a pole-series candidate `Zpole` with its locally
uniform convergence API; the archimedean package; a nonnegative threshold;
and the explicit-formula split. Both the principal parts (h_pp campaign) and
the meromorphy of `Zpole` on Ω (meromorphy campaign, incl. the M3-vacuity
discovery that every pole point inside Ω comes from an off-critical zero) are
now supplied by theorems. The manifest's content inputs: real-zero-freeness,
the convergence of the pole series, and the explicit formula.
-/
theorem RH_from_designed_D_convergence_only
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (Zpole : ℂ → ℂ)
    (convergence :
      ZeroPoleLocalUniformConvergenceAPI defaultZeroMultiplicityData
        defaultZeroExhaustion Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (hσH : 0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        designedY.B.Cshared.Bshared s =
          HarchPackage.Harch s - Zpole s) :
    RiemannHypothesis :=
  RH_from_designed_D_convergence h_real_zero_free
    Zpole convergence
    { h_meromorphic := fun _ _ =>
        meromorphicOn_from_convergence defaultZeroMultiplicityData
          Zpole convergence }
    HarchPackage sigmaH hσH h_split

#print axioms RH_from_designed_D_convergence_only

end
end RHFormalization
EOF
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee cap6_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" cap6_a.log; then
  echo "FAILED -> restoring (errors below)"
  grep -B2 -A14 "error" cap6_a.log | head -60
  cp /tmp/endpoint6.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -2
  exit 1
fi
if ! grep -q "RH_from_designed_D_convergence_only' depends on axioms: \[propext, Classical.choice, Quot.sound\]" cap6_a.log; then
  echo "AXIOM CHECK FAILED -> restoring"
  cp /tmp/endpoint6.bak RHFormalization/CurrentFrontierEndpoint.lean
  exit 1
fi
lake build 2>&1 | tee cap6_root.log | tail -3
grep -q "Build completed successfully" cap6_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_CAPSTONE_V6.tar.gz . && echo "SNAPSHOT SAVED: CAPSTONE_V6"
