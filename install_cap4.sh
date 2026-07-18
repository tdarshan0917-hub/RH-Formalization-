#!/bin/zsh
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/endpoint4.bak
grep -qxF "import RHFormalization.ReflectionPairPoleClass" RHFormalization/CurrentFrontierEndpoint.lean || sed -i '' '1s/^/import RHFormalization.ReflectionPairPoleClass\n/' RHFormalization/CurrentFrontierEndpoint.lean
cat >> RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'

namespace RHFormalization
noncomputable section
open Complex

/--
CAPSTONE V4 — the honest manifest. Identical to V3 except that `h_pp` is
stated against the REFLECTION-PAIR grouped class: the principal coefficient at
each witness pole point is `m(ρ) + m(1−ρ)` with the true analytic
multiplicities — exactly the residue the genuine pole series carries (the
singleton-class form of `h_pp` is unsatisfiable by that series; defect #5).
-/
theorem RH_from_designed_D_default_Zex_M_pair
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
            (pairGroupedPoleClass defaultZeroMultiplicityData W))) :
    RiemannHypothesis := by
  have h_gp : ∀ W : ZeroWitness, HasGenuinePole Zpole W.s0 := fun W =>
    ⟨groupedResidueCoeff defaultZeroMultiplicityData
        (pairGroupedPoleClass defaultZeroMultiplicityData W),
      groupedResidueCoeff_ne_zero defaultZeroMultiplicityData W
        (pairGroupedPoleClass defaultZeroMultiplicityData W),
      h_pp W⟩
  exact RH_current_frontier h_real_zero_free
    designedY
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      defaultZeroMultiplicityData defaultZeroExhaustion Zpole convergence
      poleSeriesMeromorphic HarchPackage
      designedY.B.Cshared
      sigmaH (by rw [designedY_Cshared_sigma0]; exact hσH) h_split h_gp
      (buildHSideGroupedPoleNormalFormDataFromPrincipalPartsPair _
        defaultZeroMultiplicityData h_pp))
    (by rfl)

#print axioms RH_from_designed_D_default_Zex_M_pair

end
end RHFormalization
EOF
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee cap4_a.log | grep -e "error" -e "depends on axioms" -e "Build completed"
if grep -q "error" cap4_a.log; then
  echo "FAILED -> restoring (errors below)"
  grep -B3 -A14 "error" cap4_a.log | head -70
  cp /tmp/endpoint4.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -2
  exit 1
fi
if ! grep -q "RH_from_designed_D_default_Zex_M_pair' depends on axioms: \[propext, Classical.choice, Quot.sound\]" cap4_a.log; then
  echo "AXIOM CHECK FAILED -> restoring"
  cp /tmp/endpoint4.bak RHFormalization/CurrentFrontierEndpoint.lean
  exit 1
fi
lake build 2>&1 | tee cap4_root.log | tail -3
grep -q "Build completed successfully" cap4_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_CAPSTONE_V4.tar.gz . && echo "SNAPSHOT SAVED: CAPSTONE_V4"
