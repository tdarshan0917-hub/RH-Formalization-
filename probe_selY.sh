#!/bin/zsh
echo "===== 1. the candidate Y instance (full) ====="
cat RHFormalization/SelectedRCutoffDetailedConstructionInstance.lean
echo "===== 2. its source object (full) ====="
cat RHFormalization/SelectedRCutoffDetailedConstructionSource.lean
echo "===== 3. is it in the root import list ====="
grep -n "SelectedRCutoff" RHFormalization.lean
echo "===== 4. does the module build (truth test) ====="
lake build RHFormalization.SelectedRCutoffDetailedConstructionInstance 2>&1 | tee selY_a.log | tail -8
if grep -q "error" selY_a.log; then
  echo "VERDICT: template/holes -> the error list above IS the honest D-side obligation list. Stopping; nothing modified."
  exit 0
fi
echo "VERDICT: COMPLETE Y WITNESS BUILDS. Wiring into endpoint."
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/cfe.bak
python3 - <<'PY'
p='RHFormalization/CurrentFrontierEndpoint.lean'
s=open(p).read()
imp="import RHFormalization.SelectedRCutoffDetailedConstructionInstance"
if imp not in s:
    s=s.replace("import RHFormalization.InterfaceFromCommonCshared",
                "import RHFormalization.InterfaceFromCommonCshared\n"+imp,1)
open(p,'w').write(s)
print("import added")
PY
cat >> RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'

namespace RHFormalization
noncomputable section
open Complex

/-- D-side fully supplied by the selected RCutoff Y witness: only the
zero side and the classical real-zero-free fact remain. -/
theorem RH_from_selected_Y
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (M : ZeroMultiplicityData)
    (Zex : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M Zex Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M Zex Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (h_C_sigma_le :
      selectedDDetailedConstructionWithOperatorLegality.B.Cshared.sigma0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        selectedDDetailedConstructionWithOperatorLegality.B.Cshared.Bshared s =
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
    selectedDDetailedConstructionWithOperatorLegality
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      M Zex Zpole convergence poleSeriesMeromorphic HarchPackage
      selectedDDetailedConstructionWithOperatorLegality.B.Cshared
      sigmaH h_C_sigma_le h_split h_gp
      (buildHSideGroupedPoleNormalFormDataFromPrincipalParts _ M h_pp))
    (by rfl)

#print axioms RH_from_selected_Y

end
end RHFormalization
EOF
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee selY_b.log | grep -e "error" -e "RH_from_selected_Y" -e "depends on axioms" -e "Build completed"
if grep -q "error" selY_b.log; then
  echo "ENDPOINT FAILED -> restoring (errors below)"; grep -B2 -A8 "error" selY_b.log | head -40
  cp /tmp/cfe.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -3; exit 1
fi
lake build 2>&1 | tail -4 | tee selY_root.log
grep -q "Build completed successfully" selY_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_SELECTED_Y.tar.gz . && echo "SNAPSHOT SAVED: SELECTED_Y"
