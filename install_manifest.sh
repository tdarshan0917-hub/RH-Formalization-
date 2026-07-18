#!/bin/zsh
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/cfe.bak
cat >> RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'

namespace RHFormalization
noncomputable section
open Complex

/--
Raw-inputs manifest: RH from bottom-layer data only.

Both sides are built against the single shared canonical package
`C := SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S`,
so the interface equation holds by construction. X's genuine-pole
obligations are derived from the principal-part input via the proven
residue-nonvanishing lemma.
-/
theorem RH_from_raw_inputs
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    -- Appendix D raw inputs
    (finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData finiteOperatorLayer)
    (F : DFHLimitData finiteOperatorLayer.toStagePackage)
    (R : DMasterResidualData finiteOperatorLayer.toStagePackage)
    (h_R_stage_bound :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
          ‖finiteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ finiteOperatorLayer.toStagePackage.sigma0)
    (hF_alpha : F.alpha = S.alpha)
    (hR_alpha : R.alpha = S.alpha)
    -- Appendix H raw inputs
    (M : ZeroMultiplicityData)
    (Zex : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M Zex Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M Zex Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (h_C_sigma_le :
      (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S).sigma0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S).Bshared s =
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
    (buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthWindowFRNoSpeed
      finiteOperatorLayer S F R h_R_stage_bound hσ hF_alpha hR_alpha)
    (buildHMeromorphicWithNormalFormPolesWithChosenCshared
      M Zex Zpole convergence poleSeriesMeromorphic HarchPackage
      (SharpCutoffChosenLengthSharedPackage finiteOperatorLayer S)
      sigmaH h_C_sigma_le h_split h_gp
      (buildHSideGroupedPoleNormalFormDataFromPrincipalParts _ M h_pp))
    (by rfl)

#print axioms RH_from_raw_inputs

end
end RHFormalization
EOF
python3 - <<'PY'
p='RHFormalization/CurrentFrontierEndpoint.lean'
s=open(p).read()
for imp in ["import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFRNoSpeed",
            "import RHFormalization.HMeromorphicWithNormalFormChosenCshared",
            "import RHFormalization.DefaultPoleNormalFormLayer"]:
    if imp not in s:
        s = s.replace("import RHFormalization.InterfaceFromCommonCshared",
                      "import RHFormalization.InterfaceFromCommonCshared\n"+imp, 1)
open(p,'w').write(s)
print("imports added")
PY
echo "===== build endpoint (live) ====="
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee man_a.log | grep -e "error" -e "RH_from_raw_inputs" -e "depends on axioms" -e "Build completed"
if grep -q "error" man_a.log; then
  echo "FAILED -> restoring known-good endpoint (errors below)"
  grep -B2 -A8 "error" man_a.log | head -50
  cp /tmp/cfe.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -3
  exit 1
fi
echo "===== warm root replay + snapshot ====="
lake build 2>&1 | tail -4 | tee man_root.log
grep -q "Build completed successfully" man_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_RAW_MANIFEST.tar.gz . && echo "SNAPSHOT SAVED: RAW_MANIFEST"
