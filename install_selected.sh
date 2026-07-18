#!/bin/zsh
echo "===== 1. the spike-extraction witness instance (what is it concretely) ====="
sed -n '1,60p' RHFormalization/AppendixDFiniteSpikeExtractionWitnessInstance.lean
echo "===== 2. selected alpha / cutoff-sequence data ====="
sed -n '1,50p' RHFormalization/AppendixDSelectedAlphaIndexData.lean
echo "===== 3. sigma0 of the selected layer (trace the value) ====="
grep -rn "sigma0" RHFormalization/AppendixDFiniteSpikeExtractionWitness.lean RHFormalization/AppendixDFiniteSpikeExtractionWitnessInstance.lean | head -8
echo "===== 4. any selected F / R / window data ====="
grep -rn "def selected" RHFormalization/*.lean | head -14
echo "===== 5. install: specialize manifest to the selected layer ====="
cp RHFormalization/CurrentFrontierEndpoint.lean /tmp/cfe.bak
cat >> RHFormalization/CurrentFrontierEndpoint.lean <<'EOF'

namespace RHFormalization
noncomputable section
open Complex

/--
Manifest specialized to the concrete selected operator layer: raw input #1
(the finite-stage operator construction) is supplied by
`selectedFiniteOperatorLayer`, a built witness.
-/
theorem RH_from_selected_operator_layer
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData selectedFiniteOperatorLayer)
    (F : DFHLimitData selectedFiniteOperatorLayer.toStagePackage)
    (R : DMasterResidualData selectedFiniteOperatorLayer.toStagePackage)
    (h_R_stage_bound :
      ∀ (K : Set ℂ), IsCompact K → K ⊆ Ω →
        ∃ C, 0 ≤ C ∧ ∀ (α : DFiniteStage), ∀ s ∈ K,
          ‖selectedFiniteOperatorLayer.toStagePackage.R_stage α s‖ ≤ C)
    (hσ : 0 ≤ selectedFiniteOperatorLayer.toStagePackage.sigma0)
    (hF_alpha : F.alpha = S.alpha)
    (hR_alpha : R.alpha = S.alpha)
    (M : ZeroMultiplicityData)
    (Zex : ZeroExhaustion)
    (Zpole : ℂ → ℂ)
    (convergence : ZeroPoleLocalUniformConvergenceAPI M Zex Zpole)
    (poleSeriesMeromorphic : ZpoleMeromorphicFromSeriesAPI M Zex Zpole)
    (HarchPackage : HArchPackage)
    (sigmaH : ℝ)
    (h_C_sigma_le :
      (SharpCutoffChosenLengthSharedPackage selectedFiniteOperatorLayer S).sigma0 ≤ sigmaH)
    (h_split :
      ∀ s : ℂ, s ∈ RightHalfPlane sigmaH →
        (SharpCutoffChosenLengthSharedPackage selectedFiniteOperatorLayer S).Bshared s =
          HarchPackage.Harch s - Zpole s)
    (h_pp :
      ∀ W : ZeroWitness,
        HasPrincipalPartAtC Zpole W.s0
          (groupedResidueCoeff M (defaultGroupedPoleClass M W))) :
    RiemannHypothesis :=
  RH_from_raw_inputs h_real_zero_free
    selectedFiniteOperatorLayer S F R h_R_stage_bound hσ hF_alpha hR_alpha
    M Zex Zpole convergence poleSeriesMeromorphic HarchPackage
    sigmaH h_C_sigma_le h_split h_pp

#print axioms RH_from_selected_operator_layer

end
end RHFormalization
EOF
lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tee sel_a.log | grep -e "error" -e "RH_from_selected" -e "depends on axioms" -e "Build completed"
if grep -q "error" sel_a.log; then
  echo "FAILED -> restoring (errors below)"; grep -B2 -A8 "error" sel_a.log | head -40
  cp /tmp/cfe.bak RHFormalization/CurrentFrontierEndpoint.lean
  lake build RHFormalization.CurrentFrontierEndpoint 2>&1 | tail -3; exit 1
fi
lake build 2>&1 | tail -4 | tee sel_root.log
grep -q "Build completed successfully" sel_root.log && tar --exclude='.lake' --exclude='*.bak*' --exclude='*.parked' -czf ~/Downloads/RHFormalization_SELECTED_LAYER.tar.gz . && echo "SNAPSHOT SAVED: SELECTED_LAYER"
