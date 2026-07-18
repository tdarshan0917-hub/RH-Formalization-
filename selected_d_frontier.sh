#!/bin/zsh
set -u

echo "===== SELECTED-D FRONTIER: SPECIALIZE RAW INPUTS TO selectedFiniteOperatorLayer ====="
echo "pwd=$(pwd)"
ls -d .lake RHFormalization

echo "===== 1. WRITE SELECTED-D FRONTIER FILE ====="
cat > RHFormalization/CurrentFrontierSelectedD.lean <<'EOF'
import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.SelectedFiniteOperatorLayer

/-!
# RHFormalization.CurrentFrontierSelectedD

Specializes `RH_from_raw_inputs` to the concrete selected finite operator layer.

This removes the raw parameter

  finiteOperatorLayer : DFiniteStagePackageFromOperatorLayer

by using

  selectedFiniteOperatorLayer : DFiniteStagePackageFromOperatorLayer.

Remaining selected-D frontier:
`S`, `F`, `R`, `h_R_stage_bound`, `hσ`, `hF_alpha`, `hR_alpha`.

This file does not claim that the selected D-side analytic limits are closed.
It only specializes the raw manifest to the already-built selected operator layer.
-/

namespace RHFormalization

noncomputable section

open Complex

theorem RH_from_selectedFiniteOperatorLayer_raw_inputs
    (h_real_zero_free :
      ∀ s : ℂ, s.im = 0 → 0 < s.re → s.re < 1 → riemannZeta s ≠ 0)
    (S : CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData selectedFiniteOperatorLayer)
    (F : DFHLimitData selectedFiniteOperatorLayer.toStagePackage)
    (R : DMasterResidualData selectedFiniteOperatorLayer.toStagePackage)
    (h_R_stage_bound :
      ∀ (K : Set ℂ),
        IsCompact K →
          K ⊆ Ω →
            ∃ C, 0 ≤ C ∧
              ∀ (α : DFiniteStage), ∀ s ∈ K,
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
      ∀ s ∈ RightHalfPlane sigmaH,
        (SharpCutoffChosenLengthSharedPackage selectedFiniteOperatorLayer S).Bshared s =
          HarchPackage.Harch s - Zpole s)
    (h_pp :
      ∀ (W : ZeroWitness),
        HasPrincipalPartAtC Zpole W.s0
          (groupedResidueCoeff M (defaultGroupedPoleClass M W))) :
    RiemannHypothesis := by
  exact
    RH_from_raw_inputs
      h_real_zero_free
      selectedFiniteOperatorLayer
      S
      F
      R
      h_R_stage_bound
      hσ
      hF_alpha
      hR_alpha
      M
      Zex
      Zpole
      convergence
      poleSeriesMeromorphic
      HarchPackage
      sigmaH
      h_C_sigma_le
      h_split
      h_pp

#print axioms RH_from_selectedFiniteOperatorLayer_raw_inputs

end

end RHFormalization
EOF

echo "===== 2. BUILD SELECTED-D FRONTIER ONLY ====="
lake build RHFormalization.CurrentFrontierSelectedD \
  2>&1 | tee selected_d_frontier_build.log || true

echo "===== 3. SEARCH FOR PROVIDERS OF REMAINING SELECTED-D INPUTS ====="
grep -R --line-number --include='*.lean' \
  -E "CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData selectedFiniteOperatorLayer|DFHLimitData selectedFiniteOperatorLayer.toStagePackage|DMasterResidualData selectedFiniteOperatorLayer.toStagePackage|selected.*SharpCutoff|selected.*MassEnvelope|selected.*DFH|selected.*DMaster|selected.*Residual|selected.*Limit|h_R_stage_bound|hF_alpha|hR_alpha" \
  RHFormalization \
  | grep -v ".bak" \
  | tee selected_d_provider_search.log || true

echo "===== 4. LEAN SHAPE PROBE FOR REMAINING D INPUTS ====="
cat > SelectedDProviderShapeProbe.lean <<'EOF'
import RHFormalization.CurrentFrontierSelectedD
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFRNoSpeed

namespace RHFormalization

noncomputable section

#check selectedFiniteOperatorLayer
#check RH_from_selectedFiniteOperatorLayer_raw_inputs

#check CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData selectedFiniteOperatorLayer
#print CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData

#check DFHLimitData selectedFiniteOperatorLayer.toStagePackage
#print DFHLimitData

#check DMasterResidualData selectedFiniteOperatorLayer.toStagePackage
#print DMasterResidualData

#check buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthWindowFRNoSpeed

end

end RHFormalization
EOF

lake env lean SelectedDProviderShapeProbe.lean \
  2>&1 | tee selected_d_provider_shape_probe.log || true

echo "===== 5. RELEVANT OUTPUT ONLY ====="
grep -n \
  -e "error:" \
  -e "unknown identifier" \
  -e "unsolved goals" \
  -e "sorryAx" \
  -e "RH_from_selectedFiniteOperatorLayer_raw_inputs" \
  -e "selectedFiniteOperatorLayer" \
  -e "CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData" \
  -e "DFHLimitData" \
  -e "DMasterResidualData" \
  -e "h_R_stage_bound" \
  -e "hF_alpha" \
  -e "hR_alpha" \
  -e "depends on axioms" \
  -e "Build completed" \
  selected_d_frontier_build.log \
  selected_d_provider_search.log \
  selected_d_provider_shape_probe.log || true
