#!/bin/zsh
set -u

OUT=operator_layer_census.txt
: > "$OUT"

echo "===== OPERATOR-LAYER CENSUS: READ ONLY =====" | tee -a "$OUT"
echo "pwd=$(pwd)" | tee -a "$OUT"
ls -d .lake RHFormalization | tee -a "$OUT"

echo "\n===== 1. CURRENT FRONTIER / RAW INPUT MANIFEST =====" | tee -a "$OUT"
grep -rn -B5 -A90 \
  -e "theorem RH_current_frontier" \
  -e "theorem RH_from_raw_inputs" \
  RHFormalization/CurrentFrontierEndpoint.lean \
  | tee -a "$OUT"

echo "\n===== 2. SELECTED FINITE OPERATOR LAYER DEFINITIONS =====" | tee -a "$OUT"
grep -R --line-number --include='*.lean' \
  -B4 -A35 \
  -e "selectedFiniteOperatorLayer" \
  -e "selectedAppendixDFiniteSpikeExtractionWitness" \
  -e "DFiniteStagePackageFromOperatorLayer" \
  RHFormalization \
  | grep -v ".bak" \
  | head -260 \
  | tee -a "$OUT"

echo "\n===== 3. RAW D-SIDE BUILDER / REQUIRED INPUT STRUCTURES =====" | tee -a "$OUT"
grep -R --line-number --include='*.lean' \
  -B4 -A45 \
  -e "buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthWindowFRNoSpeed" \
  -e "structure CanonicalPrimePowerSharpCutoffChosenLength" \
  -e "structure DFHLimitData" \
  -e "structure DMasterResidualData" \
  -e "h_R_stage_bound" \
  -e "hF_alpha" \
  -e "hR_alpha" \
  RHFormalization \
  | grep -v ".bak" \
  | head -320 \
  | tee -a "$OUT"

echo "\n===== 4. SELECTED D-SIDE CANDIDATE MODULES =====" | tee -a "$OUT"
ls RHFormalization/*Selected*.lean RHFormalization/*SharpCutoff*Selected*.lean 2>/dev/null \
  | tee -a "$OUT"

echo "\n===== 5. LEAN #CHECK CENSUS =====" | tee -a "$OUT"
cat > OperatorLayerCensus.lean <<'EOF'
import RHFormalization.CurrentFrontierEndpoint
import RHFormalization.SelectedFiniteOperatorLayer
import RHFormalization.CanonicalPrimePowerSharpCutoffChosenLengthSelectedYFromWindowFRNoSpeed

namespace RHFormalization

noncomputable section

open Complex

#check RH_current_frontier
#check RH_from_raw_inputs

#check selectedFiniteOperatorLayer
#check DFiniteStagePackageFromOperatorLayer
#print DFiniteStagePackageFromOperatorLayer

#check selectedFiniteOperatorLayer.toStagePackage
#check selectedFiniteOperatorLayer.toFiniteCanonicalPrimePowerFormula

#check buildDDetailedConstructionWithOperatorLegalityFromSharpCutoffChosenLengthWindowFRNoSpeed

#check CanonicalPrimePowerSharpCutoffChosenLengthMassEnvelopeData
#check DFHLimitData
#check DMasterResidualData

-- Sanity: selectedFiniteOperatorLayer really has the expected raw operator-layer type.
example : DFiniteStagePackageFromOperatorLayer := selectedFiniteOperatorLayer

end

end RHFormalization
EOF

lake env lean OperatorLayerCensus.lean \
  2>&1 | tee operator_layer_census_lean.log

echo "\n===== 6. RELEVANT LEAN OUTPUT =====" | tee -a "$OUT"
grep -n \
  -e "error:" \
  -e "unknown identifier" \
  -e "unsolved goals" \
  -e "RH_current_frontier" \
  -e "RH_from_raw_inputs" \
  -e "selectedFiniteOperatorLayer" \
  -e "DFiniteStagePackageFromOperatorLayer" \
  -e "buildDDetailedConstructionWithOperatorLegality" \
  -e "CanonicalPrimePowerSharpCutoffChosenLength" \
  -e "DFHLimitData" \
  -e "DMasterResidualData" \
  operator_layer_census_lean.log \
  | tee -a "$OUT" || true

echo "\n===== DONE: paste operator_layer_census.txt and operator_layer_census_lean.log ====="
