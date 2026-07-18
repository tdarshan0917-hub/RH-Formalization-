#!/bin/zsh
echo "===== 1. HasGenuinePole: exact definition ====="
grep -rn -B4 -A10 "def HasGenuinePole\|abbrev HasGenuinePole\|structure HasGenuinePole" RHFormalization/*.lean | head -20
echo "===== 2. HasPrincipalPartAtC: exact definition ====="
grep -rn -B4 -A12 "def HasPrincipalPartAtC\|abbrev HasPrincipalPartAtC\|structure HasPrincipalPartAtC" RHFormalization/*.lean | head -22
echo "===== 3. groupedResidueCoeff: definition + any nonzero lemma ====="
grep -rn -B2 -A10 "def groupedResidueCoeff" RHFormalization/*.lean | head -16
grep -rn "groupedResidueCoeff" RHFormalization/*.lean | grep -e "ne_zero" -e "≠ 0" -e "pos" | head -8
echo "===== 4. is PrincipalPartImpliesGenuinePoleAPI consumed in the live spine? ====="
grep -rn "PrincipalPartImpliesGenuinePoleAPI" RHFormalization/*.lean | grep -v "HSidePoleWitness.lean" | head -10
echo "===== 5. any existing default/discharge attempt ====="
grep -rn "defaultPrincipalPart\|buildPrincipalPartImplies" RHFormalization/*.lean | head -8
echo "===== 6. Mathlib hinge battery ====="
cat > PPGPBattery.lean <<'EOF'
import RHFormalization.HSidePoleWitness
open Filter Topology
#check @tendsto_cobounded_of_meromorphicOrderAt_neg
#check @meromorphicOrderAt_eq_int_iff
#check @AnalyticAt.meromorphicOrderAt_eq
#check @MeromorphicAt.tendsto_cobounded_iff_meromorphicOrderAt_neg
EOF
lake env lean PPGPBattery.lean 2>&1
